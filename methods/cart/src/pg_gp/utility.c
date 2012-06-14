/*
 *
 * @file utility.c
 *
 * @brief Utility functions written in C for madlib.
 *
 * @date June 1, 2012
 */

#include <float.h>
#include <math.h>
#include <stdlib.h>
#include <time.h>
#include <ctype.h>

#include "postgres.h"
#include "fmgr.h"
#include "utils/array.h"
#include "utils/lsyscache.h"
#include "utils/syscache.h"
#include "utils/builtins.h"
#include "utils/fmgroids.h"
#include "utils/tqual.h"
#include "utils/typcache.h"
#include "utils/formatting.h"
#include "catalog/pg_type.h"
#include "catalog/namespace.h"
#include "catalog/indexing.h"
#include "catalog/pg_class.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_proc.h"
#include "catalog/pg_ts_config.h"
#include "catalog/pg_ts_dict.h"
#include "nodes/execnodes.h"
#include "nodes/nodes.h"
#include "miscadmin.h"
#include "funcapi.h"

#ifndef NO_PG_MODULE_MAGIC
PG_MODULE_MAGIC;
#endif

#define DOT_CHAR '.'
#define COMMA_CHAR ','
#define SPACE_CHAR ' '

#define do_assert(condition, message) \
			do { \
				if (!(condition)) \
					ereport(ERROR, \
							(errcode(ERRCODE_RAISE_EXCEPTION), \
							 errmsg(message) \
							) \
						   ); \
			} while (0)

#define do_assert_value(condition, message, value)          \
			do { \
				if (!(condition)) \
					ereport(ERROR, \
							(errcode(ERRCODE_RAISE_EXCEPTION), \
							 errmsg(message, (value))          \
							) \
						   ); \
			} while (0)

/*
 * Catenate t1 and t2 of text*.
 *
 * Arguments can be in short-header form, but not compressed or out-of-line
 */
static text* text_catenate_internal(text *t1, text *t2)
{
	text	   *result;
	int			len1,
				len2,
				len;
	char	   *ptr;

	len1 = VARSIZE_ANY_EXHDR(t1);
	len2 = VARSIZE_ANY_EXHDR(t2);

	/* paranoia ... probably should throw error instead? */
	if (len1 < 0)
		len1 = 0;
	if (len2 < 0)
		len2 = 0;

	len = len1 + len2 + VARHDRSZ;
	result = (text *) palloc(len);

	/* Set size of result string... */
	SET_VARSIZE(result, len);

	/* Fill data field of result string... */
	ptr = VARDATA(result);
	if (len1 > 0)
		memcpy(ptr, VARDATA_ANY(t1), len1);
	if (len2 > 0)
		memcpy(ptr + len1, VARDATA_ANY(t2), len2);

	return result;
}

static bool table_exists_internal(text* full_table_name)
{
    List           *names;
    Oid             relid;

    names = textToQualifiedNameList(full_table_name);
    relid = RangeVarGetRelid(makeRangeVarFromNameList(names), true);
    
    return OidIsValid(relid); 
}

/*
 * Remove the longest string consisting only SPACE_CHAR
 * from the start and end of input string
 */
static char* btrim_internal(char* string, int* string_len)
{
    if (string_len > 0)
    {
        /* remove left spaces */
        while (string_len > 0)
        {
            if (*string == SPACE_CHAR)
            {
                string++;
                (*string_len)--;
            }
            else
                break;
        }
        /* remove right spaces */
        while (string_len > 0)
        {
            if (string[*string_len - 1] == SPACE_CHAR)
            {
                (*string_len)--;
            }
            else
                break;
        }
    }
    return string;
}

/*
 * @brief Cast any value to text.
 *
 * @param val	A value with any specific type.
 * @return The text format string for the value.
 *
 * @note Greenplum doesn't support boolean to text casting.
 *
 */
Datum to_char(PG_FUNCTION_ARGS)
{
    bool        input;
    char       *result;
    
    if (PG_ARGISNULL(0))
        PG_RETURN_NULL();
    
    input = PG_GETARG_BOOL(0);
    
    if (input)
        result = "t";
    else
        result = "f";
    

    PG_RETURN_TEXT_P(cstring_to_text(result));
}
PG_FUNCTION_INFO_V1(to_char);

/*
 * @brief Cast regclass to text. 
 *        
 * @param rc	The regclass of the table.
 * @return The text representation for the regclass.
 *
 */
Datum regclass_to_text(PG_FUNCTION_ARGS)
{
    Oid         classid = PG_GETARG_OID(0);
    char       *result;
    HeapTuple   classtup;
 
    if (classid == InvalidOid)
    {
        result = pstrdup("-");
        PG_RETURN_CSTRING(result);
    }
 
    classtup = SearchSysCache1(RELOID, ObjectIdGetDatum(classid));
 
    if (HeapTupleIsValid(classtup))
    {
        Form_pg_class classform = (Form_pg_class) GETSTRUCT(classtup);
        char       *classname = NameStr(classform->relname);
 
        /*
         * In bootstrap mode, skip the fancy namespace stuff and just return
         * the class name.  (This path is only needed for debugging output
         * anyway.)
         */
        if (IsBootstrapProcessingMode())
            result = pstrdup(classname);
        else
        {
            char       *nspname;
            
            /* Would this class be found by regclassin? If not, qualify it. */
            if (RelationIsVisible(classid))
                nspname = NULL;
            else
                nspname = get_namespace_name(classform->relnamespace);
            
            result = quote_qualified_identifier(nspname, classname);
        }
        
        ReleaseSysCache(classtup);
    }
    else
    {
        /* If OID doesn't match any pg_class entry, return it numerically */
        result = (char *) palloc(NAMEDATALEN);
        snprintf(result, NAMEDATALEN, "%u", classid);
    }
    
    PG_RETURN_TEXT_P(cstring_to_text(result));
}
PG_FUNCTION_INFO_V1(regclass_to_text);

/*
 * @brief Raise exception if the condition is false.
 *
 * @param condition		The assert condition.
 * @param reason		The reason string displayed when assert failure.
 *
 */
void assert(PG_FUNCTION_ARGS)
{
    bool        condition;
    text       *reason;

    condition = PG_GETARG_BOOL(0);
    reason = PG_GETARG_TEXT_PP(1);
    
    do_assert(condition,
              text_to_cstring(reason));
              
}
PG_FUNCTION_INFO_V1(assert);

/*
 * @brief This function checks whether the specified table exists or not.
 *
 * @param input    The table name to be tested.
 *
 * @return A boolean value indicating whether the table exists or not.
 */
Datum table_exists(PG_FUNCTION_ARGS)
{
    text           *input;

    if (PG_ARGISNULL(0))
        PG_RETURN_BOOL(false);

    input = PG_GETARG_TEXT_PP(0);
    
    PG_RETURN_BOOL(table_exists_internal(input));
}
PG_FUNCTION_INFO_V1(table_exists);

/*
 * @brief Test if the specified column exists or not.
 *
 * @param full_table_name	The full table name.
 * @param column_name    The column name.
 * @return True if the column exists, otherwise return false.
 *
 */
Datum column_exists(PG_FUNCTION_ARGS)
{
    text              *full_table_name;
    text              *column_name;
    List              *names;
    Oid                relid;
    Relation           rel;
    TupleDesc          td;
    int                i;
    bool               existence = false;

    if (PG_ARGISNULL(0))
        PG_RETURN_BOOL(false);
    if (PG_ARGISNULL(1))
        PG_RETURN_BOOL(false);

    full_table_name = PG_GETARG_TEXT_PP(0);
    column_name = PG_GETARG_TEXT_PP(1);
    
    names = textToQualifiedNameList(full_table_name);
    relid = RangeVarGetRelid(makeRangeVarFromNameList(names), true);

    do_assert_value(OidIsValid(relid),
                    "table \"%s\" does not exist",
                    (text_to_cstring(full_table_name)));
    
    /* open the relation to get info */
    rel = relation_open(relid, AccessShareLock);
    td = RelationGetDescr(rel);

    for (i = 0; i < td->natts; ++i)
    {
        if (strncmp(NameStr((td->attrs[i])->attname), text_to_cstring(column_name), NAMEDATALEN) == 0)
        {
            existence = true;
            break;
        }
  
    }

    relation_close(rel, AccessShareLock);
    
    PG_RETURN_BOOL(existence);
}
PG_FUNCTION_INFO_V1(column_exists);

/*
 * @brief Assert if the specified table exists or not.
 *
 * @param full_table_name	The full table name.
 *
 */
void assert_table(PG_FUNCTION_ARGS)
{
    text        *full_table_name;
    bool         existence;
    text        *err_msg;
    text        *msg1;
    text        *msg2;

    full_table_name = PG_GETARG_TEXT_PP(0);
    existence = PG_GETARG_BOOL(1);

    err_msg = cstring_to_text("assertion failure. Table: ");
    msg1 = cstring_to_text(" does not exist");
    msg2 = cstring_to_text(" already exist");
    err_msg = text_catenate_internal(err_msg, full_table_name);

    if (existence)
        err_msg = text_catenate_internal(err_msg, msg1);
    else
        err_msg = text_catenate_internal(err_msg, msg2);

    do_assert((table_exists_internal(full_table_name) == existence),
              text_to_cstring(err_msg));
}
PG_FUNCTION_INFO_V1(assert_table);

/*
 * @brief  Strip the schema name from the full table name.
 *
 * @param full_table_name   The full table name. 
 *
 * @return The table name without schema name.
 *
 */
Datum strip_schema_name(PG_FUNCTION_ARGS)
{
    text      *full_table_name;
    List      *names;
    RangeVar  *rel;

    do_assert(!PG_ARGISNULL(0),
              "Table name should not be null");

    full_table_name = PG_GETARG_TEXT_PP(0);
    names = textToQualifiedNameList(full_table_name);
    rel = makeRangeVarFromNameList(names);

    PG_RETURN_TEXT_P(cstring_to_text(rel->relname));
}
PG_FUNCTION_INFO_V1(strip_schema_name);

/*
 * @brief Get the schema name from a full table name.
 *        if there is no schema name in the full table name, then
 *        if the table exists, we return the schema name from catalog
 *        else the current schema name,
 *        else return the schema name from the full table name directly.
 *
 * @param full_table_name   The full table name.
 *
 * @return The schema name of the table.
 *
 */
Datum get_schema_name(PG_FUNCTION_ARGS)
{
    text      *full_table_name;
    List      *names;
    RangeVar  *rel;
    char      *nspname;
    List      *search_path = fetch_search_path(false);

    do_assert(!PG_ARGISNULL(0),
              "Table name should not be null"
              );

    full_table_name = PG_GETARG_TEXT_PP(0);
    names = textToQualifiedNameList(full_table_name);
    rel = makeRangeVarFromNameList(names);

    if (rel->schemaname)
        /* get schema name directly */
        PG_RETURN_TEXT_P(cstring_to_text(rel->schemaname));
    else
    {
        /* table exists */
        if (OidIsValid(rel))
        {
            /* might have several search paths, table is in one of them */
            Oid        relid;
            Oid        nspid;
            
            relid = RelnameGetRelid(rel->relname);
            nspid = get_rel_namespace(relid);
            nspname = get_namespace_name(nspid);

            if (nspname)
                PG_RETURN_TEXT_P(cstring_to_text(nspname));
        }
        
        /*
         * Table exists, but not in provided search paths
         * Return current namespace instead
         */
        if (search_path == NIL)
            PG_RETURN_NULL();
        nspname = get_namespace_name(linitial_oid(search_path));
        list_free(search_path);
        if (!nspname)
            PG_RETURN_NULL();		/* recently-deleted namespace? */
        PG_RETURN_TEXT_P(cstring_to_text(nspname));
    }
}
PG_FUNCTION_INFO_V1(get_schema_name);

/*
 * @brief Convert a string with delimiter ',' to an array. 
 *        Each element in the array is trimed from the start
 *        and end using a space.
 *
 * @param csv_str   The string with elements delimited by ','.
 *
 * @return The splitting string array.
 *
 * @note If the input string is NULL or an empty string
 *       after trimmed with ' ', then NULL will be returned.
 *
 */
Datum csvstr_to_array(PG_FUNCTION_ARGS)
{
    text            *inputstring;
    int              inputstring_len;
    char            *start_ptr = NULL;
    char            *str = NULL;
    char            *orig_str = NULL;
    int              orig_str_len;
    int              posn = 0;
    int              chunk_len = 0;
    text            *result_text;
    ArrayBuildState *astate = NULL;
    
    if (PG_ARGISNULL(0))
        PG_RETURN_NULL();

    inputstring = PG_GETARG_TEXT_PP(0);
    inputstring_len = VARSIZE_ANY_EXHDR(inputstring);

    /* return empty array for empty input string */
    if (inputstring_len < 1)
        PG_RETURN_ARRAYTYPE_P(construct_empty_array(TEXTOID));

    /* start_ptr points to the start_posn'th character of inputstring */
    orig_str = str_tolower(VARDATA_ANY(inputstring),
                           inputstring_len,
                           PG_GET_COLLATION());
    orig_str_len = strlen(orig_str);
    str = orig_str;
    start_ptr = str;
    
    for (; str != NULL && *str != '\0'; ++str)
    {
        if (*str == COMMA_CHAR)
        {
            /* must build a temp text datum to pass to accumArrayResult */
            start_ptr = btrim_internal(start_ptr, &chunk_len);
            result_text = cstring_to_text_with_len(start_ptr, chunk_len);
            /* stash away this field */
			astate = accumArrayResult(astate,
									  PointerGetDatum(result_text),
									  false,
									  TEXTOID,
									  CurrentMemoryContext);
            pfree(result_text);
            chunk_len = 0;
            start_ptr = str + 1;
            posn = start_ptr - VARDATA_ANY(inputstring);
        }
        else
            chunk_len++;
    }

    /* field after the last COMMA_CHAR */
    start_ptr = btrim_internal(start_ptr, &chunk_len);
    result_text = cstring_to_text_with_len(start_ptr, chunk_len);
    astate = accumArrayResult(astate,
                              PointerGetDatum(result_text),
                              false,
                              TEXTOID,
                              CurrentMemoryContext);
    pfree(result_text);
    pfree(orig_str);
    
    PG_RETURN_ARRAYTYPE_P(makeArrayResult(astate,
										  CurrentMemoryContext));
}
PG_FUNCTION_INFO_V1(csvstr_to_array);

/*
 * @brief Get the number of columns for a given table.
 *
 * @param table_name    The full table name.      
 * 
 * @return The number of columns in the given table. 
 *
 */
Datum num_of_columns(PG_FUNCTION_ARGS)
{
    text            *table_name;
    List            *names;
    Oid              relid;
    HeapTuple        relTup;
    Form_pg_class    relForm;
    int              result;

    do_assert(!PG_ARGISNULL(0),
              "Table name should not be null");

    table_name = PG_GETARG_TEXT_PP(0);
    names = textToQualifiedNameList(table_name);
    relid = RangeVarGetRelid(makeRangeVarFromNameList(names), true);

    /* check whether table exists */
    do_assert_value(OidIsValid(relid),
              "table \"%s\"does not exist",
              (text_to_cstring(table_name)));

    relTup = SearchSysCache1(RELOID,
							 ObjectIdGetDatum(relid));
    relForm = (Form_pg_class) GETSTRUCT(relTup);
    result = relForm->relnatts;

    ReleaseSysCache(relTup);

    PG_RETURN_INT32(result);
}
PG_FUNCTION_INFO_V1(num_of_columns);

/*
 * @brief Test if each element in the given array is a column of the table.
 *
 * @param column_names      The array containing the columns to be tested.
 * @param table_name        The full table name.
 * 
 * @return True if each element of column_names is a column of the table.
 *
 */
Datum columns_in_table(PG_FUNCTION_ARGS)
{
    ArrayType         *column_names;
    text              *full_table_name;
    List              *names;
    Oid                relid;
    Relation           rel;
    TupleDesc          td;
    bool               existence;
    bool               all_in;
    int                i;
    int                j;
    int                ndims;
    int                nitems;
    int               *dims;
    int                typlen;
    bool               typbyval;
    char               typalign;
    char              *ptr;
    Oid                element_type;
    TypeCacheEntry    *typentry;
    Datum              elt;

    if (PG_ARGISNULL(0))
        PG_RETURN_BOOL(false);
    if (PG_ARGISNULL(1))
        PG_RETURN_BOOL(false);


    full_table_name = PG_GETARG_TEXT_PP(0);
    column_names = PG_GETARG_ARRAYTYPE_P(1);

    ndims = ARR_NDIM(column_names);
    element_type = ARR_ELEMTYPE(column_names);

    if (ndims == 0)
        PG_RETURN_BOOL(false);

    dims = ARR_DIMS(column_names);
    ptr = ARR_DATA_PTR(column_names);
    nitems = ArrayGetNItems(ndims, dims);

    /*
	 * We arrange to look up the equality function only once per series of
	 * calls, assuming the element type doesn't change underneath us.  The
	 * typcache is used so that we have no memory leakage when being used as
	 * an index support function.
	 */
    typentry = (TypeCacheEntry *) fcinfo->flinfo->fn_extra;
    if (typentry == NULL ||	typentry->type_id != element_type)
    {
        typentry = lookup_type_cache(element_type, TYPECACHE_EQ_OPR_FINFO);
        fcinfo->flinfo->fn_extra = (void *) typentry;
    }
    typlen = typentry->typlen;
    typbyval = typentry->typbyval;
    typalign = typentry->typalign;
    
    names = textToQualifiedNameList(full_table_name);
    relid = RangeVarGetRelid(makeRangeVarFromNameList(names), true);

    do_assert_value(OidIsValid(relid),
                    "table \"%s\" does not exist",
                    (text_to_cstring(full_table_name)));
    
    /* open the relation to get info */
    rel = relation_open(relid, AccessShareLock);
    td = RelationGetDescr(rel);

    /* Compare each column name got from input and from tuple descriptor */
    all_in = true;
    for (i = 0; i < nitems; ++i)
    {
        elt = fetch_att(ptr, typbyval, typlen);
        ptr = att_addlength_pointer(ptr, typlen, ptr);
        ptr = (char *) att_align_nominal(ptr, typalign);
        existence = false;

        for (j = 0; j < td->natts; ++j)
        {
            if (strncmp(NameStr((td->attrs[j])->attname), text_to_cstring(DatumGetTextPP(elt)), NAMEDATALEN) == 0)
            {
                existence = true;
                break;
            }
        }
        if (existence == false)
        {
            all_in = false;
            break;
        }
    }
    
    relation_close(rel, AccessShareLock);
    PG_FREE_IF_COPY(column_names, 0);

    PG_RETURN_BOOL(all_in);
}
PG_FUNCTION_INFO_V1(columns_in_table);

Datum mad_array_search(PG_FUNCTION_ARGS)
{
    bool            result;
    Datum           find;
    Datum           elt;
    ArrayType      *arr;
    Oid             collation;
    bool            contains;
    Oid             element_type;
    TypeCacheEntry *typentry;
    int             nitems;
    int             typlen;
    bool            typbyval;
    char            typalign;
    char           *ptr;
    int             i;
    FunctionCallInfoData  locfcinfo;

    if (PG_ARGISNULL(0))
        PG_RETURN_BOOL(false);
    if (PG_ARGISNULL(1))
        PG_RETURN_BOOL(false);

    find = PG_GETARG_DATUM(0);
    arr = PG_GETARG_ARRAYTYPE_P(1);
    collation = PG_GET_COLLATION();

    /* Check type, only compare find and arr element of the same type */
    element_type = ARR_ELEMTYPE(arr);

    /* We don't use here because errcode are different */
    if (element_type != get_fn_expr_argtype(fcinfo->flinfo, 1))
    {
        ereport(ERROR,
				(errcode(ERRCODE_DATATYPE_MISMATCH),
				 errmsg("cannot compare arrays of different element types")));
    }

    /*
	 * We arrange to look up the equality function only once per series of
	 * calls, assuming the element type doesn't change underneath us.  The
	 * typcache is used so that we have no memory leakage when being used as
	 * an index support function.
	 */
    typentry = (TypeCacheEntry *) fcinfo->flinfo->fn_extra;
    if (typentry == NULL || typentry->type_id != element_type)
	{
		typentry = lookup_type_cache(element_type, TYPECACHE_EQ_OPR_FINFO);
		if (!OidIsValid(typentry->eq_opr_finfo.fn_oid))
			ereport(ERROR,
					(errcode(ERRCODE_UNDEFINED_FUNCTION),
                     errmsg("could not identify an equality operator for type %s",
                            format_type_be(element_type))));
		fcinfo->flinfo->fn_extra = (void *) typentry;
	}
	typlen = typentry->typlen;
	typbyval = typentry->typbyval;
	typalign = typentry->typalign;

	/* Apply the comparison operator to each pair of array elements. */
	InitFunctionCallInfoData(locfcinfo, &typentry->eq_opr_finfo, 2, collation, NULL, NULL);

    /* Loop over source array */
    nitems = ArrayGetNItems(ARR_NDIM(arr), ARR_DIMS(arr));
    ptr = ARR_DATA_PTR(arr);
    contains = false;
    
    for (i = 0; i < nitems; ++i)
    {
        elog(WARNING, text_to_cstring(DatumGetTextPP(find)));

        elt = fetch_att(ptr, typbyval, typlen);
        ptr = att_addlength_pointer(ptr, typlen, ptr);
        ptr = (char *) att_align_nominal(ptr, typalign);

        /* Apply the operator to the element pair */
        locfcinfo.arg[0] = find;
        locfcinfo.arg[1] = elt;
        locfcinfo.argnull[0] = false;
        locfcinfo.argnull[1] = false;
        locfcinfo.isnull = false;
        contains = DatumGetBool(FunctionCallInvoke(&locfcinfo));
        if (contains)
            break;
    }
    
    PG_FREE_IF_COPY(arr, 1);

    PG_RETURN_BOOL(contains);
}
PG_FUNCTION_INFO_V1(array_search);
