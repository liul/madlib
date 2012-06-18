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

#define mad_do_assert(condition, message)               \
    do {                                                \
        if (!(condition))                               \
            ereport(ERROR,                              \
                    (errcode(ERRCODE_RAISE_EXCEPTION),  \
                     errmsg(message)                    \
                     )                                  \
                    );                                  \
    } while (0)

#define mad_do_assert_value(condition, message, value)  \
    do {                                                \
        if (!(condition))                               \
            ereport(ERROR,                              \
                    (errcode(ERRCODE_RAISE_EXCEPTION),  \
                     errmsg(message, (value))           \
                     )                                  \
                    );                                  \
    } while (0)

/* 
 * This function checks whether the specified table exists or not.
 */
static bool table_exists_internal(text* full_table_name)
{
    List   *names = textToQualifiedNameList(full_table_name);
    Oid     relid = RangeVarGetRelid(makeRangeVarFromNameList(names), true);

    return OidIsValid(relid); 
}

/*
 * @brief Use % as the delimiter to split the given string. The char '\' is used
 *        to escape %. We will not change the default behavior of '\' in PG/GP.
 *        For example, assume the given string is E"\\\\\\\\\\%123%123". Then it only
 *        has one delimiter; the string will be split to two substrings:
 *        E'\\\\\\\\\\%123' and '123'; the position array size is 1, where position[0] = 9;
 *        ; (*len) = 13.
 *
 * @param str       The string to be split.
 * @param position  An array to store the position of each un-escaped % in the string.
 * @param num_pos   The expected number of un-escaped %s in the string.
 * @param len       The length of the string. It doesn't include the terminal.
 *
 * @return The position array which records the positions of all un-escaped %s
 *         in the give string.
 *
 * @note If the number of %s in the string is not equal to the expected number,
 *       we will report error via elog.
 */
static
int*
mad_split_string
	(
	char *str,
	int  *position,
    int  num_pos,
	int  *len
	)
{
	int i 				  = 0;
	int j 				  = 0;
	
	/* the number of the escape chars which occur continuously */
	int num_cont_escapes  = 0;

	for(; str != NULL && *str != '\0'; ++str, ++j)
	{
		if ('%' == *str)
		{
			/*
			 * if the number of the escapes is even number
			 * then no need to escape. Otherwise escape the delimiter
			 */
			if (!(num_cont_escapes & 0x01))
			{
            	mad_do_assert
	            	(
                        i < num_pos,
                        "the number of the elements in the array is less than "
                        "the format string expects."
                    );

				/*  convert the char '%' to '\0' */
				position[i++] 	= j;
				*str 			= '\0';
			}

			/* reset the number of the continuous escape chars */
			num_cont_escapes = 0;
		}
		else if ('\\' == *str)
		{
			/* increase the number of continuous escape chars */
			++num_cont_escapes;
		}
		else
		{
			/* reset the number of the continuous escape chars */
			num_cont_escapes = 0;
		}
	}

	*len      = j;
	
    mad_do_assert
        (
            i == num_pos,
            "the number of the elements in the array is greater than "
            "the format string expects. "
        );

	return position;
}


/*
 * @brief Change all occurrences of '\%' in the give string to '%'. Our split
 *        method will ensure that the char immediately before a '%' must be a '\'.
 *        We traverse the string from left to right, if we meet a '%', then
 *        move the substring after the current '\%' to the right place until
 *        we meet next '\%' or the '\0'. Finally, set the terminal symbol for
 *        the replaced string.
 *
 * @param str   The null terminated string to be escaped.
 *              The char immediately before a '%' must be a '\'.
 *
 * @return The new string with \% changed to %.
 *
 */
static
char*
mad_escape_pct_sym
	(
	char *str
	)
{
	int num_escapes		  = 0;

	/* remember the start address of the escaped string */
	char *p_new_string 	 = str;

	while(str != NULL && *str != '\0')
	{
		if ('%' == *str)
		{
			mad_do_assert_value
				(
					(str - 1) && ('\\' == *(str - 1)),
					"The char immediately before a %s must be a \\",
					"%"
				);

			/*
			 * The char immediately before % is \
			 * increase the number of escape chars
			 */
			++num_escapes;
			do
			{
				/*
				 * move the string which is between the current "\%"
				 * and next "\%"
				 */
				*(str - num_escapes) = *str;
				++str;
			} while (str != NULL && *str != '\0' && *str != '%');
		}
		else
		{
			++str;
		}
	}

	/* if there is no escapes, then set the end symbol for the string */
	if (num_escapes > 0)
		*(str - num_escapes) = '\0';

	return p_new_string;
}

/*
 * This is the guts of mad_format. Takes a cstring fmt and cstring array
 * arrgs_array and build the query string.
 */
static text* mad_format_internal(char *fmt, char **args_array, int nargs)
{
    int            *position  = (int *) palloc0(nargs * sizeof(int));
    int             last_posn = 0;
    int             fmt_len   = 0;
    int             i         = 0;
    char           *ptr       = NULL;
    StringInfoData  buf;
    
    /*
	 * split the format string, so that later we can replace the delimiters
	 * with the given arguments
	 */
	mad_split_string(fmt, position, nargs, &fmt_len);
    initStringInfo(&buf);

    for (i = 0; i < nargs; i++)
    {
        /* There is no string befor the delimiter. */
        if (last_posn == position[i])
        {
            appendStringInfo(&buf, "%s", DatumGetCString(args_array[i]));
            ++last_posn;
        }
        else
        {
            /*
			 * has a string before the delimiter
			 * we replace "\%" in the string to "%", since "%" is escaped
			 * then combine the string and argument string together
			 */
            appendStringInfo
				(
                 &buf,
                 "%s%s",
                 mad_escape_pct_sym(fmt + last_posn),
                 args_array[i]
                 );

			last_posn = position[i] + 1;
        }
    }
    /* The last char in the format string is not delimiter. */
	if (last_posn < fmt_len)
		appendStringInfo(&buf, "%s", fmt + last_posn);

    pfree(position);
    
    return cstring_to_text_with_len(buf.data, buf.len);
}

/*
 * @brief Cast regclass to text. 
 *        
 * @param rc	The regclass of the table.
 * @return The text representation for the regclass.
 *
 */
Datum mad_regclass_to_text(PG_FUNCTION_ARGS)
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
        Form_pg_class  classform = (Form_pg_class) GETSTRUCT(classtup);
        char          *classname = NameStr(classform->relname);
        char          *nspname;
        
        /* Would this class be found by regclassin? If not, qualify it. */
        if (RelationIsVisible(classid))
            nspname = NULL;
        else
            nspname = get_namespace_name(classform->relnamespace);
            
        result = quote_qualified_identifier(nspname, classname);
           
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
PG_FUNCTION_INFO_V1(mad_regclass_to_text);

/*
 * @brief Raise exception if the condition is false.
 *
 * @param condition		The assert condition.
 * @param reason		The reason string displayed when assert failure.
 *
 */
void mad_assert(PG_FUNCTION_ARGS)
{
    bool    condition = PG_GETARG_BOOL(0);
    text   *reason    = PG_GETARG_TEXT_PP(1);
    
    mad_do_assert(condition,
                  text_to_cstring(reason));
}
PG_FUNCTION_INFO_V1(mad_assert);

/*
 * @brief This function checks whether the specified table exists or not.
 *
 * @param input    The table name to be tested.
 *
 * @return A boolean value indicating whether the table exists or not.
 */
Datum mad_table_exists(PG_FUNCTION_ARGS)
{
    text           *input;

    if (PG_ARGISNULL(0))
        PG_RETURN_BOOL(false);

    input = PG_GETARG_TEXT_PP(0);
    
    PG_RETURN_BOOL(table_exists_internal(input));
}
PG_FUNCTION_INFO_V1(mad_table_exists);

/*
 * @brief Test if the specified column exists or not.
 *
 * @param full_table_name	The full table name.
 * @param column_name    The column name.
 * @return True if the column exists, otherwise return false.
 *
 */
Datum mad_column_exists(PG_FUNCTION_ARGS)
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

    mad_do_assert_value
        (
            OidIsValid(relid),
            "table \"%s\" does not exist",
            (text_to_cstring(full_table_name))
        );
    
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
PG_FUNCTION_INFO_V1(mad_column_exists);

/*
 * @brief Assert if the specified table exists or not.
 *
 * @param full_table_name	The full table name.
 *
 */
void mad_assert_table(PG_FUNCTION_ARGS)
{
    text        *full_table_name;
    bool         existence;

    mad_do_assert
        (
            !PG_ARGISNULL(0),
            "Table name should not be null"
        );
    mad_do_assert
        (
            !PG_ARGISNULL(1),
            "Existence should not be null"
        );
    
    full_table_name = PG_GETARG_TEXT_PP(0);
    existence = PG_GETARG_BOOL(1);

    if (existence)
        mad_do_assert_value
            (
                (table_exists_internal(full_table_name) == existence),
                "Assertion failure. Talbe \"%s\" does not exit.",
                (text_to_cstring(full_table_name))
            );
    else
        mad_do_assert_value
            (
                (table_exists_internal(full_table_name) == existence),
                "Assertion failure. Talbe \"%s\" already exit.",
                (text_to_cstring(full_table_name))
            );
}
PG_FUNCTION_INFO_V1(mad_assert_table);

/*
 * @brief  Strip the schema name from the full table name.
 *
 * @param full_table_name   The full table name. 
 *
 * @return The table name without schema name.
 *
 */
Datum mad_strip_schema_name(PG_FUNCTION_ARGS)
{
    text      *full_table_name;
    List      *names;
    RangeVar  *rel;

    mad_do_assert
        (
            !PG_ARGISNULL(0),
            "Table name should not be null"
        );

    full_table_name = PG_GETARG_TEXT_PP(0);
    names = textToQualifiedNameList(full_table_name);
    rel = makeRangeVarFromNameList(names);

    PG_RETURN_TEXT_P(cstring_to_text(rel->relname));
}
PG_FUNCTION_INFO_V1(mad_strip_schema_name);

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
Datum mad_get_schema_name(PG_FUNCTION_ARGS)
{
    text      *full_table_name;
    List      *names;
    RangeVar  *rel;
    char      *nspname;
    List      *search_path = fetch_search_path(false);

    mad_do_assert
        (
            !PG_ARGISNULL(0),
            "Table name should not be null"
        );

    full_table_name = PG_GETARG_TEXT_PP(0);
    names           = textToQualifiedNameList(full_table_name);
    rel             = makeRangeVarFromNameList(names);

    if (rel->schemaname)
    {
        /* get schema name directly */
        PG_RETURN_TEXT_P(cstring_to_text(rel->schemaname));
    }
    else
    {
        /* table exists */
        if (OidIsValid(rel))
        {
            /* might have several search paths, table is in one of them */
            Oid    relid = RelnameGetRelid(rel->relname);
            Oid    nspid = get_rel_namespace(relid);

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
            PG_RETURN_NULL();
        
        PG_RETURN_TEXT_P(cstring_to_text(nspname));
    }
}
PG_FUNCTION_INFO_V1(mad_get_schema_name);

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
Datum mad_csvstr_to_array(PG_FUNCTION_ARGS)
{
    text            *inputstring;
    int              inputstring_len = 0;
    char            *start_ptr       = NULL;
    char            *str             = NULL;
    char            *orig_str        = NULL;
    int              orig_str_len    = 0;
    int              posn            = 0;
    int              chunk_len       = 0;
    text            *result_text;
    ArrayBuildState *astate          = NULL;
    
    if (PG_ARGISNULL(0))
        PG_RETURN_NULL();

    inputstring     = PG_GETARG_TEXT_PP(0);
    inputstring_len = VARSIZE_ANY_EXHDR(inputstring);

    /* return empty array for empty input string */
    if (inputstring_len < 1)
        PG_RETURN_ARRAYTYPE_P(construct_empty_array(TEXTOID));

    /* start_ptr points to the start_posn'th character of inputstring */
    orig_str = str_tolower
        (
            VARDATA_ANY(inputstring),
            inputstring_len,
            PG_GET_COLLATION()
        );
    
    orig_str_len = strlen(orig_str);
    str          = orig_str;
    start_ptr    = str;
    
    for (; str != NULL && *str != '\0'; ++str)
    {
        if (*str == COMMA_CHAR)
        {
            /* must build a temp text datum to pass to accumArrayResult */
            result_text = DirectFunctionCall1(btrim1, cstring_to_text_with_len(start_ptr, chunk_len));
            /* stash away this field */
			astate = accumArrayResult
                (
                    astate,
                    PointerGetDatum(result_text),
                    false,
                    TEXTOID,
                    CurrentMemoryContext
                );
            pfree(result_text);
            chunk_len = 0;
            start_ptr = str + 1;
            posn = start_ptr - VARDATA_ANY(inputstring);
        }
        else
            chunk_len++;
    }

    /* field after the last COMMA_CHAR */
    result_text = DirectFunctionCall1(btrim1, cstring_to_text_with_len(start_ptr, chunk_len));
    astate = accumArrayResult
        (
            astate,
            PointerGetDatum(result_text),
            false,
            TEXTOID,
            CurrentMemoryContext
        );
    pfree(result_text);
    pfree(orig_str);
    
    PG_RETURN_ARRAYTYPE_P(makeArrayResult(astate,
										  CurrentMemoryContext));
}
PG_FUNCTION_INFO_V1(mad_csvstr_to_array);

/*
 * @brief Get the number of columns for a given table.
 *
 * @param table_name    The full table name.      
 * 
 * @return The number of columns in the given table. 
 *
 */
Datum mad_num_of_columns(PG_FUNCTION_ARGS)
{
    text            *table_name;
    List            *names;
    Oid              relid;
    HeapTuple        relTup;
    Form_pg_class    relForm;
    int              result;

    mad_do_assert
        (
            !PG_ARGISNULL(0),
            "Table name should not be null"
        );

    table_name = PG_GETARG_TEXT_PP(0);
    names = textToQualifiedNameList(table_name);
    relid = RangeVarGetRelid(makeRangeVarFromNameList(names), true);

    /* check whether table exists */
    mad_do_assert_value
        (
            OidIsValid(relid),
            "table \"%s\"does not exist",
            (text_to_cstring(table_name))
        );

    relTup = SearchSysCache1(RELOID,
							 ObjectIdGetDatum(relid));
    relForm = (Form_pg_class) GETSTRUCT(relTup);
    result = relForm->relnatts;

    ReleaseSysCache(relTup);

    PG_RETURN_INT32(result);
}
PG_FUNCTION_INFO_V1(mad_num_of_columns);

/*
 * @brief Test if each element in the given array is a column of the table.
 *
 * @param column_names      The array containing the columns to be tested.
 * @param table_name        The full table name.
 * 
 * @return True if each element of column_names is a column of the table.
 *
 */
Datum mad_columns_in_table(PG_FUNCTION_ARGS)
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
    column_names    = PG_GETARG_ARRAYTYPE_P(1);

    ndims        = ARR_NDIM(column_names);
    element_type = ARR_ELEMTYPE(column_names);

    if (ndims == 0)
        PG_RETURN_BOOL(false);

    dims   = ARR_DIMS(column_names);
    ptr    = ARR_DATA_PTR(column_names);
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
    typlen   = typentry->typlen;
    typbyval = typentry->typbyval;
    typalign = typentry->typalign;
    
    names = textToQualifiedNameList(full_table_name);
    relid = RangeVarGetRelid(makeRangeVarFromNameList(names), true);

    mad_do_assert_value(OidIsValid(relid),
                        "table \"%s\" does not exist",
                        (text_to_cstring(full_table_name)));
    
    /* open the relation to get info */
    rel = relation_open(relid, AccessShareLock);
    td  = RelationGetDescr(rel);

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
PG_FUNCTION_INFO_V1(mad_columns_in_table);

/*
 * @brief Test if the given element is in the specified array or not.
 *
 * @param find      The element to be found.
 * @param arr       The array containing the elements.
 * 
 * @return True the element is in the array. Otherwise returns false.
 *
 */
Datum mad_array_search(PG_FUNCTION_ARGS)
{
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

    find      = PG_GETARG_DATUM(0);
    arr       = PG_GETARG_ARRAYTYPE_P(1);
    collation = PG_GET_COLLATION();
    
    /* Check type, only compare find and arr element of the same type */
    element_type = ARR_ELEMTYPE(arr);

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
            /* We don't use here because errcode are different */
			ereport(ERROR,
					(errcode(ERRCODE_UNDEFINED_FUNCTION),
                     errmsg("could not identify an equality operator for type %s",
                            format_type_be(element_type))));
		fcinfo->flinfo->fn_extra = (void *) typentry;
	}
	typlen   = typentry->typlen;
	typbyval = typentry->typbyval;
	typalign = typentry->typalign;

	/* Apply the comparison operator to each pair of array elements. */
	InitFunctionCallInfoData(locfcinfo, &typentry->eq_opr_finfo, 2, collation, NULL, NULL);

    /* Loop over source array */
    nitems   = ArrayGetNItems(ARR_NDIM(arr), ARR_DIMS(arr));
    ptr      = ARR_DATA_PTR(arr);
    contains = false;
    
    for (i = 0; i < nitems; ++i)
    {
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
PG_FUNCTION_INFO_V1(mad_array_search);

/*
 * @brief Short form to format a string with a parameter.
 *
 * @param arg1	The first argument.
 *
 * @return The formated string.
 *
 */
Datum mad_format1(PG_FUNCTION_ARGS)
{
    char        *fmt;
    char       **args_array;
    text        *result;
    int          i;
    
    mad_do_assert
        (
            !(PG_ARGISNULL(0) || PG_ARGISNULL(1)),
            "the format string and its arguments must not be null"
        );
    
    fmt = text_to_cstring(PG_GETARG_TEXT_PP(0));
    args_array = (char **) palloc0(3 * sizeof(char *));

    for (i = 0; i < 1; i++)
    {
        args_array[i] = text_to_cstring(PG_GETARG_TEXT_PP(i+1));
    }
    
    result = mad_format_internal(fmt, args_array, 1);
    pfree(args_array);
    
    PG_RETURN_TEXT_P(result);
}
PG_FUNCTION_INFO_V1(mad_format1);

/*
 * @brief Short form to format a string with two parameters.
 *
 * @param arg1	The first argument.
 * @param arg2	The second argument.
 *
 * @return The formated string.
 *
 */
Datum mad_format2(PG_FUNCTION_ARGS)
{
    char        *fmt;
    char       **args_array;
    text        *result;
    int          i;
    
    mad_do_assert
        (
            !(PG_ARGISNULL(0) || PG_ARGISNULL(1)
              || PG_ARGISNULL(2)),
            "the format string and its arguments must not be null"
        );
    
    fmt = text_to_cstring(PG_GETARG_TEXT_PP(0));
    args_array = (char **) palloc0(3 * sizeof(char *));

    for (i = 0; i < 2; i++)
    {
        args_array[i] = text_to_cstring(PG_GETARG_TEXT_PP(i+1));
    }
    
    result = mad_format_internal(fmt, args_array, 2);
    pfree(args_array);
    
    PG_RETURN_TEXT_P(result);
}
PG_FUNCTION_INFO_V1(mad_format2);

/*
 * @brief Short form to format a string with three parameters.
 *
 * @param arg1	The first argument.
 * @param arg2	The second argument.
 * @param arg3	The third argument.
 *
 * @return The formated string.
 *
 */
Datum mad_format3(PG_FUNCTION_ARGS)
{
    char        *fmt;
    char       **args_array;
    text        *result;
    int          i;
    
    mad_do_assert
        (
            !(PG_ARGISNULL(0) || PG_ARGISNULL(1)
              || PG_ARGISNULL(2) || PG_ARGISNULL(3)),
            "the format string and its arguments must not be null"
        );
    
    fmt = text_to_cstring(PG_GETARG_TEXT_PP(0));
    args_array = (char **) palloc0(3 * sizeof(char *));

    for (i = 0; i < 3; i++)
    {
        args_array[i] = text_to_cstring(PG_GETARG_TEXT_PP(i+1));
    }
    
    result = mad_format_internal(fmt, args_array, 3);
    pfree(args_array);
    
    PG_RETURN_TEXT_P(result);
}
PG_FUNCTION_INFO_V1(mad_format3);

/*
 * @brief Short form to format a string with four parameters.
 *
 * @param arg1	The first argument.
 * @param arg2	The second argument.
 * @param arg3	The third argument.
 * @param arg4	The fouth argument.
 *   
 * @return The formated string.
 *
 */
Datum mad_format4(PG_FUNCTION_ARGS)
{
    char        *fmt;
    char       **args_array;
    text        *result;
    int          i;
    
    mad_do_assert
        (
            !(PG_ARGISNULL(0) || PG_ARGISNULL(1)
              || PG_ARGISNULL(2) || PG_ARGISNULL(3) || PG_ARGISNULL(4)),
            "the format string and its arguments must not be null"
        );
    
    fmt = text_to_cstring(PG_GETARG_TEXT_PP(0));
    args_array = (char **) palloc0(4 * sizeof(char *));

    for (i = 0; i < 4; i++)
    {
        args_array[i] = text_to_cstring(PG_GETARG_TEXT_PP(i+1));
    }
    
    result = mad_format_internal(fmt, args_array, 4);
    pfree(args_array);
    
    PG_RETURN_TEXT_P(result);
}
PG_FUNCTION_INFO_V1(mad_format4);

/*
 * @brief We need to build a lot of query strings based on a set of arguments. For that
 *        purpose, this function will take a format string (the template) and an array
 *        of values, scan through the format string, and replace the %s in the format
 *        string with the corresponding values in the array. The result string is
 *        returned as a PG/GP text Datum. The escape char for '%' is '\'. And we will
 *        not change it's default behavior in PG/GP. For example, assume that
 *        fmt = E'\\\\\\\\ % \\% %', args[] = {"100", "20"}, then the returned text
 *        of this function is E'\\\\\\\\ 100 % 20'
 *
 * @param fmt       The format string. %s are used to indicate a position
 *                  where a value should be filled in.
 * @param args      An array of values that should be used for replacements.
 *                  args[i] replaces the i-th % in fmt. The array length should
 *                  equal to the number of %s in fmt.
 *
 * @return A string with all %s which were not escaped in first argument replaced
 *         with the corresponding values in the second argument.
 *
 */
Datum mad_format(PG_FUNCTION_ARGS)
{
    char           *fmt;
    text           *result;
    ArrayType      *args;
    int             nitems       = 0;
    ArrayMetaState *my_extra     = NULL;
    Oid             element_type;
    int			    typlen       = 0;
	bool		    typbyval;
	char		    typalign;
    char          **args_array;
    int             i            =0;
    Datum           elt;
    char           *ptr;
    
    mad_do_assert
        (
            !(PG_ARGISNULL(0) || PG_ARGISNULL(1)),
            "the format string and its arguments must not be null"
        );

    fmt = text_to_cstring(PG_GETARG_TEXT_PP(0));
    args = PG_GETARG_ARRAYTYPE_P(1);

    mad_do_assert
        (
            !ARR_NULLBITMAP(args),
            "the argument array must not has null value"
        );
    
    element_type = ARR_ELEMTYPE(args);
    /*
	 * We arrange to look up info about element type, including its output
	 * conversion proc, only once per series of calls, assuming the element
	 * type doesn't change underneath us.
	 */
	my_extra = (ArrayMetaState *) fcinfo->flinfo->fn_extra;
	if (my_extra == NULL)
	{
		fcinfo->flinfo->fn_extra = MemoryContextAlloc
									(
										fcinfo->flinfo->fn_mcxt,
										sizeof(ArrayMetaState)
									);
		my_extra = (ArrayMetaState *) fcinfo->flinfo->fn_extra;
		my_extra->element_type = ~element_type;
	}

    if (my_extra->element_type != element_type)
	{

        /* Get info about element type, including its output conversion proc. */
		get_type_io_data
			(
				element_type,
				IOFunc_output,
				&my_extra->typlen,
				&my_extra->typbyval,
				&my_extra->typalign,
				&my_extra->typdelim,
				&my_extra->typioparam,
				&my_extra->typiofunc
			);
		fmgr_info_cxt
			(
				my_extra->typiofunc,
				&my_extra->proc,
				fcinfo->flinfo->fn_mcxt
			);
		my_extra->element_type = element_type;
	}
	typlen = my_extra->typlen;
	typbyval = my_extra->typbyval;
	typalign = my_extra->typalign;
    nitems = ArrayGetNItems(ARR_NDIM(args), ARR_DIMS(args));

    args_array = (char **) palloc0(nitems * sizeof(char *));
    ptr = ARR_DATA_PTR(args);

    /* Construct char** type args array from args. */
    for (i = 0; i < nitems; i++)
    {
        elt = fetch_att(ptr, typbyval, typlen);
        ptr = att_addlength_pointer(ptr, typlen, ptr);
        ptr = (char *) att_align_nominal(ptr, typalign);
        args_array[i] = OutputFunctionCall(&my_extra->proc, elt);
    }

    result = mad_format_internal(fmt, args_array, nitems);
    
    pfree(args_array);
    PG_FREE_IF_COPY(args, 1);
    
    PG_RETURN_TEXT_P(result);
}
PG_FUNCTION_INFO_V1(mad_format);
