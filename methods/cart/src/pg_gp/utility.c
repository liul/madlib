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

/*
 * text_catenate
 *	Guts of textcat(), broken out so it can be used by other functions
 *
 * Arguments can be in short-header form, but not compressed or out-of-line
 */
static text* text_catenate(text *t1, text *t2)
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
    List*           names;
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
    bool    input;
    char*   result;
    
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
 
                    /*
                     * Would this class be found by regclassin? If not, qualify it.
                     */
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
    bool    condition;
    //  char*   reason ;
    text*   reason;

    condition = PG_GETARG_BOOL(0);
    //    reason = text_to_cstring(PG_GETARG_TEXT_PP(1));
    reason = PG_GETARG_TEXT_PP(1);
    
    if (!(condition)) {
        ereport(ERROR,
                (errcode(ERRCODE_RAISE_EXCEPTION),
                 errmsg(text_to_cstring(reason))));
    }
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
    text*           input;

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
    text*    full_table_name;
    text*    column_name;

    if (PG_ARGISNULL(0))
        PG_RETURN_BOOL(false);
    if (PG_ARGISNULL(1))
        PG_RETURN_BOOL(false);

    full_table_name = PG_GETARG_TEXT_PP(0);
    column_name = PG_GETARG_TEXT_PP(1);

    if (table_exists_internal(full_table_name)) {
        
    }
    return true;
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
    text*    full_table_name;
    bool     existence;
    text*    err_msg;
    text*    msg1;
    text*    msg2;

    full_table_name = PG_GETARG_TEXT_PP(0);
    existence = PG_GETARG_BOOL(1);

    err_msg = cstring_to_text("assertion failure. Table: ");
    msg1 = cstring_to_text(" does not exist");
    msg2 = cstring_to_text(" already exist");
    err_msg = text_catenate(err_msg, full_table_name);

    if (existence)
        err_msg = text_catenate(err_msg, msg1);
    else
        err_msg = text_catenate(err_msg, msg2);

    if (table_exists_internal(full_table_name) != existence) {
        ereport(ERROR,
                (errcode(ERRCODE_RAISE_EXCEPTION),
                 errmsg(text_to_cstring(err_msg))));
    }
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
    char*      full_table_name;
    char*      short_table_name;
    char*      str;    
    char*      posn;

    if (PG_ARGISNULL(0))
        ereport(ERROR,
                (errcode(ERRCODE_RAISE_EXCEPTION),
                 errmsg("Table name should not be null")));

    full_table_name = text_to_cstring(PG_GETARG_TEXT_PP(0));
    posn = str = full_table_name;

    for (; str != NULL && *str != '\0'; ++str)
    {
        /* get the position of DOT_CHAR in str */
        if (*str == DOT_CHAR)
            posn = str;
    }
    
    short_table_name = (char *)palloc(sizeof(char) * (str - posn));
    strcpy(short_table_name, ++posn);

    PG_RETURN_TEXT_P(cstring_to_text(short_table_name));
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
    char*      full_table_name;
    char*      schema_name;
    char*      short_table_name;
    char*      str;
    char*      posn;
    List*      search_path        = fetch_search_path(false);
    char*      nspname;
    
    if (PG_ARGISNULL(0))
        ereport(ERROR,
                (errcode(ERRCODE_RAISE_EXCEPTION),
                 errmsg("Table name should not be null")));

    full_table_name = text_to_cstring(PG_GETARG_TEXT_PP(0));
    posn = str = full_table_name;

    for(; str != NULL && *str != '\0'; ++str) {
        if (*str == DOT_CHAR)
            posn = str;
    }

    schema_name = (char *)palloc(sizeof(char) * (posn - full_table_name));
    strncpy(schema_name, full_table_name, posn - full_table_name);
    short_table_name = (char *)palloc(sizeof(char) * (str - posn));
    strcpy(short_table_name, ++posn);

    if (schema_name == NULL) {
        /*
         * might have several search paths
         */
        if (table_exists_internal(full_table_name))
        {
            if (search_path == NIL)
                PG_RETURN_NULL();
            nspname = get_namespace_name(linitial_oid(search_path));
            list_free(search_path);
            if (!nspname)
                PG_RETURN_NULL();       /* recently-deleted namespace? */
            PG_RETURN_TEXT_P(cstring_to_text(nspname));
        }

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
    int              posn = 0;
    int              chunk_len = 0;
    text            *result_text;
    ArrayBuildState *astate = NULL;
    
    if (PG_ARGISNULL(0))
        PG_RETURN_NULL();

    inputstring = PG_GETARG_TEXT_PP(0);
    inputstring_len =  VARSIZE_ANY_EXHDR(inputstring);

    /* return empty array for empty input string */
    if (inputstring_len < 1)
        PG_RETURN_ARRAYTYPE_P(construct_empty_array(TEXTOID));

    /* start_ptr points to the start_posn'th character of inputstring */

    orig_str = str_tolower(VARDATA_ANY(inputstring),
                      inputstring_len,
                      PG_GET_COLLATION());
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
    chunk_len = inputstring_len - posn;
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
