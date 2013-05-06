#ifndef SQLITE_PROVIDER_H
#define SQLITE_PROVIDER_H

#include <stdio.h>
#include <sqlite3.h>

sqlite3 *sqlite3_open_file(char *filename);
unsigned char* sqlite3_get_schema(char* filename, char* table);
sqlite3_stmt *query_get_tables(sqlite3 *db);
sqlite3_stmt *prepare_query(sqlite3 *db, char* query);
#endif
