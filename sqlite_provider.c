#include "sqlite_provider.h"

sqlite3 *sqlite3_open_file(char *filename) {
  sqlite3 *db;

  int res = sqlite3_open(filename, &db);
  if (res != SQLITE_OK) {
    printf("Could not open db %s", filename);
    return NULL;
  }
  else return db;
}

sqlite3_stmt *prepare_query(sqlite3 *db, char* query) {
  sqlite3_stmt *ppStmt;
  const char *rest;
  int res = sqlite3_prepare_v2(db, query, strlen(query), &ppStmt, &rest);
  if (res != SQLITE_OK) {
    printf("Could not prepare query, res=%d\n\tquery=%s\n", res, query);
    printf("Error: %s\n", sqlite3_errmsg(db));
    return NULL;
  }
  return ppStmt;
}

sqlite3_stmt *query_get_tables(sqlite3 *db) {
  sqlite3_stmt *ppStmt;
  const char *rest;
  int res = sqlite3_prepare_v2(db, "SELECT name, sql FROM sqlite_master WHERE type='table'", 100, &ppStmt, &rest);
  if (res != SQLITE_OK) {
    printf("Could not prepare query, res=%d\n", res);
    return NULL;
  }
  return ppStmt;
}


unsigned char* sqlite3_get_schema(char *filename, char *table) {
  const unsigned char *schema;

  sqlite3 *db;

  db = sqlite3_open_file(filename);

  sqlite3_stmt *ppStmt;
  const char *rest;
  int res = sqlite3_prepare_v2(db, "SELECT sql FROM sqlite_master WHERE NAME = ?1", 100, &ppStmt, &rest);
  if (res != SQLITE_OK) {
    printf("Could not prepare statement, res=%d.\n", res);
    return NULL;
  }

  res = sqlite3_bind_text(ppStmt, 1, table, -1, SQLITE_STATIC);
  if (res != SQLITE_OK) {
    printf("Could not bind table name %s, res=%d.\n", table, res);
    return NULL;
  }

  res = sqlite3_step(ppStmt);
  if (res != SQLITE_ROW) {
    printf("No row, res=%d.\n", res);
    return NULL;
  }

  schema = sqlite3_column_text(ppStmt, 0);
  return schema;
}
