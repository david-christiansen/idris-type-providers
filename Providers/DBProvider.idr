module Providers.DBProvider

import Providers.DB

import Providers.DBParser

%lib C "sqlite3"
%link C "sqlite_provider.o"
%include C "sqlite_provider.h"
%dynamic "libsqlite3"
%dynamic "./sqlite_provider.so"


namespace TypeProvider

  getTable : Ptr -> IO (Maybe (String, String))
  getTable ptr = do res <- mkForeign (FFun "sqlite3_step" [FPtr] FInt) ptr
                    if res /= SQLITE_ROW
                      then return Nothing
                      else do name <- mkForeign (FFun "sqlite3_column_text" [FPtr, FInt] FString) ptr 0
                              sch <- mkForeign (FFun "sqlite3_column_text" [FPtr, FInt] FString) ptr 1
                              return (Just (name, sch))

  getTables : Ptr -> IO (List (String, String))
  getTables ptr = do tbl <- getTable ptr
                     case tbl of
                       Just x => do tbls <- getTables ptr
                                    return (the (List (String, String)) (x :: tbls))
                       Nothing => return List.Nil

  getDB : String -> IO Database
  getDB file = do ptr <- mkForeign (FFun "sqlite3_open_file" [FString] FPtr) file
                  stmt <- mkForeign (FFun "query_get_tables" [FPtr] FPtr) ptr
                  tblInfo <- getTables stmt
                  return (mapMaybe (getSchema . snd) tblInfo)

  loadSchema : String -> IO (Provider Database)
  loadSchema file = do db <- getDB file
                       return (Provide db)

  getResultVal : Ptr -> Int -> (t : SQLType) -> IO (interpSql t)
  getResultVal stmt i INTEGER = mkForeign (FFun "sqlite3_column_int" [FPtr, FInt] FInt) stmt i
  getResultVal stmt i TEXT = mkForeign (FFun "sqlite3_column_text" [FPtr, FInt] FString) stmt i
  getResultVal stmt i (NULLABLE t) = do tp <- mkForeign (FFun "sqlite3_column_type" [FPtr, FInt] FInt) stmt i
                                        if tp == SQLITE_NULL
                                          then return Nothing
                                          else fmap Just (getResultVal stmt i t)
  getResultVal stmt i REAL = mkForeign (FFun "sqlite3_column_double" [FPtr, FInt] FFloat) stmt i
  getResultVal stmt i BOOLEAN = do val <- mkForeign (FFun "sqlite3_column_int" [FPtr, FInt] FFloat) stmt i
                                   return (val /= 0)

  getResultRow : Ptr -> Int -> (s : Schema) -> IO (Row s)
  getResultRow stmt _ [] = return Row.Nil
  getResultRow stmt i (c:::t :: s) = do val <- getResultVal stmt i t
                                        rest <- getResultRow stmt (i+1) s
                                        return (the (Row (c:::t :: s)) (val :: rest))

  getResults : Ptr -> (s : Schema) -> IO (Table s)
  getResults stmt s = do more <- mkForeign (FFun "sqlite3_step" [FPtr] FInt) stmt
                         if more /= SQLITE_ROW
                           then return Table.Nil
                           else do r <- getResultRow stmt 0 s
                                   next <- getResults stmt s
                                   return (the (Table s) (r::next))

  doQuery : String -> Query db s -> IO (Table s)
  doQuery file q = do let q' = compile q ++ ";"
                      db <- mkForeign (FFun "sqlite3_open_file" [FString] FPtr) file
                      stmt <- mkForeign (FFun "prepare_query" [FPtr, FString] FPtr) db q'
                      getResults stmt (getSchema q)
