module Main

import Providers
import Providers.DB
import Providers.DBProvider

%language TypeProviders

%provide (testDB : Database) with loadSchema "test.sqlite"

query : TableExpr testDB ["name":::TEXT, "wheels":::NULLABLE INTEGER, "description":::TEXT]
query = Project (Select (Product (T testDB "people") (Rename (T testDB "transport") "id" "transport_id"))
                        (Col "id" INTEGER == Col "owner" INTEGER))
                ["name":::TEXT, "wheels":::NULLABLE INTEGER, "description":::TEXT]

main : IO ()
main = do q <- doQuery "test.sqlite" query
          putStrLn $ printTable q
