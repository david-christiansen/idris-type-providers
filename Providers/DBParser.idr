module Providers.DBParser

import Providers.DB


people : String
people = "CREATE TABLE \"people\" (\"id\" INTEGER PRIMARY KEY  AUTOINCREMENT  NOT NULL  UNIQUE , \"name\" VARCHAR NOT NULL , \"age\" INTEGER)"

--quote : Char
--quote = '\"'

--createTable : Parser Char List ()
--createTable = str (unpack "CREATE") ~ many1 space ~ str (unpack "TABLE") ^^^ ()

-- schema : Parser String
-- schema = do createTable
--             many1 space
--             is quote
--             res <- many1 (isNot quote)
--             is quote
--             many1 space
--             return (pack res)
-- --            sequence_ [ is quote, many1 space, is '(']
-- --            return (pack res)

dropPrefix : (Eq a) => List a -> List a -> Maybe (List a)
dropPrefix [] ys = Just ys
dropPrefix (x::xs) [] = Nothing
dropPrefix (x::xs) (y::ys) = if x == y then dropPrefix xs ys else Nothing

getWhile : (a -> Bool) -> List a -> (List a, List a)
getWhile p [] = ([], [])
getWhile p (x::xs) with (p x)
  | True = let (ok, rest) = getWhile p xs
           in (x :: ok, rest)
  | False = ([], x::xs)



isPrefix : (Eq a) => List a -> List a -> Bool
isPrefix [] _ = True
isPrefix (x::xs) [] = False
isPrefix (x::xs) (y::ys) = x == y && isPrefix xs ys

subList : (Eq a) => List a -> List a -> Bool
subList [] _ = False
subList (x::xs) [] = False
subList (x::xs) (y::ys) = (x == y && isPrefix xs ys) || subList (x::xs) ys

isNullable : String -> Bool
isNullable = not . subList ["NOT", "NULL"] . split (==' ')

getType : String -> Maybe String
getType opts = List.find isType (split (==' ') opts)
    where isType : String -> Bool
          isType x = List.elem x ["INTEGER", "VARCHAR", "TEXT"]


colNameTypeNullable : String -> Maybe (String, String, Bool)
colNameTypeNullable col = case dropPrefix ['"'] (unpack (trim col)) of
                            Nothing   => Nothing
                            Just rest => let (name, rest') = (getWhile (/= '\"') rest)
                                         in case dropPrefix ['"', ' '] rest' of
                                            Just rest'' => case getType (pack rest'') of
                                                             Just tp => Just (pack name, tp, isNullable (pack rest''))
                                                             Nothing => Nothing
                                            Nothing     => Nothing

nameCols : String -> Maybe (String, List String)
nameCols schema = case dropPrefix (unpack "CREATE TABLE \"") (unpack schema) of
                    Nothing => Nothing
                    Just rest => let (name, rest') = (getWhile (/= '"') rest)
                                 in case dropPrefix ['"', ' ', '('] rest' of
                                      Just rest'' => case dropPrefix [')'] (reverse rest'') of
                                                       Just rest''' =>
                                                         Just (pack name, split (==',') $ pack (reverse rest'''))
                                                       Nothing => Nothing
                                      Nothing => Nothing

parse : String -> Maybe (String, List (String, String, Bool))
parse schema = case nameCols schema of
                 Just (n, cols) => case sequence {f=Maybe} (map colNameTypeNullable cols) of
                                     Just cols' => Just (n, cols')
                                     Nothing => Nothing
                 Nothing => Nothing

toSchema : List (String, String, Bool) -> Maybe Schema
toSchema [] = Just []
toSchema ((colName, colT, nullable)::cols) = do tp <- getType colT nullable
                                                rest <- toSchema cols
                                                return (colName:::tp :: rest)
    where getType : String -> Bool -> Maybe SQLType
          getType t         True  = fmap NULLABLE (getType t False)
          getType "VARCHAR" False = Just TEXT
          getType "TEXT"    False = Just TEXT
          getType "INTEGER" False = Just INTEGER
          getType "REAL"    False = Just REAL
          getType _         False = Nothing

getSchema : String -> Maybe (String, Schema)
getSchema str = do nameCols <- parse str
                   tableSchema <- toSchema (snd nameCols)
                   Just (fst nameCols, tableSchema)
