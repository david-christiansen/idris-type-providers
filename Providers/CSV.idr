module Providers.CSV

import Data.NamedVect
import Decidable.Equality

import Providers
%language TypeProviders

%default total

-- | Get the lines of a file as a list of strings
partial
readLines : String -> IO (List String)
readLines fname = fmap (Strings.split (\c => List.elem c ['\n', '\r'])) (readFile fname)

-- | Split into columns
cols : Char -> String -> List String
cols delim row = map trim (split (==delim) row)

-- | Convert a List to a Vect n iff the list has n elements
lengthIs : (n : Nat) -> List a -> Maybe (Vect a n)
lengthIs O     []        = Just []
lengthIs O     (x :: xs) = Nothing
lengthIs (S n) []        = Nothing
lengthIs (S n) (x :: xs) = fmap (Vect.(::) x) (lengthIs n xs)

-- | A representation of the "schema" of a CSV file.
data CSVType : Type where
  MkCSVType : (delim : Char) ->
              (n : Nat) ->
              (header : Vect String n) ->
              CSVType

delim : CSVType -> Char
delim (MkCSVType d _ _) = d

colCount : CSVType -> Nat
colCount (MkCSVType _ n _) = n

header : (t : CSVType) -> Vect String (colCount t)
header (MkCSVType _ _ h) = h

vectEq : Eq a => Vect a n -> Vect a n -> Bool
vectEq Nil Nil = True
vectEq (x :: xs) (y :: ys) = x == y && vectEq xs ys

instance Eq CSVType where
  (==) (MkCSVType delim1 n1 header1) (MkCSVType delim2 n2 header2) with (decEq n1 n2)
    (==) (MkCSVType delim1 n header1)  (MkCSVType delim2 n header2)  | Yes refl =
      delim1 == delim2 && vectEq header1 header2
    (==) (MkCSVType delim1 n1 header1) (MkCSVType delim2 n2 header2) | No _ = False


-- A row corresponding to a schema is just a named vector matching the schema
Row : CSVType -> Type
Row (MkCSVType d n h) = NamedVect String n h

row_lemma : (t : CSVType) -> NamedVect String (colCount t) (header t) -> Row t
row_lemma (MkCSVType d n h) v = v


-- Attempt to read a string as a row in some schema
readRow : (t : CSVType) -> String -> Maybe (Row t)
readRow t r = fmap (row_lemma t . applyNames (header t)) .
              lengthIs (colCount t) .
              cols (delim t) $ r

readRows : (type : CSVType) -> List String ->
           List (Maybe (Row type))
readRows type rows = map (readRow type) rows

-- Construct a CSV type from the first line of the CSV file
inferCSVType : (delim : Char) -> (header : String) -> CSVType
inferCSVType delim header =
  let cs = cols delim header
  in MkCSVType delim (length cs) (fromList cs)

%assert_total -- seems to be a totality checker bug: is possibly not total due to: {Prelude.Strings.unpack1010}
readCSV : (delim : Char) ->
          (header : String) ->
          List String ->
          List (Maybe (NamedVect String (length (cols delim header)) (fromList (cols delim header))))
readCSV delim header rows = readRows (inferCSVType delim header) rows

-- Type provider for CSV. Attempt to infer a CSV type from the provided file.
partial
csvType : Char -> String -> IO (Provider CSVType)
csvType delim filename =
  do lines <- readLines filename
     return $
     case lines of
       []       => Error $ "Could not read header of " ++ filename
       (h :: _) => Provide $ inferCSVType delim h

-- Read the well-formed rows from a CSV file according to some schema
partial
readCSVFile : (t : CSVType) -> String -> IO (Maybe (List (Row t)))
readCSVFile t file =
  do lines <- readLines file
     case lines of
       [] => return Nothing
       (h::body) =>
         if inferCSVType (delim t) h == t
           then return (Just (mapMaybe (readRow t) (drop 1 lines)))
           else return Nothing

test : NamedVect Int 3 ["a", "b", "c"]
test = applyNames _ [1,2,3]

