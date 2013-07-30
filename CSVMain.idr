module Main
import Data.NamedVect
import Providers.CSV

%language TypeProviders

%provide (t : CSVType) with csvType ';' "test.csv"

getAge : Row t -> String
getAge r = NamedVect.lookup "Age" r

partial
main : IO ()
main = do f <- readCSVFile t "test.csv"
          case f of
            Nothing => putStrLn "Couldn't open CSV file"
            Just rows =>
              do let ages = map getAge rows
                 let names = map (NamedVect.index fZ) rows
                 putStrLn (show ages)
                 putStrLn (show names)

