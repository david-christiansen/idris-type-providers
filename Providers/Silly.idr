module Silly

%language TypeProviders

charToInt : Char -> Maybe Int
charToInt c = let i = cast {to=Int} c in
              let zero = cast {to=Int} '0' in
              let nine = cast {to=Int} '9' in
              if i < zero || i > nine
                then Nothing
                else Just (i - zero)

total
parse' : Int -> List Int -> Maybe Int
parse' _   []      = Nothing
parse' acc [d]     = Just (10 * acc + d)
parse' acc (d::ds) = parse' (10 * acc + d) ds


total parseInt : String -> Maybe Int
parseInt str = (sequence (map charToInt (unpack str))) >>= parse' 0

confirmAge : IO Bool
confirmAge = do putStrLn "How old are you?"
                input <- getLine
                let age = parseInt (trim input)
                case age of
                  Nothing => do putStrLn "Didn't understand"
                                confirmAge
                  Just x => return (if x >= 18 then True else False)

adultsOnly : IO (Provider Bool)
adultsOnly = do oldEnough <- confirmAge
                if oldEnough
                  then do { putStrLn "ok" ; return (Provide True) }
                  else return (Error "Only adults may compile this program")

%provide (ok : Bool) with adultsOnly

