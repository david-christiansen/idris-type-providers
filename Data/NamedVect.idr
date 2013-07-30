module Data.NamedVect

import Decidable.Equality

soNot : so p -> so (not p) -> _|_
soNot oh oh impossible


-- | NamedVect a n ss is an n-length vector of as, named by the elements in ss
data NamedVect : Type -> (n : Nat) -> (Vect n String) -> Type where
  Nil : NamedVect a Z []
  (::) : a -> NamedVect a n ss -> NamedVect a (S n) (s :: ss)

using (n : Nat, ss : Vect n String)
  data Elem : Vect n String -> String -> Type where
    Here : so (s == s') -> Elem {n=S n} (s :: ss) s'
    There : Elem {n=n} ss s' -> Elem {n=S n} (s::ss) s'

elemCase : Elem {n=S n} (s :: ss) s' -> (so (s == s') -> a) -> (Elem ss s' -> a) -> a
elemCase (Here h) ifHere _ = ifHere h
elemCase (There th) _ ifThere = ifThere th

elemEmpty : Elem [] s -> a
elemEmpty (Here _)  impossible
elemEmpty (There _) impossible

-- | Decide whether a name is an element of a Vect of Strings.
decElem : (ss : Vect n String) -> (s : String) -> Dec (Elem ss s)
decElem [] s = No elemEmpty
decElem (s :: ss) s' with (choose (s == s'), decElem ss s')
  decElem (s :: ss) s  | (Left h, _)   = Yes (Here h)
  decElem (s :: ss) s' | (_, Yes rest) = Yes (There rest)
  decElem (s :: ss) s' | (Right notHere, No notThere) =
    No $ \h => elemCase h (\h' => soNot h' notHere) notThere

-- | Extract a named element through straightforward recursion on a proof of membership
lookup' : (s : String) -> NamedVect a n ss -> Elem ss s -> a
lookup' s (x::xs) (Here _)     = x
lookup' s (x::xs) (There rest) = lookup' s xs rest
lookup' s []      prf          = elemEmpty prf

-- | Find a proof of membership, then extract the element
lookup : (s : String) ->
         NamedVect a n ss ->
         {prf : Elem ss s } ->
         {auto x : decElem ss s = Yes prf} ->
         a
lookup s nv {prf=p} = lookup' s nv p

index : Fin n -> NamedVect a n ss -> a
index fO     (x :: xs) = x
index (fS f) (x :: xs) = index f xs

-- | Name an unnamed vector
applyNames : (ss : Vect n String) -> Vect n a -> NamedVect a n ss
applyNames [] [] = []
applyNames (s::ss) (x::xs)= x :: applyNames ss xs

-- | Convert to an unnamed vector
forgetNames : NamedVect a n ss -> Vect n a
forgetNames [] = []
forgetNames (x :: xs) = x :: forgetNames xs

-- | Convert to a list
toList : NamedVect a n ss -> List a
toList = Vect.toList . forgetNames
