module Providers.DB

import Data.BoundedList
import Decidable.Equality
import Language.Reflection
import Language.Reflection.Utils
import SQLiteConstants
import SQLiteTypes

%default total

varchar : (s : String) -> BoundedList Char n
varchar {n=n} s = take n (unpack s)

partial
getProofYes : Dec p -> p
getProofYes (Yes prf) = prf

partial
getProofNo : Dec p -> p -> _|_
getProofNo (No prf) = prf

isYes : Dec p -> Type
isYes (Yes _) = ()
isYes (No _) = _|_

isNo : Dec p -> Type
isNo (Yes _) = _|_
isNo (No _)  = ()

soNot : so p -> so (not p) -> _|_
soNot oh oh impossible

instance Cast Nat Int where
  cast O = 0
  cast (S n) = 1 + (cast n)

namespace Types
  data SQLType = INTEGER | TEXT | NULLABLE SQLType | REAL | BOOLEAN

  instance Show SQLType where
    show INTEGER = "INTEGER"
    show TEXT = "TEXT"
    show (NULLABLE t) = "NULLABLE " ++ show t
    show REAL = "REAL"
    show BOOLEAN = "BOOLEAN"

  instance Eq SQLType where
    INTEGER       == INTEGER        = True
    TEXT          == TEXT           = True
    (NULLABLE t1) == (NULLABLE t2)  = t1 == t2
    REAL          == REAL           = True
    BOOLEAN       == BOOLEAN        = True
    a             == b              = False

  interpSql : SQLType -> Type
  interpSql INTEGER = Int
  interpSql TEXT = String
  interpSql (NULLABLE t) = Maybe (interpSql t)
  interpSql REAL = Float
  interpSql BOOLEAN = Bool

  printVal : (interpSql t) -> String
  printVal {t=INTEGER} x = show x
  printVal {t=TEXT} x = x
  printVal {t=NULLABLE t'} Nothing = "null"
  printVal {t=NULLABLE t'} (Just x) = printVal x
  printVal {t=REAL} x = show x
  printVal {t=BOOLEAN} x = show x

  intNotText : INTEGER = TEXT -> _|_
  intNotText refl impossible

  intNotNullable : INTEGER = NULLABLE t -> _|_
  intNotNullable refl impossible

  intNotReal : INTEGER = REAL -> _|_
  intNotReal refl impossible

  intNotBool : INTEGER = BOOLEAN -> _|_
  intNotBool refl impossible

  textNotNullable : TEXT = NULLABLE t -> _|_
  textNotNullable refl impossible

  textNotReal : TEXT = REAL -> _|_
  textNotReal refl impossible

  textNotBool : TEXT = BOOLEAN -> _|_
  textNotBool refl impossible

  nullableNotReal : NULLABLE t = REAL -> _|_
  nullableNotReal refl impossible

  nullableNotBool : NULLABLE t = BOOLEAN -> _|_
  nullableNotBool refl impossible

  realNotBool : REAL = BOOLEAN -> _|_
  realNotBool refl impossible

  nullableInjective : NULLABLE t = NULLABLE t' -> t = t'
  nullableInjective refl = refl

  instance DecEq SQLType where
    decEq INTEGER INTEGER = Yes refl
    decEq INTEGER TEXT = No intNotText
    decEq INTEGER (NULLABLE t) = No intNotNullable
    decEq INTEGER REAL = No intNotReal
    decEq INTEGER BOOLEAN = No intNotBool
    decEq TEXT INTEGER = No $ \h => intNotText (sym h)
    decEq TEXT TEXT = Yes refl
    decEq TEXT (NULLABLE t) = No textNotNullable
    decEq TEXT REAL = No textNotReal
    decEq TEXT BOOLEAN = No textNotBool
    decEq (NULLABLE t) INTEGER = No $ \h => intNotNullable (sym h)
    decEq (NULLABLE t) TEXT = No $ \h => textNotNullable (sym h)
    decEq (NULLABLE t) (NULLABLE t') with (decEq t t')
      decEq (NULLABLE t) (NULLABLE t)  | Yes refl = Yes refl
      decEq (NULLABLE t) (NULLABLE t') | No p = No $ \h => p (nullableInjective h)
    decEq (NULLABLE t) REAL = No nullableNotReal
    decEq (NULLABLE t) BOOLEAN = No nullableNotBool
    decEq REAL INTEGER = No $ \h => intNotReal (sym h)
    decEq REAL TEXT = No $ \h => textNotReal (sym h)
    decEq REAL (NULLABLE t) = No $ \h => nullableNotReal (sym h)
    decEq REAL REAL = Yes refl
    decEq REAL BOOLEAN = No realNotBool
    decEq BOOLEAN INTEGER = No $ \h => intNotBool (sym h)
    decEq BOOLEAN TEXT = No $ \h => textNotBool (sym h)
    decEq BOOLEAN (NULLABLE t) = No $ \h => nullableNotBool (sym h)
    decEq BOOLEAN REAL = No $ \h => realNotBool (sym h)
    decEq BOOLEAN BOOLEAN = Yes refl

  -- Necessary because type class resolution and universes are hard to unite
  infix 9 <==>

  (<==>) : (interpSql t1) -> (interpSql t2) -> Bool
  (<==>) {t1=t1}         {t2=t2}         a        b        with (decEq t1 t2, t1)
  (<==>) {t1=INTEGER}    {t2=INTEGER}    a        b        | (Yes refl, INTEGER)    = a == b
  (<==>) {t1=TEXT}       {t2=TEXT}       a        b        | (Yes refl, TEXT)       = a == b
  (<==>) {t1=NULLABLE t} {t2=NULLABLE t} Nothing  Nothing  | (Yes refl, NULLABLE t) = True
  (<==>) {t1=NULLABLE t} {t2=NULLABLE t} (Just a) (Just b) | (Yes refl, NULLABLE t) = a <==> b
  (<==>) {t1=REAL}       {t2=REAL}       a        b        | (Yes refl, REAL)       = a == b
  (<==>) {t1=BOOLEAN}    {t2=BOOLEAN}    a        b        | (Yes refl, BOOLEAN)    = a == b
  (<==>) {t1=t1}         {t2=t2}         a        b        | (No no,    _)          = False


namespace Schemas
  data Attribute : Type where
    (:::) : String -> SQLType -> Attribute

  infix 8 :::

  instance Show Attribute where
    show (c:::t) = c ++ ":::" ++ show t

  getName : Attribute -> String
  getName (n ::: t) = n

  getType : Attribute -> SQLType
  getType (n ::: t) = t

  data AttrEq : Attribute -> Attribute -> Type where
    attrRefl : {colMatch : so (c1 == c2)} -> AttrEq (c1 ::: t) (c2 ::: t)

  data Schema : Type where
    Nil : Schema
    (::) : (a : Attribute) -> (s : Schema) -> Schema

  instance Cast Schema (List Attribute) where
    cast [] = []
    cast (a::as) = a :: cast as

  instance Show Schema where
    show s = show (cast {to=List Attribute} s)

  colNames : Schema -> List String
  colNames [] = []
  colNames (c ::: _ :: s) = c :: colNames s

  data HasType : Schema -> String -> SQLType -> Type where
    Here : so (col == col') -> HasType (col' ::: t :: s) col t
    There : HasType s col t -> HasType (col' ::: t' :: s) col t

  nilSchemaEmpty : HasType [] c t -> _|_
  nilSchemaEmpty Here impossible
  nilSchemaEmpty (There _) impossible

  hasTypeInv : so (not (col == c)) -> (HasType s col t -> _|_) -> HasType (c ::: t' :: s) col t -> _|_
  hasTypeInv notEq _        (Here eq)   = soNot eq notEq
  hasTypeInv _     notThere (There prf) = notThere prf


  decHasType : (s : Schema) -> (col : String) -> (t : SQLType) -> Dec (HasType s col t)
  decHasType [] c t = No nilSchemaEmpty
  decHasType (col':::t' :: s) col t with (choose (col == col'), decEq t t', decHasType s col t)
    decHasType (col':::t :: s) col t | (Left prf,    Yes refl, _)       = Yes (Here prf)
    decHasType (col':::t' :: s) col t | (_,           _,        Yes prf) = Yes (There prf)
    decHasType (col':::t' :: s) col t | (Right notEqual, _,        No notPresent) = No $ \h => hasTypeInv notEqual notPresent h

  lookup : (s : Schema) -> (col : String) -> Maybe (t ** HasType s col t)
  lookup [] _ = Nothing
  lookup (c:::t :: s) c' =
    case choose ( c' == c) of
      Left eq => Just (t ** Here eq)
      Right neq => case lookup s c' of
                     Nothing => Nothing
                     Just (Ex_intro t prf) => Just (t ** There prf)

  -- Convenience function for eliminating type annotations on queries
  partial lookup' : (s : Schema) -> (col : String) -> SQLType
  lookup' (c:::t :: s) c' = if c == c' then t else lookup' s c'


  -- Gives both a proof of sub-schema-ness and a means of performing the projection
  SubSchema : (sub, super : Schema) -> Type
  SubSchema [] s = ()
  SubSchema (col:::t :: s') s = (HasType s col t, SubSchema s' s)

  decSubSchema : (sub, super : Schema) -> Dec (SubSchema sub super)
  decSubSchema [] s = Yes ()
  decSubSchema (col:::t :: s') s with (decHasType s col t, decSubSchema s' s)
    | (Yes p1, Yes p2) = Yes (p1, p2)
    | (No p1, _)       = No $ \(h, _) => p1 h
    | (_, No p2)       = No $ \(_, h) => p2 h



  -- The schema of a cartesian product -- unsafe due to no overlapping column check
  product : Schema -> Schema -> Schema
  product [] s' = s'
  product (attr :: s) s' = attr :: (product s s')

  namespace Occurs
    data Occurs : Schema -> String -> Type where
      Here : so (c == c') -> Occurs (c:::t :: s) c'
      There : Occurs s c' -> Occurs (c:::t :: s) c'

    noOccursNil : Occurs [] c -> _|_
    noOccursNil (Here p) impossible
    noOccursNil (There occ) impossible

    occursInv : (c, c': String) -> (s : Schema) -> so (not (c == c')) -> (Occurs s c' -> _|_) -> Occurs (c:::t :: s) c' -> _|_
    occursInv c c' s notHere notThere (Here here) = soNot here notHere
    occursInv c c' s notHere notThere (There there) = notThere there

    decOccurs : (s : Schema) -> (col : String) -> Dec (Occurs s col)
    decOccurs [] c' = No noOccursNil
    decOccurs (c:::t :: s) c' with (choose (c==c'), decOccurs s c')
      | (Left yep, _) = Yes (Here yep)
      | (Right nope, Yes inRest) = Yes (There inRest)
      | (Right nope, No notInRest) = No $ \h => occursInv _ _ _ nope notInRest h



  data Disjoint : Schema -> Schema -> Type where
    EmptyDisjoint : Disjoint [] s
    ConsDisjoint  : Disjoint s1 s2 -> (Occurs s2 c -> _|_) -> Disjoint (c ::: t :: s1) s2


  decDisjoint_lemma1 : Occurs s2 c -> Disjoint (c ::: t :: s1) s2 -> _|_
  decDisjoint_lemma1 occ (ConsDisjoint rest notOcc) = notOcc occ

  decDisjoint : (s1, s2 : Schema) -> Dec (Disjoint s1 s2)
  decDisjoint [] s2 = Yes EmptyDisjoint
  decDisjoint (c ::: t :: s1) s2 with (decOccurs s2 c, decDisjoint s1 s2)
    | (Yes occ, _) = No $ \h => decDisjoint_lemma1 occ h
    | (_, No restBad) = No $ \(ConsDisjoint rest _) => restBad rest
    | (No notIn, Yes restOk) = Yes (ConsDisjoint restOk notIn)


  rename : (s : Schema) -> (from : String) -> (to : String) ->
           Occurs s from -> (Occurs s to -> _|_) ->
           Schema
  rename (f:::t :: s) from to (Here eq) _     = to:::t :: s
  rename (c:::t :: s) from to (There rest) ok = c:::t :: rename s from to rest (\h => ok (There h))





namespace Data
  namespace Row
    data Row : Schema -> Type where
      Nil : Row []
      (::) : (interpSql t) -> Row s -> Row (col ::: t :: s)

    (++) : Row s1 -> Row s2 -> Row (product s1 s2)
    (++) []          r2 = r2
    (++) (col :: r1) r2 = col :: (r1 ++ r2)

    printRow : Row s -> String
    printRow [] = "\n"
    printRow (c :: cs) = printVal c ++ " | " ++ printRow cs

    -- Get the element of the column named in the HasType proof
    getCol : (c : String) -> HasType s c t -> Row s -> interpSql t
    getCol c (Here eq)      (v::_)    = v
    getCol c (There inRest) (_::rest) = getCol c inRest rest

    -- Perform a project by following the "recipe" in the proof of SubSchema
    project : Row s -> (s' : Schema) -> SubSchema s' s -> Row s'
    project row []          ()            = []
    project row (c:::t::s') prf = getCol c (fst prf) row :: project row s' (snd prf)

    renameRow : Row s -> (from, to : String) ->
                (okFrom : Occurs s from) -> (okTo : Occurs s to -> _|_) ->
                Row (rename s from to okFrom okTo)
    renameRow (v::vs) _ _ (Here p) _ =  v :: vs
    renameRow (v::vs) from to (There p) okTo = v :: renameRow vs from to p (\h => okTo (There h))

  namespace Table
    data Table : Schema -> Type where
      Nil : Table s
      (::) : Row s -> Table s -> Table s

    count : Table s -> Nat
    count []        = 0
    count (r :: rs) = S (count rs)

    (++) : Table s -> Table s -> Table s
    (++) [] t2 = t2
    (++) (r::rs) t2 = r :: rs ++ t2

    map : (Row s1 -> Row s2) -> Table s1 -> Table s2
    map f [] = []
    map f (r :: rs) = f r :: map f rs

    filter : (Row s -> Bool) -> Table s -> Table s
    filter p [] = []
    filter p (r :: rs) = if p r then r :: filter p rs else filter p rs

    (*) : Table s1 -> Table s2 -> Table (product s1 s2)
    (*) [] t2 = []
    (*) (r1::r1s) t2 = (map (r1 ++) t2) ++ r1s * t2

    printTable : Table s -> String
    printTable {s=s} t = printHeader s ++ printTable' t
    where printAttr : Attribute -> String
          printAttr (col ::: tp) = col
          printHeader : Schema -> String
          printHeader [] = "\n"
          printHeader (attr :: s') = printAttr attr ++ " | " ++ printHeader s'
          printTable' : Table s -> String
          printTable' [] = "\n"
          printTable' (r :: rs) = printRow r ++ printTable' rs

namespace Expr

  data Expr : Schema -> SQLType -> Type where
    Col : (c : String) -> (t : SQLType) ->
          {default tactics { compute; applyTactic findHasType; solve;}
           what : HasType s c t} ->
          Expr s t
    (+) : Expr s INTEGER -> Expr s INTEGER -> Expr s INTEGER
    (-) : Expr s INTEGER -> Expr s INTEGER -> Expr s INTEGER
    (==) : Expr s t1 -> Expr s t2 -> Expr s BOOLEAN
    NotNull : Expr s (NULLABLE t) -> Expr s BOOLEAN
    Length : Expr s TEXT -> Expr s INTEGER
    Const : (t : SQLType) -> (c : interpSql t) -> Expr s t

  expr : Expr s t -> Row s -> (interpSql t)
  expr (Col c t {what=what}) r = getCol c what r
  expr (e1 + e2) r = expr e1 r + expr e2 r
  expr (e1 - e2) r = expr e1 r - expr e2 r
  expr (e1 == e2) r = expr e1 r <==> expr e2 r
  expr (NotNull e) r = case expr e r of
                         Nothing => False
                         Just _  => True
  expr (Length e) r = cast {to=Int} (length (expr e r))
  expr (Const t c) r = c

  %assert_total
  compileExpr : Expr s t -> String
  compileExpr (Col c t) = "\"" ++ c ++ "\""
  compileExpr (e1 + e2) = "(" ++ compileExpr e1 ++ ") + (" ++ compileExpr e2 ++ ")"
  compileExpr (e1 - e2) = "(" ++ compileExpr e1 ++ ") - (" ++ compileExpr e2 ++ ")"
  compileExpr (e1 == e2) = "(" ++ compileExpr e1 ++ ") = (" ++ compileExpr e2 ++ ")"
  compileExpr (NotNull e) = "(" ++ compileExpr e ++ ") is not null"
  compileExpr (Length e) = "length(" ++ compileExpr e ++ ")"
  compileExpr (Const TEXT str) = "'" ++ str ++ "'" -- FIXME escape strings
  compileExpr (Const INTEGER i) = show i
  compileExpr (Const (NULLABLE t) Nothing) = "null"
  compileExpr {s=s} (Const (NULLABLE t) (Just x)) = compileExpr {s=s} (Const t x)
  compileExpr (Const REAL r) = show r
  compileExpr (Const BOOLEAN True) = "true"
  compileExpr (Const BOOLEAN False) = "false"

namespace Database
  Database : Type
  Database = List (String, Schema)

  namespace HasTable
    data HasTable : Database -> String -> Schema -> Type where
      Here : HasTable ((n,s)::db) n s
      There : HasTable db n s -> HasTable ((n',s')::db) n s

namespace Automation

  -- "Blunderbuss" tactic for taking care of very trivial goals
  easy : List (TTName, Binder TT) -> TT -> Tactic
  easy ctxt goal = try $ findAssumption ctxt goal ++
                         [ (Refine (MN 0 "__II")) -- unit
                         , Trivial                -- refl from context
                         ]
    where findAssumption : List (TTName, Binder TT) -> TT -> List Tactic
          findAssumption [] _ = []
          findAssumption ((n, b)::ctxt) goal =
              if (goal == binderTy b) then [Refine n] else findAssumption ctxt goal


  extractAttr : (TT, List TT) -> (TT, TT) -- Extract the components of attribute (c ::: t)
  extractAttr (P _ (NS (UN ":::") ["Schemas", "DB", "Providers"]) _, [col, ty]) = (col, ty)
  extractAttr (fn, args) = (P Ref (UN (show fn ++ "  " ++ show args)) Erased, Erased)

  typeHere : TTName
  typeHere = (NS "Here" ["Schemas", "DB", "Providers"])

  typeThere : TTName
  typeThere = (NS "There" ["Schemas", "DB", "Providers"])


  findHasTypeProof : TT -> TT
  findHasTypeProof goal =
    case unApply goal of
      (hasType, [s, c, t]) => hasTypeProof (unApply s) c t
      _ => (P Ref "Wrong type" Erased)
    where %assert_total hasTypeProof : (TT, List TT) -> TT -> TT -> TT
          hasTypeProof (P _ (NS (UN "::") ["Schemas", "DB", "Providers"]) _, [hd, tl]) c t =
            let (c', t') = extractAttr (unApply hd) in
            if (c == c' && t == t')
              then mkApp (P Ref typeHere Erased) [c, c', t, tl, P Ref "oh" Erased]
              else mkApp (P Ref typeThere Erased) [tl, c, t, c', t', hasTypeProof (unApply tl) c t]
          hasTypeProof fail c t = P Ref ("hasTypeProof failure for " ++ show c ++ " and " ++ show t) Erased

  findHasType : List (TTName, Binder TT) -> TT -> Tactic
  findHasType ctxt goal = Exact $ findHasTypeProof goal


  %assert_total
  findSubSchemaProof : TT -> TT
  findSubSchemaProof goal =
    case unApply goal of
      (P _ (MN _ "__Unit") _, []) => (P Ref (MN 0 "__II") Erased)
      (n, [hasType, next]) => mkApp (P Ref "mkPair" Erased) [ hasType
                                                            , next
                                                            , findHasTypeProof hasType
                                                            , findSubSchemaProof next
                                                            ]
      other => P Ref ("Fail " ++ show other) Erased

  findSubSchema : List (TTName, Binder TT) -> TT -> Tactic
  findSubSchema ctxt goal = Exact $ findSubSchemaProof goal

  occursHere : TTName
  occursHere = (NS "Here" ["Occurs", "Schemas", "DB", "Providers"])

  occursThere : TTName
  occursThere = (NS "There" ["Occurs", "Schemas", "DB", "Providers"])

  -- Construct a proof term witnessing that some key is found in a schema
  findOccursProof : TT -> TT
  findOccursProof goal =
    case unApply goal of
      (occurs, [s, c]) => occursProof (unApply s) c
    where %assert_total occursProof : (TT, List TT) -> TT -> TT
          occursProof (P _ (NS (UN "::") ["Schemas", "DB", "Providers"]) _, [hd, tl]) c =
            let (col, t) = extractAttr (unApply hd) in
            if col == c
              then mkApp (P Ref occursHere Erased) [col, c, t, tl, P Ref (UN "oh") Erased]
              else mkApp (P Ref occursThere Erased) [tl, c, col, t, occursProof (unApply tl) c]
          occursProof other c = (P Ref ("Failed to construct proof that " ++ show c ++ " is in " ++ show other) Erased)

  findOccurs : List (TTName, Binder TT) -> TT -> Tactic
  findOccurs ctxt goal = Exact $ findOccursProof goal

  -- Given a premise that an item occurs in a context where it doesn't, give a proof that it doesn't
  findNotOccursProof : TT -> Maybe TT
  findNotOccursProof h =
    case unApply h of
      (occurs, [s, c]) => notOccursProof' (unApply s) c
      _ => Nothing
    where
          %assert_total notOccursProof' : (TT, List TT) -> TT -> Maybe TT
          notOccursProof' (P _ (NS (UN "Nil") ["Schemas", "DB", "Providers"]) _,  []) c =
            Just $ mkApp (P Ref (NS (UN "noOccursNil") ["Occurs", "Schemas", "DB", "Providers"]) Erased) [c]
          notOccursProof' (P _ (NS (UN "::") ["Schemas", "DB", "Providers"]) _, [hd, tl]) c =
            let step = \tm => mkApp (P Ref (NS (UN "occursInv") ["Occurs", "Schemas", "DB", "Providers"]) Erased)
                                    [ snd (extractAttr (unApply hd))
                                    , fst (extractAttr (unApply hd))
                                    , c
                                    , tl
                                    , P Ref (UN "oh") Erased
                                    , tm
                                    ]
            in [| step (notOccursProof' (unApply tl) c) |]
          notOccursProof' found c =
            Just (P Ref ("b: " ++ show (fst found) ++ " and " ++ show (snd found)) Erased)

  -- Find a proof for a contradiction of an Occurs
  findNotOccurs : List (TTName, Binder TT) -> TT -> Tactic
  findNotOccurs ctxt (Bind n (Pi h) false) =
      case findNotOccursProof h of
        Just prf => Exact prf
        Nothing => Refine ("Couldn't find proof for " ++ show h) -- easy ctxt (Bind n (Pi h) false)
  findNotOccurs ctxt goal = Refine ("Goal not a negation of occurs: " ++ show goal)-- easy ctxt goal

  findHasTable : Nat -> List (TTName, Binder TT) -> TT -> Tactic
  findHasTable O ctxt goal = Refine (NS (UN "Here") ["HasTable"]) `Seq` Solve
  findHasTable (S n) ctxt goal = Try (Refine (NS (UN "Here") ["HasTable"]) `Seq` Solve)
                                     (seq [ Refine (NS (UN "There") ["HasTable"])
                                          , Solve
                                          , findHasTable n ctxt goal])


namespace Query

  data Query : Database -> Schema -> Type where
    T : (db : Database) -> (tbl : String) ->
        {default tactics {applyTactic findHasTable 50; solve; }
         ok : HasTable db tbl s} ->
        Query db s
    Union : Query db s -> Query db s -> Query db s
    Product : Query db s1 -> Query db s2 ->
              {default ()
               ok : isYes (decDisjoint s1 s2)} ->
              Query db (product s1 s2)
    Project : Query db s -> (s' : Schema) ->
              {default tactics { compute; applyTactic findSubSchema; solve; }
               ok : SubSchema s' s } ->
              Query db s'
    Select : Query db s -> Expr s BOOLEAN -> Query db s
    Rename : Query db s -> (from, to : String) ->
             {default tactics { compute; applyTactic findOccurs; solve; }
              fromOK : Occurs s from} ->
             {default tactics { compute; applyTactic findNotOccurs; solve; }
              toOK : Occurs s to -> _|_} ->
             Query db (Schemas.rename s from to fromOK toOK)

  getSchema : Query db s -> Schema
  getSchema {s=s} _ = s

  compileRename : (s : Schema) -> (from, to : String) -> String
  compileRename s from to = foldl (++) "" (intersperse ", " (compileRename' s))
    where
      compileRename' : Schema -> List String
      compileRename' [] = []
      compileRename' (col:::t :: s) =
        if col == from
          then ("\"" ++ from ++ "\" AS \"" ++ to ++ "\"") :: colNames s
          else col :: (compileRename' s)

  compile : Query db s -> String
  compile te = "SELECT * FROM (" ++ compile' te ++ ")"
    where compile' : Query db s -> String
          compile' (T db tbl) = tbl
          compile' (Union t1 t2) = "(" ++ compile' t1 ++ ") UNION (" ++ compile' t2 ++ ")"
          compile' (Product t1 t2) = "(" ++ compile' t1 ++ ") , (" ++ compile' t2 ++ ")"
          compile' (Project t1 s') = "SELECT " ++
                                     (foldl (++) ""
                                       (intersperse ", "
                                         (map (\c => "\"" ++ c ++ "\"") (colNames s')))) ++
                                     " FROM (" ++ compile' t1 ++ ")"
          compile' {s=s} (Select t e) = "SELECT " ++ (foldl (++) "" (intersperse ", " (map (\c => "\"" ++ c ++ "\"") (colNames s)))) ++
                                        " FROM (" ++ compile' t ++ ") WHERE " ++ compileExpr e
          compile' (Rename t from to) = "SELECT " ++ (compileRename (getSchema t) from to) ++
                                        " FROM (" ++ compile' t ++ ")"


  partial  query : Query db s -> Table s
--  query (T t) = t
  query (Union t1 t2) = (query t1) ++ (query t2)
  query (Product t1 t2) = (query t1) * (query t2)
  query (Project t s' {ok=ok}) = map (\r => project r s' ok) (query t)
  query (Select t e) = filter (expr e) (query t)
  query (Rename t from to {fromOK=fromOK} {toOK=toOK}) = map (\r => renameRow r from to fromOK toOK) (query t)


