-- ** Options
{-# LANGUAGE
  GADTs
 , MultiParamTypeClasses
 , LambdaCase
 , TypeSynonymInstances
 , RankNTypes
 , TypeOperators
 , TypeFamilies
 , ViewPatterns
 #-}
-- ** Module
module Desk where
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)

type a :-> b = forall n . a n -> b n

-- ** Datatypes
data PROG
data EXP 
data FACT
data DEFS
data DEF 

  -- ** Base functor
data F x n where
  Print :: x EXP -> x DEFS -> F x PROG
  Add   :: x EXP -> x FACT -> F x EXP
  Fct   :: x FACT -> F x EXP
  Var   :: String -> F x FACT
  Cst   :: Int -> F x FACT
  DCons :: x DEF -> x DEFS -> F x DEFS
  DNil  :: F x DEFS
  Def   :: String -> Int -> F x DEF

-- ** Derivative
data D x m n where
  Print'Exp  :: x DEFS -> D x PROG EXP
  Add'Left   :: x FACT -> D x EXP EXP
  Add'Right  :: x EXP -> D x EXP FACT
  Fct'       :: D x EXP FACT
  Print'Defs :: x EXP -> D x PROG DEFS
  Tail       :: x DEF -> D x DEFS DEFS
  Head       :: x DEFS -> D x DEFS DEF

-- ** expressions
data E n = In {outE :: F E n}

-- ** context
data C n where
  Root :: C n
  (:-) :: C m -> D E m n -> C n

data OutCtx t n where
  Top :: OutCtx t n
  (:>) :: t m -> D t m n -> OutCtx t n

-- ** Zipper
data Z n = C n :| E n

-- ** Views
class Out t where
  out :: t n -> F t n

instance Out E where
  out = outE

instance Out Z where
  out (c :| e) = case out e of
    Print e ds -> Print (c :- Print'Exp ds :| e)
                        (c :- Print'Defs e :| ds)
    Add   e f  -> Add   (c :- Add'Left f  :| e)
                        (c :- Add'Right e :| f)
    Fct   f    -> Fct   (c :- Fct' :| f)
    Var   s    -> Var   s
    Cst   x    -> Cst   x
    DCons d ds -> DCons (c :- Head ds :| d)
                        (c :- Tail d  :| ds)
    DNil       -> DNil  
    Def   s x  -> Def   s x

-- *** Context View
class Out t => Ctx t where
  ctx :: t n -> OutCtx t n

instance Ctx Z where
  ctx (c :| e) = case c of
    Root -> Top
    c :- d -> (c :| up e d) :> sibling c e d

up :: E n -> D E m n -> E m
up x d = In $ case d of
  Print'Exp ds  -> Print x ds
  Add'Left  f   -> Add x f
  Add'Right e   -> Add e x
  Fct'          -> Fct x
  Print'Defs e  -> Print e x
  Tail       d  -> DCons d x
  Head       ds -> DCons x ds

sibling :: C m -> E n -> D E m n -> D Z m n
sibling c x = \case
  Print'Exp  ds  -> Print'Exp  $ c :- Print'Defs x :| ds
  Add'Left   f   -> Add'Left   $ c :- Add'Right x :| f
  Add'Right  e   -> Add'Right  $ c :- Add'Left x :| e
  Fct'           -> Fct'
  Print'Defs e   -> Print'Defs $ c :- Print'Exp x :| e
  Tail       d   -> Tail       $ c :- Head x :| d
  Head       ds  -> Head       $ c :- Tail x :| ds

-- ** Attribute Grammar
data Instr = LOAD Int | ADD Int | PRINT | HALT
  deriving Show

-- *** Attributes

type family Code n where
  Code PROG = [Instr]
  Code EXP = [Instr]
  Code n = ()

type family Name n where
  Name DEF = String
  Name n = ()

type family Value n where
  Value DEF = Int
  Value FACT = Int
  Value n = ()

type family Ok n where
  Ok DEFS = Bool
  Ok FACT = Bool
  Ok n = ()

type SymbolTable = Map String Int
type family Envs n where
  Envs DEFS = SymbolTable
  Envs n = ()

type family Envi n where
  Envi EXP = SymbolTable
  Envi FACT = SymbolTable
  Envi n = ()
  
-- *** Semantic Rules

code :: (Ctx t) => t :-> Code
code x = case out x of
  Print e ds -> if ok ds then code e ++ [PRINT, HALT] else [HALT]
  Add e f    -> if ok f then code e ++ [ADD $ value f] else [HALT]
  Fct f      -> if ok f then [LOAD $ value f] else [HALT]
  Var   {}   -> ()
  Cst   {}   -> ()
  DCons {}   -> ()
  DNil  {}   -> ()
  Def   {}   -> ()

ok :: (Ctx t) => t :-> Ok
ok x = case out x of
  Print {}  -> ()
  Add   {}  -> ()
  Fct   {}  -> ()
  Var name  -> Map.member name (envi x)
  Cst _     -> True
  DCons h t -> ok t && not (Map.member (name h) (envs t))
  DNil      -> True
  Def   {}  -> ()

value :: (Ctx t) => t :-> Value
value x = case out x of
  Print {} -> ()
  Add   {} -> ()
  Fct   {} -> ()
  Var name -> fromJust $ Map.lookup name (envi x)
  Cst x    -> x
  DCons {} -> ()
  DNil  {} -> ()
  Def n x  -> x

name :: (Out t) => t :-> Name
name x = case out x of
  Print {} -> ()
  Add   {} -> ()
  Fct   {} -> ()
  Var   {} -> ()
  Cst   {} -> ()
  DCons {} -> ()
  DNil  {} -> ()
  Def n x  -> n


envs :: (Ctx t) => t :-> Envs
envs x = case out x of
  Print {}  -> ()
  Add   {}  -> ()
  Fct   {}  -> ()
  Var   {}  -> ()
  Cst   {}  -> ()
  DCons h t -> Map.insert (name h) (value h) (envs t)
  DNil      -> Map.empty
  Def   {}  -> ()  
  
-- An inherited attribute inspects its context.
envi :: (Ctx t) => t :-> Envi
envi x = case ctx x of
  c :> Print'Exp ds -> envs ds
  c :> Add'Left{}   -> envi c -- copy from parents
  c :> Add'Right{}  -> envi c
  c :> Fct'{}       -> envi c
  c :> Print'Defs{} -> envi c
  c :> Tail{}       -> envi c
  c :> Head{}       -> envi c

-- ** Example
res2 f g x y = f $ g x y

iprint = res2 In Print
(+:) = res2 In Add
fct = In . Fct
var = In . Var
cst = In . Cst
defs = foldr (res2 In DCons) (In DNil)
(=:) = res2 In Def

deskExample =
  iprint (fct (var "x") +: var "y" +: cst 11)
    $ defs ["x" =: 22, "y" =: 33]

test = code $ Root :| deskExample

-- * Partial version
{-
{-   Simple type synonyms don't capture the fact that
   attributes are not defined for every non-terminals. -}

type Code n = [Instr]
type Name n = String
type Value n = Int
type Ok n = Bool
type SymbolTable = Map String Int
type Envs n = SymbolTable
type Envi n = SymbolTable

code :: (Ctx t) => t :-> Code
code x = case out x of
  Print e ds -> if ok ds then code e ++ [PRINT, HALT] else [HALT]
  Add e f -> if ok f then code e ++ [ADD $ value f] else [HALT]
  Fct f -> if ok f then [LOAD $ value f] else [HALT]

ok :: (Ctx t) => t :-> Ok
ok x = case out x of
  Var name -> Map.member name (envi x)
  Cst _ -> True
  DNil -> True
  DCons h t -> ok t && not (Map.member (name h) (envs t))

value :: (Ctx t) => t :-> Value
value x = case out x of
  Var name -> fromJust $ Map.lookup name (envi x)
  Cst x -> x
  Def n x -> x

name :: (Out t) => t :-> Name
name (out -> Def n x) = n 

envs :: (Ctx t) => t :-> Envs
envs x = case out x of
  DNil -> Map.empty
  DCons h t -> Map.insert (name h) (value h) (envs t)

-- An inherited attribute inspects its context.
envi :: (Ctx t) => t :-> Envi
envi x = case ctx x of
  c :> Print'Exp ds -> envs ds
  c :> _ -> envi c
-}

