{- Florent Balestrieri -- August 2015

A new way to define fixed-points for mutually recursive
datatypes using type families instead of gadts.

We apply this technique to the
definition of zippers and attribute grammars.
-}

-- ** Options
{-# Language
  TypeOperators
, DataKinds
, FlexibleInstances
, FlexibleContexts
, UndecidableInstances
, MultiParamTypeClasses
, TypeFamilies
, ConstraintKinds
, NoMonomorphismRestriction
, ViewPatterns
, RecordWildCards
 #-}

module Desk where
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)

-- * Type proxy
data P t = P

-- * A new way to define fixed-points for mutually recursive datatypes
{- using type families instead of gadts -}
-- ** A type family
-- it is a defunctionalisation technique: our functions are
-- given a name "t :: *" and the family ":@" applies those functions.
type family (:@) t (f :: * -> *)

-- ** Base functors
data Prog t = Print (EXP t) (DEFS t)
data Exp  t = EXP t :+ FACT t | Fct (FACT t)
data Fact t = Var String | Cst Int
data Defs t = DCons (DEF t) (DEFS t) | DNil
data Def  t = String := Int

type PROG t =  t :@ Prog
type EXP  t =  t :@ Exp 
type FACT t =  t :@ Fact
type DEFS t =  t :@ Defs
type DEF  t =  t :@ Def

-- ** fixed-points
{- what's beautiful with this technique is
that we don't need another constructor like "InFix"
as in:
data Fix f = InFix (f (Fix f))
-}
data Fix
fixP = P :: P Fix

type instance Fix :@ f = f Fix
type FIX f = Fix :@ f

deskExample :: FIX Prog
deskExample =
  Print (Fct (Var "x") :+ Var "y" :+ Cst 11)
    $ defs ["x" := 22, "y" := 33]

defs = foldr DCons DNil

-- * Case analysis
{- Unfortunately we need a type proxy in order to identify
the correct instance. To avoid it, we could tag every
constructor with the proxy, but then its the same burden as having the
"InFix" constructor.
-}

class View t f where
  view :: P t -> t :@ f -> f t
  view = const view'
  view' :: t :@ f -> f t
  view' = view P

fview = view fixP
zview = view zipP

instance View Fix Prog where view' = id
instance View Fix Exp  where view' = id
instance View Fix Fact where view' = id
instance View Fix Defs where view' = id
instance View Fix Def  where view' = id

-- ** Example
{- Case analysis is polymorphic, thus we can define
recursive functions that work both on the datatype and its zipper
-}

{- one advantage compared to using gadts is that
types are inferred.
-}
defsFold t c n x = case view t x of
  DNil -> n
  DCons d ds -> c d (defsFold t c n ds)

defsLength t = defsFold t (const (+1)) 0

progDefs t (view t -> Print e ds) = ds
progDefsLen t = defsLength t . progDefs t

exView = 
  ( progDefsLen fixP deskExample
  , progDefsLen zipP $ top deskExample)

-- * Contexts and Zipper
data ProgC c t = TopProg
data ExpC c t = TopExp
  | Print'Exp (PROG c) (DEFS t)
  | Add'Left (EXP c) (FACT t)
data FactC c t = TopFact
  | Add'Right (EXP c) (EXP t)
  | Fct' (EXP c)
data DefsC c t = TopDefs
  | Print'Defs (PROG c) (EXP t)
  | Tail (DEFS c) (DEF t)
data DefC c t = TopDef
  | Head (DEFS c) (DEFS t)

type family Context (f :: * -> *) where
  Context Prog = ProgC
  Context Exp  = ExpC
  Context Fact = FactC
  Context Defs = DefsC
  Context Def  = DefC

data Ctx
type instance Ctx :@ f  = Context f Ctx Fix
type CTX f = Ctx :@ f

infixr 5 :-
data c :- e = c :- e

data Zip = Zip
zipP = P :: P Zip
type instance Zip :@ f = CTX f :- FIX f
type ZIP f = Zip :@ f

data ZipCtx
type instance ZipCtx :@ f = Context f Zip Zip
type ZCTX f = ZipCtx :@ f

-- ** View, ZCtx instances for Zipper
class View Zip f => ZCtx f where
  ctx :: ZIP f -> ZCTX f
  top :: FIX f -> ZIP f

instance View Zip Prog where
  view' (c :- Print e ds) =
    Print (Print'Exp c ds :- e) (Print'Defs c e :- ds)

instance ZCtx Prog where
  top = (TopProg :-)
  ctx (TopProg :- e) = TopProg

instance View Zip Exp where
  view' (c :- e :+ f) =
    (Add'Left c f :- e) :+ (Add'Right c e :- f)
  view' (c :- Fct f) = Fct (Fct' c :- f)

instance ZCtx Exp where
  top = (TopExp :-)
  ctx (TopExp :- e) = TopExp
  ctx (Print'Exp p ds :- e) =
    Print'Exp (p :- Print e ds) (Print'Defs p e :- ds)
  ctx (Add'Left c f :- e) =
    Add'Left (c :- (e :+ f)) (Add'Right c e :- f)

instance View Zip Fact where
  view' (c :- Var s) = Var s
  view' (c :- Cst f) = Cst f

instance ZCtx Fact where
  top = (TopFact :-)
  ctx (TopFact :- f) = TopFact
  ctx (Add'Right c e :- f) =
    Add'Right (c :- (e :+ f)) (Add'Left c f :- e)
  ctx (Fct' c :- f) = Fct' (c :- Fct f)

instance View Zip Defs where
  view' (c :- DNil) = DNil
  view' (c :- DCons d ds) =
    DCons (Head c ds :- d) (Tail c d :- ds)

instance ZCtx Defs where
  top = (TopDefs :-)
  ctx (TopDefs :- ds) = TopDefs
  ctx (Tail c d :- ds) =
    Tail (c :- DCons d ds) (Head c ds :- d)
  ctx (Print'Defs c e :- ds) =
    Print'Defs (c :- Print e ds) (Print'Exp c ds :- e)

instance View Zip Def where
  view' (c :- s := i) = s := i

instance ZCtx Def where
  top = (TopDef :-)
  ctx (TopDef :- d) = TopDef
  ctx (Head c ds :- d) =
    Head (c :- DCons d ds) (Tail c d :- ds)

-- * Attribute Grammar
data Instr = LOAD Int | ADD Int | PRINT | HALT
  deriving Show

codeProg (zview -> Print e ds) =
  if okDefs ds then codeExp e ++ [PRINT, HALT] else [HALT]

codeExp x = case zview x of
  e :+ f -> if okFact f then codeExp e ++ [ADD $ valueFact f] else [HALT]
  Fct f -> if okFact f then [LOAD $ valueFact f] else [HALT]

okFact x = case zview x of
  Var name -> Map.member name (enviFact x)
  Cst _ -> True

okDefs x = case zview x of
  DNil -> True
  DCons h t -> okDefs t && not (Map.member (name h) (envs t))

valueFact x = case zview x of
  Var name -> fromJust $ Map.lookup name (enviFact x)
  Cst x -> x
valueDef (zview -> n := x) = x
name (zview -> n := x) = n

envs x = case zview x of
  DNil -> Map.empty
  DCons h t -> Map.insert (name h) (valueDef h) (envs t)

-- An inherited attribute inspects its context.
enviExp x = case ctx x of
  Print'Exp c ds -> envs ds
  Add'Left c f -> enviExp c -- copy from parent

enviFact x = case ctx x of
  Add'Right c e -> enviExp c -- copy from parent
  Fct' c -> enviExp c -- copy from parent

test1 = codeProg (TopProg :- deskExample)
test2 = codeProg $ TopProg :-
        Print (Fct (Cst 11)) (defs ["x" := 22, "x" := 33])
test3 = codeProg $ TopProg :-
        Print (Fct (Var "x")) DNil
