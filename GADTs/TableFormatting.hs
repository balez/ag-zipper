-- ** Options
{-# LANGUAGE
  GADTs
 , MultiParamTypeClasses
 , LambdaCase
 , TypeSynonymInstances
 , RankNTypes
 , TypeOperators
 , TypeFamilies
 #-}
-- ** Module
module TableFormatting where
{-
newtype Table = Table Rows
type Rows = [Row]
newtype Row = Row Elems
type Elems = [Elem]
data Elem = Str String | Tab Table
-}

res2 f g x y = f $ g x y

type a :-> b = forall n . a n -> b n

-- ** Datatypes
data TABLE
data ROWS
data ROW
data ELEMS
data ELEM

-- ** Base functor
data F x n where
  Table     :: x ROWS -> F x TABLE
  RowsNil   :: F x ROWS
  RowsCons  :: x ROW -> x ROWS -> F x ROWS
  Row       :: x ELEMS -> F x ROW
  ElemsNil  :: F x ELEMS
  ElemsCons :: x ELEM -> x ELEMS -> F x ELEMS
  Str       :: String -> F x ELEM
  Tab       :: x TABLE -> F x ELEM

-- ** Derivative
data D x m n where
  TableRows :: D x TABLE ROWS
  RowsHead  :: x ROWS -> D x ROWS ROW
  RowsTail  :: x ROW -> D x ROWS ROWS
  RowElems  :: D x ROW ELEMS
  ElemsHead :: x ELEMS -> D x ELEMS ELEM
  ElemsTail :: x ELEM -> D x ELEMS ELEMS
  ElemTable :: D x ELEM TABLE

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
    Table     r   -> Table (c :- TableRows :| r)
    RowsNil       -> RowsNil
    RowsCons  h t -> RowsCons (c :- RowsHead t :| h)
                              (c :- RowsTail h :| t)
    Row       l   -> Row (c :- RowElems :| l)
    ElemsNil      -> ElemsNil
    ElemsCons h t -> ElemsCons (c :- ElemsHead t :| h)
                               (c :- ElemsTail h :| t)
    Str       s   -> Str s
    Tab       t   -> Tab (c :- ElemTable :| t)

-- *** Context View
class Out t => Ctx t where
  ctx :: t n -> OutCtx t n

instance Ctx Z where
  ctx (c :| e) = case c of
    Root -> Top
    c :- d -> (c :| up e d) :> sibling c e d

up :: E n -> D E m n -> E m
up e d = In $ case d of
  TableRows   -> Table e
  RowsHead t  -> RowsCons e t
  RowsTail h  -> RowsCons h e
  RowElems    -> Row e
  ElemsHead t -> ElemsCons e t
  ElemsTail h -> ElemsCons h e
  ElemTable   -> Tab e

sibling :: C m -> E n -> D E m n -> D Z m n
sibling c e = \case
  TableRows   -> TableRows
  RowsHead t  -> RowsHead $ c :- RowsTail e :| t
  RowsTail h  -> RowsTail $ c :- RowsHead e :| h  
  RowElems    -> RowElems
  ElemsHead t -> ElemsHead $ c :- ElemsTail e :| t 
  ElemsTail h -> ElemsTail $ c :- ElemsHead e :| h 
  ElemTable   -> ElemTable   

-- ** Example
table = In . Table
rowsNil = In RowsNil
rowsCons = In `res2` RowsCons
row = In . Row
elemsNil = In ElemsNil
elemsCons = res2 In ElemsCons
elemStr = In . Str
elemTab = In . Tab
exTable = table $ rowsCons (row $ elemsCons (elemStr "the")
                                $ elemsCons (elemStr "table")
                                $ elemsNil)
                $ rowsCons (row $ elemsCons (elemTab innerTable)
                                $ elemsCons (elemStr "carte")
                                $ elemsNil)
                $ rowsNil
 where
    innerTable = table $ rowsCons (row $ elemsCons (elemTab t1)
                                       $ elemsCons (elemStr "using")
                                       $ elemsNil)
                       $ rowsCons (row $ elemsCons (elemTab t2)
                                       $ elemsCons (elemTab t3)
                                       $ elemsNil)
                  $ rowsNil
    t1 = table $ rowsCons (row $ elemsCons (elemStr "formatter") elemsNil)
               $ rowsCons (row $ elemsCons (elemStr "written") elemsNil)
               $ rowsNil
    t2 = table $ rowsCons (row $ elemsCons (elemStr "attribute")
                               $ elemsCons (elemStr "grammars")
                               $ elemsNil)
               $ rowsNil
    t3 = table $ rowsCons (row $ elemsCons (elemStr "a") elemsNil)
               $ rowsCons (row $ elemsCons (elemStr "la") elemsNil)
               $ rowsNil

-- * Rules

-- minheight
-- the type signature can't be inferred.  
mh :: Out t => t n -> Int
mh t = case out t of
  Table     r    -> mh r + 1
  RowsNil        -> 0
  RowsCons  r rs -> mh r + mh rs
  Row       e    -> mh e
  ElemsNil       -> 0
  ElemsCons e es -> mh e `max` mh es
  Str       s    -> 2
  Tab       t    -> mh t + 1

-- minwidths
type family MWS n where
  MWS TABLE = Int
  MWS ROWS  = [Int]
  MWS ROW   = [Int]
  MWS ELEMS = [Int]
  MWS ELEM  = Int

-- type cannot be inferred
lmw :: Out t => t ROWS -> Int
lmw r = sum (mws r)

-- type cannot be inferred
mws :: Out t => t :-> MWS 
mws t = case out t of
  Table     r    -> lmw r + 1
  RowsNil        -> repeat 0
  RowsCons  r rs -> zipWith max (mws r) (mws rs)
  Row       e    -> mws e
  ElemsNil       -> []
  ElemsCons e es -> mws e : mws es
  Str       s    -> length s + 1
  Tab       t    -> mws t + 1
