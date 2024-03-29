{-# LANGUAGE GADTs #-} -- used in testing infrastructure
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Hako where

import Data.Map (Map)
import qualified Data.Map as Map

import Data.List          -- used in testing infrastructure
import Control.Monad      -- used in testing infrastructure
import Control.Exception  -- used in testing infrastructure
import System.IO          -- used in testing infrastructure

import qualified Debug.Trace as Debug

-- Variable names
type VName = String

-- Class names
type CName = String

-- Field names
type FName = String

-- Method names
type MName = String

-- Expressions
data Expr =
     IntE Integer
  |  BoolE Bool
  |  PlusE Expr Expr
  |  TimesE Expr Expr
  |  LtE Expr Expr
  |  GtE Expr Expr
  |  EqE Expr Expr
  |  IfE Expr Expr Expr
  |  VarE VName
  |  LetE VName Expr Expr
  |  BoxE Expr Label
  |  UnboxE Expr
  |  AssignE Expr Expr
  |  FunE String SType Expr
  |  AppE Expr Expr
  |  WhileE Expr Expr
  |  NewE CName [Expr]
  |  GetFieldE Expr FName
  |  SetFieldE Expr FName Expr
  |  CallE Expr MName Expr
  deriving (Eq,Ord,Show)

data Label = Public
           | Secret
  deriving (Eq,Ord,Show)

data Type = IntT
          | BoolT
          | ArrowT SType SType
          | RefT SType
          --
          | ObjectT CName
          | VoidT
  deriving (Eq,Ord,Show)

data MType = MethodT Type Type
  deriving (Eq,Ord,Show)

data SType = ST Type Label
  deriving (Eq,Ord,Show)

type TEnv = Map String SType

-- A sequence expression—written as a semicolon in concrete syntax—is syntactic
-- sugar for a let statement with a variable name that is not used
-- (e₁ ; e₂) ≜ LET _ = e₁ IN e₂
seqE :: Expr -> Expr -> Expr
seqE e1 e2 = LetE "_" e1 e2

-- class declaration
data CDecl = CDecl CName [CName] [FDecl] [MDecl]
  deriving (Eq,Ord,Show)

data FDecl = FDecl FName Type
  deriving (Eq,Ord,Show)

-- method declaration
data MDecl = MDecl MName VName MType Expr
  deriving (Eq,Ord,Show)

-- (See test suite for some example class declarations, method declarations,
-- and expressions that use them.)

-- programs
-- p ∈ prog ⩴ cd … cd DO e
--                       main
--                       expression
--                       ⌄⌄⌄⌄
data Prog = Prog [CDecl] Expr
--               ^^^^^^^
--               class
--               declarations
  deriving (Eq,Ord,Show)

-- object values
data Object = Object CName [Object] (Map FName (Loc,Type)) (Map MName (VName,MType,Expr))
  deriving (Eq,Ord,Show)

-- values
data Value = IntV Integer
           | BoolV Bool
           | FunV Env String Expr
           | ObjectV Object
           | LocV Loc
  deriving (Eq,Ord,Show)

-- locations (domain of the store)
type Loc = Integer

-- environment (maps variable names to values)
type Env = Map VName Value

-- store (maps locations to values)
type Store = Map Loc Value

-- allocate a fresh location in the store
freshLoc :: Store -> Loc
freshLoc store = maximum ((-1):Map.keys store) + 1

-- Allocates a value to fresh location in the store. Returns the fresh location
-- that was generated, and the updated store which maps that location to the
-- value argument.
alloc :: Store -> Value -> (Loc,Store)
alloc store v =
  let l = freshLoc store
  in (l,Map.insert l v store)

-- Perform `alloc` on a list of values.
allocMany :: Store -> [Value] -> ([Loc],Store)
allocMany store [] = ([],store)
allocMany store (v:vs) =
  let (l,store') = alloc store v
      (ls,store'') = allocMany store' vs
  in (l:ls,store'')

-- Lookup the class declaration that corresponds to the given name. Returns
-- `Nothing` if there is no class with the argument name.
lookupClass :: [CDecl] -> CName -> Maybe CDecl
lookupClass [] _ = Nothing
lookupClass (CDecl cn exs fns mds:cds) cn' | cn == cn' = Just (CDecl cn exs fns mds)
lookupClass (CDecl cn exs fns mds:cds) cn' | otherwise = lookupClass cds cn'

-- Constructs a field map from a list of field names and a list of locations.
buildFieldMap :: [FDecl] -> [Loc] -> Maybe (Map FName (Loc, Type))
buildFieldMap [] [] = Just Map.empty
buildFieldMap (FDecl fn t:fds) (l:ls) = case buildFieldMap fds ls of
  Just fm -> Just (Map.insert fn (l,t) fm)
  Nothing -> Nothing
buildFieldMap [] (_:_) = Nothing
buildFieldMap (_:_) [] = Nothing

-- Constructs a method map from a list of method declarations.
buildMethodMap :: [MDecl] -> Map MName (VName,MType,Expr)
buildMethodMap [] = Map.empty
buildMethodMap (MDecl mn x t e:mds) =
  let mm = buildMethodMap mds
  in Map.insert mn (x,t,e) mm

interp :: [CDecl] -> Env -> Store -> Expr -> Maybe (Value,Store)
interp cds env store e0 = case e0 of
  IntE i -> Just (IntV i,store)
  BoolE b -> Just (BoolV b,store)
  PlusE e1 e2 -> case interp cds env store e1 of
    Just (IntV i1,store') -> case interp cds env store' e2 of
      Just (IntV i2,store'') -> Just (IntV (i1 + i2),store'')
      _ -> Nothing
    _ -> Nothing
  TimesE e1 e2 -> case interp cds env store e1 of
    Just (IntV i1,store') -> case interp cds env store' e2 of
      Just (IntV i2,store'') -> Just (IntV (i1 * i2),store'')
      _ -> Nothing
    _ -> Nothing
  LtE e1 e2 -> case interp cds env store e1 of
    Just (IntV i1,store') -> case interp cds env store' e2 of
      Just (IntV i2,store'') -> Just (BoolV (i1 < i2),store'')
      _ -> Nothing
    _ -> Nothing
  GtE e1 e2 -> case interp cds env store e1 of
    Just (IntV i1,store') -> case interp cds env store' e2 of
      Just (IntV i2,store'') -> Just (BoolV (i1 > i2),store'')
      _ -> Nothing
    _ -> Nothing
  EqE e1 e2 -> case interp cds env store e1 of
    Just (IntV i1,store') -> case interp cds env store' e2 of
      Just (IntV i2,store'') -> Just (BoolV (i1 == i2),store'')
      _ -> Nothing
    _ -> Nothing
  IfE e1 e2 e3 -> case interp cds env store e1 of
    Just (BoolV True,store') -> interp cds env store' e2
    Just (BoolV False,store') -> interp cds env store' e3
    _ -> Nothing
  VarE x -> case Map.lookup x env of
    Just v -> Just (v,store)
    Nothing -> Nothing
  LetE x e1 e2 -> case interp cds env store e1 of
    Just (v,store') -> interp cds (Map.insert x v env) store' e2
    Nothing -> Nothing
  FunE x _ e -> Just (FunV env x e,store)
  AppE e1 e2 -> case (interp cds env store e1,interp cds env store e2) of
    (Just (FunV env' x e',store'),Just (v,s)) -> interp cds (Map.insert x v env') store' e'
    _ -> Nothing
  WhileE e1 e2 -> case interp cds env store e1 of
    Just (BoolV b,store') -> if b
                             then case interp cds env store' e2 of
                               Just (v,store'') -> interp cds env store'' (WhileE e1 e2)
                               _ -> Nothing
                             else Just (BoolV True,store')
    _ -> Nothing
  BoxE e _ -> case interp cds env store e of
    Just (v,store') ->
      let l = freshLoc store'
      in Just (LocV l,Map.insert l v store')
    _ -> Nothing
  UnboxE e -> case interp cds env store e of
    Just (LocV l,store') -> case Map.lookup l store' of
      Just v -> Just (v,store')
      Nothing -> Nothing
    _ -> Nothing
  AssignE e1 e2 -> case interp cds env store e1 of
    Just (LocV l,store') -> case interp cds env store' e2 of
      Just (v,store'') -> Just (v,Map.insert l v store'')
      _ -> Nothing
    _ -> Nothing
  NewE cn es -> case lookupClass cds cn of
    Just cd @ (CDecl _ pns _ _) -> case initMany cds env store pns es of
      Just (res,ps,store') -> case new cds env store' cd res of
        Just (ObjectV (Object _ _ fm mm),store'') -> Just (ObjectV (Object cn ps fm mm),store'')
        _ -> Nothing
      Nothing -> Nothing
    Nothing -> Nothing
  GetFieldE e fn -> case interp cds env store e of
    Just (ObjectV (Object _ ps fm _),store') -> case Map.lookup fn fm of
      Just (l,t) -> case Map.lookup l store' of
        Just v -> Just (v,store')
        Nothing -> Nothing
      Nothing -> dispatch cds env store' ps e0
    _ -> Nothing
  SetFieldE e1 fn e2 -> case interp cds env store e1 of
    Just (ObjectV (Object _ ps fm _),store') -> case interp cds env store' e2 of
      Just (v,store'') -> case Map.lookup fn fm of
        Just (l,t) -> Just (v,Map.insert l v store'')
        Nothing -> dispatch cds env store' ps e0
      Nothing -> Nothing
    _ -> Nothing
  CallE e1 mn e2 -> case interp cds env store e1 of
    Just (ObjectV (Object cn ps fm mm),store') -> case interp cds env store' e2 of
      Just (v,store'') -> case Map.lookup mn mm of
        Just (x,t,e) ->
          let env' = mapNames (Map.fromList [("this",ObjectV (Object cn ps fm mm)), (x,v)]) ps
          in case ps of
            (_:_) -> super cds env' store'' ps e
            [] -> interp cds env' store'' e
        Nothing -> dispatch cds env store'' ps e0
      Nothing -> Nothing
    _ -> undefined

-- Perform `interp` on a list of expressions.
interpMany :: [CDecl] -> Env -> Store -> [Expr] -> Maybe ([Value],Store)
interpMany cds env store [] = Just ([],store)
interpMany cds env store (e:es) = case interp cds env store e of
  Just (v,store') -> case interpMany cds env store' es of
    Just (vs,store'') -> Just (v:vs,store'')
    Nothing -> Nothing
  Nothing -> Nothing

-- Create values in the store.
new :: [CDecl] -> Env -> Store -> CDecl -> [Expr] -> Maybe (Value,Store)
new cds env store (CDecl cn _ fns mds) es = case interpMany cds env store es of
  Just (vs,store') ->
    let (ls,store'') = allocMany store' vs
        mm = buildMethodMap mds
    in case buildFieldMap fns ls of
      Just fm -> Just (ObjectV (Object cn [] fm mm),store'')
      Nothing -> Nothing
  Nothing -> Nothing

-- Create objects given a list of class names and expressions. May return a
-- store and uninterpreted expressions.
initMany :: [CDecl] -> Env -> Store -> [CName] -> [Expr] -> Maybe ([Expr],[Object],Store)
initMany cds env store [] es = Just (es,[],store)
initMany cds env store (_:_) [] = Nothing
initMany cds env store (cn:cns) es = case lookupClass cds cn of
  Just cd @ (CDecl _ pns fds _) -> case initMany cds env store pns es of
    Just (res,ps,store') -> case buildExprList fds res of
      Just (es',res') -> case new cds env store' cd es' of
        Just (ObjectV (Object _ _ fm mm),store'') ->
          let o = Object cn ps fm mm
          in case initMany cds env store'' cns res' of
            Just (res'',mps,store''') -> Just (res'',o:mps,store''')
            _ -> Nothing
        _ -> Nothing
      Nothing -> Nothing
    Nothing -> Nothing
  Nothing -> Nothing

-- Map the class name with the object in the environment
mapNames :: Env -> [Object] -> Env
mapNames env [] = env
mapNames env (o @ (Object cn _ _ _):os) =
  mapNames (Map.insert cn (ObjectV o) env) os

-- Decide a subset of a list of expressions that should correspond to a field
-- list. Returns a tuple of expressions: the first is the corresponding
-- expressions, the second being the unmatched expressions.
buildExprList :: [FDecl] -> [Expr] -> Maybe ([Expr],[Expr])
buildExprList [] es = Just ([],es)
buildExprList (_:_) [] = Nothing
buildExprList (fn:fns) (e:es) = case buildExprList fns es of
  Just (es1, es2) -> Just ((e:es1), es2)
  Nothing -> Nothing

-- searches for a valid result from a list of objects in evaluating an
-- expression using 'super'
super :: [CDecl] -> Env -> Store -> [Object] -> Expr -> Maybe (Value,Store)
super cds env store [] e0 = Nothing
super cds env store (o:os) e0 =
  let env' = Map.insert "super" (ObjectV o) env
  in case interp cds env' store e0 of
    Just (v,store') -> Just (v,store')
    Nothing -> super cds env' store os e0

-- Search for an inherited field or method and evaluate it.
dispatch :: [CDecl] -> Env -> Store -> [Object] -> Expr -> Maybe (Value,Store)
dispatch cds env store [] e0 = Nothing
dispatch cds env store (o @ (Object _ ps _ _):os) e0 =
  let env' = Map.insert "this" (ObjectV o) env
      e0' = case e0 of
        GetFieldE e fn -> GetFieldE (VarE "this") fn
        SetFieldE e1 fn e2 -> SetFieldE (VarE "this") fn e2
        CallE e1 mn e2 -> CallE (VarE "this") mn e2
        _ -> e0
  in case interp cds env' store e0' of
    Just (v,store') -> Just (v,store')
    Nothing -> case dispatch cds env' store ps e0 of
      Just (v,store') -> Just (v,store')
      Nothing -> dispatch cds env' store os e0

-- Finds the least upper bound of two elements with respect to our security lattice
joinLabel :: Label -> Label -> Label
joinLabel l1 l2 = if (l1==Secret|| l2==Secret) then Secret else Public

-- Finds the greatest lower bound of two elements with respect to our security lattice
meetLabel :: Label -> Label -> Label
meetLabel l1 l2 = if (l1==Public || l2==Public) then Public else Secret

-- Typable expressions evaluate to final type
-- Implemented with confidentiality/secrecy in mind.
typecheck :: [CDecl] -> TEnv -> Expr -> Maybe SType
typecheck cds env e0 = case e0 of
  IntE i -> Just (ST IntT Public)
  BoolE b -> Just (ST BoolT Public)
  PlusE e1 e2 -> case (typecheck cds env e1, typecheck cds env e2) of
    (Just (ST IntT l1), Just (ST IntT l2)) -> Just (ST IntT (joinLabel l1 l2))
    _ -> Nothing
  TimesE e1 e2 -> case (typecheck cds env e1, typecheck cds env e2) of
    (Just (ST IntT l1), Just (ST IntT l2)) -> Just (ST IntT (joinLabel l1 l2))
    _ -> Nothing
  IfE e1 e2 e3 -> case typecheck cds env e1 of
    Just (ST BoolT l1) -> case (typecheck cds env e2, typecheck cds env e3) of
      (Just (ST t2 l2), Just (ST t3 l3)) ->
        if (t2==t3 && l2==l3 && l1 <= l2)
        then Just (ST t2 (joinLabel l1 (joinLabel l2 l3)))
        else Nothing
      _ -> Nothing
    _ -> Nothing
  LtE e1 e2 -> case (typecheck cds env e1, typecheck cds env e2) of
    (Just (ST IntT l1), Just (ST IntT l2)) -> Just (ST BoolT (joinLabel l1 l2))
    _ -> Nothing
  GtE e1 e2 -> case (typecheck cds env e1, typecheck cds env e2) of
    (Just (ST IntT l1), Just (ST IntT l2)) -> Just (ST BoolT (joinLabel l1 l2))
    _ -> Nothing
  EqE e1 e2 -> case (typecheck cds env e1, typecheck cds env e2) of
    (Just (ST t1 l1), Just (ST t2 l2)) ->
      if t1==t2
      then Just (ST BoolT (joinLabel l1 l2))
      else Nothing
    _ -> Nothing
  VarE x -> Map.lookup x env
  LetE x e1 e2 -> case typecheck cds env e1 of
    Just t1 -> typecheck cds (Map.insert x t1 env) e2
    _ -> Nothing
  FunE x t e -> case typecheck cds (Map.insert x t env) e of
    Just t' -> Just (ST (ArrowT t t') Public)
    Nothing -> Nothing
  AppE e1 e2 -> case (typecheck cds env e1, typecheck cds env e2) of
    (Just (ST (ArrowT s1 (ST t1 l1)) l2), Just s2) ->
      if s1==s2
      then Just (ST t1 (joinLabel l1 l2))
      else Nothing
    _ -> Nothing
  BoxE e1 l1 -> case typecheck cds env e1 of
    Just (ST t2 l2) -> Just (ST (RefT (ST t2 l1)) Public)
    _ -> Nothing
  UnboxE e1 -> case typecheck cds env e1 of
    Just (ST (RefT (ST t1 l1)) Public) -> Just (ST t1 l1)
    _ -> Nothing
  AssignE e1 e2 -> case typecheck cds env e1 of
    Just (ST (RefT (ST t1 l1)) Public) -> case typecheck cds env e2 of
      Just (ST t2 l2) ->
        if (t1==t2 && l1 >= l2)
        then Just (ST t2 l2)
        else Nothing
      _ -> Nothing
    _ -> Nothing
  WhileE e1 e2 -> case typecheck cds env e1 of
    Just (ST BoolT l1) -> case typecheck cds env e2 of
      Just (ST _ l2) ->
        if (l1 <= l2)
        then Just (ST BoolT (joinLabel l1 l2))
        else Nothing
      _ -> Nothing
    _ -> Nothing
  NewE cn es -> case lookupClass cds cn of
    Just cd -> case newFieldCheck cds env cd es of
      True -> Just (ST (ObjectT cn) Public)
      False -> Nothing
    _ -> Nothing
  GetFieldE e1 fn -> case typecheck cds env e1 of
    Just (ST (ObjectT cn) Public) -> case lookupClass cds cn of
      Just (CDecl _ pns fds mds) -> case lookupField fds fn of
        Just (FDecl fn t) -> Just (ST t Public)
        _ -> Nothing
      _ -> Nothing
    _ -> Nothing
  SetFieldE e1 fn e2 -> case typecheck cds env e1 of
    Just (ST (ObjectT cn) Public) -> case lookupClass cds cn of
      Just (CDecl _ pns fds mds) -> case lookupField fds fn of
        Just (FDecl fn t1) -> case typecheck cds env e2 of
          Just (ST t2 Public) ->
            if t1==t2
            then Just (ST VoidT Public)
            else Nothing
          _ -> Nothing
        _ -> Nothing
      _ -> Nothing
    _ -> Nothing
  CallE e1 mn e2 -> case typecheck cds env e1 of
    Just (ST (ObjectT cn) Public) -> case typecheck cds env e2 of
      Just (ST t1 Public) -> case lookupClass cds cn of
        Just (CDecl _ pns fds mds) -> case lookupMethod mds mn of
          Just (MDecl _ vn (MethodT t2 t3) e') ->
            if t1==t2
            then Just (ST t3 Public)
            else Nothing
          _ -> Nothing
        _ -> Nothing
      _ -> Nothing
    _ -> Nothing

newFieldCheck :: [CDecl] -> TEnv -> CDecl -> [Expr] -> Bool
newFieldCheck cds env cd es =
  let (ts) = getAllFieldTypes cds cd in
  let (ts') = getExprTypes cds env es in
  compareTypeList ts ts'

compareTypeList :: [Type] -> [Type] -> Bool
compareTypeList [] [] = True
compareTypeList [] (t':ts') = False
compareTypeList (t:ts) [] = False
compareTypeList (t:ts) (t':ts') = (t==t') && (compareTypeList ts ts')

getAllFieldTypes :: [CDecl] -> CDecl -> [Type]
getAllFieldTypes cds (CDecl cn [] fds mds) = case lookupClass cds cn of
  Just cd -> getFieldTypes cds cd
  _ -> []
getAllFieldTypes cds (CDecl cn (p:ps) fds mds) = case lookupClass cds cn of
  Just cd -> case lookupClass cds p of
    Just (CDecl _ ps' _ _ ) -> case getFieldTypes cds cd of
      ts -> ts ++ (getAllFieldTypes cds (CDecl p (ps++ps') fds mds))
    _ -> []
  _ -> []

getFieldTypes :: [CDecl] -> CDecl -> [Type]
getFieldTypes cds (CDecl cn [] [] mds) = []
getFieldTypes cds (CDecl cn (_:_) [] mds) = []
getFieldTypes cds (CDecl cn ps (FDecl _ t:fds) mds) = t:(getFieldTypes cds (CDecl cn ps fds mds))

getExprTypes :: [CDecl] -> TEnv -> [Expr] -> [Type]
getExprTypes cds env [] = []
getExprTypes cds env (e:es) = case typecheck cds env e of
  Just (ST t Public) -> t:(getExprTypes cds env es)
  _ -> []

lookupMethod :: [MDecl] -> MName -> Maybe MDecl
lookupMethod [] _ = Nothing
lookupMethod (MDecl mn vn t e:mds) mn' | mn == mn' = Just (MDecl mn vn t e)
lookupMethod (MDecl mn vn t e:mds) mn' | otherwise = lookupMethod mds mn'

lookupField :: [FDecl] -> FName -> Maybe FDecl
lookupField [] _ = Nothing
lookupField (FDecl fn t:fds) fn' | fn == fn' = Just (FDecl fn t)
lookupField (FDecl fn t:fds) fn' | otherwise = lookupField fds fn'

interpTests :: [CDecl] -> (Int,String,Expr -> Maybe (Value,Store),[(Expr,Maybe (Value,Store))])
interpTests cds =
  (1
  ,"interp"
  ,interp cds Map.empty Map.empty
  ,[ -- e = LET x = BOX false IN
     --     LET y = BOX 20 IN
     --     IF (x ← true) THEN !x ELSE (y ← 100))
   ( LetE "x" (BoxE (BoolE False) Public) $
     LetE "y" (BoxE (IntE 20) Public) $
     IfE (AssignE (VarE "x") (BoolE True))
         (UnboxE (VarE "x"))
         (AssignE (VarE "y") (IntE 100))
   , Just (BoolV True,Map.fromList [(0,BoolV True),(1,IntV 20)])
   )
   , -- LET b1 = BOX true IN
     -- LET b2 = BOX 3 IN
     -- LOOP !b1 { b2 ← !b2 * !b2 ; b1 ← false }
   ( LetE "b1" (BoxE (BoolE True) Public) $
     LetE "b2" (BoxE (IntE 3) Public) $
     WhileE (UnboxE (VarE "b1")) $
       seqE (AssignE (VarE "b2") (TimesE (UnboxE (VarE "b2")) (UnboxE (VarE "b2")))) $
       AssignE (VarE "b1") (BoolE False)
     -- True
   , Just (BoolV True,Map.fromList [(0,BoolV False),(1,IntV 9)])
   )
   , -- LET i = Box 3 IN
     -- WHILE(!i <= 20) {i ← !i + 3}
   ( LetE "i" (BoxE (IntE 3) Public) $
     WhileE (IfE (EqE (UnboxE (VarE "i")) (IntE 20))
                 (BoolE True)
                 (IfE (LtE (UnboxE (VarE "i")) (IntE 20)) (BoolE True) (BoolE False))) $
            (AssignE (VarE "i") (PlusE (UnboxE (VarE "i")) (IntE 3)))
     -- True
   , Just (BoolV True,Map.fromList [(0,IntV 21)])
   )
   , -- LET p = new Point3D(0,2,3,4) IN
     -- p.mdist(0)
   ( LetE "p" (NewE "Point3D" [IntE 0,IntE 2,IntE 3,IntE 4]) $
     CallE (VarE "p") "mdist" (IntE 0)
     -- ⟨v,σ⟩ = ⟨9,{0↦0,1↦2,2↦3,3↦4}⟩
   , Just (IntV 9,Map.fromList [(0,IntV 0),(1,IntV 2),(2,IntV 3),(3,IntV 4)])
   )
   , -- LET p = new Point3D(2,3,4) IN
     -- p.mdist2(0)
   ( LetE "p" (NewE "Point3D" [IntE 0,IntE 2,IntE 3,IntE 4]) $
     CallE (VarE "p") "mdist2" (IntE 0)
     -- ⟨v,σ⟩ = ⟨9,{0↦0,1↦2,2↦3,3↦4}⟩
   , Just (IntV 9,Map.fromList [(0,IntV 0),(1,IntV 2),(2,IntV 3),(3,IntV 4)])
   )
   , -- LET p = new Point3D(0,2,3,4) IN
     -- p.getX(0)
   ( LetE "p" (NewE "Point3D" [IntE 0,IntE 2,IntE 3,IntE 4]) $
     (CallE (VarE "p") "getX" (IntE 0))
     -- ⟨v,σ⟩ = ⟨2,{0↦2,1↦3,2↦4}⟩
   , Just (IntV 2,Map.fromList [(0,IntV 0),(1,IntV 2),(2,IntV 3),(3,IntV 4)])
   )
   , -- LET p = new Point3D(0,2,3,4) IN
     -- p.x ← 10
     -- p.x
   ( LetE "p" (NewE "Point3D" [IntE 0,IntE 2,IntE 3,IntE 4]) $
     seqE (SetFieldE (VarE "p") "x" (IntE 10)) (GetFieldE (VarE "p") "x")
     -- ⟨v,σ⟩ = ⟨10,{0↦10,1↦3,2↦4}⟩
   , Just (IntV 10,Map.fromList [(0,IntV 0),(1,IntV 10),(2,IntV 3),(3,IntV 4)])
   )
   , -- LET p = new Point3DBool(0,2,3,True,4) IN
     -- p.getB(0)
   ( LetE "p" (NewE "Point3DBool" [IntE 0,IntE 2,IntE 3,BoolE True,IntE 4]) $
     CallE (VarE "p") "getB" (IntE 0)
     -- ⟨v,σ⟩ = ⟨True,{0↦0,1↦2,2↦3,3↦True,4↦4}⟩
   , Just (BoolV True,Map.fromList [(0,IntV 0),(1,IntV 2),(2,IntV 3),(3,BoolV True),(4,IntV 4)])
   )
   , -- LET p = new Point3DBool(0,2,3,True,4) IN
     -- p.getNotB(0)
   ( LetE "p" (NewE "Point3DBool" [IntE 0,IntE 2,IntE 3,BoolE True,IntE 4]) $
     CallE (VarE "p") "getNotB" (IntE 0)
     -- ⟨v,σ⟩ = ⟨True,{0↦0,1↦2,2↦3,3↦True,4↦4}⟩
   , Just (BoolV False,Map.fromList [(0,IntV 0),(1,IntV 2),(2,IntV 3),(3,BoolV True),(4,IntV 4)])
   )
   ]
  )

typecheckTests :: [CDecl] -> (Int,String,Expr -> Maybe SType,[(Expr,Maybe SType)])
typecheckTests cds =
  (2
  ,"typecheck"
  ,typecheck cds Map.empty
  ,[
    -- data should be designated as secret to prevent information flow leakage
    -- technically not illegal because it has not violated non-interference.
    -- !(Box:Secret 10) + 10
    ( PlusE (UnboxE (BoxE (IntE 10) Secret)) (IntE 10)
    -- Int, Secret
    , Just (ST IntT Secret)
    )
    ,
    -- Cannot logically add bool to int. Nothing really to do with security.
    -- 1 + True
    ( PlusE (IntE 1) (BoolE True)
    , Nothing
    )
    ,
    -- Unpredictable final type due to branching, not typable. Nothing to really do with security.
    -- IF False THEN True ELSE 10
    ( IfE (BoolE False) (BoolE True) (IntE 10)
    , Nothing
    )
    ,
    -- Direct Flow of Secret Data to Public Location. Obvious example of bad security.
    -- (Box:Public 0) := !(Box:Secret 1)
    ( AssignE (BoxE (IntE 0) Public) (UnboxE (BoxE (IntE 1) Secret))
    , Nothing
    )
    ,
    -- Basic function application type checking, plus let
    -- let f = (fun x:int,pub -> x + 10) in f(2)
    ( LetE "f" (FunE "x" (ST IntT Public) (PlusE (VarE "x") (IntE 10))) (AppE (VarE "f") (IntE 2))
    , Just (ST IntT Public)
    )
    ,
    -- Same as above, but with type mismatch
    -- let f = (fun x:int,pub -> x + 10) in f(false)
    ( LetE "f" (FunE "x" (ST IntT Public) (PlusE (VarE "x") (IntE 10))) (AppE (VarE "f") (BoolE False))
    , Nothing
    )
    ,
    -- LET b1 = BOX:public true IN
    -- LET b2 = BOX:pulic 3 IN
    -- LOOP !b1 { b2 ← !b2 * !b2 ; b1 ← false }
    ( LetE "b1" (BoxE (BoolE True) Public) $
      LetE "b2" (BoxE (IntE 3) Public) $
      WhileE (UnboxE (VarE "b1")) $
        seqE (AssignE (VarE "b2") (TimesE (UnboxE (VarE "b2")) (UnboxE (VarE "b2")))) $
        AssignE (VarE "b1") (BoolE False)
    , Just (ST BoolT Public)
    )
    ,
    -- This is indirect information flow.
    -- Whether or not the loop happens tells us something about the secret.
    -- LET b1 = BOX:secret true IN
    -- LET b2 = BOX:public 3 IN
    -- LOOP !b1 { b2 ← !b2 * !b2 ; b1 ← false }
    ( LetE "b1" (BoxE (BoolE True) Secret) $
      LetE "b2" (BoxE (IntE 3) Public) $
      WhileE (UnboxE (VarE "b1")) $
        seqE (AssignE (VarE "b2") (TimesE (UnboxE (VarE "b2")) (UnboxE (VarE "b2")))) $
        AssignE (VarE "b1") (BoolE False)
    , Nothing
    )
    ,
    -- We designate objects as strictly public entities.
    -- Not allowed to use secret value as method argument.
    -- LET b1 = BOX:secret true IN
    -- LET p = New Point2D(0,1,2) IN
    -- p.setx(!b1)
    ( LetE "b1" (BoxE (IntE 0) Secret) $
      LetE "p" (NewE "Point2D" [IntE 0,IntE 1,IntE 2]) $
      CallE (VarE "p") "setX" (UnboxE (VarE "b1"))
    , Nothing
    )
    ,
    -- We designate objects as strictly public entities.
    -- Not allowed to use secret value as initialization parameter.
    -- LET b1 = BOX:secret true IN
    -- LET p = New Point2D(!b1,1,2) IN
    -- p.setx(0)
    ( LetE "b1" (BoxE (IntE 0) Secret) $
      LetE "p" (NewE "Point2D" [(UnboxE (VarE "b1")),IntE 1,IntE 2]) $
      CallE (VarE "p") "setX" (IntE 0)
    , Nothing
    )
    ,
    -- Breaks no rules with public data. All Good.
    ( LetE "b1" (BoxE (IntE 0) Public) $
      LetE "p" (NewE "Point2D" [IntE 0,(UnboxE (VarE "b1")),IntE 2]) $
      CallE (VarE "p") "setX" ((UnboxE (VarE "b1")))
    , Just (ST VoidT Public)
    )
    ,
    -- Incorrect Object Creation
    ( NewE "Point2D" [IntE 1,IntE 2]
    , Nothing
    )
    ,
    -- Correct Object Creation (with 2 levels of inheritance)
    ( NewE "Point3D" [IntE 0,IntE 1,IntE 2,IntE 3]
    , Just (ST (ObjectT "Point3D") Public)
    )
    ,
    -- Correct Object Creation (with 2 levels of inheritance, plus multiple inheritance)
    ( NewE "Point3DBool" [IntE 0,IntE 1,IntE 2,BoolE True, IntE 3]
    , Just (ST (ObjectT "Point3DBool") Public)
    )
    ,
    -- Type mismatch, x field has int type. Doesn't work with SetFieldE either.
    ( LetE "p" (NewE "Point2D" [IntE 0,IntE 1,IntE 2]) $
      CallE (VarE "p") "setX" (BoolE True)
    , Nothing
    )
    ,
    -- Indirect information flow from guard to branches.
    ( LetE "b1" (BoxE (IntE 0) Secret) $
      IfE (LtE (UnboxE (VarE "b1")) (IntE 1)) (NewE "Object" [IntE 0]) (NewE "Object" [IntE 1])
      , Nothing
    )
    ]
  )

testInterference :: IO()
testInterference = do
  traceInterference 0 2 3 (AssignE (VarE "hi") (UnboxE (VarE "low")))
-- M1 = { low ↦ 0 , hi ↦ 2 }, M2 = { low ↦ 0 , hi ↦ 3 }
-- e = (low := !hi)
  traceInterference 0 2 3 (AssignE (VarE "low") (UnboxE (VarE "hi")))
-- M1 = { low ↦ 0 , hi ↦ 2 }, M2 = { low ↦ 0 , hi ↦ 3 }
-- e ≜ if (!hi = 3) then low := 1 else low :=2
  traceInterference 0 2 3 (IfE (EqE (UnboxE (VarE "hi")) (IntE 3)) (AssignE (VarE "low") (IntE 1)) (AssignE (VarE "low") (IntE 2)))
-- M1 = { low ↦ 0 , hi ↦ 0 }, M2 = { low ↦ 0 , hi ↦ 1 }
-- e ≜ while (!hi < 0) { low := 8; hi := !hi + 1 }
  traceInterference 0 0 1 (WhileE (LtE (UnboxE (VarE "hi")) (IntE 1)) $
        seqE (AssignE (VarE "low") (IntE 8)) $
        AssignE (VarE "hi") (PlusE (IntE 1) (UnboxE (VarE "hi"))))

-- Δ = { low ↦ int·Public , hi ↦ int·Secret }
--                 M1 & M2 Low   M1 hi      M2 hi
--                    vvvvv      vvvvv      vvvvv
traceInterference :: Integer -> Integer -> Integer -> Expr -> IO()
traceInterference low hi1 hi2 e' =
  let e1 = LetE "low" (BoxE (IntE low) Public) $ LetE "hi" (BoxE (IntE hi1) Secret) (e') in
  let e2 = LetE "low" (BoxE (IntE low) Public) $ LetE "hi" (BoxE (IntE hi2) Secret) (e') in
  case (interp [] Map.empty Map.empty e1, interp [] Map.empty Map.empty e2) of
  (Just (_,s1), Just (_,s2)) -> do
    putStrLn ""
    putStr $ "Input: M1 = {low -> " ++ show low ++ ", hi -> " ++ show hi1 ++ "}, "
    putStrLn $ "M2 = {low -> " ++ show low ++ ", hi -> " ++ show hi2 ++ "}"
    putStrLn $ "Expr: " ++ show e'
    putStr $ "Output: M1' = {low -> " ++ show (getV 0 s1) ++ ", hi -> " ++ show (getV 1 s1) ++ "}, "
    putStrLn $ "M2' = {low -> " ++ show (getV 0 s2) ++ ", hi -> " ++ show (getV 1 s2) ++ "}"
    if (getV 0 s1) == (getV 0 s2)
    then putStrLn "Secure: change in secret input does not affect public output. Typing should succeed"
    else putStrLn "Not Secure: change in secret input affects public output. Typing Should Fail."
  _ -> putStrLn "Expression invalid."

getV :: Loc -> Store -> Integer
getV loc store = case Map.lookup loc store of
  Just (IntV v) -> v
  _ -> 0

---------------
-- ALL TESTS --
---------------

allTests :: [Test]
allTests =
  let cds =
        [ CDecl "Object" []
                [ FDecl "hash" IntT]
                [ MDecl "getHash" "_" (MethodT IntT IntT) (GetFieldE (VarE "this") "hash") ]
        , CDecl "ABool" []
                [ FDecl "b" BoolT]
                [ MDecl "getB" "_" (MethodT IntT BoolT) (GetFieldE (VarE "this") "b")
                , MDecl "setB" "b" (MethodT BoolT VoidT) (SetFieldE (VarE "this") "b" (VarE "b"))
                ]
        , CDecl "Point2D" ["Object"]
                [ FDecl "x" IntT, FDecl "y" IntT]
                [ MDecl "getX" "_" (MethodT IntT IntT) (GetFieldE (VarE "this") "x")
                , MDecl "getY" "_" (MethodT IntT IntT) (GetFieldE (VarE "this") "y")
                , MDecl "setX" "x" (MethodT IntT VoidT) (SetFieldE (VarE "this") "x" (VarE "x"))
                , MDecl "setY" "y" (MethodT IntT VoidT) (SetFieldE (VarE "this") "y" (VarE "y"))
                , MDecl "mdist" "_" (MethodT IntT IntT) (PlusE (CallE (VarE "this") "getX" (IntE 1))
                                                               (CallE (VarE "this") "getY" (IntE 2)))
                ]
        , CDecl "Point3D" ["Point2D"]
                [ FDecl "z" IntT]
                [ MDecl "getZ" "_" (MethodT IntT IntT) (GetFieldE (VarE "this") "z")
                , MDecl "setZ" "z" (MethodT IntT VoidT) (SetFieldE (VarE "this") "z" (VarE "z"))
                , MDecl "mdist" "_" (MethodT IntT IntT) (PlusE (CallE (VarE "super") "mdist" (IntE 3))
                                                               (CallE (VarE "this") "getZ" (IntE 4)))
                , MDecl "mdist2" "_" (MethodT VoidT IntT) (PlusE (CallE (VarE "Point2D") "mdist" (IntE 3))
                                                                 (CallE (VarE "this") "getZ" (IntE 4)))
                ]
        , CDecl "Point3DBool" ["Point2D", "ABool"]
                [ FDecl "z" IntT]
                [ MDecl "getZ" "_" (MethodT IntT IntT) (GetFieldE (VarE "this") "z")
                , MDecl "setZ" "z" (MethodT IntT VoidT) (SetFieldE (VarE "this") "z" (VarE "z"))
                , MDecl "mdist" "_" (MethodT IntT IntT) (PlusE (CallE (VarE "super") "mdist" (IntE 3))
                                                               (CallE (VarE "this") "getZ" (IntE 4)))
                , MDecl "getNotB" "_" (MethodT IntT BoolT) (LetE "b" (CallE (VarE "super") "getB" (IntE 0))
                                                                     (IfE (VarE "b") (BoolE False) (BoolE True)))
                ]
        ]
  in
  [ Test1 (interpTests cds)
  , Test1 (typecheckTests cds)
  ]

----------------------
-- MAIN = RUN TESTS --
----------------------

main :: IO ()
main = do
  runTests allTests
  testInterference

----------------------------
-- TESTING INFRASTRUCTURE --
----------------------------

mapOn :: [a] -> (a -> b) -> [b]
mapOn = flip map

foldMOn :: (Foldable t,Monad m) => b -> t a -> (b -> a -> m b) -> m b
foldMOn i xs f = foldM f i xs

data Test where
  Test1 :: (Show a,Eq b,Show b) => (Int,String,a -> b,[(a,b)]) -> Test
  Test2 :: (Show a,Show b,Eq c,Show c) => (Int,String,a -> b -> c,[((a,b),c)]) -> Test
  Test3 :: (Show a,Show b,Show c,Eq d,Show d) => (Int,String,a -> b -> c -> d,[((a,b,c),d)]) -> Test

runTests :: [Test] -> IO ()
runTests ts = do
  rs <- forM ts $ \ t -> do
    y <- case t of
      Test1 t -> runTests1 t
      Test2 t -> runTests2 t
      Test3 t -> runTests3 t
    putStrLn ""
    return y
  forM_ (zip [1..] rs) $ \ (m,(n,passed,failed)) -> do
    when (m /= 1) $ putStrLn ""
    putStrLn $ "++ E" ++ show n ++ " Tests Passed: " ++ show passed
    putStrLn $ "-- E" ++ show n ++ " Tests Failed: " ++ show failed

showTestResult :: (Eq a,Show a) => String -> a -> Either String a -> (Int,Int) -> IO (Int,Int)
showTestResult fx y y'M (passed,failed) = do
  let eM = case y'M of
        Left e -> Just $ "[ERROR]: " ++ e
        Right y' ->
          if y' == y
          then Nothing
          else Just $ show y'
  case eM of
    Nothing -> do
      putStrLn $ "   [TEST PASSED]: " ++ fx
      hFlush stdout
      return (passed+1,failed)
    Just s -> do
      putStrLn $ "   [TEST FAILED]:"
      putStrLn $ "     -- the input"
      putStrLn $ "     " ++ fx
      putStrLn $ "   =="
      putStrLn $ "     -- the output"
      putStrLn $ "     " ++ s
      putStrLn $ "   /="
      putStrLn $ "     -- the expected result"
      putStrLn $ "     " ++ show y
      hFlush stdout
      return (passed,failed+1)

runTestsN :: (Eq a,Show a) => Int -> String -> [(String,() -> a,a)] -> IO (Int,Int,Int)
runTestsN n name tests = do
  putStrLn $ ">> E" ++ show n ++ " Tests: " ++ name
  (passed,failed) <- foldMOn (0,0) tests $ \ pf (s,fx,y) -> do
    y'M <- catch (Right <$> evaluate (fx ())) $ \ (SomeException e) -> return $ Left $ chomp $ unwords $ lines $ show e
    showTestResult s y y'M pf
  return (n,passed,failed)
  where
    chomp s0 = concat $ mapOn (group s0) $ \ s ->
      if " " `isPrefixOf` s then " " else s

runTests1 :: (Eq b,Show a,Show b) => (Int,String,a -> b,[(a,b)]) -> IO (Int,Int,Int)
runTests1 (n,name,f,tests) = runTestsN n name $ mapOn tests $ \ (x,y) ->
  (name ++ " " ++ showsPrec 11 x [],\() -> f x,y)

runTests2 :: (Eq c,Show a,Show b,Show c) => (Int,String,a -> b -> c,[((a,b),c)]) -> IO (Int,Int,Int)
runTests2 (n,name,f,tests) = runTestsN n name $ mapOn tests $ \ ((x,y),z) ->
  (name ++ " " ++ showsPrec 11 x [] ++ " " ++ showsPrec 11 y [],\() -> f x y,z)

runTests3 :: (Eq d,Show a,Show b,Show c,Show d) => (Int,String,a -> b -> c -> d,[((a,b,c),d)]) -> IO (Int,Int,Int)
runTests3 (n,name,f,tests) = runTestsN n name $ mapOn tests $ \ ((w,x,y),z) ->
  (name ++ " " ++ showsPrec 11 w [] ++ " " ++ showsPrec 11 x [] ++ " " ++ showsPrec 11 y [],\() -> f w x y,z)
