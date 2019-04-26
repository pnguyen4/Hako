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
-- x ∈ vname ≈ symbol
type VName = String
-- Class names
-- cn ∈ cname ≈ symbol
type CName = String
-- Field names
-- fn ∈ fname ≈ symbol
type FName = String
-- Method names
-- mn ∈ mname ≈ symbol
type MName = String

-- Expressions
-- e ∈ expr ⩴ i | e + e | e × e
--          | x | LET x = e IN e
--          | FUN (x:τ) ⇒ e
--          | e(e)
--          | WHILE(e){e}
--          | BOX(e)
--          | !e
--          | e ← e
--          | NEW cn(e,…,e)
--          | e.fn
--          | e.fn ← e
--          | e.mn(e)    -- all methods take exactly one argument
--
data Expr =
     IntE Integer Label
  |  BoolE Bool Label
  |  PlusE Expr Expr
  |  TimesE Expr Expr
  |  IfE Expr Expr Expr
  |  VarE VName
  |  LetE VName Expr Expr
  |  BoxE Expr Label
  |  UnboxE Expr
  |  AssignE Expr Expr
  |  FunE String Type Expr
  |  AppE Expr Expr
  |  WhileE Expr Expr
  |  NewE CName [Expr]
  |  GetFieldE Expr FName
  |  SetFieldE Expr FName Expr
  |  CallE Expr MName Expr
  deriving (Eq,Ord,Show)

-- ς ∈ label ⩴ Secret
--           | public
data Label = Secret
           | Public
  deriving (Eq,Ord,Show)

-- τ ∈ type ⩴ int
--          | bool
--          | φ ⇒ φ
data Type = IntT
          | BoolT
          | ArrowT SType SType
          | LocT SType
  deriving (Eq,Ord,Show)

-- φ ∈ stype ⩴ τ:ς
data SType = ST Type Label
  deriving (Eq,Ord,Show)

-- Γ ∈ tenv ≜ var ⇀ stype
type TEnv = Map String SType

-- A sequence expression—written as a semicolon in concrete syntax—is syntactic
-- sugar for a let statement with a variable name that is not used
-- (e₁ ; e₂) ≜ LET _ = e₁ IN e₂
seqE :: Expr -> Expr -> Expr
seqE e1 e2 = LetE "_" e1 e2

-- class declaration
-- cd ∈ cdecl ⩴ CLASS cn EXTENDS cn … cn FIELDS fn … fn ~ md … md
--
--                                 field
--                                 names
--                                 ⌄⌄⌄⌄⌄⌄⌄
data CDecl = CDecl CName [CName] [FName] [MDecl]
--                 ^^^^^                   ^^^^^^^
--                 class                   method
--                 name                    declarations
  deriving (Eq,Ord,Show)

-- method declaration
-- md ∈ mdecl ⩴ METHOD mn(x) ⇒ e
--
--                       parameter
--                       name
--                       ⌄⌄⌄⌄⌄
data MDecl = MDecl MName VName Expr
--                 ^^^^^       ^^^^
--                 method      method
--                 name        body
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
-- o ∈ object ⩴ OBJECT cn[o,…,o]({fn↦ℓ,…,fn↦ℓ}) {mn↦[FUN(x)⇒e],…,mn↦[FUN(x)⇒e]}
--                                  field map
--                                  ⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄
data Object = Object CName [Object] (Map FName Loc) (Map MName (VName,Expr))
--                   ^^^^^                 ^^^^^^^^^^^^^^^^^^^^^^^^
--                   class                 method map
--                   name
  deriving (Eq,Ord,Show)

-- values
-- v ∈ value ⩴ i | o
data Value = IntV Integer
           | BoolV Bool
           | FunV Env String Expr
           | ObjectV Object
           | LocV Loc
  deriving (Eq,Ord,Show)

-- locations (domain of the store)
-- ℓ ∈ loc ≈ ℕ
type Loc = Integer
-- environment (maps variable names to values)
-- γ ∈ env ≜ vname ⇀ value
type Env = Map VName Value
-- store (maps locations to values)
-- σ ∈ store ≜ loc ⇀ value
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
buildFieldMap :: [FName] -> [Loc] -> Maybe (Map FName Loc)
buildFieldMap [] [] = Just Map.empty
buildFieldMap (fn:fns) (l:ls) = case buildFieldMap fns ls of
  Just fm -> Just (Map.insert fn l fm)
  Nothing -> Nothing
buildFieldMap [] (_:_) = Nothing
buildFieldMap (_:_) [] = Nothing

-- Constructs a method map from a list of method declarations.
buildMethodMap :: [MDecl] -> Map MName (VName,Expr)
buildMethodMap [] = Map.empty
buildMethodMap (MDecl mn x e:mds) =
  let mm = buildMethodMap mds
  in Map.insert mn (x,e) mm

-- interp ∈ list(cdecl) × env × store × expr ⇀ value × store
-- interp(cds,γ,σ,i) ≜ ⟨i,σ⟩
-- interp(cds,γ,σ,b) ≜ ⟨b,σ⟩
-- interp(cds,γ,σ,e₁+e₂) ≜ ⟨i₁+i₂,σ″⟩
--   where ⟨i₁,σ′⟩ = interp(cds,γ,σ,e₁)
--   where ⟨i₂,σ″⟩ = interp(cds,γ,σ′,e₂)
-- interp(cds,γ,σ,e₁+e₂) ≜ ⟨i₁×i₂,σ″⟩
--   where ⟨i₁,σ′⟩ = interp(cds,γ,σ,e₁)
--   where ⟨i₂,σ″⟩ = interp(cds,γ,σ′,e₂)
-- interp(γ,σ,IF e₁ THEN e₂ ELSE e₃) ≜ interp(γ,σ′,e₂)
--   when ⟨true,σ′⟩ = interp(γ,σ,e₁)
-- interp(γ,σ,IF e₁ THEN e₂ ELSE e₃) ≜ interp(γ,σ′,e₃)
--   when ⟨false,σ′⟩ = interp(γ,σ,e₁)
-- interp(cds,γ,σ,x) ≜ γ(x)
-- interp(cds,γ,σ,LET x = e₁ IN e₂) ≜ interp(cds,γ[x↦v],σ′,e₂)
--   where ⟨v,σ′⟩ = interp(cds,γ,σ,e₁)
-- interp(γ,FUN(x)⇒e) ≜ ⟨FUN(x)⇒e,γ⟩
-- interp(γ,e₁(e₂)) ≜ interp(γ′[x↦v],e′)
--   where ⟨FUN(x)⇒e′,γ′⟩ = interp(γ,e₁)
--         v = interp(γ,e₂)
-- interp(γ,σ,WHILE(e₁){e₂}) ≜ ⟨true,σ′⟩
--   when ⟨false,σ′⟩ = interp(γ,σ,e₁)
-- interp(γ,σ,WHILE(e₁){e₂}) ≜ interp(γ,σ″,WHILE(e₁){e₂})
--   when ⟨true,σ′⟩ = interp(γ,σ,e₁)
--           ⟨v,σ″⟩ = interp(γ,σ′,e₂)
-- interp(γ,σ,BOX(e)) ≜ ⟨ℓ,σ′[ℓ↦v]⟩
--   where ⟨v,σ′⟩ = interp(γ,σ,e)
--         ℓ = fresh-loc(σ′)
-- interp(γ,σ,!e) ≜ ⟨σ′(ℓ),σ′⟩
--   where ⟨ℓ,σ′⟩ = interp(γ,σ,e)
-- interp(γ,σ,e₁ ← e₂) ≜ ⟨v,σ″[ℓ↦v]⟩
--   where ⟨ℓ,σ′⟩ = interp(γ,σ,e₁)
--         ⟨v,σ″⟩ = interp(γ,σ′,e₂)
-- interp(cds,γ,σ₀,NEW cn(e₁,…,eₙ)) ≜ ⟨OBJECT cn[o₁,…,oₜ](fn₁↦ℓ₁,…,fnₘ↦ℓₘ) {mn₁↦[FUN(x₁)⇒e₁′],…,mnₙ↦[FUN(xₙ)⇒eₙ′]},σₘ[ℓ₁↦v₁,…,ℓₘ↦vₘ]
--   where ⟨v₁,σ₁⟩ = interp(cds,γ,σ₀,e₁)
--                 ⋮
--         ⟨vₘ,σₘ⟩ = interp(cds,γ,σₘ₋₁,eₙ)
--         (CLASS cn EXTENDS cn₁ … cnₒ FIELDS fn₁ … fnₘ ~ METHOD mn₁(x₁) ⇒ e₁′ … METHOD mnₙ(xₙ) ⇒ eₙ′) = cds(cn)
--         ℓᵢ ≢ ℓⱼ for i ≢ j , 1 ≤ i ≤ m , 1 ≤ j ≤ m
--         {ℓ₁,…,ℓₘ} ∩ dom(σₘ) = ∅
-- interp(cds,γ,σ,e.fn) ≜ ⟨σ(fm(fn)),σ′⟩
--   where ⟨OBJECT cn(fm) mm,σ′⟩ = interp(cds,γ,σ,e)
-- interp(cds,γ,σ,e₁.fn ← e₂) ≜ ⟨v,σ″[fm(fn)↦v]⟩
--   where ⟨OBJECT cn(fm) mm,σ′⟩ = interp(cds,γ,σ,e₁)
--         ⟨v,σ″⟩ = interp(cds,γ,σ′,e₂)
-- interp(cds,γ,e₁.mn(e₂)) ≜ interp(cds,{x↦v,this↦o},σ″,e′)
--   where ⟨o,σ′⟩ = interp(cds,γ,σ,e₁)
--         (OBJECT cn(fm) mm) = o
--         ⟨v,σ″⟩ = interp(cds,γ,σ′,e₂)
--         ⟨x,e′⟩ = mm(mn)

interp :: [CDecl] -> Env -> Store -> Expr -> Maybe (Value,Store)
interp cds env store e0 = case e0 of
  IntE i _ -> Just (IntV i,store)
  BoolE b _ -> Just (BoolV b,store)
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
    Just (CDecl _ cns fns mds) -> case initMany cds env store cns es of
      Just (es',os,store') -> case interpMany cds env store' es' of
        Just (vs,store'') ->
          let (ls,store''') = allocMany store'' vs
              mm = buildMethodMap mds
          in case buildFieldMap fns ls of
            Just fm -> Just (ObjectV (Object cn os fm mm),store''')
            Nothing -> Nothing
        Nothing -> Nothing
      Nothing -> Nothing
    Nothing -> Nothing
    Nothing -> Nothing
  GetFieldE e fn -> case interp cds env store e of
    Just (ObjectV (Object _ os fm _),store') -> case Map.lookup fn fm of
      Just l -> case Map.lookup l store' of
        Just v -> Just (v,store')
        Nothing -> Nothing
      Nothing -> dispatch cds env store' os e0
    _ -> Nothing
  SetFieldE e1 fn e2 -> case interp cds env store e1 of
    Just (ObjectV (Object _ os fm _),store') -> case interp cds env store' e2 of
      Just (v,store'') -> case Map.lookup fn fm of
        Just l -> Just (v,Map.insert l v store'')
        Nothing -> dispatch cds env store' os e0
      Nothing -> Nothing
    _ -> Nothing
  CallE e1 mn e2 -> case interp cds env store e1 of
    Just (ObjectV (Object cn os fm mm),store') -> case interp cds env store' e2 of
      Just (v,store'') -> case Map.lookup mn mm of
        Just (x,e) ->
          let env' = Map.fromList [("this",ObjectV (Object cn os fm mm)), (x,v)]
          in case os of
            o':_ -> interp cds (Map.insert "super" (ObjectV o') (mapParents env' os)) store'' e
            [] -> interp cds env' store'' e
        Nothing -> dispatch cds env store'' os e0
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

-- Create objects given a list of class names and expressions. May return a
-- store and uninterpreted expressions.
initMany :: [CDecl] -> Env -> Store -> [CName] -> [Expr] -> Maybe ([Expr],[Object],Store)
initMany cds env store [] [] = Just ([],[],store)
initMany cds env store [] es = Just (es,[],store)
initMany cds env store (_:_) [] = Nothing
initMany cds env store (cn:cns) es = case lookupClass cds cn of
  Just (CDecl _ _ fns _) -> case buildExprList fns es of
    Just (es', es'') -> case interp cds env store (NewE cn es') of
      Just (ObjectV o,store') -> case initMany cds env store' cns es'' of
        Just (es''',pos,store'') -> Just (es''',(o:pos),store'')
        Nothing -> Nothing
      _ -> Nothing
    Nothing -> Nothing
  Nothing -> Nothing

-- Map the class name with the parent object
mapParents :: Env -> [Object] -> Env
mapParents env [] = env
mapParents env (o @ (Object cn _ _ _):os) =
  mapParents (Map.insert cn (ObjectV o) env) os

-- Decide a subset of a list of expressions that should correspond to a field
-- list. Returns a tuple of expressions: the first is the corresponding
-- expressions, the second being the unmatched expressions.
buildExprList :: [FName] -> [Expr] -> Maybe ([Expr],[Expr])
buildExprList [] [] = Just ([],[])
buildExprList [] es = Just ([],es)
buildExprList (_:_) [] = Nothing
buildExprList (fn:fns) (e:es) = case buildExprList fns es of
  Just (es1, es2) -> Just ((e:es1), es2)
  Nothing -> Nothing

-- Search for an inherited field or method and evaluate it.
dispatch :: [CDecl] -> Env -> Store -> [Object] -> Expr -> Maybe (Value,Store)
dispatch cds env store [] e0 = Nothing
dispatch cds env store (o @ (Object cn os' fm mm):os) e0 = 
  let env' = Map.insert "this" (ObjectV o) env
      e0' = case e0 of
        GetFieldE e fn -> GetFieldE (VarE "this") fn
        SetFieldE e1 fn e2 -> SetFieldE (VarE "this") fn e2
        CallE e1 mn e2 -> CallE (VarE "this") mn e2
        _ -> e0
  in case interp cds env' store e0' of
    Just (v,store') -> Just (v,store')
    Nothing -> case dispatch cds env' store os' e0 of
      Just (v,store') -> Just (v,store')
      Nothing -> dispatch cds env' store os e0

-- Finds the least upper bound of two elements with respect to our security lattice
joinLabel :: Label -> Label -> Label
joinLabel l1 l2 = if (l1==Secret|| l2==Secret) then Secret else Public

-- Finds the greatest lower bound of two elements with respect to our security lattice
meetLabel :: Label -> Label -> Label
meetLabel l1 l2 = if (l1==Public || l2==Public) then Public else Secret

-- Typable expressions evaluate to final type
-- Implemented with confidentiality/secrecy in mind. Integrity is also possible
typecheck :: TEnv -> Expr -> Maybe SType
typecheck env e0 = case e0 of
  IntE _ l1 -> Just (ST IntT l1)
  BoolE _ l1 -> Just (ST BoolT l1)
  PlusE e1 e2 -> case (typecheck env e1, typecheck env e2) of
    (Just (ST IntT l1), Just (ST IntT l2)) -> Just (ST IntT (joinLabel l1 l2))
    _ -> Nothing
  IfE e1 e2 e3 -> case typecheck env e1 of
    Just (ST BoolT l1) -> case (typecheck env e2, typecheck env e3) of
      (Just (ST t2 l2), Just (ST t3 l3)) ->
        if t2==t3
        then Just (ST t2 (joinLabel l1 (joinLabel l2 l3)))
        else Nothing
      _ -> Nothing
    _ -> Nothing

interpTests :: (Int,String,Expr -> Maybe (Value,Store),[(Expr,Maybe (Value,Store))])
interpTests =
  let cds = 
        -- CLASS Object
        --   FIELDS hash
        --   ~
        --   METHOD getHash(_) ⇒ this.hash
        --   METHOD mdist(_) ⇒ this.hash + this.hash
        [ CDecl "Object" []
                ["hash"]
                [ MDecl "getHash" "_" (GetFieldE (VarE "this") "hash")
                , MDecl "toInt" "_" (PlusE (GetFieldE (VarE "this") "hash")
                                           (GetFieldE (VarE "this") "hash"))
                ]
        , CDecl "Boolable" []
                ["b"]
                [ MDecl "getB" "_" (GetFieldE (VarE "this") "b")
                , MDecl "setB" "b" (SetFieldE (VarE "this") "b" (VarE "b"))
                ]
        -- CLASS Point2D
        --   FIELDS x y
        --   ~
        --   METHOD getX(_) ⇒ this.x
        --   METHOD getY(_) ⇒ this.y
        --   METHOD setX(x) ⇒ this.x ← x
        --   METHOD setY(y) ⇒ this.y ← y
        --   METHOD mdist(_) ⇒ this.getX(0) + this.getY(0) 
        , CDecl "Point2D" ["Object"]
                ["x","y"] 
                [ MDecl "getX" "_" (GetFieldE (VarE "this") "x")
                , MDecl "getY" "_" (GetFieldE (VarE "this") "y")
                , MDecl "setX" "x" (SetFieldE (VarE "this") "x" (VarE "x"))
                , MDecl "setY" "y" (SetFieldE (VarE "this") "y" (VarE "y"))
                , MDecl "mdist" "_" (PlusE (CallE (VarE "this") "getX" (IntE 1 Public))
                                           (CallE (VarE "this") "getY" (IntE 2 Public)))
                ]
        -- CLASS Point3D EXTENDS Point2D
        --   FIELDS z
        --   ~
        --   METHOD getZ(_) ⇒ this.z
        --   METHOD setZ(z) ⇒ this.z ← z
        --   METHOD mdist(_) ⇒ super.mdist(0) + this.getZ(0) 
        , CDecl "Point3D" ["Point2D"]
                ["z"]
                [ MDecl "getZ" "_" (GetFieldE (VarE "this") "z")
                , MDecl "setZ" "z" (SetFieldE (VarE "this") "z" (VarE "z"))
                , MDecl "mdist" "_" (PlusE (CallE (VarE "super") "mdist" (IntE 3 Public))
                                           (CallE (VarE "this") "getZ" (IntE 4 Public)))
                , MDecl "mdist2" "_" (PlusE (CallE (VarE "Point2D") "mdist" (IntE 3 Public))
                                            (CallE (VarE "this") "getZ" (IntE 4 Public)))
                ]
        ]
  in
  (1
  ,"interp"
  ,interp cds Map.empty Map.empty
  -- in each test: interp(e) = ⟨v,σ⟩
  --
  ,[
    -- e = LET x = BOX 10 IN !x
    ( LetE "x" (BoxE (IntE 10 Public) Public) (VarE "x")
    , Just (LocV 0,Map.fromList [(0,IntV 10)])
    )
    -- e = LET x = BOX false IN
    --     LET y = BOX 20 IN
    --     IF (x ← true) THEN !x ELSE (y ← 100))
   ,( LetE "x" (BoxE (BoolE False Public) Public)
      (LetE "y" (BoxE (IntE 20 Public) Public)
      (IfE (AssignE (VarE "x") (BoolE True Public))
           (UnboxE (VarE "x"))
           (AssignE (VarE "y") (IntE 100 Public))))
    , Just (BoolV True,Map.fromList [(0,BoolV True),(1,IntV 20)])
    )
    -- LET f = FUN (x) → x + 1 IN
    -- f(2)
   ,( LetE "f" (FunE "x" IntT (PlusE (IntE 1 Public) (VarE "x"))) $
      AppE (VarE "f") (IntE 2 Public)
      -- 3
    , Just (IntV 3,Map.empty)
    )
    -- LET b1 = BOX true IN
    -- LET b2 = BOX 3 IN
    -- LOOP !b1 { b2 ← !b2 * !b2 ; b1 ← false }
   ,( LetE "b1" (BoxE (BoolE True Public) Public) $
      LetE "b2" (BoxE (IntE 3 Public) Public) $
      WhileE (UnboxE (VarE "b1")) $
        LetE "_" (AssignE (VarE "b2") (TimesE (UnboxE (VarE "b2")) (UnboxE (VarE "b2")))) $
        AssignE (VarE "b1") (BoolE False Public)
      -- True
    , Just (BoolV True,Map.fromList [(0,BoolV False),(1,IntV 9)])
    )
   , -- LET p = new Point3D(2,3,4) IN
     -- p.mdist(0)
    ( LetE "p" (NewE "Point3D" [IntE 2 Public,IntE 3 Public,IntE 4 Public]) $
      CallE (VarE "p") "mdist" (IntE 0 Public)
      -- ⟨v,σ⟩ = ⟨9,{0↦2,1↦3,2↦4}⟩
    , Just (IntV 9,Map.fromList [(0,IntV 2),(1,IntV 3),(2,IntV 4)])
    )
   , -- LET p = new Point3D(2,3,4) IN
     -- p.mdist2(0)
    ( LetE "p" (NewE "Point3D" [IntE 2 Public,IntE 3 Public,IntE 4 Public]) $
      CallE (VarE "p") "mdist2" (IntE 0 Public)
      -- ⟨v,σ⟩ = ⟨9,{0↦2,1↦3,2↦4}⟩
    , Just (IntV 9,Map.fromList [(0,IntV 2),(1,IntV 3),(2,IntV 4)])
    )
   , -- LET p = new Point3D(2,3,4) IN
     -- p.getX(0)
    ( LetE "p" (NewE "Point3D" [IntE 10 Public,IntE 2 Public,IntE 3 Public,IntE 4 Public]) $
      (CallE (VarE "p") "getX" (IntE 0 Public))
      -- ⟨v,σ⟩ = ⟨2,{0↦2,1↦3,2↦4}⟩
    , Just (IntV 2,Map.fromList [(0,IntV 2),(1,IntV 3),(2,IntV 4)])
    )
   , -- LET p = new Point3D(2,3,4) IN
     -- p.x ← 10
     -- p.x
    ( LetE "p" (NewE "Point3D" [IntE 107 Public,IntE 2 Public,IntE 3 Public,IntE 4 Public]) $
      seqE (SetFieldE (VarE "p") "x" (IntE 10 Public)) (GetFieldE (VarE "p") "x")
      -- ⟨v,σ⟩ = ⟨10,{0↦10,1↦3,2↦4}⟩
    , Just (IntV 10,Map.fromList [(0,IntV 10),(1,IntV 3),(2,IntV 4)])
    )
   ]
  )

typecheckTests :: (Int,String,Expr -> Maybe SType,[(Expr,Maybe SType)])
typecheckTests =
  (1
  ,"typecheck"
  ,typecheck Map.empty
  ,[
    -- data should be designated as secret to prevent information flow leakage
    ( PlusE (IntE 1 Public) (IntE 2 Secret)
    , Just (ST IntT Secret)
    )
    ,
    -- cannot logically add bool to int
    ( PlusE (IntE 1 Public) (BoolE True Public)
    , Nothing
    )
    ,
    -- unpredictable final type due to branching, not typable
    ( IfE (BoolE False Secret) (BoolE True Public) (IntE 10 Public)
    , Nothing
    )
   ]
  )

---------------
-- ALL TESTS --
---------------

allTests :: [Test]
allTests =
  [ Test1 interpTests,
    Test1 typecheckTests
  ]

----------------------
-- MAIN = RUN TESTS --
----------------------

main :: IO ()
main = runTests allTests

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
