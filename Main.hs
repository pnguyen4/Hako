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
-- cd ∈ cdecl ⩴ CLASS cn FIELDS fn … fn ~ md … md
--
--                       field
--                       names
--                       ⌄⌄⌄⌄⌄⌄⌄
data CDecl = CDecl CName [FName] [MDecl]
--                 ^^^^^         ^^^^^^^
--                 class         method
--                 name          declarations
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
-- o ∈ object ⩴ OBJECT cn({fn↦ℓ,…,fn↦ℓ}) {mn↦[FUN(x)⇒e],…,mn↦[FUN(x)⇒e]}
--                         field map
--                         ⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄
data Object = Object CName (Map FName Loc) (Map MName (VName,Expr))
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
lookupClass (CDecl cn fns mds:cds) cn' | cn == cn' = Just (CDecl cn fns mds)
lookupClass (CDecl cn fns mds:cds) cn' | otherwise = lookupClass cds cn'

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
-- interp(γ,σ,BOX(e)) ≜ ⟨ℓ,σ′[ℓ↦v]⟩
--   where ⟨v,σ′⟩ = interp(γ,σ,e)
--         ℓ = fresh-loc(σ′)
-- interp(γ,σ,!e) ≜ ⟨σ′(ℓ),σ′⟩
--   where ⟨ℓ,σ′⟩ = interp(γ,σ,e)
-- interp(γ,σ,e₁ ← e₂) ≜ ⟨v,σ″[ℓ↦v]⟩
--   where ⟨ℓ,σ′⟩ = interp(γ,σ,e₁)
--         ⟨v,σ″⟩ = interp(γ,σ′,e₂)
-- interp(cds,γ,σ₀,NEW cn(e₁,…,eₙ)) ≜ ⟨OBJECT cn(fn₁↦ℓ₁,…,fnₘ↦ℓₘ) {mn₁↦[FUN(x₁)⇒e₁′],…,mnₙ↦[FUN(xₙ)⇒eₙ′]},σₘ[ℓ₁↦v₁,…,ℓₘ↦vₘ]
--   where ⟨v₁,σ₁⟩ = interp(cds,γ,σ₀,e₁)
--                 ⋮
--         ⟨vₘ,σₘ⟩ = interp(cds,γ,σₘ₋₁,eₙ)
--         (CLASS cn FIELDS fn₁ … fnₘ ~ METHOD mn₁(x₁) ⇒ e₁′ … METHOD mnₙ(xₙ) ⇒ eₙ′) = cds(cn)
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
    Just (CDecl _ fns mds) -> case interpMany cds env store es of
      Just (vs,store') ->
        let (ls,store'') = allocMany store' vs
            mm = buildMethodMap mds
        in case buildFieldMap fns ls of
          Just fm -> Just (ObjectV (Object cn fm mm),store'')
          Nothing -> Nothing
      Nothing -> Nothing
    Nothing -> Nothing
  GetFieldE e fn -> case interp cds env store e of
    Just (ObjectV (Object _ fm _),store') -> case Map.lookup fn fm of
      Just l -> case Map.lookup l store' of
        Just v -> Just (v,store')
        Nothing -> Nothing
      Nothing -> Nothing
    _ -> Nothing
  SetFieldE e1 fn e2 -> case interp cds env store e1 of
    Just (ObjectV (Object _ fm _),store') -> case interp cds env store' e2 of
      Just (v,store'') -> case Map.lookup fn fm of
        Just l -> Just (v,Map.insert l v store'')
        Nothing -> Nothing
      Nothing -> Nothing
    _ -> Nothing
  CallE e1 mn e2 -> case interp cds env store e1 of
    Just (ObjectV (Object cn fm mm),store') -> case interp cds env store' e2 of
      Just (v,store'') -> case Map.lookup mn mm of
        Just (x,e) ->
          let env' = Map.fromList [("this",ObjectV (Object cn fm mm)),(x,v)]
          in interp cds env' store'' e
        Nothing -> Nothing
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
  let cds = undefined
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
