----------------------------------
-- Isaac McAuley
-- 30062463
-- April 15, 2020
-- LambdaType.hs
----------------------------------
import Control.Monad.State
import Data.List

----------------------------------
-- Data Section
----------------------------------
data Types v = 
    Func (Types v) (Types v) 
  | TVar String
  | TList (Types v)
  | TTuple (Types v) (Types v)
  deriving (Eq, Show)

data TypeEq a = 
    TEq (Types a, Types a) 
  | Exists [a] [TypeEq a]
  deriving (Eq, Show)

data Lam = 
    App (Lam) (Lam)
  | Abst String (Lam)
  | Var String
  | Fix (Lam)

  | Unit
  | UnitCase (Lam) (Lam) (Lam)

  | Pair (Lam) (Lam)
  | PairCase (Lam) (Lam) (Lam)

  | Zero
  | Succ

  deriving (Eq, Show)

test0 =  ((Abst) "x" (Var "x"))
test1 =  ((Abst) "y" (App (Succ) (Var "y")))
test2 = ((Abst) "x" ((Abst) "y" (App (Var "x") (Var "y"))))

----------------------------------
-- Main Program
----------------------------------

getTypeForProgram l = case evalState (makeTypeEquations l 0) startState of
  (Left e) -> e --case (solveEqs (flattenEquations e)) of
    -- (Left err) ->  Left $ putStrLn $ "Error :" ++ err
    -- (Right solve) -> solve
  -- (Right err) -> putStrLn $ "Error :" ++ err


----------------------------------
-- Printing Section
----------------------------------

stringType (TVar s) = s
stringType (Func f t) = stringType f ++ "->" ++ stringType t
stringType (TList t) = "L(" ++ stringType t ++ ")"
stringType (TTuple l r) = "(" ++ (stringType l) ++ "," ++ (stringType r) ++ ")" 

stringTypeEq (TEq (l, r)) = stringType l ++ "=" ++ stringType r
stringTypeEq (Exists vs eqs) = "∃" ++ show vs ++ "[" ++ (concat (map ((++) ", ") (map stringTypeEq eqs))) ++ " ]"

printTypeEq t = putStrLn (stringTypeEq t)

----------------------------------
-- Equation Creation Section
----------------------------------

type EqState v = (  ([(Lam, Types v)]), Int )

startState = ([], 0)
lambdaTypeEquations l = case evalState (makeTypeEquations l 0) startState of
  (Left e) -> printTypeEq e
  (Right err) -> putStrLn $ "Error :" ++ err


makeTypeEquations :: Lam -> Int -> State (EqState String) (Either (TypeEq String) String)
makeTypeEquations (Var x) q = do
  (con, _) <- get
  case lookup (Var x) con of
    Just p -> return $ Left $ (TEq (TVar (show q), p))
    Nothing -> return $ Right $ "Undeclared variable: " ++ x 

makeTypeEquations (Abst s t) q = do
  (con, n) <- get
  let x = n + 1
  let y = n + 2
  put (((Var s), TVar (show x)):con, n + 3)
  e <- makeTypeEquations t y
  case e of
    Left e' -> return $ Left $ Exists [(show x), (show y)] [(TEq (TVar (show q), (Func (TVar (show x)) (TVar (show y)) ))), e']
    Right error -> return $ Right $ "Abstraction problem"

makeTypeEquations (App f t) q = do
  (con, n) <- get
  let l = n + 1
  let r = n + 2
  put(con, n + 3)

  e1 <- makeTypeEquations f l
  (con', x') <- get
  put (con', x')
  e2 <- makeTypeEquations t r
  case (e1, e2) of
    (Left e1', Left e2') -> return $ Left $ Exists [(show l), (show r)] [(TEq (TVar (show r), (Func (TVar (show l)) (TVar (show q)) ))), e1', e2']
    (Right e1', Left e2') -> return $ Right $ "Error in left hand side: " ++ e1'
    (Left e1', Right e2') -> return $ Right $ "Error in right hand side: " ++ e2'

makeTypeEquations (Fix t) q = do
  (con,z) <- get
  put (con, z+2)

  e <- makeTypeEquations t (z + 1)
  case e of
    Left e' -> return $ Left $ Exists [(show z)] [(TEq ((TVar (show z), (Func (TVar (show q)) (TVar (show q))) )) ), e' ]
    Right err -> return $ Right $ err

makeTypeEquations (Zero) q = do
  return $ Left $ TEq ((TVar (show q)), (TVar "Nat"))

makeTypeEquations (Unit) q = do
  return $ Left $ TEq ((TVar (show q)), (TVar "Unit"))

makeTypeEquations (UnitCase t (Unit) s) q = do
  (con, n) <- get
  let z = n + 1
  put(con, n + 2)
  e1 <- makeTypeEquations t z
  (con', x') <- get
  put (con', x')
  e2 <- makeTypeEquations s q
  case (e1, e2) of
    (Left e1', Left e2') -> return $ Left $ Exists [(show z)] [(TEq ((TVar (show z)), (TVar "Units"))), e1', e2']
    (Right e1', Left e2') -> return $ Right $ "Error in left hand side: " ++ e1'
    (Left e1', Right e2') -> return $ Right $ "Error in right hand side: " ++ e2'

makeTypeEquations (Succ) q = do
  return $ Left $ TEq ((TVar (show q)), (Func (TVar "Nat") (TVar "Nat")))

makeTypeEquations (Pair t s) q = do
  (con, n) <- get
  let l = n + 1
  let r = n + 2
  put(con, n + 3)

  e1 <- makeTypeEquations t l
  (con', x') <- get
  put (con', x')
  e2 <- makeTypeEquations s r
  case (e1, e2) of
    (Left e1', Left e2') -> return $ Left $ Exists [(show l), (show r)] [(TEq (TVar (show q), (TTuple (TVar (show l)) (TVar (show r)) ))), e1', e2']
    (_,_) -> return $ Right $ "Bad app"

makeTypeEquations (PairCase t (Pair x y) s) q = do
  (con, a) <- get
  put (con, a+1)
  e1 <- makeTypeEquations t a
  (con', b) <- get
  put ((x,(TVar (show b))):(y,(TVar (show (b+1)))):con', b+2)
  e2 <- makeTypeEquations s (b+2)
  case (e1, e2) of
    (Left e1', Left e2') -> return $ Left $ Exists [(show b), (show (b+1)), (show a)] [(TEq (TVar (show q), (TTuple (TVar (show b)) (TVar (show (b+1))) ))), e1', e2']



replace_test = [TEq (TVar "1",TVar "2"),TEq (TVar "0",Func (TVar "1") (TVar "2"))]
replace_test0 = [TEq (TVar "1",TVar "1"), TEq (TVar "2",TVar "1"), TEq (TVar "1",TVar "2"), TEq (TVar "0",Func (TVar "1") (TVar "2"))]
replace_test1 = [TEq (TVar "1",TVar "0"), TEq (TVar "0",Func (TVar "1") (TVar "2"))]

m1 = [TEq (TVar "2",Func (TVar "4") (TVar "5")),
      TEq (TVar "8",Func (TVar "7") (TVar "5")),
      TEq (TVar "7",TVar "1"),
      TEq (TVar "8",TVar "4")]

n1 = TEq (TVar "0",Func (TVar "1") (TVar "8"))

----------------------------------
-- Equation Solving Section
----------------------------------

unify eqs = solveEqs (getMainFunc eqs') (notMain eqs')
  where eqs' = removeTrivial eqs

solveEqs main subs = 
  case occurence (main:subs) of
    True -> Left "Failed occurence check"
    False -> case substitution main subs of
      Just (main') -> solveEqs main' subs
      Nothing -> Right main

getMainFunc ((TEq (TVar "0", x)):_) = (TEq (TVar "0", x))
getMainFunc (_:rest) = getMainFunc rest

notMain [] = []
notMain ((TEq (TVar "0", x)):rest) = notMain rest
notMain (x:rest) = [x] ++ (notMain rest)

removeTrivial :: [TypeEq String] -> [TypeEq String]
removeTrivial [] = []
removeTrivial ((TEq (TVar a, (TVar b))):rest) = removeTrivial (removeTrivial' (TEq (TVar a, (TVar b))) rest)
removeTrivial (nontriv:rest) = [nontriv] ++ (removeTrivial rest)

removeTrivial' triv [] = []
removeTrivial' triv (eq:eqs) = case substitution eq [triv] of
  (Just eq') -> [eq'] ++ (removeTrivial' triv eqs)
  (Nothing) -> [eq] ++ (removeTrivial' triv eqs)

getVaraiblesInEquation :: TypeEq String -> [String]
getVaraiblesInEquation (TEq (_,n)) = getVariablesInTypes n
getVaraiblesInEquation (Exists _ ms) = concat (map (getVaraiblesInEquation) ms)

flattenEquations :: TypeEq String -> [TypeEq String]
flattenEquations (TEq x) = [(TEq x)]
flattenEquations (Exists _ xs) = concat (map flattenEquations xs)

substitution :: TypeEq String -> [TypeEq String] -> Maybe (TypeEq String)
substitution main [] = Nothing
substitution (TEq (m,t)) (s:subs) = case varToSub (TEq (m,t)) s of
  Just (v,t1) -> Just (TEq (m, (replaceInType t v t1)))
  Nothing -> substitution (TEq (m,t)) subs

varToSub :: TypeEq String -> TypeEq String -> Maybe (String, (Types String))
varToSub (TEq (_, t)) (TEq (TVar a, (TVar b))) 
  | elem a (getVariablesInTypes t) = Just (a,(TVar b))
  | elem b (getVariablesInTypes t) = Just (b,(TVar a))
  | otherwise = Nothing
varToSub (TEq (_, t)) (TEq (TVar a, t1)) 
  | elem a (getVariablesInTypes t) = Just (a,t1)
  | otherwise = Nothing
varToSub (TEq (_, t)) (TEq (t1, TVar a))
  | elem a (getVariablesInTypes t) = Just (a,t1)
  | otherwise = Nothing
varToSub _ _ = Nothing

replaceInType :: Types String -> String -> Types String -> Types String
replaceInType (TVar a) v t1
  | a == v = t1
  | otherwise = (TVar a)
replaceInType (Func f t) v t1 = (Func (replaceInType f v t1) (replaceInType t v t1))
replaceInType (TTuple l r) v t1 = (TTuple (replaceInType l v t1)(replaceInType r v t1))
replaceInType (TList l) v t1 = (TList (replaceInType l v t1))




-- Inconsistency Checking
--------------------------


occurence [] = False
occurence (s:ss) = occurence' s && (occurence ss)
occurence' (TEq ((TVar a), t)) = elem a (getVariablesInTypes t)
occurence' (_) = False

getVariablesInTypes :: Types String -> [String]
getVariablesInTypes (TVar n) = [n]
getVariablesInTypes (Func f t) = getVariablesInTypes f ++ getVariablesInTypes t
getVariablesInTypes (TTuple l r) = getVariablesInTypes l ++ getVariablesInTypes r
getVariablesInTypes (TList t) = getVariablesInTypes t
-- typesAgree :: [TypeEq String] -> Maybe String
-- typesAgree eqs
--   -- | not $ equationsAgree eqs = Just "Inconsistent variable"
--   | not $ functionsAgree eqs = Just "Inconsistent function"
--   | otherwise = Nothing

-- equationsAgree [] = True
-- equationsAgree ((TEq ((TVar a), t)):rest) =  && equationsAgree rest


-- functionsAgree [] = True
-- functionsAgree ((TEq (f,g)):rest) = functionsAgree f g && functionsAgree rest

subFunc :: (TypeEq v) -> [TypeEq v] -> (Either String [TypeEq v])
subFunc (TEq (x,(Func a b))) ((TEq (y,(Func d c))):subs)
  | x == y = functionsAgree (Func a b) (Func d c)
  | otherwise = case subFunc (TEq (x,(Func a b))) subs of
    (Right rest) -> Right $ [(TEq (y,(Func d c)))] ++ rest
    (Left err) -> Left err
subFunc _ [] = Right []
subFunc _ subs = Right subs


functionsAgree :: (Types v) -> (Types v) -> (Either String [TypeEq v])
functionsAgree (Func x1 x2) (Func k1 k2) = do
  case (functionsAgree x1 k1, functionsAgree x2 k2) of
    (Right p1', Right p2') -> Right $ p1' ++ p2'
    (_,_) -> Left "Functions don't agree"
functionsAgree (Func _ _) (TVar _) = Left "Bad function"
functionsAgree (TVar _) (Func _ _) = Left "Bad function"
functionsAgree x y = Right [(TEq (x,y))]


