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

----------------------------------
-- Main Program
----------------------------------

-- getTypeForProgram l = case evalState (makeTypeEquations l 0) startState of
--   (Left e) -> (unify (flattenEquations e) [])
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


----------------------------------
-- Equation Solving Section
----------------------------------

getVaraiblesInEquation :: TypeEq String -> [String]
getVaraiblesInEquation (TEq (_,n)) = getVariablesInTypes n
getVaraiblesInEquation (Exists _ ms) = concat (map (getVaraiblesInEquation) ms)

getVariablesInTypes :: Types String -> [String]
getVariablesInTypes (TVar n) = [n]
getVariablesInTypes (Func f t) = getVariablesInTypes f ++ getVariablesInTypes t
getVariablesInTypes (TTuple l r) = getVariablesInTypes l ++ getVariablesInTypes r
getVariablesInTypes (TList t) = getVariablesInTypes t

checkEquations :: TypeEq String -> Types String -> Bool
checkEquations eqs (TVar var) = elem var (getVaraiblesInEquation eqs)

flattenEquations :: TypeEq String -> [TypeEq String]
flattenEquations (TEq x) = [(TEq x)]
flattenEquations (Exists _ xs) = concat (map flattenEquations xs)

replaceInEq :: TypeEq String -> TypeEq String -> TypeEq String
replaceInEq r (TEq (x,y)) = (TEq (x, (replaceInType r y)))
replaceInEq r (Exists vars []) = (Exists vars [])
replaceInEq r (Exists vars (x:xs)) = (Exists vars ((replaceInEq r x):rest))
  where (Exists vars rest) = replaceInEq r (Exists vars xs)

replaceInType :: TypeEq String -> Types String -> Types String
replaceInType (TEq ((TVar x),y)) (TVar v)
  | v == x = y
  | otherwise = (TVar v)
replaceInType r (Func f t) = (Func (replaceInType r f) (replaceInType r t))
replaceInType r (TTuple f t) = (TTuple (replaceInType r f) (replaceInType r t))
replaceInType r (TList l) = (TList (replaceInType r l))

-- TODO Function Substitution

replace_test = [TEq (TVar "2",TVar "1"),TEq (TVar "0",Func (TVar "1") (TVar "2"))]
replace_test0 = [TEq (TVar "1",TVar "1"), TEq (TVar "2",TVar "1"), TEq (TVar "1",TVar "2"), TEq (TVar "0",Func (TVar "1") (TVar "2"))]
replace_test1 = [TEq (TVar "1",TVar "0"), TEq (TVar "0",Func (TVar "1") (TVar "2"))]

check :: TypeEq String -> TypeEq String -> Maybe (TypeEq String)
check eq (TEq (x,y))
  | checkEquations eq x = Nothing
  | otherwise = Just (replaceInEq (TEq (x,y)) eq)

unify :: [TypeEq String] -> Maybe [TypeEq String]
unify eqs
  | canPerformTransformation eqs = 
    case performTransformation eqs of
      Just eqs' -> unify eqs'
      Nothing -> Nothing
  | otherwise = Just eqs


canPerformTransformation :: [TypeEq String] -> Bool
canPerformTransformation [] = False

performTransformation :: [TypeEq String] -> Maybe [TypeEq String]
performTransformation eqs = Just eqs

removeTrivial :: [TypeEq String] -> [TypeEq String]
removeTrivial [] = []
removeTrivial ((TEq ((TVar x), (TVar y))):rest)
  | x == y = removeTrivial rest
  | otherwise = (TEq ((TVar x), (TVar y))):(removeTrivial rest)
removeTrivial (eq:rest) = eq:(removeTrivial rest)

replaceVars eqs = replaceVars' eqs (allTuples eqs)
allTuples xs = [ (x,y) | x <- xs, y <- xs, x /= y ]

replaceVars' :: Eq a => [TypeEq a] -> [(TypeEq a, TypeEq a)] -> [TypeEq a]
replaceVars' eqs [] = eqs
replaceVars' eqs ((n,m):rest) = case (replaceVar n m) of
  Just (a,b,new) -> (delete b (delete a eqs)) ++ [new]
  Nothing -> (replaceVars' eqs rest)

replaceVar :: TypeEq a -> TypeEq a -> Maybe (TypeEq a, TypeEq a, TypeEq a)
replaceVar (TEq ((TVar x),x_eq)) (TEq (t,(TVar x')))
  | x == x' = Just ((TEq ((TVar x),x_eq)), (TEq (t,(TVar x'))), (TEq (t,x_eq)))
  | otherwise = Nothing
replaceVar _ _ = Nothing

functionsHaveSameSize [] = True
functionsHaveSameSize ((TEq (f,g)):rest) = functionsHaveSameSize' f g && functionsHaveSameSize rest

functionsHaveSameSize' (Func _ (Func _ fs)) (Func _ (Func _ gs)) = functionsHaveSameSize' fs gs
functionsHaveSameSize' (Func _ (Func _ fs)) (Func _ _) = False
functionsHaveSameSize' (Func _ _) (Func _ (Func _ gs)) = False
functionsHaveSameSize' (Func _ fs) (Func _ gs) = functionsHaveSameSize' fs gs
functionsHaveSameSize' _ _ = True


replaceFunc :: [TypeEq a] -> [TypeEq a]
replaceFunc eqs = concat $ map replaceFunc' eqs


replaceFunc' (TEq ((Func x1 x2), (Func k1 k2))) = [TEq (x1, k2), TEq (x2, k2)]
replaceFunc' a = [a]

-- functions to add
-- equations agree i.e. (no x = x + t)
-- functions agree i.e. (t1=t2 t1=f(x1,x2..xn) t2=g(k1,k2..kn))