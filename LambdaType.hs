--------------------------------------------------
-- Isaac McAuley
-- 30062463
-- April 15, 2020
-- Lambda.hs
--------------------------------------------------
import Control.Monad.State

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

getVaraiblesInEquation :: TypeEq a -> [String]
getVaraiblesInEquation (TEq (_,n)) = getVariablesInTypes n
getVaraiblesInEquation (Exists _ ms) = concat (map (getVaraiblesInEquation) ms)

getVariablesInTypes :: Types a -> [String]
getVariablesInTypes (TVar n) = [n]
getVariablesInTypes (Func f t) = getVariablesInTypes f ++ getVariablesInTypes t
getVariablesInTypes (TTuple l r) = getVariablesInTypes l ++ getVariablesInTypes r
getVariablesInTypes (TList t) = getVariablesInTypes t 
