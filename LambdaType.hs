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

  | NatCase (Lam) (Lam) (Lam) (Lam)
  | Zero
  | Succ
  
  | Unit
  | UnitCase (Lam) (Lam) (Lam)

  | Pair (Lam) (Lam)
  | PairCase (Lam) (Lam) (Lam)

  | Nil 
  | Cons
  | ListCase (Lam) (Lam) (Lam) (Lam)

  deriving (Eq, Show)

test0 =  ((Abst) "x" (Var "x"))
test1 =  ((Abst) "y" (App (Succ) (Var "y")))
test2 = ((Abst) "x" ((Abst) "y" (App (Var "x") (Var "y"))))

----------------------------------
-- Main Program
----------------------------------

getTypeForProgram l = case evalState (makeTypeEquations l 0) startState of
  (Left e) -> case (solveEqs (flattenEquations e)) of
    (Left err) ->  putStrLn $ "Error: " ++ err
    (Right solved) -> printTypeEq solved
  (Right err) -> putStrLn $ "Error: " ++ err


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
  (Right err) -> putStrLn $ "Error: " ++ err

typeEquations l = evalState (makeTypeEquations l 0) startState

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
    (Left e1', Left e2') -> return $ Left $ Exists [(show l), (show r)] [(TEq (TVar (show l), (Func (TVar (show r)) (TVar (show q)) ))), e1', e2']
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

makeTypeEquations (NatCase t (App Succ n) t0 t1) q = do
  (con, x1) <- get
  put (con, x1+1)
  e1 <- makeTypeEquations t x1

  (con', y1) <- get
  put (con', y1+1)
  e2 <- makeTypeEquations t0 y1

  (ctx, y2) <- get
  put (((n,(TVar (show (y2+1)))):ctx), y2+2)
  e3 <- makeTypeEquations t x1

  case (e1, e2, e3) of
    (Left e1', Left e2', Left e3') ->
      return $ Left $ Exists [(show x1), (show y1), (show y2), (show (y2+1))] 
      [(TEq (TVar (show x1), TVar "Nat")), (TEq (TVar (show (y2+1)), TVar "Nat")), 
      (TEq (TVar (show (y1)), TVar (show q))), (TEq (TVar (show (y2)), TVar (show q))), 
      e1', e2', e3']

makeTypeEquations (Nil) q = do
  (con, x1) <- get
  put (con, x1+1)
  
  return $ Left $ Exists [(show x1)] [(TEq (TVar (show q), TList (TVar (show x1))))]

makeTypeEquations (Cons) q = do
  (con, x1) <- get
  put (con, x1+1)

  return $ Left $ Exists [(show x1)] 
    [(TEq (TVar (show q), Func (TTuple (TVar (show x1)) (TList (TVar (show x1))) ) (TList (TVar (show x1))) )) ]

makeTypeEquations (ListCase t (App Cons v) t0 t1) q = do
  (con, x1) <- get
  put (con, x1+1)
  e1 <- makeTypeEquations t x1

  (con', y1) <- get
  put (con', y1+1)
  e2 <- makeTypeEquations t0 y1

  (ctx, y2) <- get
  put (((v,(TVar (show (y2+1)))):ctx), y2+3)
  e3 <- makeTypeEquations t x1

  let x = y2 + 2 in
    case (e1, e2, e3) of
      (Left e1', Left e2', Left e3') ->
        return $ Left $ Exists [(show x1), (show y1), (show y2), (show (y2+1)), (show x)] 
        [(TEq ((TVar (show x1)), TList (TVar (show x)))),
        (TEq (TVar (show (y2+1)), TTuple (TVar (show x)) (TList (TVar (show x))) )),
        (TEq (TVar (show q), TVar (show y1))),
        (TEq (TVar (show q), TVar (show y2))),
        e1', e2', e3']
----------------------------------
-- Equation Solving Section
----------------------------------

solveEqs eqs =
  case eqChecks eqs of
    (Left err) -> Left err
    (Right eqs') -> 
      let (main,subs) = getMainAndSubs eqs' in
      case substitution main subs of
      Just (main') -> solveEqs (main':subs)
      Nothing -> Right main

getMainAndSubs eqs = ((getMainFunc eqs'), (notMain eqs'))
  where eqs' = removeTrivial (splitFunctions (removeTrivial eqs))

eqChecks eqs
  | occurence (eqs) =  Left "Failed occurence check"
  | (not $ functionsAgree (eqs)) = Left "Functions don't agree"
  | otherwise = Right eqs

getMainFunc ((TEq (TVar "0", x)):_) = (TEq (TVar "0", x))
getMainFunc (_:rest) = getMainFunc rest

notMain [] = []
notMain ((TEq (TVar "0", x)):rest) = notMain rest
notMain (x:rest) = [x] ++ (notMain rest)


removeTrivial :: [TypeEq String] -> [TypeEq String]
removeTrivial eqs = removeTrivial' eqs (findTrivial eqs)

removeTrivial' eqs [] = eqs
removeTrivial' eqs (t:ts) = removeTrivial' (removeTriv eqs t) ts

removeTriv [] _ = []
removeTriv (eq:rest) t
  | eq == t = removeTriv rest t
  | otherwise = [(TEq ((newName x v r), (replaceInType y v r)))] ++ (removeTriv rest t)
    where (TEq (TVar v, r)) = t
          (TEq (x,y)) = eq

newName (TVar x) v (TVar r)
  | x == v = (TVar r)
  | otherwise = (TVar x)
newName x _ _ = x

findTrivial [] = []
findTrivial ((TEq (TVar a, (TVar b))):rest) = (TEq (TVar a, (TVar b))):(findTrivial rest)
findTrivial (_:rest) = findTrivial rest

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
  -- | elem b (getVariablesInTypes t) = Just (b,(TVar a))
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
occurence (s:ss) = occurence' s || (occurence ss)
occurence' (TEq ((TVar a), t)) = elem a (getVariablesInTypes t)
occurence' (_) = False

getVariablesInTypes :: Types String -> [String]
getVariablesInTypes (TVar n) = [n]
getVariablesInTypes (Func f t) = getVariablesInTypes f ++ getVariablesInTypes t
getVariablesInTypes (TTuple l r) = getVariablesInTypes l ++ getVariablesInTypes r
getVariablesInTypes (TList t) = getVariablesInTypes t



functionsAgree :: [TypeEq v] -> Bool
functionsAgree [] = True
functionsAgree (eq:eqs) = and (map (functionsAgree' eq) eqs) && (functionsAgree eqs)

functionsAgree' (TEq ((TVar a), (Func f t))) (TEq ((TVar b), (Func g r)))
  | a == b = functionTypeAgree (Func f t) (Func g r)
  | otherwise = True
functionsAgree' _ _ = True

functionTypeAgree (Func f t) (Func g r) =
   (functionTypeAgree f g) && (functionTypeAgree t r)
functionTypeAgree (Func f t) n = False
functionTypeAgree n (Func f t) = False
functionTypeAgree _ _ = True


splitFunctions :: [TypeEq v] -> [TypeEq v]
splitFunctions [] = []
splitFunctions (eq:eqs) = case splitFunctions' eq eqs of
  (Just new_list) -> splitFunctions new_list
  (Nothing) -> [eq] ++ (splitFunctions eqs)

splitFunctions' _ [] = Nothing -- No changes
splitFunctions' (TEq (a, (Func n m) )) ((TEq (b, (Func u v) )):rest)
  | a == b = Just ((splitTypeFunctions (Func n m) (Func u v) ) ++ rest)
  | otherwise = Nothing
splitFunctions' t1 (t2:rest) = case splitFunctions' t1 rest of
  (Just new_list) -> Just ([t2] ++ new_list)
  Nothing -> Nothing

splitTypeFunctions :: (Types v) -> (Types v) -> [TypeEq v]
splitTypeFunctions (Func a b) (Func c d) =
  (splitTypeFunctions a c) ++ (splitTypeFunctions b d)
splitTypeFunctions v t = [TEq (v,t)]
