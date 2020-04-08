--------------------------------------------------
-- Isaac McAuley
-- 30062463
-- April 15, 2020
-- Lambda.hs
--------------------------------------------------
import Control.Monad.State


data Types v = 
    Func (Types v) (Types v) 
  | TVar String

data TypeEq a = 
    TEq (Types a, Types a) 
  | Exists [a] [TypeEq a]

data Lam = 
    App (Lam) (Lam)
  | Abst String (Lam)
  | Var String

type EqState v = (  ([(String, Types v)]), Int )

-- printTypes (Func l r) = (printTypes l) ++ " -> " ++ (printTypes l)
-- printTypes (TVar v) = v

-- printTypeEq (TEq (l, r)) = (printTypeEq l) ++ " = " ++ (printTypes r)
-- printTypeEq (Exists e t) 

-- startState = ([], 0)
-- lambdaTypeEquations l = evalState (makeTypeEquations l 0) startState


makeTypeEquations :: Lam -> Int -> State (EqState String) (Either (TypeEq String) String)
makeTypeEquations (Var x) q = do
  (con, _) <- get
  case lookup x con of
    Just p -> return $ Left $ (TEq (TVar x, p))
    Nothing -> return $ Right $ "Undeclared variable" 

makeTypeEquations (Abst s t) q = do
  (con, x) <- get
  let y = x + 1
  put ((s, TVar (show x)):con, y)
  e <- makeTypeEquations t y
  case e of
    Left e' -> return $ Left $ Exists [(show x), (show y)] [(TEq (TVar (show q), (Func (TVar (show x)) (TVar (show y)) ))), e']
    Right error -> return $ Right $ "Abstraction problem"

makeTypeEquations (App f t) q = do
  (con, x) <- get
  let l = x
  let r = x + 1
  put(con, x + 2)

  e1 <- makeTypeEquations f l
  (con', x') <- get
  put (con', x')
  e2 <- makeTypeEquations t r
  case (e1, e2) of
    (Left e1', Left e2') -> return $ Left $ Exists [(show l), (show r)] [(TEq (TVar (show r), (Func (TVar (show l)) (TVar (show q)) ))), e1', e2']
    (_,_) -> return $ Right $ "Bad app"
  -- return $ Right $ "Undeclared variable" 

  -- Var x -> do
  --     (con, _) <- get
  --     case lookup x con of
  --       Just p -> return $ Left $ (TEq (Type x) p)
  --       Nothing -> return $ Right $ "Undeclared variable" 


-- makeTypeEquations :: (Eq a) => (Lam a t) -> State (EqState a t) [TypeEq t]
-- makeTypeEquations (Var v_type value) = do
--   (types, counter) <- get
--   case getVarType (Var v_type value) types of
--     Just t -> return [(t,t)]

-- getVarType :: (Eq a) => (Lam a t) -> [((Lam a t), (Type t))] -> Maybe (Type t)
-- getVarType (Var (AT at) _) _ = Just (AT at)
-- getVarType (Var None v1) (((Var _ v2), t):types)
--   | v1 == v2 = Just t
--   | otherwise = getVarType (Var None v1) types
-- getVarType _ [] = Nothing