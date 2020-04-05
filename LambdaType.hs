--------------------------------------------------
-- Isaac McAuley
-- 30062463
-- April 15, 2020
-- Lambda.hs
--------------------------------------------------
data Type a = 
    AT a
  | Func (Type a) (Type a)

  | Nat
  | Boolean

data TypeEq t1 t2 = TE (Type t1) (Type t2)

data Lam a t = 
    App (Lam a t) (Lam a t)
  | Abst (Type t) (Lam a t)
  | Var (Type t) a

-- getTypeEquations :: (Lam a t) -> [(TypeEq t1 t2)]
-- getTypeEquations 