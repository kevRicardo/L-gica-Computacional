module LProp where
-- Tipo de datos que representa el lenguaje
-- de la lógica proposicional.
data Prop = 
    PTrue 
  | PFalse
  | PVar Char
  | PNeg Prop
  | POr Prop Prop
  | PAnd Prop Prop
  | PImpl Prop Prop
  | PEquiv Prop Prop

-- Instancia de Show para Prop para poder 
-- imprimir fórmulas bonito. 
instance Show Prop where
  show PTrue = "true"
  show PFalse = "false"
  show (PVar x) = show x
  show (PNeg p) = "¬"++ (show p)
  show (POr p1 p2) = "(" ++ show p1 ++ " v " ++ show p2 ++ ")"
  show (PAnd p1 p2) = "(" ++ show p1 ++ " ^ " ++ show p2 ++ ")"
  show (PImpl p1 p2) = "(" ++ show p1 ++ " -> " ++ show p2 ++ ")"
  show (PEquiv p1 p2) = "(" ++ show p1 ++ " <-> " ++ show p2 ++ ")"
  
-- Instancia de Eq para Prop para decidir
-- si dos fórmulas son SINTÁCTICAMENTE iguales.
-- (en otras palabras, AvB no es igual a BvA).
instance Eq Prop where
  PTrue == PTrue = True
  PFalse == PFalse = True
  (PVar x) == (PVar y) = x == y
  (PNeg x) == (PNeg y) = x == y
  (POr x y) == (POr z w) = (x == z) && (y == w)
  (PAnd x y) == (PAnd z w) = (x == z) && (y == w)
  (PImpl x y) == (PImpl z w) = (x == z) && (y == w)
  (PEquiv x y) == (PEquiv z w) = (x == z) && (y == w)
  _ == _ = False
