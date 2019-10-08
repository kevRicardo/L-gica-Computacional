{-Facultad de Ciencias UNAM - Lógica Computacional 2020-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Sara Doris Montes Incin
		  Laboratorio: Mauricio Esquivel Reyes-}

module SintaxisPLI
  where

-- Tipo de dato indice
type Indice = Int

-- Tipo de dato fórmula
data PLI = Bot | Var Indice | Oimp PLI PLI 
        deriving (Eq,Show,Ord,Read)

-- Top en el sistema L
oTop :: PLI
oTop = Oimp Bot Bot

-- Negación en el sistema L
oNeg :: PLI -> PLI
oNeg phi = Oimp phi Bot

-- Disyunción en el sistema L
oAnd :: PLI -> PLI -> PLI
oAnd alpha beta = (alpha `Oimp` (beta `Oimp` Bot)) `Oimp` Bot 

-- Conjunción en el sistema L
oOr :: PLI -> PLI -> PLI
oOr alpha beta = (alpha `Oimp` Bot) `Oimp` beta

-- Función que nos muestas los elmentos de la PLI
showPLI :: PLI -> String
showPLI phi = case phi of
  Bot                            -> "FF" 
  Var v                          -> "v"++show v
  -- toLuk(Top)= ~Bot
  Oimp Bot Bot                   -> "TT"
  -- toLuk(f ^ g) = toLuk(¬(f -> ¬g))
  (a`Oimp`(b`Oimp`Bot))`Oimp`Bot -> "("++ (showPLI a) ++" & "++ (showPLI b) ++")"
   -- toLuk(f v g) = toLuk((¬f) -> g)
  (alpha `Oimp` Bot) `Oimp` beta -> "("++ (showPLI alpha) ++" | "++ (showPLI beta) ++")"
  -- toLuk(¬f) = ~toLuk(f)
  Oimp alpha Bot                 -> "~("++ (showPLI alpha) ++")"
  Oimp alpha beta                -> "("++ (showPLI alpha) ++" -> "++ (showPLI beta) ++")"
