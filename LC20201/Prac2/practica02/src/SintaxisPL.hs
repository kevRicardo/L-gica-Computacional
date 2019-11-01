module SintaxisPL (PL(..), Indice, showPL)
--Sintaxis de la PL 
--mcb
where
--
--------------------------------------------------------
--
--Tipo de datos para indices de variables
type Indice = Int

-- Tipo de datos para formulas de la PL
data PL = Top | Bot | Var Indice 
        | Oneg PL | Oand PL PL | Oor PL PL | Oimp PL PL deriving (Eq,Show,Ord,Read)
--
showPL :: PL -> String
-- muestra una formula de la PL
showPL phi = case phi of
    Top         -> "TT"
    Bot         -> "FF"
    Var v       -> "v"++show v
    Oneg p      -> "¬"++(showPL p)
    Oand p q    -> "("++ (showPL p) ++" & "++ (showPL q) ++")"
    Oor  p q    -> "("++ (showPL p) ++" | "++ (showPL q) ++")"
    Oimp p q    -> "("++ (showPL p) ++" -> "++ (showPL q) ++")" 
    --_           -> error $ "showPL: no definida en este caso, phi="++show phi
--
