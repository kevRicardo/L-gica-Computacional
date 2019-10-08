{-Facultad de Ciencias UNAM - Lógica Computacional 2020-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Sara Doris Montes Incin
		  Laboratorio: Mauricio Esquivel Reyes-}

module DeduccionL
  where

import SintaxisPLI

-- Función que nos dice si una formula de PLI cumple el Axioma 1
esAxL1 :: PLI -> Bool
esAxL1 phi = case phi of
  (a `Oimp` (b `Oimp` c)) -> a == c
  otherwise -> False

-- Función que nos dice si una formula de PLI cumple el Axioma 2
esAxL2 :: PLI -> Bool
esAxL2 phi = case phi of
  ((a `Oimp` (b `Oimp` c)) `Oimp` ((d `Oimp` e) `Oimp` (f `Oimp` g))) -> a == d && d == f && b == e && c == g
  otherwise -> False

-- Función que nos dice si una formula de PLI cumple el Axioma 3
esAxL3 :: PLI -> Bool
esAxL3 phi = case phi of
  (((a `Oimp` Bot) `Oimp` (b `Oimp` Bot)) `Oimp` (c `Oimp` d)) -> a == d && b == c
  otherwise -> False

-- Función que nos dice si una formula es una Axioma del sistema L
esAxiomaDeL :: PLI -> Bool
esAxiomaDeL phi = esAxL1 phi || esAxL2 phi || esAxL3 phi

-- Función que nos dice si se aplico de manera correcta Modus Ponens
esModusPonens :: (PLI, PLI, PLI) -> Bool
esModusPonens (phi, chi, psi) = case (phi, chi, psi) of
  (a, (b `Oimp` c), d) -> a == b && c == d
  otherwise -> False

-- Reglas del sistema L
data ReglaL = Prem           -- Las premisas son validas
            | Ax             -- Las formulas pueden ser axiomas
            | ModPon Int Int -- Es resultado de aplicar MP a dos formulas anteriores
            deriving (Eq,Show)
-- Tipo Paso
-- Una fomula PLI y la Regla utilizada
type Paso = (PLI, ReglaL)

-- Tipo Numero de Paso
type NumPaso = (Int, Paso)

-- Nos regresa la formula del paso n
phiPasoNum :: Int -> [NumPaso] -> PLI
phiPasoNum i lpasos = case mpi of
  Just (phi, _) -> phi
  _ -> error $ "phiPasoNum: indice fuera de rango."
  where
    mpi = lookup i lpasos
    
-- Nos regresa el último NumPaso de una lista
ultimoPaso :: [NumPaso] -> NumPaso
ultimoPaso lpasos
  | lpasos /= [] = (n,p)
  | otherwise = (0,(oTop,Prem))
  where
    (n,p) = last lpasos

-- Revisa que el paso sea correcto
checkPaso :: [PLI] -> [NumPaso] -> NumPaso -> Bool
checkPaso lprem lpp p = case p of
  (n, (phi, Prem)) -> elem phi lprem -- Revisamos que phi sea parte de lprem
  (n, (phi, Ax)) -> esAxiomaDeL phi -- Revisamos que phi sea un axioma
  (n, (phi, ModPon i j)) -> esModusPonens (alpha, beta, phi) && n == nU+1 -- Revisamos que phi sea resultado de hacer modus ponens con i y j
    where
      alpha = phiPasoNum i lpp
      beta = phiPasoNum j lpp
  where
    (nU,(fU,_)) = ultimoPaso lpp

-- Revisa que la prueba sea correcta
checkPrueba :: [PLI] -> [NumPaso] -> Bool
checkPrueba lprem lpasos = case lpasos of
  []      -> True -- Si la lista es vacía entonces es cierto
  _:_     -> checkPrueba lprem lpp && checkPaso lprem lpp p -- Hacemos recursión.
  where
    n = length lpasos
    lpp = Prelude.take (n-1) lpasos
    p = last lpasos

--Muestra una lista de formulas.
showLphi :: [PLI] -> String
showLphi lphi= case lphi of
                    [f]     -> showPLI f
                    f:lf    -> showPLI f ++","++ showLphi lf
                    []      -> ""

-- Muesta la regla
showRegla :: ReglaL -> String
showRegla r = case r of
  Prem -> "premisa"
  Ax -> "axioma"
  ModPon i j -> "Modus Ponens "++show i++","++show j

-- Muestra un paso indicando, mediante b, si es correcto, o no.
showNumPasoCheck :: Int -> NumPaso -> Bool -> String
showNumPasoCheck fSize (n,(phi, r)) b = "\t" ++ (show n) ++ ", " ++ fS ++ spaceAfterPhi ++ rS ++ checks
  where
    fS = showPLI phi
    spaceAfterPhi = " " ++ Prelude.take (fSize-(length fS)) (repeat ' ')
    rS = "\t" ++ (showRegla r)
    checks = if b
      then ". Correcto"
      else ". Incorrecto"

-- Muestra los pasos de lpasos indicando si son correctos, o no.
-- Initial call: showLpasos fSize lprem [] lpasos
showLpasos :: Int -> [PLI] -> [NumPaso] -> [NumPaso] -> IO ()
showLpasos fSize lprem prevLp lpasos = case lpasos of
  [] -> putStr ""
  p:lps -> do
    putStrLn $ showNumPasoCheck fSize p (checkPaso lprem prevLp p)
    showLpasos fSize lprem (prevLp++[p]) lps

-- Muestra el resultado de la prueba realizada.
showCheckConclusion :: [PLI] -> [NumPaso] -> PLI -> IO ()
showCheckConclusion lpremisas lpasos phi =
  do
    putStrLn mensaje
    putStrLn ""
    where
      mensaje
        | not pruebaOK = "\t*** Hay pasos incorrectos. ***"
        | phi /= fN = "\t*** La ultima formula no es el objetivo: ***"++ (showPLI phi) ++" /= "++ (showPLI fN)
        | otherwise =  "\tCorrecto. Mediante el sistema L: "++ lpremS ++ " |- " ++ showPLI fN
      pruebaOK = checkPrueba lpremisas lpasos
      (_,(fN,_)) = ultimoPaso lpasos
      lpremS = if lpremisas /= []
        then "{" ++ showLphi lpremisas ++"}"
        else ""
        
-- Función que nos regresa el elemento más grande.
maxL :: Ord a => [a] -> a
maxL = foldr1 (\x y ->if x >= y then x else y)

-- Revisa si los pasoso son correctos y el resultado de la prueba realizada.
esDeduccionEnL :: [PLI] -> [NumPaso] -> PLI -> IO()
esDeduccionEnL lpremisas lpasos phi =
  do
    showLpasos fSize lpremisas [] lpasos
    showCheckConclusion lpremisas lpasos phi
  where
    fSize = maxL [length (showPLI f) | (_,(f,_)) <- lpasos ]
