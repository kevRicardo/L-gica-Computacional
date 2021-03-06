--Lógica Computacional 2020-1
--Profesor: Dr. Miguel Carrillo Barajas
--Ayudante: Sara Doris Montes Incin
--Ayudante Lab.: Mauricio Esquivel Reyes

--Práctica 02
--Lógica Proposicional
--Alumno: Francisco Javier Tonatoiuh Fuentes Juárez
--Alumno: Kevin Ricardo Villegas Salvador
--Alumno: Roberto Carlos Uribe Cerda

module LP where

import SintaxisPL
import Data.List

-- Tipo de datos para modelos
type Modelo = [Indice]

-- 1.1 Elimina implicaciones

--1.1.1 Dada una fórmula cambiar las instancias de las implicaciones
eliminaImp :: PL -> PL
eliminaImp lp = case lp of
                  Oneg a -> Oneg (eliminaImp a)
                  Oand a b -> Oand (eliminaImp a) (eliminaImp b)
                  Oor a b -> Oor (eliminaImp a) (eliminaImp b)
                  Oimp a b -> Oor (eliminaImp (Oneg a)) (eliminaImp b)
                  _ -> lp

-- 1.2 Forma Normal de Negación
        
--1.2.1 Dada una fórmula de la lógica proposicional 
--      se debe regresar su traducción a forma normal de negación.
aNNF :: PL -> PL
aNNF lp = case lp of
            Oneg Top -> Bot
            Oneg Bot -> Top
            Oneg (Var i) ->  lp
            Oneg (Oneg a) -> aNNF a
            Oneg (Oor a b) -> Oand (aNNF (Oneg (aNNF a))) (aNNF (Oneg (aNNF b)))
            Oneg (Oand a b) -> Oor (aNNF (Oneg (aNNF a))) (aNNF (Oneg (aNNF b)))
            Oand a b -> Oand (aNNF a) (aNNF b)
            Oor a b -> Oor (aNNF a) (aNNF b)
            Oimp a b -> aNNF $eliminaImp lp
            _ -> lp

--1.2.2 Dada una fórmula de la lógica proposicional 
--      verificar si se encuentra en forma normal de negación.
esNNF :: PL -> Bool
esNNF lp = lp == aNNF lp

-- 1.3 Forma Normal Conjuntiva

--1.3.1 Dada una fórmula en forma normal de negación,
--      dar su forma normal conjuntiva, tal que sean lógicamente equivalentes.
aCNF :: PL -> PL
aCNF lp = if esNNF lp
  then case lp of
         Oand a b -> Oand (aCNF a) (aCNF b)
         Oor a b -> dist (aCNF a) (aCNF b)
         Oimp a b -> aCNF (aNNF lp)
         otherwise -> lp
  else aCNF $ aNNF lp

dist :: PL -> PL -> PL
dist (Oand a b) c = Oand (dist a c) (dist b c)
dist a (Oand b c) = Oand (dist a b) (dist a c)
dist a b = Oor a b

--1.3.2 Dada una fórmula de la lógica proposicional
--      revisa si se encuentra en forma normal conjuntiva.
esCNF :: PL -> Bool
esCNF lp = lp == aCNF lp

-- 1.4 Forma Normal Disyuntiva
    
--1.4.1 Dada una fórmula de la lógica proposicional
--      revisa si es un término.
esTermino :: PL -> Bool
esTermino lp = case lp of
                 Top -> True
                 Bot -> True
                 Var i -> True
                 Oneg a -> esTermino a
                 Oand a b -> esTermino a && esTermino b
                 Oor a b -> False
                 Oimp a b -> False

--1.4.2 Dada una fórmula de la lógica proposicional
--      revisa si se encuentra en forma normal disyuntiva.
esDNF :: PL -> Bool
esDNF lp = case lp of
             Oor a b -> esTermino a && esTermino b
             Oimp a b -> esTermino (Oneg a) && esTermino b
             Oand a b -> False
             otherwise -> esTermino lp

-- 1.5 Semántica
  
--1.5.1 Dado un modelo y una fórmula de la lógica proposicional
--      se debe indicar si es satisfacible.
satMod :: Modelo -> PL -> Bool
satMod m pl = eval pl (modifica m)

modifica :: Modelo -> Interpretacion
modifica [] = []
modifica (x:xs) = [(x,True)] ++ modifica xs

type Interpretacion = [(Indice, Bool)]

var :: PL -> Modelo
var lp = case lp of
           Top -> []
           Bot -> []
           Var v -> [v]
           Oneg p -> var p
           Oand p q -> union (var p) (var q)
           Oor p q -> union (var p) (var q)
           Oimp p q -> union (var p) (var q)

--Todas las interpretaciones dadas
interpretaciones :: Modelo -> [Interpretacion]
interpretaciones [] = [[]]
interpretaciones (x:xs) = let i = interpretaciones xs
                          in
                            [(x, True):n | n <- i] ++
                            [(x, False):n | n <- i]

busca :: PL -> Interpretacion -> Bool
busca _ [] = False
busca lp ((x,y):xs) = if lp == Var x
                      then y
                      else busca lp xs

eval :: PL -> Interpretacion -> Bool
eval Top _ = True
eval Bot _ = False
eval lp int = case lp of
                Var i -> busca (Var i) int
                Oneg a -> not $eval lp int
                Oand a b -> (eval a int) && (eval b int)
                Oor a b -> (eval a int) || (eval b int)
                Oimp a b -> not (eval a int) || (eval b int)

--1.5.2 Dada una fórmula de la lógica proposicional indicar si es satisfacible.
esSatPL :: PL -> Bool
esSatPL lp = or[eval lp i | i <- interpretaciones $var lp]

--1.5.3 Dada una fórmula de la lógica proposicional indicar si es valida.
esValPL :: PL -> Bool
esValPL lp = and[eval lp i | i <- interpretaciones $var lp]

{----------Pruebas(PDF)----------}

--Debe regresar: Oor (Oneg (Var 1)) (Var 2)
prueba1 = eliminaImp $Oimp (Var 1) (Var 2)

--Debe regresar: Oand Top Bot
prueba2 = eliminaImp (Oand Top Bot)

--Debe regresar: Oor (Oand (Var 1) (Var 2)) (Oor (Var 3) Bot)
prueba3 = aNNF (Oimp (Oneg $ (Oand (Var 1) (Var 2))) (Oor (Var 3) (Oneg $ Top)))

--Debe regresar: Oand (Oor (Oneg (Var 1)) (Oneg (Var 2))) (Oand (Oneg (Var 3)) Top)
prueba4 = aNNF (Oand (Oneg $ (Oand (Var 1) (Var 2))) (Oneg $ Oor (Var 3) (Oneg $ Top)))

--Debe regresar: False
prueba5 = esNNF (Oneg $ (Oand (Var 1) (Var 2)))

--Debe regresar: True
prueba6 = esNNF (Oor (Oneg $ Var 1) (Oneg $ Var 2))

--Debe regresar: Oand (Oor (Var 1) (Oor (Var 3) Bot)) (Oor (Var 2) (Oor (Var 3) Bot))
prueba7 = aCNF $ Oimp (Oneg $ Oand (Var 1) (Var 2)) (Oor (Var 3) (Oneg $ Top))

--Debe regresar: Oand (Oand (Var 1) (Oneg (Var 2))) (Oand (Oneg (Var 3)) (Oneg (Var 4)))
prueba8 = aCNF $ Oneg $ Oor (Oimp (Var 1) (Var 2)) (Oor (Var 3) (Var 4))

--Debe regresar: False
prueba9 = esCNF (Oimp (Var 1) (Oand (Var 2) (Oor (Var 3) (Var 4))))

--Debe regresar: True
prueba10 = esCNF (Oand (Oor (Var 2) (Oneg $ Var 2)) (Oor (Var 4) (Oor (Var 5) (Var 7))))

--Debe regresar: False
prueba11 = esTermino $ Oand (Var 1) (Oor (Var 2) (Var 3))

--Debe regresar: True
prueba12 = esTermino $ Oand (Oand (Var 1) (Var 2)) (Oneg $ Var 3)

--Debe regresar: True
prueba13 = esDNF (Oor (Oand (Var 2) (Oneg $ Var 2)) (Oand (Var 4) (Oand (Var 5) (Var 7))))

--Debe regresar: False
prueba14 = esDNF (Oor (Oand (Var 2) (Oneg $ Var 2)) (Oand (Var 4) (Oor (Var 5) (Var 7))))

--Debe regresar: False
prueba15 = satMod [1] (Oimp (Var 1) (Var 2))

--Debe regresar: True
prueba16 = satMod [1,2] (Oand (Var 1) (Oor (Var 2) (Var 3)))

--Debe regresar: False
prueba17 = esSatPL $ Oand (Var 1) (Oneg $ Var 1)

--Debe regresar: True
prueba18 = esSatPL $ Oimp (Oand (Var 1) (Var 2)) (Oor (Var 3) (Oneg $ Var 4))

--Debe regresar: False
prueba19 = esValPL (Oand (Var 1) (Oor (Var 2) (Var 3)))

--Debe regresar: True
prueba20 = esValPL (Oor (Var 1) (Oor (Oneg $ Var 2) (Var 3)))
