--Lógica Comoutacional 2020-1
--Profesor: Dr. Miguel Carrillo Barajas
--Ayudante: Sara Doris Montes Incin
--Ayudante Lab.: Mauricio Esquivel Reyes

--Práctica 01
--Lógica Proposicional
--Francisco Javier Tonatiuh Fuentes Juárez
--Kevin Ricardo Villegas Salvador
--Roberto Carlos Uribe Cerda

module LP where

    --Tipo de dato índice
    type Indice = Int

    --Tipo de dato fórmula
    data PL = Top | Bot | Var Indice
              | Oneg PL
              | Oand PL PL | Oor PL PL
              | Oimp PL PL deriving(Eq, Show)

    --Dada una fórmula regresa un valor de verdad 
    --si hay una implicación en dicha fórmula.
    hayImplicacion :: PL -> Bool
    hayImplicacion pl = case pl of
        Top -> False
        Bot -> False
        Var i -> False
        Oneg p -> hayImplicacion p
        Oand p q -> hayImplicacion p || hayImplicacion q
        Oor p q -> case p of
            Oneg r -> True
            _        -> hayImplicacion p || hayImplicacion q
        Oimp p q -> True
        
    --Dada una fórmula regresar una lista con las disyunciones de dicha fórmula
    disy :: PL -> [PL]
    disy pl = case pl of
        Top -> []
        Bot -> []
        Var i -> []
        Oneg p -> disy p
        Oand p q -> disy p ++ disy q
        Oor p q -> [pl] ++ disy p ++ disy q
        Oimp p q -> disy p ++ disy q
                  --[pl] ya que p -> q = ¬p v q

    --Dada una fórmula regresar el número de conjunciones que tiene dicha fórmula
    numConj :: PL -> Int
    numConj pl = case pl of
        Top -> 0
        Bot -> 0
        Var i -> 0
        Oneg p -> numConj p
        Oand p q -> 1 + numConj p + numConj q
        Oor p q -> numConj p + numConj q
        Oimp p q -> numConj p + numConj q