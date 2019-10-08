{-Facultad de Ciencias UNAM - Lógica Computacional 2020-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Sara Doris Montes Incin
		  Laboratorio: Mauricio Esquivel Reyes-}

module DeduccionLEjemplos
  where

import SintaxisPLI
import DeduccionL (ReglaL(..),esDeduccionEnL)

ejemplo1 :: IO ()
ejemplo1 = -- {Var 1, Var 1 -> Bot} |- Bot
  let
    v1 = Var 1
    gamma = [v1, oNeg v1]
    lpasos = [
        (1, (v1, Prem)),
        (2, (oNeg v1, Prem)),
        (3, (Bot, ModPon 1 2))
        ]
    phi = Bot
      in esDeduccionEnL gamma lpasos phi

ejemplo2 :: IO ()
ejemplo2 =
  let
    v1 = Var 1
    v2 = Var 2
    v3 = Var 3
    gamma = [v1⇒(v2⇒v3), v1⇒v2]
    (⇒) :: PLI->PLI->PLI
    f⇒g = Oimp f g
    lpasos = [
        (1, (v1⇒(v2⇒v3), Prem)),
        (2, (v1⇒v2, Prem)),
        (3, ((v1⇒(v2⇒v3)) ⇒ ((v1⇒v2) ⇒ (v1⇒v3)), Ax)),
        (4, ((v1⇒v2) ⇒ (v1⇒v3), ModPon 1 3)),
        (5, (v1⇒v3, ModPon 2 4))
        ]
    phi = v1⇒v3
  in esDeduccionEnL gamma lpasos phi
