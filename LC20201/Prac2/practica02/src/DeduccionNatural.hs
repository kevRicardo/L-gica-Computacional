module DeduccionNatural (ReglaDN(..),Paso,checkPrueba,showCheckDedNat) 
--Verifica que los pasos de una deduccion natural sean correctos.
--mcb
where
import Data.List as L (delete,(\\)) -- (nub,union)
--import Data.Set as S
import SintaxisPL
--
--
---------------------------------------------------------------------------------------------------------------
-- Deduccion Natural:
--
data ReglaDN = 
              Icon  Int Int | Econ1 Int | Econ2 Int     -- reglas para la conjuncion
            | Iimp  Int Int | Eimp Int Int              -- reglas para la implicacion
            | Ineg  Int Int | Eneg Int Int              -- reglas para la negacion
            | Idis1 Int | Idis2 Int | Edis Int Int Int  -- reglas para la disyuncion
            | Ebot  Int -- regla para bottom (no hay introduccion de bottom)
            | Isup      -- regla para suposiciones (Assumptions). Las suposiciones se introducen con cajas en una prueba. 
            | Prem      -- ragla para premisas (premises). Las premisas se consideran validas en una prueba.
            | E2neg Int -- regla para eliminacion de doble negacion 
            | Itop      -- regla para top (no hay eliminacion de top). Esta regla no se usa.
            | Copy Int  -- Esta regla permite repetir una formula previa. Huth-Ryan p.20:
                -- The rule ‘copy’ allows us to repeat something that we know already. 
                -- We need to do this in this example, because the rule →i requires that we end the inner box with p. 
                -- The copy rule entitles us to copy formulas that appeared before,
                -- unless they depend on temporary assumptions whose box has already been closed. 
                -- Though a little inelegant, this additional rule is a small price to pay
                -- for the freedom of being able to use premises, or any other ‘visible’ formulas, more than once.            
            deriving (Eq,Show,Read)
--
type Caja   = (Int,Int) -- Caja de suposiciones. Huth-Ryan p.12.
                        -- (i,j), 0<i<=j: caja cerrada de i a j
                        -- (i,j), 0=j<i : caja abierta de i a ...
            -- Proofs may nest boxes or open new boxes after old ones have been closed.
            -- There are rules about which formulas can be used at which points in the proof. 
            -- Generally, we can only use a formula φ in a proof at a given point if:
            --      (1) that formula occurs prior to that point and
            --      (2) no box which encloses that occurrence of φ has been closed already.
            -- The line immediately following a closed box has to match 
            -- the pattern of the conclusion of the rule that uses the box. 
            -- For implies-introduction, this means that we have to continue after the box with φ → ψ, 
            -- where φ was the first and ψ the last formula of that box.
--
type Paso   = (PL,ReglaDN,[Caja])   -- Un paso de una prueba, 
                                    -- (formula,regla_aplicada,listaDeCajas)
type NumPaso= (Int,Paso)            -- Un paso numerado, (numero, paso)
--
phiOfPaso :: Int->[NumPaso] -> PL
--formula del paso numero i en lpasos
phiOfPaso i lpasos = case mpi of
                    Just (fi,_,_) -> fi
                    _               -> error $ "phiOfPaso: i fuera de rango, (i,lpasos)="++show (i,lpasos)
    where
    mpi = lookup i lpasos
--
ultimoPaso :: [NumPaso] -> NumPaso 
ultimoPaso lpasos
    | lpasos /= [] = (n,p)
--     | otherwise = error $ "ultimoPaso: no hay pasos, lpasos="++show lpasos
    | otherwise = (0,(Top,Itop,[]))   -- (nN,(fN,r,lcN))
    where
    (n,p)   = last lpasos
--
conKof :: Int -> PL -> PL
-- conyunto k de f
conKof k f = case f of
              f1 `Oand` f2
                    | k==1  -> f1
                    | k==2  -> f2
                    | otherwise     -> error $ "conKof: k debe ser 1 o 2, k= "++show k
              _                     -> error $ "conKof: f debe ser una conjuncion, f="++show f
--
--
usableP :: Int->[Caja]->Int -> Bool
-- True si la formula del paso j es usable en el paso nN. Es decir, si 0<j<=nN y j no esta en ninguna caja cerrada.
usableP j lcajas nN =   0<j && j<=nN    -- j>0 y j es menor o igual que el ultimo paso previo
                    && and [not (k<=j && j<=l) | (k,l) <- cajasCerradas] -- j no está en ninguna caja cerrada.
                    where
                    cajasCerradas= [(k,l) | (k,l) <- lcajas, l/=0]
--
cerrarCaja :: [Caja]->Int->Int -> [Caja]
-- Cierra correctamente la caja (i,0), de lcajas, en el paso j. 
cerrarCaja lcajas i j
    | (i,0) `notElem` cajasAbiertas     = error laCajaNoEstaAbierta
    | cajasInternasAbiertas /= []       = error hayUnaCajaInternaAbierta
    | j < i                             = error jMenorQuei
    | otherwise                         = (i,j): (L.delete (i,0) lcajas)
    where
    laCajaNoEstaAbierta     = "\n cerrarCaja: la caja "++show (i,j) ++" no esta abierta."
    hayUnaCajaInternaAbierta= "\n cerrarCaja: hay al menos una caja interna abierta: "++show (head cajasInternasAbiertas)
    jMenorQuei              = "\n cerrarCaja: finalDeCaja(j) debe ser >= que inicioDeCaja(i), (i,j)= "++show (i,j)
    cajasAbiertas           = [(k,l) | (k,l) <- lcajas, l==0]
    cajasInternasAbiertas   = [(k,l) | (k,l) <- cajasAbiertas, i<k, l<j]
--
-- Verificacion de los pasos de una prueba mediante deduccion natural: ----------------------------
--
checkIcon :: [NumPaso] -> NumPaso -> Bool
-- Sean lpp una lista de pasos numerados y p un paso numerado.
-- checkIcon lpp p=True sii p cumple los requisitos para ser el siguiente paso de lpp mediante introduccion de la conjuncion.
checkIcon lpp p = -- listaDePasosPrevios pasoActual
    case p of -- pasoNumerado = (numPaso,(phi,regla,listaCajas))
        (m,(phi,Icon i j,lc))   ->     lpp/=[]          -- hay pasos previos
                                    && m==nN+1          -- m se incrementa en 1.
                                    && lc== lcN         -- las cajas no cambiaron
                                    && usableP i lc nN  -- i es usable, i<nN && i no esta en una caja cerrada 
                                    && usableP j lc nN  -- j es usable, j<nN && j no esta en una caja cerrada 
                                    && (   (phi == fi `Oand` fj)    --phi=fi&fj: fi,fj |- fi&fj
                                        || (phi == fj `Oand` fi))   --phi=fj&fi: fi,fj |- fj&fi
                                    where 
                                    fi= phiOfPaso i lpp -- paso i
                                    fj= phiOfPaso j lpp -- paso j
        _                       -> False
        where
        (nN,(_,_,lcN))= ultimoPaso lpp
--
checkEcon1 :: [NumPaso] -> NumPaso -> Bool
-- Sean lpp una lista de pasos numerados y p un paso numerado.
-- checkEcon1 lpp p=True sii p cumple los requisitos para ser el siguiente paso de lpp mediante eliminacion de la conjuncion 1.
checkEcon1 lpp p = -- listaDePasosPrevios pasoActual
    case p of -- pasoNumerado = (numPaso,(phi,regla,listaCajas))
        (m,(g,Econ1 i,lc))           ->    lpp/=[]          -- hay pasos previos
                                        && m==nN+1          -- m se incrementa en 1.
                                        && lc== lcN         -- las cajas no cambiaron
                                        && usableP i lc nN  -- i es usable, i<nN && i no esta en una caja cerrada 
                                        && g == conKof 1 fi -- g= conyunto 1 de fi: gi & hi |- gi
                                        where 
                                        fi = phiOfPaso i lpp -- paso i, fi= gi & hi
        _                               -> False
        where
        (nN,(_,_,lcN))= ultimoPaso lpp
--
checkEcon2 :: [NumPaso] -> NumPaso -> Bool
-- Sean lpp una lista de pasos numerados y p un paso numerado.
-- checkEcon2 lpp p=True sii p cumple los requisitos para ser el siguiente paso de lpp mediante eliminacion de la conjuncion 2.
checkEcon2 lpp p = -- listaDePasosPrevios pasoActual
    case p of -- pasoNumerado = (numPaso,(phi,regla,listaCajas))
        (m,(g,Econ2 i,lc))           ->    lpp/=[]          -- hay pasos previos
                                        && m==nN+1          -- m se incrementa en 1.
                                        && lc== lcN         -- las cajas no cambiaron
                                        && usableP i lc nN  -- i es usable, i<nN && i no esta en una caja cerrada 
                                        && g == conKof 2 fi -- g= conyunto 2 de fi: gi & hi |- hi
                                        where 
                                        fi = phiOfPaso i lpp -- paso i, fi= gi & hi
        _                               -> False
        where
        (nN,(_,_,lcN))= ultimoPaso lpp
--
esDisyuncion :: PL-> (Bool,PL,PL)
--esDisyuncion f= (True,g,h) si f= g v h.
esDisyuncion f = case f of
                      g `Oor`h -> (True,g,h)
                      _         -> (False,Bot,Bot) 
--
checkEdis :: [NumPaso] -> NumPaso -> Bool
-- Sean lpp una lista de pasos numerados y p un paso numerado.
-- checkEdis lpp p=True sii p cumple los requisitos para ser el siguiente paso de lpp mediante eliminacion de la disyuncion.
checkEdis lpp p = -- listaDePasosPrevios pasoActual
    case p of -- pasoNumerado = (numPaso,(phi,regla,listaCajas))
        (m,(w,Edis i j k,lc))   -> -- Eliminacion de la disyuncion: si fi=gvh, fj=g->w y fk=h->w, ent. fi,fj,fk |- w
                                        lpp/=[]          -- hay pasos previos
                                    && m==nN+1          -- m se incrementa en 1.
                                    && lc== lcN         -- las cajas no cambiaron
                                    && usableP i lc nN  -- i es usable, i<nN && i no esta en una caja cerrada 
                                    && usableP j lc nN  -- j es usable, j<nN && j no esta en una caja cerrada 
                                    && usableP k lc nN  -- k es usable, k<nN && k no esta en una caja cerrada 
                                    -- 
                                    && fiESgORh                                 -- fi= g`Oor`h
                                    && (   (fj==(g`Oimp`w) && fk==(h`Oimp`w))   -- (fj=g->w) & (fk=h->w)
                                        || (fk==(g`Oimp`w) && fj==(h`Oimp`w)))  -- (fk=g->w) & (fj=h->w)
                                    where 
                                    (fiESgORh,g,h) = esDisyuncion fi
                                    fi  = phiOfPaso i lpp -- paso i
                                    fj  = phiOfPaso j lpp -- paso j
                                    fk  = phiOfPaso k lpp -- paso k
        _                       -> False
        where
        (nN,(_,_,lcN))= ultimoPaso lpp
--
checkIdis1 :: [NumPaso] -> NumPaso -> Bool
-- Sean lpp una lista de pasos numerados y p un paso numerado.
-- checkEdis1 lpp p=True sii p cumple los requisitos para ser el siguiente paso de lpp mediante introduccion de la disyuncion 1.
checkIdis1 lpp p = -- listaDePasosPrevios pasoActual
    error $ "checkIdis1: caso no implementado aun, (p,lpp)="++show (p,"  ",lpp)
--
checkIdis2 :: [NumPaso] -> NumPaso -> Bool
-- Sean lpp una lista de pasos numerados y p un paso numerado.
-- checkEdis2 lpp p=True sii p cumple los requisitos para ser el siguiente paso de lpp mediante introduccion de la disyuncion 2.
checkIdis2 lpp p = -- listaDePasosPrevios pasoActual
    error $ "checkIdis2: caso no implementado aun, (p,lpp)="++show (p,"  ",lpp)
--
checkE2neg :: [NumPaso] -> NumPaso -> Bool
-- Sean lpp una lista de pasos numerados y p un paso numerado.
-- checkE2neg lpp p=True sii p cumple los requisitos para ser el siguiente paso de lpp mediante eliminacion de doble negacion.
checkE2neg lpp p = -- listaDePasosPrevios pasoActual
    error $ "E2neg: caso no implementado aun, (p,lpp)="++show (p,"  ",lpp)
--
checkIimp :: [NumPaso] -> NumPaso -> Bool
-- Sean lpp una lista de pasos numerados y p un paso numerado.
-- checkIimp lpp p=True sii p cumple los requisitos para ser el siguiente paso de lpp mediante introduccion de la implicacion.
checkIimp lpp p = -- listaDePasosPrevios pasoActual
    case p of -- pasoNumerado = (numPaso,(phi,regla,listaCajas))
        (m,(f,Iimp i j,lc)) ->    lpp/=[]                  -- hay pasos previos
                                        && m==nN+1                  -- m se incrementa en 1.
                                        && i <= j                   -- j no ocurre antes de i
                                        && j==nN && fj==fN          -- fj= formula del paso inmediato anterior.Huth-Ryan
                                        && lc L.\\ lcNijCerrada==[] -- se cerro la caja (i,j)
                                        && usableP i lcN nN -- i es usable, i<=nN && i no esta en una caja cerrada 
                                        && usableP j lcN nN -- j es usable, j<=nN && j no esta en una caja cerrada 
                                        && i <= j           -- j no ocurre antes de i
                                        && f==fi `Oimp` fj  -- introduccion de la implicacion: [fi...fj] |- fi->fj 
                                        where 
                                        lcNijCerrada= cerrarCaja lcN i j
                                        fi= phiOfPaso i lpp -- formula del paso i.
                                        fj= phiOfPaso j lpp -- formula del paso j.
        _                       -> False
        where
        (nN,(fN,_,lcN))= ultimoPaso lpp
--
checkEimp :: [NumPaso] -> NumPaso -> Bool
-- Sean lpp una lista de pasos numerados y p un paso numerado.
-- checkEimp lpp p=True sii p cumple los requisitos para ser el siguiente paso de lpp mediante eliminacion de la implicacion.
checkEimp lpp p = -- listaDePasosPrevios pasoActual
    case p of -- pasoNumerado = (numPaso,(phi,regla,listaCajas))
        (m,(h,Eimp i j,lc)) ->     lpp/=[]              -- hay pasos previos
                                && m==nN+1              -- m se incrementa en 1.
                                && lc== lcN             -- las cajas no cambiaron
                                && usableP i lc nN      -- i es usable, i<nN && i no esta en una caja cerrada 
                                && usableP j lc nN      -- j es usable, j<nN && j no esta en una caja cerrada 
                                && (   fj==fi `Oimp` h  
                                    || fi==fj `Oimp` h) -- eliminacion de la implicacion: f,f->h |- h
                                    where 
                                    fi= phiOfPaso i lpp -- paso i
                                    fj= phiOfPaso j lpp -- paso j
        _                   -> False
        where
        (nN,(_,_,lcN))= ultimoPaso lpp
--
checkIneg :: [NumPaso] -> NumPaso -> Bool
-- Sean lpp una lista de pasos numerados y p un paso numerado.
-- checkIneg lpp p=True sii p cumple los requisitos para ser el siguiente paso de lpp mediante introduccion de la negacion.
checkIneg lpp p = -- listaDePasosPrevios pasoActual
    case p of -- pasoNumerado = (numPaso,(phi,regla,listaCajas))
        (m,(Oneg g,Ineg i j,lc))    ->     lpp/=[]                  -- hay pasos previos
                                        && m==nN+1                  -- m se incrementa en 1.
                                        && i <= j                   -- j no ocurre antes de i
                                        && lc L.\\ lcNijCerrada==[] -- se cerro la caja (i,j)
                                        && usableP i lcN nN -- i es usable, i<=nN && i no esta en una caja cerrada 
                                        && usableP j lcN nN -- j es usable, j<=nN && j no esta en una caja cerrada 
                                        && fi==g    -- fi=g
                                        && j ==nN   -- j es el paso inmediato anterior.Huth-Ryan
                                        && fj==Bot  -- introduccion de la negacion: [fi...Bot] |- fi->Bot = ¬g
                                            where 
                                            lcNijCerrada= cerrarCaja lcN i j
                                            fi= phiOfPaso i lpp -- paso i
                                            fj= phiOfPaso j lpp -- formula del paso j.
        _                       -> False
        where
        (nN,(_,_,lcN))= ultimoPaso lpp
--
checkEneg :: [NumPaso] -> NumPaso -> Bool
-- Sean lpp una lista de pasos numerados y p un paso numerado.
-- checkEneg lpp p=True sii p cumple los requisitos para ser el siguiente paso de lpp mediante eliminacion de la negacion.
checkEneg lpp p = -- listaDePasosPrevios pasoActual
    case p of -- pasoNumerado = (numPaso,(phi,regla,listaCajas))
        (m,(Bot,Eneg i j,lc))   ->     lpp/=[]                  -- hay pasos previos
                                    && m==nN+1                  -- m = ultimoPaso + 1.
                                    && lc== lcN                 -- las cajas no cambiaron
                                    && usableP i lc nN          -- i es usable, i<nN && i no esta en una caja cerrada 
                                    && usableP j lc nN          -- j es usable, j<nN && j no esta en una caja cerrada 
                                    && (   fj==fi `Oimp` Bot   
                                        || fi==fj `Oimp` Bot)   -- eliminacion de la negacion: f,f->Bot |- Bot 
                                        where 
                                        fi= phiOfPaso i lpp -- paso i
                                        fj= phiOfPaso j lpp -- paso j
        _                       -> False
        where
        (nN,(_,_,lcN))= ultimoPaso lpp
--
checkIsup :: [NumPaso] -> NumPaso -> Bool
-- Sean lpp una lista de pasos numerados y p un paso numerado.
-- checkIsup lpp p=True sii p cumple los requisitos para ser el siguiente paso de lpp mediante introduccion de suposicion.
checkIsup lpp p = -- listaDePasosPrevios pasoActual
    case p of -- pasoNumerado = (numPaso,(phi,regla,listaCajas))
        (m,(_,Isup,lc)) ->     m==nN+1                  -- m se incrementa en 1.
                            && lc== lcN ++ [(nN+1,0)]   -- la caja (nN+1,0) se agrego a las cajas
        _               -> False
        where
        (nN,(_,_,lcN))= ultimoPaso lpp
--
checkPrem :: [PL]->[NumPaso]->NumPaso -> Bool
-- Sean lprem una lista de premisas, lpp una lista de pasos numerados, y p un paso numerado.
-- checkPrem lprem lpp p=True sii p cumple los requisitos para ser el siguiente paso de lpp mediante el uso de una premisa.
checkPrem lprem lpp p = -- listaDePasosPrevios pasoActual
    case p of -- pasoNumerado = (numPaso,(phi,regla,listaCajas))
        (m,(f,Prem,_))  ->     f `elem` lprem   -- basta que f este en la lista de premisas
                            && m==nN+1          -- m = nN+1
        _               -> False
        where
        (nN,(_,_,_))= ultimoPaso lpp
--
checkEbot :: [NumPaso] -> NumPaso -> Bool
-- Sean lpp una lista de pasos numerados y p un paso numerado.
-- checkEbot lpp p=True sii p cumple los requisitos para ser el siguiente paso de lpp mediante eliminacion de bottom.
checkEbot lpp p = -- listaDePasosPrevios pasoActual
    case p of -- pasoNumerado = (numPaso,(phi,regla,listaCajas))
        (m,(_,Ebot i,lc))   ->     lpp/=[]          -- hay pasos previos
                                && m==nN+1          -- m se incrementa en 1.
                                && lc== lcN         -- las cajas no cambiaron
                                && usableP i lc nN  -- i es usable, i<nN && i no esta en una caja cerrada 
                                && fi==Bot          -- eliminacion de Bot: Bot |- f
                                where
                                fi= phiOfPaso i lpp -- paso i
        _                   -> False
        where
        (nN,(_,_,lcN))= ultimoPaso lpp
--
checkItop :: [NumPaso] -> NumPaso -> Bool
-- Sean lpp una lista de pasos numerados y p un paso numerado.
-- checkItop lpp p=True sii p cumple los requisitos para ser el siguiente paso de lpp mediante introduccion de top.
checkItop lpp p = -- listaDePasosPrevios pasoActual
    case p of -- pasoNumerado = (numPaso,(phi,regla,listaCajas))
        (m,(Top,Itop,_))    ->     True     -- Top se puede derivar sin restricciones
                                && m==nN+1  -- m se incrementa en 1.
        _                   -> False
        where
        (nN,(_,_,_))= ultimoPaso lpp
--
checkCopyR :: [NumPaso] -> NumPaso -> Bool
-- Sean lpp una lista de pasos numerados y p un paso numerado.
-- checkCopyR lpp p=True sii p cumple los requisitos para ser el siguiente paso de lpp mediante la regla Copy.
checkCopyR lpp p = -- listaDePasosPrevios pasoActual
    case p of -- pasoNumerado = (numPaso,(phi,regla,listaCajas))
        (m,(f,Copy i,lc))   ->     lpp/=[]          -- hay pasos previos
                                && m==nN+1          -- m se incrementa en 1.
                                && lc== lcN         -- las cajas no cambiaron
                                && usableP i lcN nN -- i es usable, i<=nN && i no esta en una caja cerrada 
                                && f== fi           -- f es la formula del paso i
                                where 
                                fi= phiOfPaso i lpp -- formula del paso i.
        _                   -> False
        where
        (nN,(_,_,lcN))= ultimoPaso lpp
--
--
--
checkPaso :: [PL]->[NumPaso]->NumPaso -> Bool
checkPaso lprem lpp p@(_,(_,dnRule,_)) = -- listaDePremisas listaDePasosPrevios pasoActual
    case dnRule of
         --Reglas para la conjuncion:
        Icon _ _    -> checkIcon lpp p  -- verifica que p es una introduccion de la conjuncion
        Econ1 _     -> checkEcon1 lpp p -- verifica que p es una eliminacion de la conjuncion 1
        Econ2 _     -> checkEcon2 lpp p -- verifica que p es una eliminacion de la conjuncion 2
         --Reglas para la disyuncion:
        Edis _ _ _  -> checkEdis lpp p  -- verifica que p es una eliminacion de la disyuncion
        Idis1 _     -> checkIdis1 lpp p -- No implementado ####
        Idis2 _     -> checkIdis2 lpp p -- No implementado ####
        --Reglas para la implicacion:
        Iimp _ _    -> checkIimp lpp p  -- verifica que p es una introduccion de la implicacion
        Eimp _ _    -> checkEimp lpp p  -- verifica que p es una eliminacion de la implicacion
        --Reglas para la negacion (¬g = g -> Bot):
        Ineg _ _    -> checkIneg lpp p  -- verifica que p es una introduccion de la negacion
        Eneg _ _    -> checkEneg lpp p  -- verifica que p es una eliminacion de la negacion
        E2neg _     -> checkE2neg lpp p -- No implementado ####
        -- Regla para suposiciones (Assumptions):
        Isup        -> checkIsup lpp p  -- verifica que p es una introduccion de suposicion (Assumption)
        -- Regla para premisas (Premises):
        Prem        -> checkPrem lprem lpp p -- verifica que p es el uso de una premisa.
        -- Regla para Bot (no hay introduccion de Bot):
        Ebot _      -> checkEbot lpp p  -- verifica que p es el uso de eliminacion de bottom.
        -- Regla para Top:
        Itop        -> checkItop lpp p  -- verifica que p es una introduccion de top.
        -- Regla para usar formulas previas:
        Copy _      -> checkCopyR lpp p -- verifica que p es un uso de la regla Copy.
        --_                               -> error $ "checkPaso: caso no implementado aun, p="++show p
--
--
checkPrueba :: [PL]->[NumPaso] -> Bool
-- True sii todos los pasos de lpasos son pasos válidos mediante alguna regla de deduccion natural.
checkPrueba lprem lpasos= -- listaDePremisas listaDePasos 
    case lpasos of
         []     -> True -- la lista de pasos vacia es valida
         _:_    -> checkPrueba lprem lpp && checkPaso lprem lpp p
         where
         n  = length lpasos
         lpp= Prelude.take (n-1) lpasos
         p  = last lpasos
--
--
---------------------------------------------------------------------------------------------------------------
--
showRegla :: ReglaDN->String
showRegla r= case r of
            -- reglas para la conjuncion:
            Icon  i j   -> "iCon "++show i++","++show j
            Econ1 i     -> "eCon1 "++show i
            Econ2 i     -> "eCon2 "++show i
            -- reglas para la implicacion:
            Iimp  i j   -> "iImp "++show i++"-"++show j
            Eimp i j    -> "eImp "++show i++","++show j
            -- reglas para la negacion:
            Ineg  i j   -> "iNeg "++show i++"-"++show j
            Eneg i j    -> "eNeg "++show i++","++show j
            -- reglas para la disyuncion:
            Idis1 i     -> "iDis1 "++show i
            Idis2 i     -> "iDis2 "++show i
            Edis i j k  -> "eDis "++show i++","++show j++","++show k
            -- regla para bottom (no hay introduccion de bottom):
            Ebot  i     -> "eBot "++show i
            -- regla para suposiciones (Assumptions):
            Isup        ->  "suposicion"
            -- regla para premisas (Premises):
            Prem        ->  "premisa"
            -- regla para eliminacion de la doble negacion:
            E2neg i     ->  "E¬¬ "++show i
            -- regla para top (no hay eliminacion de top). Esta regla no se usa:
            Itop        ->  "iTop"
            -- La siguiente regla permite repetir una formula previa. (***):
            Copy i      ->  "copy "++show i
--             _           ->  show r
            --
--
showLphi :: [PL] -> String
--Muestra una lista de formulas.
showLphi lphi= case lphi of
                    [f]     -> showPL f
                    f:lf    -> showPL f ++","++ showLphi lf
                    []      -> ""
--     
showCaja :: Caja -> String
showCaja (k,l) = showN k++"-"++ showN l
    where
    showN n= if n==0
                then "?"
                else show n
--
--
showLcajas :: [Caja] -> String
--Muestra una lista de cajas.
showLcajas lcajas= case lcajas of
                    [(i,j)] -> showCaja (i,j)
                    c:lc    -> showCaja c ++","++ showLcajas lc
                    []      -> ""
--
--                    
showNumPasoCheck :: Int->NumPaso->Bool -> String
-- Muestra un paso indicando, mediante b, si es correcto, o no.
showNumPasoCheck fSize (n,(f,r,lc)) b = "\t" ++ (show n) ++". "++ fS++ spaceAfterPhi++ rS ++ lcS  ++ checkS
    where
    fS              = showPL f
    spaceAfterPhi   = " " ++ Prelude.take (fSize-(length fS)) (repeat ' ')
    rS              = "\t " ++ (showRegla r)
    lcS             = ". Cajas=["++ showLcajas lc ++"]"
    checkS          = if b 
                        then ". Correcto" 
                        else ". Incorrecto"
--
showLpasos :: Int->[PL]->[NumPaso]->[NumPaso] -> IO ()
-- Muestra los pasos de lpasos indicando si son correctos, o no.
-- Initial call: showLpasos fSize lprem [] lpasos
showLpasos fSize lprem prevLp lpasos = 
    case lpasos of
            []      -> putStr ""
            p:lps   ->  do
                        putStrLn $ showNumPasoCheck fSize p (checkPaso lprem prevLp p)
                        showLpasos fSize lprem (prevLp++[p]) lps
--
showCheckConclusion :: [PL]->[NumPaso]->PL -> IO ()
showCheckConclusion lpremisas lpasos phi =   
    do
    putStrLn mensaje
    putStrLn ""
    where 
    mensaje 
        | not pruebaOK  = "\t*** Hay pasos incorrectos. ***"
        | lcAbiertas/=[]= "\t*** Hay cajas de suposiciones que no se cerraron ***: "++ showLcajas lcAbiertas
        | phi/=fN       = "\t*** La ultima fórmula no es el objetivo ***: "++ (showPL phi) ++" /= "++ (showPL fN)
        | otherwise     = "\tCorrecto. Mediante deduccion natural: "++ lpremS ++ " |- " ++ showPL fN
    pruebaOK            = checkPrueba lpremisas lpasos
    (_,(fN,_,lc))       = ultimoPaso lpasos
    lpremS              = if lpremisas /= []
                             then "{" ++ showLphi lpremisas ++"}"
                             else ""
    lcAbiertas          = [(i,j) | (i,j)<-lc, j==0]
--
maxL :: Ord a => [a] -> a
maxL = foldr1 (\x y ->if x >= y then x else y)
--
showCheckDedNat :: [PL]->[NumPaso]->PL -> IO ()
--Muestra y verifica que lpasos sea una deduccion natural correcta de: lpremisas |- phi.
--Es decir, muestra y verifica que lpasos es una prueba, con deduccion natural, de phi a partir de lpremisas.
showCheckDedNat lpremisas lpasos phi = --listaDePremisas listaDePasos
    do
    showLpasos fSize lpremisas [] lpasos
    showCheckConclusion lpremisas lpasos phi 
    where
    --fSize= 50
    fSize= maxL [length (showPL f) | (_,(f,_,_)) <- lpasos] 

--
