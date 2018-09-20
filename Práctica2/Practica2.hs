--Villegas Salvador Kevin Ricardo
module Practica2 where
import LProp

-- Alias de tipos: Sólo sirve para referirnos
-- a un tipo existente por un nuevo nombre, 
-- pero podemos seguir manipulándolo como
-- al tipo subyacente.
type Interpretacion = [(Char, Bool)] -- El tipo Interpretacion representa
                                     -- una asignación de variables proposicionales.

-- Por ejemplo, [('A', True), ('B', False)]
-- asigna la variable A a verdadero y B a falso.


-- interpretaciones toma una lista de nombres de variables
-- proposicionales y regresa una lista de todas las posibles
-- interpretaciones para esas variables.
-- Nótese que si la lista de entrada es de longitud n,
-- la lista de salida tendrá longitud 2^n.
interpretaciones :: [Char] -> [Interpretacion]
interpretaciones [] = [[]]
interpretaciones (c:cs)  = let ints = interpretaciones cs in
                               [(c, True):xs | xs <- ints] ++
                               [(c, False):xs | xs <- ints]
                              -- ^ listas por comprensión.


-- busca toma una proposición (idealmente, una variable)
-- y una interpretación y devuelve su valor de verdad
-- asignado, si es que existe.
busca :: Prop -> Interpretacion -> Bool
busca _ [] = error "No se encontró asignación en la interpretación."
busca pr ((p,b):xs) = if(pr == PVar p) 
                         then b 
                         else busca pr xs
--          ^
--          L_ nótese que aquí estamos des-estructurando una tupla al mismo 
--         tiempo que la lista.


-- eval evalúa una fórmula proposicional según una 
-- interpretación dada.
eval :: Prop -> Interpretacion -> Bool
eval PTrue _ = True
eval PFalse _ = False
eval pr i = case pr of
                 (PVar pr) -> (busca (PVar pr) i)
                 (PNeg pr) -> not(eval pr i)
                 (POr pr1 pr2) -> ((eval pr1 i) || (eval pr2 i))
                 (PAnd pr1 pr2) -> ((eval pr1 i) && (eval pr2 i))
                 (PImpl pr1 pr2) -> (not(eval pr1 i) || (eval pr2 i))
                 (PEquiv pr1 pr2) -> (eval(PImpl pr1 pr2) i) && (eval(PImpl pr2 pr1) i)

-- satisfacible toma una fórmula proposicional
-- y devuelve si es satisfacible, esto es, existe
-- una interpretación con la que se evalúa a True.
-- Este es un problema NP-Completo, pero esto nos 
-- importa muy poco, lo hacemos por fuerza bruta 
-- como se debe.
satisfacible :: Prop -> Bool
satisfacible pr = or[eval pr i | i <- interpretaciones (quita(variable pr))]

--Enlista las variables proposicionales de una fórmula proposicional.
variable :: Prop -> [Char]
variable (PVar pr) = [pr]
variable (PNeg pr) = variable pr
variable (POr pr1 pr2) = variable pr1 ++ variable pr2
variable (PAnd pr1 pr2) = variable pr1 ++ variable pr2
variable (PImpl pr1 pr2) = variable pr1 ++ variable pr2
variable (PEquiv pr1 pr2) = variable pr1 ++ variable pr2

--Elimina los elementos repetidos de una lista de Char
quita :: [Char] -> [Char]
quita [] = []
quita (a:as) = [a] ++ (filter (/=a) (quita as))

-- fnc toma una fórmula proposicional
-- y devuelve una fórmula equivalente a ésta en forma
-- normal conjuntiva. Consúltese el documento Practica2.pdf
-- para conocer el algoritmo.
fnc:: Prop -> Prop
fnc (PVar pr) = (PVar pr)
fnc (PNeg pr) = (PNeg pr)
fnc (PAnd pr1 pr2) = PAnd (fnc pr1) (fnc pr2)
fnc (POr pr1 pr2) = dist (fnc pr1) (fnc pr2)
fnc (PImpl pr1 pr2) = fnc (neg(qimpli (PImpl pr1 pr2)))
fnc (PEquiv pr1 pr2) = fnc (neg(qimpli (PEquiv pr1 pr2)))

--lleva una proposición a su FNN
neg :: Prop -> Prop
neg (PVar pr) = (PVar pr)
neg (PNeg(PVar pr)) = (PNeg(PVar pr))
neg (PNeg(PNeg pr)) = (neg pr)
neg (PNeg(POr pr1 pr2)) = PAnd (PNeg(neg pr1)) (PNeg(neg pr2))
neg (PNeg(PAnd pr1 pr2)) = POr (PNeg(neg pr1)) (PNeg(neg pr2))
neg (PAnd pr1 pr2) = PAnd (neg pr1) (neg pr2)
neg (POr pr1 pr2) = POr (neg pr1) (neg pr2)

--Elimina las implicaciones de una proposición
qimpli :: Prop -> Prop
qimpli (PVar pr) = (PVar pr)
qimpli (PNeg pr) = PNeg (qimpli pr)
qimpli (POr pr1 pr2) = POr (qimpli pr1) (qimpli pr2)
qimpli (PAnd pr1 pr2) = PAnd (qimpli pr1) (qimpli pr2)
qimpli (PImpl pr1 pr2) = POr (PNeg(qimpli pr1)) (qimpli pr2)
qimpli (PEquiv pr1 pr2) = PAnd (POr (PNeg(qimpli pr1)) (qimpli pr2)) (POr (qimpli pr1) (PNeg(qimpli pr2)))

dist :: Prop -> Prop -> Prop
dist (PAnd pr1 pr2) pr3 = (PAnd (dist pr1 pr3) (dist pr2 pr3))
dist pr1 (PAnd pr2 pr3) = (PAnd (dist pr1 pr2) (dist pr1 pr3))
dist pr1 pr2 = POr pr1 pr2
