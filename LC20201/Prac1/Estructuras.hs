--Lógica Comoutacional 2020-1
--Profesor: Miguel Carrillo Barajas
--Ayudante: Sara Doris Montes Incin
--Ayudante Lab.: Mauricio Esquivel Reyes

--Práctica 01
--Estructuras
--Alumno: Kevin Ricardo Villegas Salvador
--No. de Cuenta: 314173739

module Estructuras where

--1.1 Naturales

    --Representación de los números naturales.
    data Natural = Cero 
                   | Suc Natural 
                   deriving(Show, Eq)

    --Dados dos naturales nos dice si el primero es mayor que el segundo.
    mayorQue :: Natural -> Natural -> Bool
    mayorQue n m = natInt n > natInt m

    --Dados os naturales nos dice si el primero es menor que el segundo.
    menorQue :: Natural -> Natural -> Bool
    menorQue n m = natInt n < natInt m

    --Dados dos naturales nos dice si son iguales.
    igual :: Natural -> Natural -> Bool
    igual n m = n == m

    --Convierte un Natural a un Int
    natInt :: Natural -> Int
    natInt n = case n of
        Cero -> 0
        (Suc n) -> 1 + natInt n

--1-2 Lista de naturales

    --Definimos la lista de naturales.
    data ListaDeNaturales = Nil 
                            | Cons Natural ListaDeNaturales 
                            deriving(Show, Eq)

    --Dados dos listas de naturales regresar la concatenación de ambas.
    concate :: ListaDeNaturales -> ListaDeNaturales -> ListaDeNaturales
    concate n m = case n of
        Nil -> m
        (Cons s r) -> Cons s $concate r m

    --Dada un lista regresar la reversa de dicha lista.
    reversa :: ListaDeNaturales -> ListaDeNaturales
    reversa n = case n of
        Nil -> Nil
        (Cons n m) -> concate (reversa m) (Cons n Nil)

    {----------Pruebas----------}

--Debe regresar: False
    prueba1 = mayorQue Cero $Suc Cero

--Debe regresar: True
    prueba2 = mayorQue (Suc Cero) Cero

--Debe regresar: True
    prueba3 = menorQue Cero $Suc Cero

--Debe regresar: False
    prueba4 = menorQue (Suc Cero) Cero

--Debe regresar: False
    prueba5 = igual Cero $Suc Cero

--Debe regresar: True
    prueba6 = igual (Suc Cero) (Suc Cero)

--Debe regresar: Cons (Suc Cero) (Cons Cero (Cons (Suc (Suc Cero)) Nil))
    prueba7 = concate (Cons (Suc Cero) Nil) (Cons Cero (Cons (Suc (Suc Cero)) Nil))

--Debe regresar: Cons Cero (Cons (Suc (Suc Cero)) (Cons (Suc Cero) Nil))
    prueba8 = concate (Cons Cero (Cons (Suc (Suc Cero)) Nil)) (Cons (Suc Cero) Nil)

--Debe regresar: Cons (Suc Cero) (Cons (Suc (Suc Cero)) (Cons Cero Nil))
    prueba9 = reversa (Cons Cero (Cons (Suc (Suc Cero)) (Cons (Suc Cero) Nil)))