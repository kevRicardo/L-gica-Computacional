--Lógica Computacional 2019-1
--Profesor: César Hernández Cruz
--Ayudante: Víctor Zamora Gutiérrez
--Ayudante Lab: Diego Carrillo Verduzco
--Práctica 1
--Alumno: Villegas Salvador Kevin Ricardo
--No. de Cuenta: 314173739

module Pract1 where

--Remueve todas las ocurrencias del elemento del tipo a, en la lista de tipo a.
rm :: Eq a => a -> [a] ->[a]
rm _ [] = []
rm a (x:xs) = if(a /= x) 
 then [x] ++ rm a xs 
 else rm a xs

--Calcula la diferencia en el sentido conjuntista.
(\\) :: Eq a => [a] -> [a] -> [a]
(\\) [] b = []
(\\) (a:as) bs = let j = [a|elem a(a:as) && (not(elem a bs))] 
 in 
 j ++ (\\) as bs

--Remueve todos los elementos duplicados de una lista.
rmdup :: Eq a => [a] -> [a]
rmdup [] = []
rmdup (a:as) = [a] ++ (filter (a/=) (rmdup as))

--Se define el tipo de dato Tree.
data Tree a = Empty						--Árbol vacío
 |Node a (Tree a) (Tree a)	--Nodo con sub-árbol izquierdo y sub-árbol derecho
 deriving Show

--Inserta un elemento en un sub-árbol
insert :: Ord a => a -> Tree a -> Tree a
insert a Empty = Node a Empty Empty
insert a (Node n t1 t2) 
 | n == a = Node n t1 t2
 | n < a = Node n t1 (insert a t2)
 | n > a = Node n (insert a t1) t2

--Toma lista de elementos ordenables y construye el árbol binario ordenado.
fromList :: Ord a => [a] -> Tree a
fromList a = aux (reverse a)

aux :: Ord a => [a] -> Tree a
aux [] = Empty
aux (a:as) = insert a (aux as)

--Devuelve una lista con los elemento del árbol ordenados según el recorrido in-order.
inOrder :: Tree a -> [a]
inOrder Empty = []
inOrder (Node a t1 t2) = inOrder t1 ++ [a] ++ inOrder t2

--Devuelve una lista de elementos ordenados
sort :: Ord a => [a] -> [a]
sort a = inOrder (fromList a)