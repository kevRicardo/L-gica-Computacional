%Practica 3
%Rodrigo Amezcua Caballero
%314353304

%relación que encuentra la reversa de una lista
reverse([],[]).
reverse([X|XS],Y) :- reverse(XS,R), append(R,[X],Y).

%relacion que decide su una lista es palindromo
palindrome(X) :- reverse(X,Y), X==Y.


%Transición del autómata
transitions(a,z,a).
transitions(a,o,b).
transitions(a,v,c).
transitions(b,z,a).
transitions(b,o,b).
transitions(b,v,c).
transitions(c,z,a).
transitions(c,v,a).
transitions(c,o,c).

%Proceso del autómata
process([],S,S).
process([X|XS],S,Y) :- process(XS,R,Y), transitions(S,X,R).

%Ejercicio 3 
%protagonista(p1)
%Viuda esposa de p1 (p2)
%Padre p1 (papa)
%hijo de p1 y p2 (hijo1) 
%hijo natural  de p1 y p2 (hijo2)
%hijo natural de papa y hijo1 (hijo3).

%parejas
parejas(p1,p2).%principal
parejas(papa,hijo1).%Pareja del padre 

%padres

%relaciones de p1.
padre(p1,hijo1).
padre(p1,papa).
padre(p1,hijo2).

%relaciones de papa.
padre(papa,p1).
padre(papa,p2).

%relaciones p2 
padre(p2,hijo2).
padre(p2,papa).
padre(p2,hijo1).

%relaciones de hijo1 
padre(hijo1,hijo3).
padre(hijo1,p1).


%Relaciones 
espareja(X,Y):- parejas(Y,X).
esHijo(X,Y):-padre(Y,X).
abuelo(X,Y):-padre(Z,Y),padre(X,Z).
visabuelo(X,Y):-abuelo(Z,Y),padre(X,Z).
