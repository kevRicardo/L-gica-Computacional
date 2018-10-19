%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    % Lógica Computacional 2019-1
    % Profesor: César Hernández Cruz
    % Ayudante: Víctor Zamora Gutiérrez
    % Ayudante Lab: Diego Carrillo Verduzco
    % Práctica 3
    % Alumno: Villegas Salvador Kevin Ricardo
    % No. de Cuenta: 314173739
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

    % Relación que define la reversa de una lista.
    reverse([],[]).
    reverse([X|XS],L):- reverse(XS,R), append(R,[X],L).

    % Relación que defina si una lista es palíndromo.
    palindrome(X):- reverse(X,Y), X==Y.

    % Hechos para la transición de un autómata.
    transition(a,z,a). transition(b,z,a). transition(c,z,a).
    transition(a,u,c). transition(b,u,c). transition(c,u,a).
    transition(a,o,b). transition(b,o,b). transition(c,o,c).

    % El proceso que sigue un autómata dado una lista de átomos.
    process([],S,S).
    process([X|XS],S,Y):- process(XS,R,Y), transition(S,X,R).

    % Hechos para la narración.
    protegonista(jose).
    esposa(ludy). % Esposa del protagonista.
    esposa(gaby). % Esposa del padre del protagonista.
    padre(max). % Padre del protagonista.
    hijo(mika). % Hija de gaby con Max.
    hijo(brandon). % Hijo de José con Ludy.
    
    casado(jose,ludy).
    casado(max,gaby).

    hijo(jose,max).
    hijo(jose,gaby).
    hijo(gaby,ludy)
    hijo(mika,gaby).
    hijo(mika,max).
    hijo(brandon,ludy).
    hijo(brandon,jose).
    hijo(gaby,jose).
    hijo(jose,gaby).
    hijo(max,jose).
    hijo(gaby,jose).

    padre(X,Y):- hijo(Y,X).
    abuelo(X,Y):- padre(Z,Y),padre(X,Z).
    visabuelo(X,Y):- abuelo(Z,Y),padre(X,Z).
