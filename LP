:-[codigo_comum].

% Prototipos dos predicados:

% combinacoes_soma/4
% permutacoes_soma/4
% espaco_fila/2
% espacos_fila/2
% espacos_puzzle/2
% espacos_com_posicoes_comuns/3
% permutacoes_soma_espacos/2
% permutacao_possivel_espaco/4
% permutacoes_possiveis_espaco/4
% permutacoes_possiveis_espacos/2
% numeros_comuns/2
% atribui_comuns/1
% retira_impossiveis/2
% simplifica/2
% inicializa/2
% escolhe menos_alternativas/2
% experimenta_perm/3
% resolve_aux/2
% resolve/1

% construtor - Espaco

cria_espacos(Soma,Variaveis,espaco(Soma,Variaveis)).

% seletores - Espaco

soma_de_espaco(espaco(Soma,_),Soma).
variaveis_de_espaco(espaco(_,Variaveis),Variaveis).
soma_nao_igual(espaco(Soma1,_),espaco(Soma2,_)):-
    diferente(Soma1,Soma2).

espacos_igual(espaco(_,Vars1),espaco(_,Vars2)):-
    diferente(Vars1,Vars2).


% Predicados Globais

igual(X,Y):- X == Y.
diferente(X,Y):- X \== Y.
maior(X,Y):- X > Y.
menor(X,Y):- X =< Y.

% Definicao dos Predicados

% 3.1.1
% combinacoes_soma(N,Els,Soma,Combs) afirma que Combs eh uma lista (ordenada)
% cujos elementos sao as combinacoes N-N, dos elementos de Els cuja soma = Soma

combinacoes_soma(N,Lin,Soma,Combs):-
    bagof(Lout, (combinacao(N, Lin, Lout), soma_lista(Lout, Soma)), Combs).

% soma_lista(Lista,Soma) afirma que Soma eh igual ao valor da soma de todos os
% elementos de Lista

soma_lista([],0).
soma_lista([P|R],Total):-
    soma_lista(R,Resto),
    Total is P + Resto.

% 3.1.2
% permutacoes_soma(N,Els,Soma,Perms) afirma que Perms eh uma lista (ordenada) 
% cujos elementos sao permutacoes das combinacoes N-N dos elementos de Els
% cuja soma eh Soma

permutacoes_soma(N,Lin,Soma,Res):-
    combinacoes_soma(N,Lin,Soma,Comb_somas),
    findall(Perms,(membros_lista_listas(X,Comb_somas),permutation(X,Perms)),Res_out),
    sort(Res_out,Res).

% Predicado membros_lista_listas/2 -> Aux
% Permite aceder ao cada membro de uma lista de listas

membros_lista_listas(X, [X|_]).
membros_lista_listas(X,[_|R]):-  
    membros_lista_listas(X,R).

% 3.1.3
% espaco_fila(Fila,Esp,H_V) afirma que Esp eh um espaco de Fila, tal como
% descrito na seccao 2.1, passo 1

espaco_fila(Lst,Res,H_V):-
    filtra_atomo(H_V),
    igual(H_V,v)
    -> 
    % A variavel eh v logo queremos aceder ao elemento que esta no indice 0 
    % de cada uma lista (valida) de uma Fila
    Filtrador is 0, 
    bagof(Res_out,espaco_fila_aux_listas(Lst,Filtrador,[],Res_out),Res_somas_vt),
    nth0(0,Res_somas_vt,Res_somas_v), %retirar [] extra
    bagof(Res_out,espaco_fila_aux_vars(Lst,Res_out),Res_vars_v),
    % associar o valores da soma as suas permutacoes correspondentes
    % criando assim os espacos,com o predicado gerador dos mesmos
    maplist(cria_espacos,Res_somas_v,Res_vars_v,Res_out),
    member(Res,Res_out); 

    % Procedimento identico ao anterior mas valor da variavel Filtrador - h
    igual(H_V,h), 
    Filtrador is 1, 
    % A variavel eh  h logo queremos aceder ao elemento que esta no indice 1 
    % de cada uma lista (valida) de uma Fila
    bagof(Res_out2,espaco_fila_aux_listas(Lst,Filtrador,[],Res_out2),Res_somas_ht),
    nth0(0,Res_somas_ht,Res_somas_h),
    bagof(Res_out2,espaco_fila_aux_vars(Lst,Res_out2),Res_vars_h),
    maplist(cria_espacos,Res_somas_h,Res_vars_h,Res_out),
    member(Res,Res_out);
    fail.

% espaco_fila_aux_lista/4 -> Predicado Auxiliar
% Afirma que Res e uma lista com todas com os valores Soma
% de uma lista segundo uma orientacao definida por Filtrador


espaco_fila_aux_listas([_],_,Res,Res).
espaco_fila_aux_listas([H,Y|TAIL],Filtrador,Acumulador,Res):-
    % funcao percorre a Fila 2-2 para casos em que temos 2 listas
    % que aparecem de seguida pelo que o valor Soma seria irrelevante
    is_list(H), 
    var(Y)
    ->
    nth0(Filtrador,H,X),
    append(Acumulador,[X],New_res),
    espaco_fila_aux_listas([Y|TAIL],Filtrador,New_res,Res);
    espaco_fila_aux_listas([Y|TAIL],Filtrador,Acumulador,Res).


% espaco_fila_aux_vars/2 -> Predicado Auxiliar
% Afirma que Esp corresponde a todas as vars que estao compreendidas
% entre 2 listas

espaco_fila_aux_vars(Fila,Esp):-
    append([P,Esp,S],Fila), 
    include(var,Esp,Esp),
    (P == [];(last(P,Ultimo),is_list(Ultimo))),
    (S == [];([H|_] = S,is_list(H))),
    diferente(Esp,[]).


% filtra_ atomo/2 -> Predicado Auxiliar
% Afirma que Letra_input eh ou v ou h, usado para escolher orientacao da Fila
% no predicado espaco_fila

filtra_atomo(Letra_input):-
    atom(Letra_input),
    igual(Letra_input,v),!;
    igual(Letra_input,h).

% 3.1.4
% espacos_fila(H_V,Fila,Espacos) afirma que Espacos eh a lista de todos os 
% espacos de Fila , da esquerda para a direita.

espacos_fila(H_V,Fila,Espacos):-
    bagof(Espacos_out,espaco_fila(Fila,Espacos_out,H_V),Espacos).

% 3.1.5
% Predicado espacos_puzzle(Puzzle,Espacos) afirma que Espacos eh a lista de
% espacos de Puzzle tal como descrito na seccao 2.1 (passo 1).
 
espacos_puzzle(Puzzle, Espacos):-
    bagof(Res_aux_l,espacos_puzzle_aux_linhas(Puzzle,Res_aux_l),Res_linhas),
    mat_transposta(Puzzle,Transp_puzzle),
    bagof(Res_aux_c,espacos_puzzle_aux_colunas(Transp_puzzle,Res_aux_c),Res_colunas),
    append(Res_linhas,Res_colunas,Espacos).

% espacos_puzzle_aux_linhas/2 -> Predicado Auxiliar
% Afirma que res eh o espacos fila segundo a orientacao h, correspondente 
% as linhas do puzzle

espacos_puzzle_aux_linhas(Puzzle,Res):-
    member(Elem,Puzzle),
    bagof(Aux,espacos_fila(h,Elem,Aux),Esp_out_linhas),
    nth0(0,Esp_out_linhas,Res1),
    member(Res,Res1).

% espacos_puzzle_aux_colunas/2 -> Predicado Auxiliar
% Afirma que res eh o espacos fila segundo a orientacao v, correspondente 
% as colunas do puzzle

espacos_puzzle_aux_colunas(Puzzle_transp,Res):-
    member(Elem,Puzzle_transp),
    bagof(Aux,espacos_fila(v,Elem,Aux),Esp_out_colunas),
    nth0(0,Esp_out_colunas,Res2),
    member(Res,Res2).
 
% 3.1.6
% Predicado espacos_com_posicoes_comuns(Espacos,Esp,Esps_com) afirma que
% Esps_com eh a lista com variaveis em comum com Esp, sem ser o proprio Esp

espacos_com_posicoes_comuns(Espacos,Esp,Esps_com):-
    bagof(Res,espacos_com_posicoes_comuns_aux(Espacos,Esp,Res),Esps_com).


espacos_com_posicoes_comuns_aux(Espacos,Esp,Esps_com):-
    member(Espaco_atual,Espacos),
    espacos_igual(Espaco_atual,Esp), % verifica se nao estamos a considerar
                                     % o proprio espaco
    variaveis_de_espaco(Espaco_atual,Vars_atual),
    variaveis_de_espaco(Esp,Vars_esp),
    interseta_vars(Vars_atual,Vars_esp),
    Esps_com = Espaco_atual.

% interseta_vars/2 -> Predicado Auxiliar
% Afirma que as vars dos espacos sao iguais

interseta_vars(Vars_atual,Vars_esp):-
    member(X,Vars_atual),
    member(Y,Vars_esp),
    igual(X,Y).

% 3.1.7
% Predicado permutacoes_soma (Espacos,Perms_somas) afirma que Perms_somas eh a 
% lista de 2 elementos em q o 1 um espaco de Espacos e o 2 uma lista ordenada
% de permutacoes cuja soma eh igual ah soma do espaco

permutacoes_soma_espacos(Espacos,Perms_somas):-
    bagof(Res,permutacoes_soma_aux(Espacos,[1,2,3,4,5,6,7,8,9],Res),Perms_somas).

permutacoes_soma_aux(Espacos,Lin,Perms_somas):-
    member(Espaco_atual,Espacos),
    variaveis_de_espaco(Espaco_atual,Vars_atual),
    soma_de_espaco(Espaco_atual,Soma),
    length(Vars_atual,N),
    permutacoes_soma(N,Lin,Soma,Perms_somas_out),
    [Espaco_atual|[Perms_somas_out]] = Perms_somas.

filtra_espacos_comuns(Perms,Filtrado):-
    member(X,Perms),
    flatten(X,Filtrado).

% 3.1.8
% Predicado permutacao_possivel_espaco(Perm,Esp,Espacos,Perms_soma) afirma que
% Perms_soma eh uma lista de listas tal como a obtida no predicado 3.1.7 
% (Perm eh uma permutacao possivel para o espaco Esp, tal como descrito na Seccao 2.1
%  passo 2)

permutacao_possivel_espaco(Perm,Esp,Espacos,Perm_somas):-
    permutacao_possivel_espaco_aux(Perms1,Esp,Espacos,Perm_somas),
    member(Perm,Perms1).


% permutacao_possivel_espaco_aux/3 -> Predicado Auxiliar
% A ideia eh que um espaco com n elementos nas permutacoes vai ter sempre 
% n espacos comuns, logo vamos ver cada elemento de cada permutacao do espaco 
% que estamos a considerar se cada elemento corresponder a pelo menos um dos elementos
% das permutacoes dos espacos comuns (Correspondente) ao Esp entao eh uma 
% permutacao possivel para esse espaco

permutacao_possivel_espaco_aux(Perms,Esp,Espacos,Perm_somas):-
    %buscar as perms do espaco que estamos a considerar
    bagof(Aux1,procura_perms_espacos([Esp],Perm_somas,Aux1),Aux2),
    nth0(0,Aux2,Perms_espaco_input),   
    bagof(Aux3,filtra_perms_somas(Espacos,Esp,Perm_somas,Aux3),Perms_espacos_comuns),
    bagof(Aux4,filtra_espacos_comuns(Perms_espacos_comuns,Aux4),Filtrado),
    length(Filtrado,L), % Ver a lenght das perms para na chamada recursiva 
                        % podermos passar por todos os elementos de uma perm
    verifica_intersecao(Perms_espaco_input,Filtrado,L,[],[],Perms),!.

    resultado_final(Res,Perms):-
        Perms = Res.

    verifica_intersecao([],_,_,_,Res,Perms):-
        Perms = Res,
        resultado_final(Res,Perms).

    % caso terminal da recursao como estamos a fazer de forma descrescente
    % o acumulador da Perms encontra-se invertido
    verifica_intersecao([H|Tail],Filtrado,0,Acumulador,Perms,Res):-
    reverse(Acumulador, Acumulador1),
    igual(Acumulador1,H)
    ->
    append(Perms,[Acumulador1],New_Perms),
    length(Acumulador1,L2),
    verifica_intersecao(Tail,Filtrado,L2,[],New_Perms,Res);


    length(H,L),
    verifica_intersecao(Tail,Filtrado,L,[],Perms,Res).
    verifica_intersecao([H|TAIL],Filtrado,L,Acumulador,Perms,Res):-
    nth1(L,H,Elem_H),
    nth1(L,Filtrado,Elem_C),
    memberchk(Elem_H,Elem_C)
    ->
    append(Acumulador,[Elem_H],Novo_acumulador),
    L1 is L-1,
    verifica_intersecao([H|TAIL],Filtrado,L1,Novo_acumulador,Perms,Res);

    length(H,L2),
    verifica_intersecao(TAIL,Filtrado,L2,[],Perms,Res).

% filtra_perms_somas/4 
% Recebe um espaco ve as suas posiceos comuns e procura as Perms desses
% espacos comuns a Esp
 
filtra_perms_somas(Espacos,Esp,Perm_somas,Perm_somas_filtrado):-
    espacos_com_posicoes_comuns(Espacos,Esp,Espacos_comuns),
    member(X,Espacos_comuns),
    procura_perms_espacos([X],Perm_somas,Perm_somas_filtrado).

% procura_perms_espacos/3 -> Predicado Auxiliar
% Procura em Perms_somas as Perms dos espacos dados como input

procura_perms_espacos(Lista_find_perms_somas,Perm_somas,Res):-
    member(E_find,Lista_find_perms_somas),
    member(E_perms,Perm_somas),
    nth0(0,E_perms,X),
    igual(E_find,X),
    nth0(1,E_perms,Res).

% 3.1.9
% Permutacoes possiveis espaco
% Afirma que Perms_poss e uma lista de 2 elemetos em que o primeiro eh a lista
% de variaveis e o segundo a lista ordenada de permutacoes possiveis para o Espaco
% tal como descrito na seccao 2.1, passo 2

permutacoes_possiveis_espaco(Espacos,Perms_somas,Esp,Perms_poss):-
    bagof(Res_out,permutacao_possivel_espaco(Res_out,Esp,Espacos,Perms_somas),Poss),
    variaveis_de_espaco(Esp,Vars),
    sort(Poss,Sorted),
    append([Vars],[Sorted],Perms_poss).


% 3.1.10 
% Predicado Permutacoes_possiveis_espacos
% Afirma que Perms_poss_esps eh a lista de permutacoes possiveis
% tal como descrito na seccao 2.1, passo 2

permutacoes_possiveis_espacos(Espacos,Perms_poss_esps):-
    bagof(Aux,permutacoes_possiveis_espacos_aux(Espacos,Aux),Perms_poss_esps).


permutacoes_possiveis_espacos_aux(Espacos,Res):-
    permutacoes_soma_espacos(Espacos,Perms_somas),
    member(X,Espacos),
    permutacoes_possiveis_espaco(Espacos,Perms_somas,X,Res).

% 3.1.11
% Predicado numeros_comuns(Lst_Perms,Numeros_comuns) afirma que Numeros comuns
% eh uma lista de pares (pos,numero) signficando que todas as Lst_Perms contem
% o numero numero na posicao pos.


numeros_comuns(Lst_Perms,Numeros_comuns):-
    [H|_] = Lst_Perms,
    bagof((Y,X),(member(X,H),nth1(Y,H,X)),Pares), 
    sort(Pares,Pares1), 
    testa_pares(Pares1,Lst_Perms,Numeros_comuns).

testa_pares(Pares1,Lst_Perms,Res) :-
    (bagof(X,(member(X,Pares1),aux2_nc(X,Lst_Perms)),Res)->!);
    Res=[].

aux2_nc(Par,Numeros) :-
    maplist(aux3_nc(Par),Numeros).

aux3_nc(Par,Perm) :-
    (Indx,N) = Par,
    nth1(Indx,Perm,N).

% 3.1.12
% Predicado atribui_comuns
% Afirma que Perms_Possiveis eh a lista actualizada com os numeros
% comuns a tods as permutacoes possiveis para esse espaco tal como
% descrito na seccao 2.1 passo 3a

atribui_comuns(Perms_Possiveis):-
    maplist(atribui_comuns_aux,Perms_Possiveis).

atribui_comuns_aux(Esp_Perms):-
    [Esp|[Perms]] = Esp_Perms,
    numeros_comuns(Perms,Comuns),
    maplist(insere_posicao(Esp),Comuns).

insere_posicao(Esp,Par):-
    (I,Numero) = Par,
    nth1(I,Esp,Numero).

% 3.1.13
% retira_impossiveis(Perms_Possiveis,Novas_Perms_Possiveis), afirma que
% Novas_Perms_Possivies eh o resultado de tirar permutacoes impossiveis de 
% Perms_Possiveis tal como descrito na Seccao 2,1 passo 3(b)

retira_impossiveis(Perms_Possiveis,Novas_Perms_Possiveis):-
    bagof(Aux,retira_impossiveis_aux(Perms_Possiveis,Aux),Novas_Perms_Possiveis).

retira_impossiveis_aux(Perms_Possiveis,Novo_termo):-
    member(Elem,Perms_Possiveis),
    [Esp|[Perms]] = Elem,
    findall(X,(member(X,Perms),subsumes_term(Esp,X)),Res),
    append([Esp],[Res],Novo_termo).


% 3.1.14
% simplifica(Perms_Possiveis,Novas_Perms_Possiveis) afirma que 
% Novas_Perms_Possiveiseh o resultado de simplificar Perms_Possiveis tal como
% descrito na seccao 2.1 passo 3

simplifica(Perms_Possiveis,Novas_Perms_Possiveis):-
    atribui_comuns(Perms_Possiveis),
    retira_impossiveis(Perms_Possiveis,Perms_possiveis_apos_retira),
    todas_alteracoes(Perms_Possiveis,Perms_possiveis_apos_retira,Novas_Perms_Possiveis).


% todas_alteracoes/3 -> Predicado Auxiliar
% Predicado auxiliar que funciona como um loop, que acaba quando ao aplicar
% predicados de resolucao as Perms_Possiveis mantem se iguais,
% o que significa que foi simplificado o maximo possivel

todas_alteracoes(Perms_Possiveis,Perms_possiveis_apos_retira,Nova_alteracao):-
    % Condicao de fim de loop :
    igual(Perms_possiveis_apos_retira,Perms_Possiveis)
    ->
    append(Perms_possiveis_apos_retira,[],Nova_alteracao);

    atribui_comuns(Perms_possiveis_apos_retira),
    retira_impossiveis(Perms_possiveis_apos_retira,Perms_loop),
    todas_alteracoes(Perms_possiveis_apos_retira,Perms_loop,Nova_alteracao).

% 3.1.15
% inicializa(Puzzle,Perms_Possiveis) afirma que Perms_Possiveis eh a lista
% de permutacoes possiveis simplificada para Puzzle

inicializa(Puzzle,Perms_Possiveis):-
    espacos_puzzle(Puzzle,Espacos),
    permutacoes_possiveis_espacos(Espacos,Perms_poss_esps),
    simplifica(Perms_poss_esps,Perms_Possiveis).

% 3.2.1
% escolhe_menos_alternativas(Perms_Possiveis,Escolha) afirma que Escolha eh 
% o elemento de Perms Possiveis escolhida segundo o criterio indicado na
% seccao 2.2 passo 1.

escolhe_menos_alternativas(Perms_Possiveis,Escolha) :-
    bagof(X,filtro1(Perms_Possiveis,X),Filtra1),
    bagof(Membro2,filtro2(Filtra1,Membro2),Possibilidades),
    nth1(1,Possibilidades,Escolha).


% Dentro das que tem mais de uma Perm ver quais tem o menor numero
escolhe_menos_alternativas_aux3(Tam,Membro):-
    [_|[Lst_Perms_Candidatos]] = Membro,
    length(Lst_Perms_Candidatos,Tam_LstPerms_Candidatos),
    menor(Tam,Tam_LstPerms_Candidatos).


filtro2(Perms_Possiveis,X):-
    member(X,Perms_Possiveis),
    [_|[Escolhas_Possiveis]] = X,
    length(Escolhas_Possiveis,L),
    maplist(escolhe_menos_alternativas_aux3(L),Perms_Possiveis).

% Ve se so tem 1 Perm
filtro1(Perms_Possiveis,X):-
    member(X,Perms_Possiveis),
    [_|[Lista_perms]] = X,
    length(Lista_perms,L),
    maior(L,1).

    
% 3.2.2
% experimenta_perm(Escolha,Perms_Possiveis,Novas_Perms_Possiveis),
% afirma que Novas_Perms_Possiveis e uma lista de permutacoes possiveis
% e Escolha e um dos seu elementos escolhido apartir dos passos:

% 1) Utilizar member para escolher Perm de Lst_Perms
% 2) Unificar Esp com Perm
% 3) Novas_Perms_Possiveis eh o resultado de substituir em Perms_Possiveis
%    o elemento Escolha pelo elemento [Esp,[Perm]].

experimenta_perm(Escolha,Perms_Possiveis,Novas_Perms_Possiveis):-
    [Esp|[Perms_lst]] = Escolha,
    member(Perm,Perms_lst),
    Esp = Perm,
    select(Escolha, Perms_Possiveis,[Esp,[Perm]],Novas_Perms_Possiveis).

% 3.2.3
% Predicado resolve_aux(Perms_Possiveis,Novas_Perms_Possiveis) afirma que
% Novas_Perms_Possiveis eh o resultado de aplicar o algoritmo descrito na 
% seccao 2.2 a Perms_Possiveis

% 1) Escolhe menos alternativas
% 2) Exeperimentar atribuir Permutacao
% 3) Simplificar lista de Permutacoes

resolve_aux(Perms_Possiveis,Novas_Perms_Possiveis):-
    simplifica(Perms_Possiveis,Novas_Perms_Possiveis_N),
    maplist(so_uma_perm,Novas_Perms_Possiveis_N) % Verificar se todas tem so 1 Perm
    ->
    append(Novas_Perms_Possiveis_N,[],Novas_Perms_Possiveis);

    escolhe_menos_alternativas(Perms_Possiveis,Escolha),
    experimenta_perm(Escolha,Perms_Possiveis,Temp_Perms_Possiveis),
    simplifica(Temp_Perms_Possiveis,Temp1_Perms_Possiveis),
    todas_listas_so_uma_perm(Temp1_Perms_Possiveis,Novas_Perms_Possiveis),!.

todas_listas_so_uma_perm(Temp_Perms_Possiveis,Novas_Perms_Possiveis):-
    maplist(so_uma_perm,Temp_Perms_Possiveis)
    ->
    append(Temp_Perms_Possiveis,[],Novas_Perms_Possiveis);

    escolhe_menos_alternativas(Temp_Perms_Possiveis,Escolha),
    experimenta_perm(Escolha,Temp_Perms_Possiveis,Temp2_Perms_Possiveis),
    simplifica(Temp2_Perms_Possiveis,Temp4_Perms_Possiveis),
    todas_listas_so_uma_perm(Temp4_Perms_Possiveis,Novas_Perms_Possiveis).

% Condicao de paragem
so_uma_perm(Esp):-
    [_,Lst_Perms] = Esp,
    length(Lst_Perms,L),
    igual(L,1).


% 3.3.1
% resolve(Puz), afirma que Puz e um puzzle em que todas as variaveis
% sao substituidas por numeros que respeitam as restricoes Puz

resolve(Puz) :-
    inicializa(Puz,Perms_Possiveis),
    resolve_aux(Perms_Possiveis,_).
