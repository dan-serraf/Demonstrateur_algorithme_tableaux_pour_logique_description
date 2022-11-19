/*=====================================================================================================*/
/*=====================================================================================================*/
/*=====================================================================================================*/
/*================ PROJET REALISE PAR ABITBOL YOSSEF, 3804139, ET SERRAF DAN, 3971120 =================*/
/*=====================================================================================================*/
/*=====================================================================================================*/
/*=====================================================================================================*/

/*-------------------------------------------------------------------------------------------------------*/
/* -------------------------------------- PARTIE 1 : PRELIMINAIRES -------------------------------------*/
/*-------------------------------------------------------------------------------------------------------*/

/* On va utiliser le fichier suivant représentant la Tbox et la Abox inspirées de l’exercice 3 du TD4.*/

% equiv ==>   C ≡ D
equiv(sculpteur,and(personne,some(aCree,sculpture))).
equiv(auteur,and(personne,some(aEcrit,livre))).
equiv(editeur,and(personne,and(not(some(aEcrit,livre)),some(aEdite,livre)))).
equiv(parent,and(personne,some(aEnfant,anything))).
% equiv(sculpture,and(objet,all(cree_par,sculpteur))). % utile pour le test de autoref

% Cnamea ==>   a : !!!- C -!!!
cnamea(personne).
cnamea(sculpture).
cnamea(livre).
cnamea(objet).
cnamea(anything).
cnamea(nothing).

% cnamena ==>   !!!- C -!!! ≡ D
cnamena(auteur).
cnamena(editeur).
cnamena(sculpteur).
cnamena(parent).
% cnamena(sculpture).

% iname ==> !!!- a -!!! : C
iname(michelAnge).
iname(david).
iname(sonnets).
iname(vinci).
iname(joconde).

% rname ==>   <a,b> : !!!- R -!!!
rname(aCree).
rname(aEcrit).
rname(aEdite).
rname(aEnfant).

% inst ==>    a : C
inst(michelAnge,personne).
inst(david,sculpture).
inst(sonnets,livre).
inst(vinci,personne).
inst(joconde,objet).

% instR ==>  < a, b > : R 
instR(michelAnge, david, aCree).
instR(michelAnge, sonnets, aEcrit).
instR(vinci, joconde, aCree).

/* /\/\/\ AUTOREF /\/\/\*/
/*Test si le predicat C apparait directement ou indirectement dans la definition de D*/
autoref(C,C). % cas de base D == C
autoref(C1,equiv(C2,X)) :- autoref(C1,X),!.
autoref(C,and(C1,C2)) :- autoref(C,C1),!.
autoref(C,and(C1,C2)) :- autoref(C,C2),!.
autoref(C,or(C1,C2)) :- autoref(C,C1),!.
autoref(C,or(C1,C2)) :- autoref(C,C2),!.
autoref(C,some(R,C1)) :- autoref(C,C1),!.
autoref(C,all(R,C1)) :- autoref(C,C1),!.
autoref(C,not(C1)) :- autoref(C,C1),!.
% on test si D est un concept non atomique, si oui, on fait un autoref sur sa valeur. 
autoref(C1,C2) :- setof(X,cnamena(X),L) , member(C2,L) ,equiv(C2,Y),autoref(C1,Y). 

/*-------------------------------------------------------------------------------------------------------*/
/* --------------------------- PARTIE 2 : SAISIE DE LA PROPOSITION A DEMONTRER --------------------------*/
/*-------------------------------------------------------------------------------------------------------*/
/*
Cette partie se résoud en plusieurs étapes,
On choisis 1 ou 2 selon notre cas, 
  (1)   I : C
      - On rentre une instance, 
      - On vérifie SEMANTIQUEMENT si cette  instance en est bien une,
      - On rentre un concept, 
      - On vérifie SEMANTIQUEMENT que ce concept existe et qu'il est correct,
      - On REMPLACE les identificateurs de concept complexes par leur définition,
      - On les mets sous FORME NORMAL NEGATIVE ( NNF ),     
      - On l'ajoute a notre liste. 

  (2)  C1 ∩ C2 ⊆ ⊥
      - On rentre un concept C1,  
      - On vérifie SEMANTIQUEMENT que ce concept existe et qu'il est correct,
      - On rentre un concept C2,
      - On vérifie SEMANTIQUEMENT que ce concept existe et qu'il est correct,
      - On REMPLACE l'intersection de C1 et C2 par leur définition,
      - La négation de cette proposition est ∃ inst, inst : C1 ⊓ C2,
      - On met sous NNF,
      - On l'ajoute a notre liste.
*/

/* -------------------- On fait la verification SEMANTIQUE --------------------*/
concept(nothing).
concept(anything).
% on decompose les concepts
concept(not(C)) :- concept(C),!.
concept(and(C1,C2)):- concept(C1), concept(C2),!.
concept(or(C1,C2)) :- concept(C1), concept(C2),!.
concept(some(R,C)) :- role(R), concept(C),!.
concept(all(R,C)) :- role(R), concept(C),!.
% on vérifie bien qu'ils existent
% concept(C1) :- setof(X,iname(X),L), member(C1,L),!.
concept(C2) :- setof(X,cnamea(X),L), member(C2,L),!.
concept(C3) :- setof(X,cnamena(X),L), member(C3,L),!.
% On vérifie pour les instances
instance(I) :- setof(I, iname(I),L), member(I,L) ,!.
% on vérifie pour les roles
role(R) :- setof(X,rname(X),L), member(R,L),!.

/* -------------------- On fait le REMPLACEMENT -------------------- */
% On remplace C1 et C2 dans RC1 et RC2
remplace(and(C1,C2),and(RC1,RC2)) :- remplace(C1,RC1), remplace(C2,RC2),!.
remplace(or(C1,C2),or(RC1,RC2)) :- remplace(C1,RC1), remplace(C2,RC2),!.
remplace(all(R,C),all(R,RC)) :- remplace(C,RC),!.
remplace(some(R,C),some(R,RC)) :- remplace(C,RC),!.
remplace(not(C),not(RC)) :- remplace(C,RC),!.

remplace(C,RC) :- setof(X,cnamena(X),L) , member(C,L) , equiv(C,C2),remplace(C2,RC),!. % concept non atomique
remplace(C,C) :- setof(X,cnamea(X),L) , member(C,L),!. % concept atomique

/* -------------------- FORME NORMALE NEGATIVE -------------------- */

nnf(not(and(C1,C2)),or(NC1,NC2)):- nnf(not(C1),NC1),
nnf(not(C2),NC2),!.
nnf(not(or(C1,C2)),and(NC1,NC2)):- nnf(not(C1),NC1), 
nnf(not(C2),NC2),!.
nnf(not(all(R,C)),some(R,NC)) :- nnf(not(C),NC),!.
nnf(not(some(R,C)),all(R,NC)):- nnf(not(C),NC),!.
nnf(not(not(X)),X):-!.
nnf(not(X),not(X)):-!.
nnf(and(C1,C2),and(NC1,NC2)):- nnf(C1,NC1),nnf(C2,NC2),!.
nnf(or(C1,C2),or(NC1,NC2)):- nnf(C1,NC1), nnf(C2,NC2),!.
nnf(some(R,C),some(R,NC)):- nnf(C,NC),!.
nnf(all(R,C),all(R,NC)) :- nnf(C,NC),!.
nnf(X,X).

/*=====================================================================================================*/
/*=====================================================================================================*/

/* Une instance donnee appartient a un concept donne I : C */
acquisition_prop_type1(Abi , Abi1 ,Tbox) :- nl,
    % INSTANCE
    write("entrer linstance "),nl, read(I), % on stock l'instance
    instance(I),nl, % on vérifie que c'est  sémantiquement  correct

    % CONCEPT
    write("entrer le concept"),nl, read(C), 
    % on vérifie que c'est  sémantiquement  correct
    concept(C),

    % On REMPLACE les identificateurs de concept complexes par leur définition,
    remplace(C,RC),
    % On les mets sous FORME NORMAL NEGATIVE ( NNF ),
    nnf(not(RC),NRC),
    % On l'ajoute a la liste 
    concat(Abi,[(I,NRC)],Abi1),
    nl, write("Abi1 etendu : "),nl, write(Abi1). 
   
/*Deux concepts ne possede aucun elements en commun(ils ont une intersection vide C1 ∩ C2 ⊆ ⊥ */
acquisition_prop_type2(Abi,Abi1,Tbox) :- nl,
    % Concept C1
    write("Entrer le concept 1 : "),nl,read(C1),
    % on vérifie que c'est  sémantiquement  correct
    concept(C1),

    % Concept C2
    nl,write("Entrer le concept 2 : "),nl,read(C2),
    % on vérifie que c'est  sémantiquement  correct
    concept(C2),

    % On REMPLACE les identificateurs de concept complexes par leur définition,
    remplace(and(C1,C2),RC),
    % On les mets sous FORME NORMAL NEGATIVE ( NNF ),
    nnf(not(RC),NRC),
    % On l'ajoute a la liste 
    genere(Nom),
    concat(Abi,[(Nom,NRC)],Abi1),
    nl, write("Abi1 etendue : "),nl, write(Abi1).


/*-------------------------------------------------------------------------------------------------------*/
/* ------------------------------ PARTIE 3 : DEMONSTRATION DE LA PROPOSITION ----------------------------*/
/*-------------------------------------------------------------------------------------------------------*/

% on commence par implementer le predicat 
%  /\/\/\  tri_Abox  /\/\/\ :
tri_Abox([],[],[],[],[],[]).

tri_Abox([(I,C)|Abi],Lie,Lpt,Li,Lu,[(I,C)|Ls]) :- setof(X,cnamea(X),L), member(C,L) , tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),!.
tri_Abox([(I,not(C))|Abi],Lie,Lpt,Li,Lu,[(I,not(C))|Ls]) :- setof(X,cnamea(X),L), member(C,L) , tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),!.

tri_Abox([(I,some(R,C))|Abi],[(I,some(R,C))|Lie],Lpt,Li,Lu,Ls)  :- tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),!.
tri_Abox([(I,all(R,C))|Abi],Lie,[(I,all(R,C))|Lpt],Li,Lu,Ls) :- tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),!.
tri_Abox([(I,and(C1,C2))|Abi],Lie,Lpt,[(I,and(C1,C2))|Li],Lu,Ls)  :- tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),!.
tri_Abox([(I,or(C1,C2))|Abi],Lie,Lpt,Li,[(I,or(C1,C2))|Lu],Ls) :- tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),!.

% Lors de la resolution, on va devoir faire evoluer la liste a chaque fois grace au predicat 
% /\/\/\  evolue  /\/\/\ : 
evolue((B,C), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu,[(B,C)| Ls]) :-   setof(C, cnamea(C),L), member(C,L),!.
evolue((B,C), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu,[(B,C)| Ls]) :-   setof(C, cnamena(C),L), member(C,L) ,!.
evolue((B,not(C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu,[(B,not(C))| Ls]) :-  setof(C, cnamena(C),L), member(C,L),!.
evolue((B,not(C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu,[(B,not(C))| Ls]) :-  setof(C, cnamea(C),L), member(C,L) ,!. 
evolue((I,and(C1,C2)), Lie, Lpt,Li, Lu, Ls, Lie, Lpt,  [(I,and(C1,C2))|Li], Lu, Ls):-!.
evolue((I,or(C1,C2)), Lie, Lpt, Li,Lu, Ls, Lie, Lpt, Li, [(I , or(C1,C2))| Lu], Ls):-!.
evolue((I,some(R,C)), Lie, Lpt, Li, Lu, Ls, [(I,some(R,C))|Lie], Lpt, Li, Lu, Ls):-!.
evolue((I,all(R,C)), Lie, Lpt, Li, Lu, Ls, Lie, [(I,all(R,C))|Lpt], Li, Lu, Ls):-!.

%----------------------------  CLASH  ------------------------------------
% et on va devoir tester si ya un clash a chaque nouvel ajout, on implemente donc le predicat, clash :
% FALSE => CLASH       &        TRUE => PAS DE CLASH
clash([]).
clash([(I,E)|L]) :- clash_elem(L,(I,E)), clash(L).

clash_elem([],(_,_)).
clash_elem([(U,A)|L],(I,E)) :-
    setof(X,iname(X),L3) , member(I,L3), member(U,L3),
    (U \== I ), clash_elem(L,(I,E)),!.

% le cas ou U et I sont des instances qui existent 
clash_elem([(U,A)|L],(I,E)) :-
    setof(X,iname(X),L3) , member(I,L3), member(U,L3),
    U == I, % on verifie que c'est les memes
    % si ya un clash ca renvoi dont False 
    A \== not(E), 
    E \== not(A),
    setof(X,iname(X),L3) , member(I,L3),
    clash_elem(L,(I,E)),!.

% Le cas ou on a genere 'inst'
clash_elem([(U,A)|L],(I,E)) :- 
    setof(X,iname(X),L3) , 
    not(member(I,L3)), 
    A \== not(E), 
    E \== not(A), 
    clash_elem(L,(I,E)),!.
% --------------------------------------------------

% Ensuite on a le prédicat 
% /\/\/\  resolution  /\/\/\  :
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-
    clash(Ls),
    complete_some(Lie,Lpt,Li,Lu,Ls,Abr),
    transformation_and(Lie,Lpt,Li,Lu,Ls,Abr),
    deduction_all(Lie,Lpt,Li,Lu,Ls,Abr),
    transformation_or(Lie,Lpt,Li,Lu,Ls,Abr).

% ce predicat fait appel a plusieurs predicat en commencant par 

% /\/\/\  complete_some  /\/\/\ : 
complete_some([],Lpt,Li,Lu,Ls,Abr).
complete_some([(A,some(R,C))|Lie],Lpt,Li,Lu,Ls,Abr):-
    genere(B), %on genere l'instance B
    evolue((inst,C), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
    concat([(A,B,R)],Abr,Abr1), % on ajoute <a,b> : R 
    % ===== AFFICHAGE =====
    nl, write(">>>>> REGLE complete_some : "),nl,
    affiche_evolution_Abox(Ls, [(A,some(R,C))|Lie], Lpt, Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr1),
    % =====================
    clash(Ls1), % on test si ya un clash 
    resolution(Lie1, Lpt1,Li1,Lu1,Ls1,Abr1).

% /\/\/\  transformation_and  /\/\/\  : 
transformation_and(Lie,Lpt,[],Lu,Ls,Abr).
transformation_and(Lie, Lpt,[(I,(and(C1,C2)))|Li],Lu, Ls,Abr) :-
    % On fais avec C1
    evolue((I,C1), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
    % ===== AFFICHAGE ===
    nl, write(">>>>> REGLE transformation_and : "),nl,
    affiche_evolution_Abox(Ls, Lie, Lpt, [(I,(and(C1,C2)))|Li], Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),
    % =====================
    clash(Ls1), % test du clash 

    % On fais avec C2
    evolue((I,C2), Lie1, Lpt1, Li1, Lu1, Ls1, Lie2, Lpt2, Li2, Lu2, Ls2),
    % ===== AFFICHAGE =====
    affiche_evolution_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr, Ls2, Lie2, Lpt2, Li2, Lu2, Abr),
    % =====================
    clash(Ls2), % test du clash
    resolution(Lie2, Lpt2, Li2, Lu2, Ls2,Abr).

% /\/\/\  deduction_all  /\/\/\  : 
deduction_all(Lie,[],Li,Lu,Ls,Abr).
deduction_all(Lie,[(A,all(R,C))|Lpt],Li,Lu,Ls, Abr) :-
    member((A,B,R),Abr), % on test si <a,b> : R est dans Abr
    evolue((B,C), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
    % ===== AFFICHAGE =====
    nl, write(">>>>> REGLE deduction_all : "),nl,
    affiche_evolution_Abox(Ls, Lie, [(A,all(R,C))|Lpt], Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),
    % =====================
    clash(Ls1), % test du clash 
    resolution(Lie1, Lpt1, Li1, Lu1, Ls1,Abr).

deduction_all(Lie,[(A,all(R,C))|Lpt],Li,Lu,Ls, Abr) :-
    not(member((A,B,R),Abr)),
    % ===== AFFICHAGE =====
    nl, write(">>>>> REGLE deduction_all : "),nl,
    write("aucun changement car il nappartient pas a la liste des assertions de roles ").
    % =====================

% /\/\/\  transformation_or  /\/\/\  : 
transformation_or(Lie,Lpt,Li,[],Ls,Abr).
transformation_or(Lie,Lpt,Li,[(I,or(C1,C2))|Lu],Ls,Abr) :-
    evolue((I,C1), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
    % ===== AFFICHAGE =====
    nl, write(">>>>> REGLE transformation_OR 1er branche  : "),nl,
    affiche_evolution_Abox(Ls, Lie, Lpt, Li, [(I,or(C1,C2))|Lu], Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),
    % =====================
    clash(Ls1),
    resolution(Lie1, Lpt1, Li1, Lu1, Ls1,Abr).

transformation_or(Lie,Lpt,Li,[(I,or(C1,C2))|Lu],Ls,Abr) :-
    evolue((I,C2), Lie, Lpt, Li, Lu, Ls, Lie2, Lpt2, Li2, Lu2, Ls2),
    % ===== AFFICHAGE =====
    nl, write(">>>>> REGLE transformation_OR 2e branche  : "),nl,
    affiche_evolution_Abox(Ls, Lie, Lpt, Li, [(I,or(C1,C2))|Lu], Abr, Ls2, Lie2, Lpt2, Li2, Lu2, Abr),
    % =====================
    clash(Ls2), % test du clash 
    resolution(Lie2, Lpt2, Li2, Lu2, Ls2,Abr).

% --------------------------------------------------------
% Fonction affichage 
affiche_evolution_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2) :-
    write("><><><><><><><><><>< AVANT ><><><><><><><><><><><><><"),nl,
    write("--------------------  Ls1 --------------------"),nl, affiche(Ls1), nl,
    write("--------------------  Lie1 --------------------"),nl, affiche(Lie1), nl,
    write("--------------------  Lpt1 --------------------"),nl, affiche(Lpt1), nl,
    write("--------------------  Li1 --------------------"),nl, affiche(Li1), nl,
    write("--------------------  Lu1 --------------------"),nl, affiche(Lu1), nl,
    write("--------------------  Abr1 --------------------"),nl, afficheRole(Abr1), nl,
    % write("><><><><><><><><><><><><><><><><><><><><><><><"),nl,
    write("><><><><><><><><><>< APRES ><><><><><><><><><><><><><"),nl,
    write("--------------------  Ls2  --------------------"),nl, affiche(Ls2), nl,
    write("--------------------  Lie2 --------------------"),nl, affiche(Lie2), nl,
    write("--------------------  Lpt2 --------------------"),nl, affiche(Lpt2), nl,
    write("--------------------  Li2 --------------------"),nl, affiche(Li2), nl,
    write("--------------------  Lu2 --------------------"),nl, affiche(Lu2), nl,
    write("--------------------  Abr2 --------------------"),nl, afficheRole(Abr2), nl, 
    write("-<>-<>-<>-<>-<>-<>-<>-<>-<>-<>-<>-<>-<>-<>-<>-<>-<>-<>-"),nl.

affiche([]).
affiche([(I , C)| L]) :- write(I),write(" : "),affiche_concept(C),nl, affiche(L),!.
afficheRole([(A , B , R)| L]) :- write("<"),write(A),write(,),write(B),write(">"), write(" : "), write(R),nl, afficheRole(L),!.
afficheRole([]).

affiche_concept(C) :- setof(X, cnamena(X),L), member(C,L), write(C).
affiche_concept(C) :- setof(X, cnamea(X),L), member(C,L), write(C).

affiche_concept(not(C)) :- write("¬"),affiche_concept(C).
affiche_concept(or(C1,C2)) :- write("(") , affiche_concept(C1) , write(" ⊔ ") , affiche_concept(C2), write(")").
affiche_concept(and(C1,C2)) :- write("(") , affiche_concept(C1) , write(" ⊓ ") , affiche_concept(C2), write(")").
affiche_concept(all(R,C)) :-  write("∀."),write(R) , write("(") , affiche_concept(C),write(")").
affiche_concept(some(R,C)) :-  write("∃."),write(R) , write("(") , affiche_concept(C),write(")").

/*\    /\    /\    /\    /\    /\    /\    /\    /\    /\    /\    /\    /\    /\    /\    /\    /\    /\ */
/* \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \*/
/*  \/    \/    \/    \/    \/    \/    \/    \/    \/    \/    \/    \/    \/    \/    \/    \/    \/    \*/
/*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ Ecriture en Prolog d’un démonstrateur basé sur ~~~~~~~~~~~~~~~~~~~~~~~~~~~ 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ l’algorithme ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ des tableaux pour la logique de description ALC ~~~~~~~~~~~~~~~~~~~~~~~~*/
/*\    /\    /\    /\    /\    /\    /\    /\    /\    /\    /\    /\    /\    /\    /\    /\    /\    /\ */
/* \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \  /  \*/
/*  \/    \/    \/    \/    \/    \/    \/    \/    \/    \/    \/    \/    \/    \/    \/    \/    \/    \*/

programme :- 
    premiere_etape(Tbox,Abi,Abr), % creation de la ABOX et TBOX
    deuxieme_etape(Abi,Abi1,Tbox), % saisie de la proposition a demontrer
    troisieme_etape(Abi1,Abr). % demonstrateur


/*<><><><><><><><><><><><><><><<><><><><><><>><> PREMIERE ETAPE <><><><><><><><><><><><><><><><><><><><><>*/

/*
On met la Tbox par une liste de doublets (1)
La Abox sera partionné en 2 sous listes :
    - une qui contient les assertions de concepts, (2)
    - une qui contient les assertions de roles. (3)
*/

premiere_etape(Tbox,Abi,Abr) :-
    setof((X,Y),equiv(X,Y),Tbox),       % (1)
    setof((X,Y),inst(X,Y),Abi),         % (2)
    setof((X,Y,Z),instR(X,Y,Z),Abr).    % (3)

/*<><><><><><><><><><><><><><><<><><><><><><>><> DEUXIEME ETAPE <><><><><><><><><><><><><><><><><><><><><>*/

deuxieme_etape(Abi,Abi1,Tbox) :-
    saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :- nl,
    write("Entrez le numero du type de proposition que vous voulez demontrer :"),nl,
    write("1 - Une instance donnee appartient a un concept donne."),nl, % (1)
    write("2 - Deux concepts ne possede aucun elements en commun(ils ont une intersection vide)."),nl, % (2)
    nl,read(R),
    suite(R,Abi,Abi1,Tbox).
    
suite(1,Abi,Abi1,Tbox) :- acquisition_prop_type1(Abi,Abi1,Tbox),!.
suite(2,Abi,Abi1,Tbox) :- acquisition_prop_type2(Abi,Abi1,Tbox),!.
suite(R,Abi,Abi1,Tbox) :- nl, write("Cette reponse est incorrecte."),
    nl, saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

/*<><><><><><><><><><><><><><><<><><><><><><>><> TROISIEME ETAPE <><><><><><><><><><><><><><><><><><><><><>*/
troisieme_etape(Abi,Abr) :-
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
    not(resolution(Lie,Lpt,Li,Lu,Ls,Abr)),
    nl,write('Youpiiiiii, on a demontre la proposition initiale !!!'). 






/*FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_*/
/*FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_*/
/*FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_FIN_
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*


*/
/*_____________________________________________________________________________________________________________*/
/*_____________________________________________________________________________________________________________*/
/*___________________________________________FONCTIONS UTILES _________________________________________________*/
/*_____________________________________________________________________________________________________________*/


/*————————————————————————————————————————*/
/*member(X,L) : prédicat prédéfini, teste si l’élément X appartient à la liste L.*/
/*————————————————————————————————————————*/
/*
————————————————————————————————————————
concat(L1,L2,L3) : concatène les deux listes L1 et L2 et renvoie la liste L3.
————————————————————————————————————————*/
concat([],L1,L1).
concat([X|Y],L1,[X|L2]) :- concat(Y,L1,L2).
/*
————————————————————————————————————————
enleve(X,L1,L2) : supprime X de la liste L1 et renvoie la liste résultante dans L2.
————————————————————————————————————————*/
enleve(X,[X|L],L) :-!.
enleve(X,[Y|L],[Y|L2]) :- enleve(X,L,L2).
/*
————————————————————————————————————————
genere(Nom) : génère un nouvel identificateur qui est fourni en sortie dans Nom.
————————————————————————————————————————*/

compteur(1).
genere(Nom) :- compteur(V),nombre(V,L1), concat([105,110,115,116],L1,L2), V1 is V+1, 
    dynamic(compteur/1), 
    retract(compteur(V)), 
    dynamic(compteur/1),
    assert(compteur(V1)),nl,nl,nl,
    name(Nom,L2).

nombre(0,[]).
nombre(X,L1) :- 
    R is (X mod 10), 
    Q is ((X-R)//10),
    chiffre_car(R,R1),
    char_code(R1,R2),
    nombre(Q,L),
    concat(L,[R2],L1).

chiffre_car(0,'0').
chiffre_car(1,'1').
chiffre_car(2,'2').
chiffre_car(3,'3').
chiffre_car(4,'4').
chiffre_car(5,'5').
chiffre_car(6,'6').
chiffre_car(7,'7').
chiffre_car(8,'8').
chiffre_car(9,'9').
/*
————————————————————————————————————————
lecture(L) : permet d’acquérir au clavier la liste L des termes Prolog entrés par 
l’utilisateur, de la façon suivante :
l’utilisateur entre un terme Prolog directement suivi d’un point et d’un retour chariot à la 
vue du prompteur et ainsi de suite. Lorsque l’utilisateur souhaite interrompre la saisie de 
termes, il doit taper fin, suivi d’un point et d’un retour chariot.
————————————————————————————————————————*/
lecture([X|L]):-
read(X), 
X \= fin, !, 
lecture(L).
lecture([]).
/*
——————————————————————————————————————————————————————————————————
flatten(Liste1,Liste2) : Aplanit Liste1 et met le résultat dans Liste2. Liste1 peut 
contenir de nombreuses listes imbriquées récursivement. flatten/2 extrait tous les 
éléments contenus dans Liste1 et stocke le résultat dans une liste "plane" (à une seule 
dimension).
—————————————————————————————————————————————————————————————————*/
