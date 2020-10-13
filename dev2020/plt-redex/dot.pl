nat(z).
nat(s(N)) :- nat(N).

fuel(N) :- nat(N).

% Types
ty(bot).
ty(top).
ty(type(S, T)) :- ty(S), ty(T).
ty(sel(X)) :- varx(X).
ty(pi(S, T)) :- ty(S), ty(T).

% Terms
tm(X) :- varx(X).
tm(lam(E)) :- tm(E).
tm(app(E1, E2)) :- tm(E1), tm(E2).
tm(type(S)) :- ty(S).

% Variables
varx(N) :- nat(N).

% Proof of inequality for variables
neqx(z, s(X)) :- varx(X).
neqx(s(X), z) :- varx(X).
neqx(s(X), s(Y)) :- neqx(X, Y).

% Type application
appT_aux(X, bot, Y, bot) :- varx(X), varx(Y).
appT_aux(X, top, Y, top) :- varx(X), varx(Y).

appT_aux(X, type(S1, T1), Y, type(S2, T2)) :- 
  appT_aux(X, S1, Y, S2), 
  appT_aux(X, T1, Y, T2).

appT_aux(X, sel(X), Y, sel(Y)) :- varx(X), varx(Y).

appT_aux(X, pi(S1, T1), Y, pi(S2, T2)) :- 
  appT_aux(X, S1, Y, S2), 
  appT_aux(s(X), T1, s(Y), T2).

appT(S, X, T) :- appT_aux(z, S, X, T).

% Proof that a variable is not in the free variables of a type
not_in_fv(X, bot, N) :- varx(X), fuel(N).
not_in_fv(X, top, N) :- varx(X), fuel(N).

not_in_fv(X, type(S, T), s(N)) :- 
  not_in_fv(X, S, N),
  not_in_fv(X, T, N).

not_in_fv(X, sel(Y), N) :- 
  neqx(X, Y),
  fuel(N).

not_in_fv(X, pi(S, T), s(N)) :-
  not_in_fv(X, S, N),
  not_in_fv(s(X), T, N).

% Contexts
cx(nil).
cx(cons(S, G)) :- ty(S), cx(G).

% Lookup variables in context
lookup(cons(S, G), z, S, N) :- cx(G), ty(S), fuel(N).
lookup(cons(T, G), s(X), S, s(N)) :- lookup(G, X, S, N), ty(T).

% Typechecking
has_type(G, X, T, N) :- % T_Var
  varx(X),
  lookup(G, X, T, N).

has_type(G, type(S), type(S, S), N) :-
  cx(G),
  fuel(N),
  ty(S). % T_Typ

has_type(G, lam(E), pi(S, T), s(N)) :- 
  has_type(cons(S, G), E, T, N). % T_Fun

has_type(G, app(E, X), appT(T, X), s(N)) :- 
  has_type(G, E, pi(S, T), N),
  has_type(G, X, S, N).

has_type(G, app(F, E), appT(T, z), s(N)) :-
  has_type(G, F, pi(S, T), N),
  has_type(G, E, S, N),
  not_in_fv(z, T, N).

has_type(G, E, T, s(N)) :-
  has_type(G, E, S, N),
  subtype(G, S, T, N).

% Subtyping
subtype(G, bot, S, N) :- cx(G), ty(S), fuel(N).
subtype(G, S, top, N) :- cx(G), ty(S), fuel(N).

subtype(G, type(S1, T1), type(S2, T2), s(N)) :-
  subtype(G, S2, S1, N),
  subtype(G, T1, T2, N).

subtype(G, S, sel(X), s(N)) :-
  has_type(G, X, type(S, _), N).

subtype(G, sel(X), T, s(N)) :-
  has_type(G, X, type(_, T), N).

subtype(G, sel(X), sel(X), s(N)) :- cx(G), varx(X), fuel(N).

subtype(G, pi(S1, T1), pi(S2, T2), s(N)) :-
  subtype(G, S2, S1, N),
  subtype(cons(S2, G), T1, T2, N).

subtype(G, S, T, s(N)) :- 
  subtype(G, S, R, N),
  subtype(G, R, T, N).
