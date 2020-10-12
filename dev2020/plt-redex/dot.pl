ty(bot).
ty(top).
ty(type(S, T)) :- ty(S), ty(T).
ty(sel(X)) :- varx(X).
ty(pi(S, T)) :- ty(S), ty(T).

tm(X) :- varx(X).
tm(lam(E)) :- tm(E).
tm(app(E1, E2)) :- tm(E1), tm(E2).
tm(type(S)) :- ty(S).

varx(z).
varx(s(X)) :- varx(X).

appT-aux(X, bot, Y, bot) :- varx(X), varx(Y).
appT-aux(X, top, Y, top) :- varx(X), varx(Y).
appT-aux(X, type(S1, T1), Y, type(S2, T2)) :- appT-aux(X, S1, Y, S2), appT-aux(X, T1, Y, T2).
appT-aux(X, sel(X), Y, sel(Y)) :- varx(X), varx(Y).
appT-aux(X, pi(S1, T1), Y, pi(S2, T2)) :- appT-aux(X, S1, Y, S2), appT-aux(s(X), T1, s(Y), T2).

