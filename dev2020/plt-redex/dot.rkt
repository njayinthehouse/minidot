#lang racket
(require redex)
(require redex/tut-subst)

(define-language
  D<:>-syntax
  (S T ::= Bot Top (Type T T) (Sel x) (Pi S T))
  (e ::= x (lam S e) (e e) (type T))
  (x y ::= z (s x)))

(define-metafunction
  D<:>-syntax
  appT-aux : x T x -> T
  [(appT-aux _ Bot _)        Bot]
  [(appT-aux _ Top _)        Top]
  [(appT-aux x (Type S T) y) (Type (appT-aux x S y) (appT-aux x T y))]
  [(appT-aux x (Sel x) y)    (Sel y)]
  [(appT-aux x (Sel x_0) y)  (Sel x_0)]
  [(appT-aux x (Pi S T) y)   (Pi (appT-aux x S y) (appT-aux (s x) T y))])

(define-metafunction
  D<:>-syntax
  appT : T x -> T
  [(appT T x) (appT-aux z T x)])

(define-metafunction
  D<:>-syntax 
  [(neqx? x x) #f]
  [(neqx? x y) #t])

(define-judgment-form
  D<:>-syntax
  #:mode (has-no-fv I I)
  #:contract (has-no-fv x T)

  [-----------------
   (has-no-fv _ Bot)]

  [-----------------
   (has-no-fv _ Top)]

  [(has-no-fv x S)
   (has-no-fv x T)
   ------------------------
   (has-no-fv x (Type S T))]

  [(side-condition (neqx? x y))
   ----------------------------
   (has-no-fv x (Sel y))]

  [(has-no-fv x S)
   (has-no-fv (s x) T)
   ----------------------
   (has-no-fv x (Pi S T))])

(define-extended-language
  D<:>+Cx
  D<:>-syntax
  (G ::= nil (T G)))

;(define-judgment-form
;  D<:>+Cx
;  #:mode (wf-Cx I)
;  #:contract (wf-Cx G)

;  [----------- "WF-Nil"
;   (wf-Cx nil)]

;  [(wf-Ty G S)
;   (wf-Cx G)
;   ----------- "WF-Cons"
;   (wf-Cx (S G))])

;(define-judgment-form
;  D<:>+Cx
;  #:mode (wf-Ty I I)
;  #:contract (wf-Ty G S)

  ;[------------- "WF-Bot"
  ; (wf-Ty G Bot)]

  ;[------------- "WF-Top"
  ; (wf-Ty G Top)]

  ;[(wf-Ty G S)
  ; (wf-Ty G T)
  ; -------------------- "WF-Typ"
  ; (wf-Ty G (Type S T))]

  ;[(has-type G x S)
  ; ------------------------- "WF-Sel"
  ; (wf-Ty G (Sel x))]

  ;[(wf-Ty G S)
  ; (wf-Ty (S G) T)
  ; ----------------- "WF-Pi"
  ; (wf-Ty G (Pi S T))])

(define-judgment-form
  D<:>+Cx
  #:mode (lookup I I O)
  #:contract (lookup G x T)

  [------------------ "X-Top"
   (lookup (S G) z S)]

  [(lookup G x S)
   -------------------- "X-Pop"
   (lookup (T G) (s x) S)])

(define-judgment-form
  D<:>+Cx
  #:contract (has-type G e T)

  [(lookup G x T)
   ---------------- "T-Var"
   (has-type G x T)]

  [-------------------------------- "T-Typ"
   (has-type G (type T) (Type T T))]

  [(has-type (S G) e T)
   ------------------------------- "T-Fun"
   (has-type G (lam S e) (Pi S T))]

  [(has-type G e (Pi S T))
   (has-type G x S)
   ----------------------------- "T-DApp"
   (has-type G (e x) (appT T x))]

  [(has-type G e_1 (Pi S T))
   (has-type G e_2 S)
   (has-no-fv z T)
   ----------------------------- "T-App"
   (has-type G (e_1 e_2) T)]

  [(has-type G e S)
   (<: G S T)
   ---------------- "T-Sub"
   (has-type G e T)])

(define-judgment-form
  D<:>+Cx
  #:contract (<: G S T)

  [------------ "S-Bot"
   (<: G Bot S)]

  [------------ "S-Top"
   (<: G S Top)]

  [(<: G S_2 S_1)
   (<: G T_1 T_2)
   ------------------------------------ "S-Typ"
   (<: G (Type S_1 T_1) (Type S_2 T_2))]

  [(has-type G x (Type S T))
   ------------------------- "S-Sel1"
   (<: G S (Sel x))]

  [(has-type G x (Type S T))
   ------------------------- "S-Sel2"
   (<: G (Sel x) T)]

  [---------------------- "S-Selx"
   (<: G (Sel x) (Sel x))])
