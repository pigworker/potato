module Pat where

open import Eq
open import Thin
open import Atom
open import Basics
open import Tm
open import Rel

data Pat (m : Nat) : Set where
  hole : forall {n} -> n <= m -> Pat m
  _&&_ : Pat m -> Pat m -> Pat m
  !_   : Atom -> Pat m
  ^_   : Pat (m su) -> Pat m

data Env (P : Nat -> Set){m : Nat} : Pat m -> Set where
  hole : forall {n}{th : n <= m} -> P n -> Env P (hole th)
  _&&_ : forall {s t} ->
         Env P s -> Env P t -> Env P (s && t)
  []   : forall {a} -> Env P (! a)
  ^_   : forall {t} -> Env P t -> Env P (^ t)

stan : forall {M m n}
  (p : Pat m)(pi : Env (\ m -> Tm{M} (n +B m) chk) p) ->
  Tm{M} (n +B m) chk
stan (hole th) (hole t) = t ^Tm (iota +th th)
stan (p && q) (pi && rh) = stan p pi & stan q rh
stan (! a) [] = ! a
stan (^ p) (^ pi) = ^ stan p pi

dep? : forall {M d n m}(th : n <= m)(t' : Tm{M} m d) ->
  One + (Tm n d >< \ t -> (t ^Tm th) ~ t')
dep? th (pair p s' t') with dep? th s' | dep? th t'
... | tt , s , r~ | tt , t , r~ = tt , pair p s t , r~
... | _ | _ = ff , <>
dep? th (! a) = tt , ! a , r~
dep? th (^ t') with dep? (th su) t'
... | tt , t , r~ = tt , ^ t , r~
... | _ = ff , <>
dep? th [ e' ] with dep? th e'
... | tt , e , r~ = tt , [ e ] , r~
... | _ = ff , <>
dep? th (# x) with pb th x
dep? th (# x) | z , a , b -^ .<> , q = ff , <>
dep? th (# x) | .([] su) , a , ([] -, .<>) , q =
  tt , # a , (#_ $~ (
    (a ^^ th) ~[ q >
    iota ^^ x ~[ iota^^ x >
    x [QED]))
dep? th (m / es') with dep? th es'
... | tt , es , r~ = tt , m / es , r~
... | _ = ff , <>
dep? th [] = tt , [] , r~

depThin : forall {M d n m}(t : Tm{M} n d)(th : n <= m) ->
  dep? th (t ^Tm th) ~ (tt , t , r~)
depThin (pair p s t) th
  with dep? th (s ^Tm th) | depThin s th
     | dep? th (t ^Tm th) | depThin t th
... | tt , s' , r~ | r~ | tt , t' , r~ | r~ = r~
depThin (! _) th = r~
depThin (^ t) th
  with dep? (th su) (t ^Tm (th su)) | depThin t (th su)
... | tt , t' , r~ | r~ = r~
depThin [ e ] th
  with dep? th (e ^Tm th) | depThin e th
... | tt , e' , r~ | r~ = r~
depThin (# x) th rewrite pbCo x th = (tt ,_) $~ (((# x) ,_) $~ uip)
depThin (m / es) th
  with dep? th (es ^Tm th) | depThin es th
... | tt , es' , r~ | r~ = r~
depThin [] th = r~


match? : forall {M n m}(p : Pat m)(t : Tm{M} (n +B m) chk) ->
         One
       + (Env (\ m -> Tm{M} (n +B m) chk) p >< \ pi ->
          stan p pi ~ t)
match? (hole th) t with dep? (iota +th th) t
... | tt , s , q = tt , hole s , q
... | _ = ff , <>
match? (p && q) (s & t)
  with match? p s | match? q t
...  | tt , pi , sq | tt , rh , tq =
  tt , (pi && rh) , (_&_ $~ sq ~$~ tq)
...  | _            | _            = ff , <>
match? (! a) (! b) with atom~? a b
... | tt , q  = tt , [] , (!_ $~ q)
... | _       = ff , <>
match? (^ p) (^ t) with match? p t
... | tt , pi , q  = tt , ^ pi , (^_ $~ q)
... | _            = ff , <>
match? _ _ = ff , <>

module _ {M N n m}
  {R : forall {d} p ->
       Tm{M} (n +B p) d -> Tm{N} (m +B p) d ->
       Set}
  (MSR : MatchStable R)
  where
  open MatchStable MSR

  Match : forall {l}(p : Pat l) ->
    Env (\ l -> Tm{M} (n +B l) chk) p ->
    Env (\ l -> Tm{N} (m +B l) chk) p ->
    Set
  Match (hole _) (hole t0) (hole t1) = R _ t0 t1
  Match (p && r) (pi0 && rh0) (pi1 && rh1) =
    Match p pi0 pi1 * Match r rh0 rh1
  Match (! _) [] [] = One
  Match (^ p) (^ pi0) (^ pi1) = Match p pi0 pi1

  matchStable : forall {l}(p : Pat l)
    (t0 : Tm{M} (n +B l) chk)(t1 : Tm{N} (m +B l) chk) ->
    R l t0 t1 ->
    forall pi0 q0 ->
    match? p t0 ~ (tt , pi0 , q0) ->
    _ >< \ pi1 -> _ >< \ q1 ->
    match? p t1 ~ (tt , pi1 , q1) *
    Match p pi0 pi1
  matchStable (hole th) ._ t1 t (hole t0) r~ y0
    with isnDep th {t0} r~ t
  ... | t1' , r~ , r 
    with dep? (iota +th th) (t0 ^Tm (iota +th th))
  matchStable (hole th) ._ ._ t (hole t0) r~ r~
    | t1' , r~ , r | tt , .t0 , .r~
    with dep? (iota +th th) (t1' ^Tm (iota +th th))
       | depThin t1' (iota +th th)
  ... | _ | r~
    = _ , _ , r~ , r
  matchStable (p && r) (s0 & t0) t1 t (pi0 && rh0) q0 y0
    with match? p s0 | matchStable p s0
       | match? r t0 | matchStable r t0
  matchStable (p && r) (._ & ._) t1 t (pi0 && rh0) r~ r~
    | tt , .pi0 , r~ | ph | tt , .rh0 , r~ | rh
    with isCons t
  ... | s' , t' , r~ , sr , tr
    with match? p s' | ph _ sr _ r~ r~
       | match? r t' | rh _ tr _ r~ r~
  ... | tt , pi1 , r~ | _ , r~ , r~ , pim
      | tt , rh1 , r~ | _ , r~ , r~ , rhm
    = _ , r~ , r~ , pim , rhm
  matchStable (! a) .(! a) t1 t [] r~ y0
    with r~ <- isAtom t
       | tt , r~ <- atom~? a a
       = _ , r~ , r~ , <>
  matchStable (^ p) (^ t0) t1 t (^ pi0) q0 y0
    with match? p t0 | matchStable p t0
  matchStable (^ p) (^ _) t1 t (^ _) .r~ r~
    | tt , _ , r~ | ph
    with isAbst t
  ... | t' , r~ , r
    with match? p t' | ph _ r _ r~ r~
  ... | tt , pi1 , r~ | _ , r~ , r~ , pim
    = _ , r~ , r~ , pim

  
