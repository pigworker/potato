module Ty where

open import Eq
open import Tuple
open import Thin
open import Tm
open import Meta
open import Red


All : forall {X} -> (X -> Set) -> List X -> Set
All P [] = One
All P (x ,- xs) = P x * All P xs

Aye : forall {X} -> (X -> Set) -> One + X -> Set
Aye P (ff , <>) = Zero
Aye P (tt , x)  = P x

And : forall {X Y} -> (X -> Set) -> (Y -> Set) -> X * Y -> Set
And P Q (x , y) = P x * Q y

data Ju (n : Nat) : Set where
  _!-_ : Tm n chk -> Ju (n su) -> Ju n
  _>>_ : Tm n chk -> Tm n chk -> Ju n

infixr 20 _!-_ _>>_

FormIntro' : Ty'
FormIntro' = Chk' [] any *' Chk' [] (gdd ff) ->' Aye'

module RULES
  (formIntro : forall {G} -> G :- FormIntro')
  (elimBeta  : forall {G} -> G :- ElimBeta')
  where
  open RED elimBeta
    

{-
module RULES
  (introRules : forall {n}(T t : Tm n chk) -> One + List (Ju n))
  (elimRules : forall {n}(T s : Tm n chk) -> One + (List (Ju n) * (Tm n syn -> Tm n chk)))
  (normTy : forall {n} -> Tm n chk -> Tm n chk)
  (normTyRed : forall {n}(T : Tm n chk) -> Star _~>_ T (normTy T))
  where

  data _|-_:>_ {n} (G : Cx n) : Tm n chk -> Tm n chk -> Set
  data _|-_<:_ {n} (G : Cx n) : Tm n syn -> Tm n chk -> Set

  Judge : forall {n} -> Cx n -> Ju n -> Set
  Judge G (S !- J) = Judge (\ x -> (G -push S) x ^Tm (iota no)) J
  Judge G (T >> t) = G |- T :> t

  data _|-_:>_ {n} G where

    embed : forall {e S T} ->
           G |- e <: S ->
           S ~ T ->
           G |- T :> ` e

    intro : forall {T t} ->
            Aye (All (Judge G)) (introRules T t) ->
            G |- T :> t

    pre : forall {T T' t} ->
           T ~> T' ->
           G |- T' :> t ->
           G |- T :> t

  data _|-_<:_ {n} G where

    #_ : (x : 1 <= n) -> G |- # x <: G x

    rad : forall {t T} ->
            G |- ! TY :> T ->
            G |- T :> t ->
            G |- t :: T <: T

    elim : forall {e S s S'} ->
            G |- e <: S ->
            Aye (And (All (Judge G)) (\ f -> f e ~ S')) (elimRules S s) ->
            G |- e $ s <: S'

    post : forall {e S S'} ->
            G |- e <: S ->
            S ~> S' ->
            G |- e <: S'

  pres : forall {n}{G : Cx n}{T T' t : Tm n chk} ->
         Star _~>_ T T' -> G |- T' :> t -> G |- T :> t
  pres [] Tt = Tt
  pres (r ,- rs) T't = pre r (pres rs T't)

  posts : forall {n}{G : Cx n}{e : Tm n syn}{S S' : Tm n chk} ->
    G |- e <: S -> Star _~>_ S S' -> G |- e <: S'
  posts eS [] = eS
  posts eS (r ,- rs) = posts (post eS r) rs

  check checkN : forall {n}(G : Cx n)(T t : Tm n chk) ->
            One + (G |- T :> t)
  checkIntro : forall {n}(G : Cx n)(T t : Tm n chk) ->
            One + Aye (All (Judge G)) (introRules T t)
  synth synthN : forall {n}(G : Cx n)(e : Tm n syn) ->
            One + (_ >< \ S -> G |- e <: S)
  check G T t with normTy T | normTyRed T
  ... | T' | r with checkN G T' t
  check G T t | T' | rs | ff , <> = ff , <>
  check G T t | T' | rs | tt , T't = tt , pres rs T't
  checkN G T (` e) with synthN G e
  checkN G T (` e) | ff , <> = ff , <>
  checkN G T (` e) | tt , S , eS with S ~Tm?~ T
  checkN G T (` e) | tt , S , eS | ff , z = ff , <>
  checkN G T (` e) | tt , S , eS | tt , q = tt , embed eS q
  checkN G T t with checkIntro G T t
  checkN G T t | ff , <> = ff , <>
  checkN G T t | tt , ps = tt , intro ps
  checkIntro G T t with introRules T t
  checkIntro G T t | ff , <> = ff , <>
  checkIntro G T t | tt , ps = {!!}
  synth G (# x) = tt , G x , # x
  synth G (e $ s) = {!!}
  synth G (t :: T) with check G (! TY) T | check G T t
  synth G (t :: T) | ff , zT | bt , zt = ff , <>
  synth G (t :: T) | tt , zT | ff , zt = ff , <>
  synth G (t :: T) | tt , TYT | tt , Tt = tt , T , rad TYT Tt
  synthN G e with synth G e
  synthN G e | ff , <> = ff , <>
  synthN G e | tt , S , eS = tt , normTy S , posts eS (normTyRed S)
  
KiplingIntro : forall {n}(T t : Tm n chk) -> One + List (Ju n)
KiplingIntro (! TY) (! A0) = tt , []
KiplingIntro (! TY) (! A1) = tt , []
KiplingIntro (! A1) (! A0) = tt , []
KiplingIntro (! TY) (! A2) = tt , []
KiplingIntro (! A2) (! A0) = tt , []
KiplingIntro (! A2) (! A1) = tt , []
KiplingIntro (! TY) (! PI & S & ^ T) =
  tt , ! TY >> S
  ,-   S !- ! TY >> T
  ,-   []
KiplingIntro (! PI & S & ^ T) (^ t) =
  tt , S !- T >> t
  ,-   []
KiplingIntro (! TY) (! SG & S & ^ T) =
  tt , ! TY >> S
  ,-   S !- ! TY >> T
  ,-   []
KiplingIntro (! SG & S & ^ T) (s & t) =
  tt , S >> s
  ,-   (T /0 (s :: S)) >> t
  ,-   []
KiplingIntro T t = ff , <>

KiplingElim : forall {n}(T s : Tm n chk) -> One + (List (Ju n) * (Tm n syn -> Tm n chk))
KiplingElim (! A0) S = tt , (! TY >> S ,- []) , \ _ -> S
KiplingElim (! A2) (! TY & F & T) = tt , ! TY >> F ,- ! TY >> T ,- [] , \ _ -> ! TY
KiplingElim (! A2) ((^ P) & f & t) =
  tt , ! A2 !- ! TY >> P
    ,- (P /0 (! A0 :: ! A2)) >> f
    ,- (P /0 (! A1 :: ! A2)) >> t
    ,- [] , \ e -> P /0 e
KiplingElim (! PI & S & ^ T) s = tt , S >> s ,- [] , \ _ -> T /0 (s :: S)
KiplingElim (! SG & S & ^ T) (! A0) = tt , [] , \ _ -> S
KiplingElim (! SG & S & ^ T) (! A1) = tt , [] , \ e -> T /0 (e $ ! A0)
KiplingElim T s = ff , <>
-}
