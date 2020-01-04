module Ru where

open import Basics
open import Thin
open import Tm
open import Pat

data PVar {m} : (p : Pat m) -> Nat -> Set where
  ho : forall {n}{th : n <= m}             -> PVar (hole th) n
  ll : forall {n}{p r : Pat m} -> PVar p n -> PVar (p && r) n
  rr : forall {n}{p r : Pat m} -> PVar r n -> PVar (p && r) n
  uu : forall {n}{p : Pat (m su)} -> PVar p n -> PVar (^ p) n
  
_??_ : forall {m n}{p : Pat m}{P : Nat -> Set} ->
       Env P p -> PVar p n -> P n
hole p     ?? ho   = p
(pi && rh) ?? ll x = pi ?? x
(pi && rh) ?? rr x = rh ?? x
(^ pi)     ?? uu x = pi ?? x

pabst : forall {m} -> Pat m -> Pat []
pabst {m su} p = pabst (^ p)
pabst {[]} p = p

gabst : forall {m P}(p : Pat m)(pi : Env P p) -> Env P (pabst p)
gabst {m su} p pi = gabst (^ p) (^ pi)
gabst {[]} p pi = pi

Prems : Pat [] -> forall {m} -> Pat m -> Set
Prems q {m} (hole th) = Tm{PVar q} m chk
Prems q (p && r)      = Prems q p * Prems (q && pabst p) r
Prems q (! a)         = One
Prems q {m} (^ p)     = Tm{PVar q} m chk * Prems q p

Proper : forall {m} -> Pat m -> Set
Proper (hole th) = Zero
Proper _         = One

record IntroChecker : Set where
  field
    classifier    : Pat []
    subject       : Pat []
    properSubject : Proper subject
    components    : Prems classifier subject

record ElimChecker : Set where
  field
    targetType    : Pat []
    eliminator    : Pat []
    components    : Prems targetType eliminator
    returnType    : Tm{PVar (targetType && eliminator)} ([] su) chk

Clo : Nat -> Set  -- this is probably short-sighted
Clo _ = Zero

Cx : Nat -> Set
Cx n = Tm{Clo} n (chk ** n)

module _ (Chk : forall {n}(Ga : Cx n)(T t : Tm{Clo} n chk) -> Set) where

  PREMS : forall (q : Pat []){m}(p : Pat m) -> Prems q p ->
          forall {n} -> Cx (n +B m) ->
          (ch : Env (\ m -> Tm{Clo} (n +B m) chk) q) ->
          (pi : Env (\ m -> Tm{Clo} (n +B m) chk) p) ->
          Set
  PREMS q (hole th) T Ga ch (hole t) =
    Chk Ga (T !Tm (ch ??_)) (t ^Tm (iota +th th))
  PREMS q (p && r) (P , R) Ga ch (pi && rh) =
    PREMS q p P Ga ch pi *
    PREMS (q && pabst p) r R Ga (ch && gabst p pi) rh
  PREMS q (! a) <> Ga ch [] = One
  PREMS q (^ p) (S , P) Ga ch (^ pi) =
    PREMS q p P ((Ga ` (S !Tm (ch ??_))) ^Tm (iota no)) ch pi
