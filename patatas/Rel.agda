module Rel where

open import Eq
open import Thin
open import Basics
open import Tm

module _ {M N n m}
  (R : forall {d} p ->
       Tm{M} (n +B p) d -> Tm{N} (m +B p) d ->
       Set)
  where
  
  record MatchStable : Set where
    field
      isnDep : forall {q p}(th : q <= p)
               {s  : Tm (n +B q) chk}
               {s' : Tm (n +B p) chk}
               {t' : Tm (m +B p) chk} ->
               s' ~ (s ^Tm (iota +th th)) ->
               R p s' t' ->
               Tm (m +B q) chk >< \ t ->
               t' ~ (t ^Tm (iota +th th)) *
               R q s t
      isAtom : forall {p a r} ->
               R p (! a) r -> r ~ (! a)
      isCons : forall {p s t r} ->
               R p (s & t) r ->
               _ >< \ s' -> _ >< \ t' ->
               r ~ (s' & t') *
               R p s s' * R p t t'
      isAbst : forall {p t r} ->
               R p (^ t) r ->
               _ >< \ t' ->
               r ~ (^ t') *
               R (p su) t t'
               
