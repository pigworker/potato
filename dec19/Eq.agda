module Eq where

data _~_ {l}{X : Set l}(x : X) : X -> Set l where
  r~ : x ~ x

{-# BUILTIN EQUALITY _~_ #-}

_~$~_ : forall {k l}{S : Set k}{T : Set l}
  {f g : S -> T}{a b : S} -> f ~ g -> a ~ b -> f a ~ g b
r~ ~$~ r~ = r~

`~_ : forall {l}{X : Set l}(x : X) -> x ~ x
`~ _ = r~

infixl 1 _~$~_
infix 2 `~_

_$~_ : forall {k l}{S : Set k}{T : Set l}
  (f : S -> T){a b : S} -> a ~ b -> f a ~ f b
f $~ q = `~ f ~$~ q

sym : forall {l}{X : Set l}{x y : X} -> x ~ y -> y ~ x
sym r~ = r~

subst : forall {k l}{X : Set k}(P : X -> Set l){x y : X} ->
  x ~ y -> P x -> P y
subst P r~ p = p

_~[_>_ : forall {l}{X : Set l}(x : X){y z : X} -> x ~ y -> y ~ z -> x ~ z
x ~[ r~ > q = q

_<_]~_ : forall {l}{X : Set l}(x : X){y z : X} -> y ~ x -> y ~ z -> x ~ z
x < r~ ]~ q = q

_[QED] : forall {l}{X : Set l}(x : X) -> x ~ x
_ [QED] = r~

infixr 1 _~[_>_ _<_]~_
infixr 2 _[QED]
