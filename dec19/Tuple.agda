module Tuple where

record One : Set where constructor <>

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public

_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T

infixr 2 _><_ _,_ _*_

data Zero : Set where

data Two : Set where ff tt : Two

_+_ : Set -> Set -> Set
S + T = Two >< \ { ff -> S ; tt -> T }

infixr 1 _>>=_
_>>=_ : forall {X Y} -> One + X -> (X -> One + Y) -> One + Y
ff , <> >>= k = ff , <>
tt , x  >>= k = k x

data Star {X : Set}(R : X -> X -> Set)(x : X) : X -> Set where
  [] : Star R x x
  _,-_ : forall {y z} -> R x y -> Star R y z -> Star R x z

_++_ : forall {X}{R : X -> X -> Set}{x y z : X} ->
  Star R x y -> Star R y z -> Star R x z
[] ++ ss = ss
(r ,- rs) ++ ss = r ,- (rs ++ ss)

infixr 4 _++_ _,-_

starB : forall {X Y : Set}{R : X -> X -> Set}{S : Y -> Y -> Set}
  (F : X -> Y)(f : forall {x y} -> R x y -> Star S (F x) (F y)) ->
  forall {x y} -> Star R x y -> Star S (F x) (F y)
starB F f [] = []
starB F f (r ,- rs) = f r ++ starB F f rs

star : forall {X Y : Set}{R : X -> X -> Set}{S : Y -> Y -> Set}
  (F : X -> Y)(f : forall {x y} -> R x y -> S (F x) (F y)) ->
  forall {x y} -> Star R x y -> Star S (F x) (F y)
star F f rs = starB F (\ r -> f r ,- []) rs

List : Set -> Set
List X = Star {One} (\ _ _ -> X) <> <>
