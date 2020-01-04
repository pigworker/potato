module Basics where

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

data ListR {X}{Y}(R : X -> Y -> Set) : List X -> List Y -> Set where
  [] : ListR R [] []
  _,-_ : forall {x xs y ys} -> R x y -> ListR R xs ys -> ListR R (x ,- xs) (y ,- ys)

_++R_ : forall {X Y}{R : X -> Y -> Set}
         {xs0 ys0 xs1 ys1}
       -> ListR R xs0 ys0
       -> ListR R xs1 ys1
       -> ListR R (xs0 ++ xs1) (ys0 ++ ys1)
[] ++R ys = ys
(x ,- xs) ++R ys = x ,- (xs ++R ys)
          

id : forall {l}{X : Set l} -> X -> X
id x = x

{-
_&&_ : Two -> Two -> Two
tt && b = b
ff && b = ff
infixr 4 _&&_

not : Two -> Two
not tt = ff
not ff = tt
-}
