module Thin where

open import Eq
open import Tuple

data Bwd (X : Set) : Set where
  _-,_ : Bwd X -> X -> Bwd X
  []  :  Bwd X

infixl 19 _-,_

module _ {X : Set} where

  _+B_ : Bwd X -> Bwd X -> Bwd X
  n +B (m -, x) = n +B m -, x
  n +B []       = n

  infix 4 _<=_ _<-_
  infixl 19 _-^_ _+B_ _+th_

  data _<=_ : Bwd X -> Bwd X -> Set where
    _-^_ : forall {n m} -> n <= m -> (x : X) -> n      <= m -, x
    _-,_ : forall {n m} -> n <= m -> (x : X) -> n -, x <= m -, x
    []   : [] <= []

  _<-_ : X -> Bwd X -> Set
  x <- n = [] -, x <= n

  _+th_ : forall {n m} -> n <= m -> forall p -> n +B p <= m +B p
  th +th (p -, x) = th +th p -, x
  th +th [] = th

  iota : forall {n} -> n <= n
  iota {n -, x} = iota -, x
  iota {[]}     = []

  none : forall {n} -> [] <= n
  none {n -, x} = none -^ x
  none {[]}     = []

  none~ : forall {n}(th ph : [] <= n) -> th ~ ph
  none~ (th -^ x) (ph -^ .x) = (_-^ _) $~ none~ th ph
  none~ [] []                = r~

  thinr : forall {n m} -> m <= n +B m
  thinr {m = m -, x} = thinr -, x
  thinr {m = []} = none

  infixl 20 _^^_
  _^^_ : forall {p n m} -> p <= n -> n <= m -> p <= m
  th        ^^ (ph -^ x) = th ^^ ph -^ x
  (th -^ x) ^^ (ph -, .x) = th ^^ ph -^ x
  (th -, x) ^^ (ph -, .x) = th ^^ ph -, x
  []        ^^ []      = []

  pred : forall {n m x} -> n -, x <= m -> n <= m
  pred (th -^ x) = pred th -^ x
  pred (th -, x) = th -^ x

  antiSym : forall {n m}(th : n <= m)(ph : m <= n) ->
    (n ~ m) >< \ { r~ -> th ~ iota * ph ~ iota }
  antiSym (th -, x) (ph -, x) with r~ , r~ , r~ <- antiSym th ph = r~ , r~ , r~
  antiSym [] [] = r~ , r~ , r~
  antiSym (th -^ x) ph      with antiSym th (pred ph)
  antiSym (th -^ x) (ph -^ y) | r~ , _ , ()
  antiSym (th -^ x) (ph -, y) | r~ , _ , ()
  antiSym th      (ph -^ x) with antiSym (pred th) ph
  antiSym (th -^ x) (ph -^ y) | r~ , () , _
  antiSym (th -, x) (ph -^ y) | r~ , () , _


  thinAssoc : forall {q p n m}(th : q <= p)(ph : p <= n)(ps : n <= m) ->
    (th ^^ (ph ^^ ps)) ~ (th ^^ ph ^^ ps)
  thinAssoc th ph (ps -^ x) rewrite thinAssoc th ph ps = r~
  thinAssoc th (ph -^ x) (ps -, x) rewrite thinAssoc th ph ps = r~
  thinAssoc (th -^ x) (ph -, x) (ps -, x) rewrite thinAssoc th ph ps = r~
  thinAssoc (th -, x) (ph -, x) (ps -, x) rewrite thinAssoc th ph ps = r~
  thinAssoc [] [] [] = r~

  none^^ : forall {n m}(th : n <= m) -> (none ^^ th) ~ none
  none^^ (th -^ x) rewrite none^^ th = r~
  none^^ (th -, x) rewrite none^^ th = r~
  none^^ [] = r~

  iota^^ : forall {n m}(th : n <= m) -> (iota ^^ th) ~ th
  iota^^ (th -^ x) rewrite iota^^ th = r~
  iota^^ (th -, x) rewrite iota^^ th = r~
  iota^^ [] = r~

  _^^iota : forall {n m}(th : n <= m) -> (th ^^ iota) ~ th
  _^^iota (th -^ x) rewrite _^^iota th = r~
  _^^iota (th -, x) rewrite _^^iota th = r~
  _^^iota [] = r~

  thinrLemma : forall {n m}(th : n <= m) p -> (thinr {_}{p} ^^ (th +th p)) ~ thinr
  thinrLemma th (p -, x) = (_-, _) $~ thinrLemma th p
  thinrLemma th [] = none~ _ _

  infixl 17 _-push_
  _-push_ : forall {n y}{T : forall x -> x <- n -, y -> Set} ->
    (forall {x}(i : x <- n) -> T x (i -^ y)) ->
    ({i : [] <= n} -> T y (i -, y)) ->
    forall {x}(i : x <- n -, y) -> T x i
  (ga -push c) (i -^ y) = ga i
  (ga -push c) (i -, y) = c

  _~Th?~_ : forall {n m}(th ph : n <= m) -> (th ~ ph -> Zero) + (th ~ ph)
  (th -^ x) ~Th?~ (ph -^ x) with th ~Th?~ ph
  ((th -^ x) ~Th?~ (ph -^ x)) | ff , z = ff , \ { r~ -> z r~ }
  ((th -^ x) ~Th?~ (.th -^ x)) | tt , r~ = tt , r~
  (th -^ x) ~Th?~ (ph -, x) = ff , \ ()
  (th -, x) ~Th?~ (ph -^ x) = ff , \ ()
  (th -, x) ~Th?~ (ph -, x) with th ~Th?~ ph
  ((th -, x) ~Th?~ (ph -, x)) | ff , z = ff , \ { r~ -> z r~ }
  ((th -, x) ~Th?~ (.th -, x)) | tt , r~ = tt , r~
  [] ~Th?~ [] = tt , r~

  assoc+B : forall xz yz zz -> (xz +B (yz +B zz)) ~ (xz +B yz +B zz)
  assoc+B xz yz (zz -, x) = (_-, _) $~ assoc+B xz yz zz
  assoc+B xz yz [] = r~

  snocInj : forall {xz yz : Bwd X}{x y : X} -> _~_ {_}{Bwd X} (xz -, x) (yz -, y) -> (xz ~ yz) * (x ~ y)
  snocInj r~ = r~ , r~

  noCycle : (xz yz : Bwd X)(y : X) -> xz ~ (xz +B yz -, y) -> Zero
  noCycle (xz -, x) yz y q with snocInj q
  noCycle (xz -, x) (yz -, y) .x q | q' , r~ with noCycle xz (([] -, x) +B yz) y
  ... | h rewrite assoc+B xz ([] -, x) yz = h q'
  noCycle [] yz y ()

  canSuffix : forall xz yz zz -> (xz +B yz) ~ (xz +B zz) -> yz ~ zz
  canSuffix xz (yz -, y) (zz -, z) q with snocInj q
  ... | qz , r~ = (_-, _) $~ canSuffix xz yz zz qz
  canSuffix xz (yz -, y) [] q with noCycle xz yz y (sym q)
  ... | ()
  canSuffix xz [] (zz -, z) q with noCycle xz zz z q
  ... | ()
  canSuffix xz [] [] q = r~

Nat = Bwd One
pattern _no th = th -^ <>
pattern _su n = n -, <>
infixl 19 _no _su

Fi : Nat -> Set
Fi n = <> <- n
