module Tm where

open import Eq
open import Tuple
open import Thin

data Atom : Set where
  A0 A1 A2 PI SG TY : Atom  -- more later

_~Atom?~_ : (a b : Atom) ->  (a ~ b -> Zero) + (a ~ b)
A0 ~Atom?~ A0 = tt , r~
A0 ~Atom?~ A1 = ff , \ ()
A0 ~Atom?~ A2 = ff , \ ()
A0 ~Atom?~ PI = ff , \ ()
A0 ~Atom?~ SG = ff , \ ()
A0 ~Atom?~ TY = ff , \ ()
A1 ~Atom?~ A0 = ff , \ ()
A1 ~Atom?~ A1 = tt , r~
A1 ~Atom?~ A2 = ff , \ ()
A1 ~Atom?~ PI = ff , \ ()
A1 ~Atom?~ SG = ff , \ ()
A1 ~Atom?~ TY = ff , \ ()
A2 ~Atom?~ A0 = ff , \ ()
A2 ~Atom?~ A1 = ff , \ ()
A2 ~Atom?~ A2 = tt , r~
A2 ~Atom?~ PI = ff , \ ()
A2 ~Atom?~ SG = ff , \ ()
A2 ~Atom?~ TY = ff , \ ()
PI ~Atom?~ A0 = ff , \ ()
PI ~Atom?~ A1 = ff , \ ()
PI ~Atom?~ A2 = ff , \ ()
PI ~Atom?~ PI = tt , r~
PI ~Atom?~ SG = ff , \ ()
PI ~Atom?~ TY = ff , \ ()
SG ~Atom?~ A0 = ff , \ ()
SG ~Atom?~ A1 = ff , \ ()
SG ~Atom?~ A2 = ff , \ ()
SG ~Atom?~ PI = ff , \ ()
SG ~Atom?~ SG = tt , r~
SG ~Atom?~ TY = ff , \ ()
TY ~Atom?~ A0 = ff , \ ()
TY ~Atom?~ A1 = ff , \ ()
TY ~Atom?~ A2 = ff , \ ()
TY ~Atom?~ PI = ff , \ ()
TY ~Atom?~ SG = ff , \ ()
TY ~Atom?~ TY = tt , r~

data Dir : Set where chk syn : Dir

data Tm (n : Nat) : Dir -> Set where
  !_   : Atom -> Tm n chk
  _&_  : Tm n chk -> Tm n chk -> Tm n chk
  ^_   : Tm (n su) chk -> Tm n chk
  `_   : Tm n syn -> Tm n chk
  #_   : Fi n -> Tm n syn
  _$_  : Tm n syn -> Tm n chk -> Tm n syn
  _::_ : Tm n chk -> Tm n chk -> Tm n syn

infix 50 !_ #_
infixl 40 _$_
infixr 30 _&_ ^_ `_
infix 20 _::_

inj# : forall {n}{x y : Fi n} -> # x ~ # y -> x ~ y
inj# r~ = r~

record Action (_|>_ : Nat -> Nat -> Set) : Set where
  field
    _+1  : forall {n m} -> n |> m -> (n su) |> (m su)
    _#>_ : forall {n m} -> Fi n -> n |> m -> Tm m syn
    var+ : forall {n m}(al be : n |> m) ->
             (forall x -> (x #> al) ~ (x #> be)) ->
              forall x -> (x #> (al +1)) ~ (x #> (be +1))
  act : forall {n m d} -> Tm n d -> n |> m -> Tm m d
  act (! a)    al = ! a
  act (s & t)  al = act s al & act t al
  act (^ t)    al = ^ act t (al +1)
  act (` e)    al = ` act e al
  act (# x)    al = x #> al
  act (e $ s)  al = act e al $ act s al
  act (t :: T) al = act t al :: act T al

  actQ : forall {n m} -> n |> m -> n |> m -> Set
  actQ al be = forall x -> (x #> al) ~ (x #> be)

  actExt : forall {n m d}(t : Tm n d)(al be : n |> m) -> actQ al be ->
    act t al ~ act t be
  actExt (! a) al be q = r~
  actExt (s & t) al be q rewrite actExt s al be q | actExt t al be q = r~
  actExt (^ t) al be q rewrite actExt t (al +1) (be +1) (var+ al be q) = r~
  actExt (` e) al be q rewrite actExt e al be q = r~
  actExt (# x) al be q = q x
  actExt (e $ s) al be q rewrite actExt e al be q | actExt s al be q = r~
  actExt (t :: T) al be q rewrite actExt t al be q | actExt T al be q = r~

THIN : Action _<=_
Action._+1  THIN th = th su
Action._#>_ THIN x th = # (x ^^ th)
Action.var+ THIN al be q (x no) = `~ #_ ~$~ (`~ _no ~$~ inj# (q x))
Action.var+ THIN al be q (x su) = `~ #_ ~$~ (`~ _su ~$~ none~ _ _)

_^Tm_ = Action.act THIN

Sb : Nat -> Nat -> Set
Sb n m = (Fi n) -> Tm m syn

_+1Sb : forall {n m} -> Sb n m -> Sb (n su) (m su)
(sg +1Sb) (x no) = sg x ^Tm (iota no)
(sg +1Sb) (x su) = # (none su)

_+Sb_ : forall {n m} -> Sb n m -> forall p -> Sb (n +B p) (m +B p)
sg +Sb (n su) = (sg +Sb n) +1Sb
sg +Sb [] = sg

SBST : Action Sb
Action._+1 SBST sg = sg +1Sb
Action._#>_ SBST x sg = sg x
Action.var+ SBST al be q (x no) rewrite q x = r~
Action.var+ SBST al be q (x su) = r~

module _ where
  open Action SBST
  _/Tm_ = act
  extSb = actExt

  _/0_ : forall {n d} -> Tm (n su) d -> Tm n syn -> Tm n d
  t /0 e = t /Tm (#_ -push e)


module ACTID {_|>_ : Nat -> Nat -> Set}(A : Action _|>_)(ida : {n : Nat} -> n |> n)
  where
  open Action A
  module LAWS
    (varId : forall {n}(x : Fi n) -> (x #> ida) ~ # x)
    (wkId : forall {n} -> actQ (ida {n} +1) ida)
    where
    actId : forall {n d}(t : Tm n d) -> act t ida ~ t
    actId (! a)    = r~
    actId (s & t)  rewrite actId s | actId t = r~
    actId (^ t)    rewrite actExt t (ida +1) ida wkId | actId t = r~
    actId (` e)    rewrite actId e = r~
    actId (# x)    = varId x
    actId (e $ s)  rewrite actId e | actId s = r~
    actId (t :: T) rewrite actId t | actId T = r~

module _ where
  open ACTID THIN iota
  open LAWS (\ x -> `~ #_ ~$~ (x ^^iota)) (\ x -> r~)
  _^Tm-iota = actId

module _ where
  open ACTID SBST #_
  open LAWS (\ _ -> r~)
    (\ { (x no) -> `~ #_ ~$~ (`~ _no ~$~ (x ^^iota))
       ; (x su) -> `~ #_ ~$~ (`~ _su ~$~ none~ _ _) })
  _/Tm-# = actId

module ACTCOMP
  {_|A>_ : Nat -> Nat -> Set}(A : Action _|A>_)
  {_|B>_ : Nat -> Nat -> Set}(B : Action _|B>_)
  {_|C>_ : Nat -> Nat -> Set}(C : Action _|C>_)
  (co : forall {p n m} -> p |A> n -> n |B> m -> p |C> m)
  (var : forall {p n m}(x : Fi p)(al : p |A> n)(be : n |B> m) ->
    Action.act B (Action._#>_ A x al) be ~ Action._#>_ C x (co al be))
  (wk : forall {p n m}(al : p |A> n)(be : n |B> m) ->
        Action.actQ C (co (Action._+1 A al) (Action._+1 B be))
                      (Action._+1 C (co al be)))
  where
  actComp : forall {p n m d}(t : Tm p d)(al : p |A> n)(be : n |B> m) ->
              Action.act B (Action.act A t al) be ~
              Action.act C t (co al be)
  actComp (! a) al be = r~
  actComp (s & t) al be rewrite actComp s al be | actComp t al be = r~
  actComp (^ t) al be
    rewrite actComp t (Action._+1 A al) (Action._+1 B be)
          | Action.actExt C t _ _ (wk al be)
    = r~
  actComp (` e) al be rewrite actComp e al be = r~
  actComp (# x) al be = var x al be
  actComp (e $ s) al be rewrite actComp e al be | actComp s al be = r~
  actComp (t :: T) al be rewrite actComp t al be | actComp T al be = r~

module _ where
  open ACTCOMP THIN THIN THIN _^^_
    (\ x th ph -> #_ $~ sym (thinAssoc x th ph))
    (\ _ _ _ -> r~)
  thinThin = actComp

module _ where
  open ACTCOMP THIN SBST SBST (\ th sg x -> sg (x ^^ th))
    (\ _ _ _ -> r~)
    (\ { th sg (x no) -> r~
       ; th sg (x su) -> r~ })
  thinSbst = actComp

module _ where
  open ACTCOMP SBST THIN SBST (\ sg th x -> sg x ^Tm th)
    (\ _ _ _ -> r~)
    (\ { sg th (x no) -> 
          ((sg x ^Tm (iota no)) ^Tm (th su)) ~[ thinThin (sg x) _ _ >
          (sg x ^Tm (iota ^^ th no)) ~[ (sg x ^Tm_) $~ (_no $~
             ((iota ^^ th) ~[ iota^^ _ > th < _ ^^iota ]~ (th ^^ iota) [QED]))
              >
          (sg x ^Tm (th ^^ iota no)) < thinThin (sg x) _ _ ]~
          ((sg x ^Tm th) ^Tm (iota no)) [QED]
       ; sg th (x su) -> `~ #_ ~$~ (`~ _su ~$~ none~ _ _) } )
  sbstThin = actComp

module _ where
  open ACTCOMP SBST SBST SBST (\ sg ta x -> sg x /Tm ta)
    (\ _ _ _ -> r~)
    (\ { sg ta (x no) -> 
          ((sg x ^Tm (iota no)) /Tm (ta +1Sb)) ~[ thinSbst (sg x) _ _ >
          (sg x /Tm \ y -> (ta +1Sb) (y ^^ iota no)) ~[ 
             extSb (sg x) _ _ (\ y -> 
               (_^Tm (iota no)) $~ (ta $~ (y ^^iota))) >
          (sg x /Tm \ y -> ta y ^Tm (iota no)) < sbstThin (sg x) _ _ ]~
          ((sg x /Tm ta) ^Tm (iota no)) [QED]
       ; sg ta (x su) -> r~ })
  sbstSbst = actComp


stabSb0 : forall {n m d}(t : Tm (n su) d)(e : Tm n syn)(sg : Sb n m) ->
  ((t /Tm (sg +1Sb)) /0 (e /Tm sg)) ~ ((t /0 e) /Tm sg)
stabSb0 t e sg =
  ((t /Tm (sg +1Sb)) /0 (e /Tm sg)) ~[ sbstSbst t _ _ >
  (t /Tm \ x -> ((sg +1Sb) x /0 (e /Tm sg))) ~[ extSb t _ _
     (\ { (x no) -> ((sg x ^Tm (iota no)) /0 (e /Tm sg))
                      ~[ thinSbst (sg x) _ _ >
                    (sg x /Tm \ y -> # (y ^^ iota)) ~[ extSb (sg x) _ _
                       (\ y -> #_ $~ (y ^^iota)) >
                    (sg x /Tm #_) ~[ sg x /Tm-# >
                    sg x [QED]
        ; (x su) -> r~
        }) >
  (t /Tm \ x -> (#_ -push e) x /Tm sg) < sbstSbst t _ _ ]~
  ((t /0 e) /Tm sg) [QED] 

thSb : forall {n m d}(t : Tm n d)(th : n <= m) ->
       (t ^Tm th) ~ (t /Tm \ x -> # (x ^^ th))
thSb t th =
  (t ^Tm th) < (t ^Tm th) /Tm-# ]~
  ((t ^Tm th) /Tm #_) ~[ thinSbst t th #_ >
  (t /Tm \ x -> # (x ^^ th)) [QED]

locSb : forall {n p} m -> Sb m (n +B p) -> Sb (n +B (p +B m)) (n +B p)
locSb (m su) sg (i no) = locSb m (\ j -> sg (j -^ _)) i
locSb (m su) sg (i su) = sg (none su)
locSb [] sg i = # i

locSbExt : forall {n p} m (sg0 sg1 : Sb m (n +B p)) ->
           (forall i -> sg0 i ~ sg1 i) ->
           forall j -> locSb {n}{p} m sg0 j ~ locSb {n}{p} m sg1 j
locSbExt (m -, x) sg0 sg1 q (j -^ .x) = locSbExt m _ _ (\ i -> q (i -^ _)) j
locSbExt (m -, .<>) sg0 sg1 q (j -, .<>) = q (none su)
locSbExt [] sg0 sg1 q j = r~


_~Tm?~_ : forall {n d}(t0 t1 : Tm n d) ->  (t0 ~ t1 -> Zero) + (t0 ~ t1)
(! a0) ~Tm?~ (! a1) with a0 ~Atom?~ a1
((! a0) ~Tm?~ (! a1)) | ff , z = ff , \ { r~ -> z r~ }
((! a0) ~Tm?~ (! .a0)) | tt , r~ = tt , r~
(! _) ~Tm?~ (_ & _) = ff , \ ()
(! _) ~Tm?~ (^ _) = ff , \ ()
(! _) ~Tm?~ (` _) = ff , \ ()
(_ & _) ~Tm?~ (! x) = ff , \ ()
(s0 & t0) ~Tm?~ (s1 & t1) with s0 ~Tm?~ s1 | t0 ~Tm?~ t1
((s0 & t0) ~Tm?~ (s1 & t1)) | ff , zs | bt , zt = ff , \ { r~ -> zs r~ }
((s0 & t0) ~Tm?~ (s1 & t1)) | tt , zs | ff , zt = ff , \ { r~ -> zt r~ }
((s0 & t0) ~Tm?~ (.s0 & .t0)) | tt , r~ | tt , r~ = tt , r~
(_ & _) ~Tm?~ (^ _) = ff , \ ()
(_ & _) ~Tm?~ (` _) = ff , \ ()
(^ _) ~Tm?~ (! _) = ff , \ ()
(^ _) ~Tm?~ (_ & _) = ff , \ ()
(^ t0) ~Tm?~ (^ t1) with t0 ~Tm?~ t1
((^ t0) ~Tm?~ (^ t1)) | ff , z = ff , \ { r~ -> z r~ }
((^ t0) ~Tm?~ (^ .t0)) | tt , r~ = tt , r~
(^ _) ~Tm?~ (` _) = ff , \ ()
(` _) ~Tm?~ (! _) = ff , \ ()
(` _) ~Tm?~ (_ & _) = ff , \ ()
(` _) ~Tm?~ (^ _) = ff , \ ()
(` e0) ~Tm?~ (` e1) with e0 ~Tm?~ e1
((` e0) ~Tm?~ (` e1)) | ff , z = ff , \ { r~ -> z r~ }
((` e0) ~Tm?~ (` .e0)) | tt , r~ = tt , r~
(# x0) ~Tm?~ (# x1) with x0 ~Th?~ x1
((# x0) ~Tm?~ (# x1)) | ff , z = ff , \ { r~ -> z r~ }
((# x0) ~Tm?~ (# .x0)) | tt , r~ = tt , r~
(# _) ~Tm?~ (_ $ _) = ff , \ ()
(# _) ~Tm?~ (_ :: _) = ff , \ ()
(_ $ _) ~Tm?~ (# _) = ff , \ ()
(e0 $ s0) ~Tm?~ (e1 $ s1) with e0 ~Tm?~ e1 | s0 ~Tm?~ s1
((e0 $ s0) ~Tm?~ (e1 $ s1)) | ff , ez | bs , zs = ff , \ { r~ -> ez r~ }
((e0 $ s0) ~Tm?~ (e1 $ s1)) | tt , ez | ff , zs = ff , \ { r~ -> zs r~ }
((e0 $ s0) ~Tm?~ (.e0 $ .s0)) | tt , r~ | tt , r~ = tt , r~
(_ $ _) ~Tm?~ (_ :: _) = ff , \ ()
(_ :: _) ~Tm?~ (# _) = ff , \ ()
(_ :: _) ~Tm?~ (_ $ _) = ff , \ ()
(t0 :: T0) ~Tm?~ (t1 :: T1) with t0 ~Tm?~ t1 | T0 ~Tm?~ T1
((t0 :: T0) ~Tm?~ (t1 :: T1)) | ff , zt | bT , zT = ff , \ { r~ -> zt r~ }
((t0 :: T0) ~Tm?~ (t1 :: T1)) | tt , zt | ff , zT = ff , \ { r~ -> zT r~ }
((t0 :: T0) ~Tm?~ (.t0 :: .T0)) | tt , r~ | tt , r~ = tt , r~

Cx : Nat -> Set
Cx n = ([] su <= n) -> Tm n chk

C0 : Cx []
C0 = \ ()

_,^_ : forall {n} -> Cx n -> Tm n chk -> Cx (n su)
(G ,^ S) x = (G -push S) x ^Tm (iota no)

data Gdd {n} : forall {un ud} -> Tm un ud -> {-strictly?-}Two -> Tm n chk -> Set where
  hic : forall {t : Tm n chk} -> Gdd t ff t
  car : forall {b un}{us ut : Tm un chk}{t : Tm n chk} -> Gdd us b t -> Gdd (us & ut) tt t
  cdr : forall {b un}{us ut : Tm un chk}{t : Tm n chk} -> Gdd ut b t -> Gdd (us & ut) tt t
  bod : forall {b un}{ut : Tm (un su) chk}{t : Tm n chk} -> (S : Tm un chk) -> Gdd ut b t -> Gdd (^ ut) tt t
  arg : forall {b un ue}{us : Tm un chk}{t : Tm n chk} -> Gdd us b t -> Gdd (ue $ us) tt t

_-car : forall {n un ud b}{u : Tm un ud}{s t : Tm n chk} -> Gdd u b (s & t) -> Gdd u tt s
hic    -car = car hic
car g   -car = car (g -car)
cdr g   -car = cdr (g -car)
bod S g -car = bod S (g -car)
arg g   -car = arg (g -car)

_-cdr : forall {n un ud b}{u : Tm un ud}{s t : Tm n chk} -> Gdd u b (s & t) -> Gdd u tt t
hic    -cdr = cdr hic
car g   -cdr = car (g -cdr)
cdr g   -cdr = cdr (g -cdr)
bod S g -cdr = bod S (g -cdr)
arg g   -cdr = arg (g -cdr)

_-bod:_ : forall {n un ud b}{u : Tm un ud}{t : Tm (n su) chk} -> Gdd u b (^ t) -> Tm n chk -> Gdd u tt t
hic -bod: S = bod S hic
car g -bod: S = car (g -bod: S)
cdr g -bod: S = cdr (g -bod: S)
bod S' g -bod: S = bod S' (g -bod: S)
arg g -bod: S = arg (g -bod: S)

_+Cx_ : forall {n un ud b}{u : Tm un ud}{t : Tm n chk} -> Cx un -> Gdd u b t -> Cx n
G +Cx hic     = G
G +Cx car g   = G +Cx g
G +Cx cdr g   = G +Cx g
G +Cx bod S g = (G ,^ S) +Cx g
G +Cx arg g   = G +Cx g

Can : forall {n} -> Tm n chk -> Set
Can (` e) = Zero
Can _     = One

data TmRec : forall {n d} -> Tm n d -> Set where

  can : forall {un}{u : Tm un chk}
     -> Can u
     -> (forall {n}{t : Tm n chk} -> Gdd u tt t -> TmRec t)
     -> TmRec u

  emb : forall {n}{e : Tm n syn}
     -> TmRec e
     -> TmRec (` e)

  var : forall {n}(x : Fi n)
     -> TmRec (# x)

  eli : forall {n}{e : Tm n syn}{s : Tm n chk}
     -> TmRec e
     -> (forall {n}{t : Tm n chk} -> Gdd (e $ s) tt t -> TmRec t)
     -> TmRec (e $ s)

  rad : forall {n}{t T : Tm n chk}
     -> TmRec t
     -> TmRec T
     -> TmRec (t :: T)

memRec : forall {un ud n b}{u : Tm un ud}{t : Tm n chk} ->
         TmRec u -> Gdd u b t -> TmRec t
memRec u hic = u
memRec (can _ k) (car g)   = k (car g)
memRec (can _ k) (cdr g)   = k (cdr g)
memRec (can _ k) (bod S g) = k (bod S g)
memRec (eli _ k) (arg g)   = k (arg g)

tmRec : forall {n d}(t : Tm n d) -> TmRec t
tmRec (! a)    = can <> \ ()
tmRec (s & t)  = can <> \ { (car g) -> memRec (tmRec s) g  ; (cdr g) -> memRec (tmRec t) g }
tmRec (^ t)    = can <> \ { (bod S g) -> memRec (tmRec t) g }
tmRec (` e)    = emb (tmRec e)
tmRec (# x)    = var x
tmRec (e $ s)  = eli (tmRec e) \ { (arg g) -> memRec (tmRec s) g }
tmRec (t :: T) = rad (tmRec t) (tmRec T)

