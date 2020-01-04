module Tm where

open import Eq
open import Thin
open import Atom
open import Basics

data Dir : Set where
  chk syn : Dir
  _**_ : Dir -> Nat -> Dir

data Pair : Dir -> Dir -> Dir -> Set where
  cons : Pair chk chk chk
  elim : Pair syn chk syn
  radi : Pair chk chk syn
  vect : forall {d n} -> Pair (d ** n) d (d ** (n su))

module _ {M : Nat -> Set}
  where

  data Tm (n : Nat) : Dir -> Set where

    pair : forall {dl dr dp} -> Pair dl dr dp ->
           Tm n dl -> Tm n dr -> Tm n dp

    !_   : Atom -> Tm n chk
    ^_   : Tm (n su) chk -> Tm n chk

    [_]  : Tm n syn -> Tm n chk

    #_   : Fi n -> Tm n syn

    _/_  : forall {m} -> M m -> Tm n (syn ** m) ->
           Tm n chk

    []   : forall {d} -> Tm n (d ** [])

  pattern _&_  s t = pair cons s t
  pattern _$_  e s = pair elim e s
  pattern _::_ t T = pair radi t T
  pattern _`_ sg e = pair vect sg e
  infixr 4 _&_
  infixl 5 _$_
  infix 3 _::_
  infixl 2 _`_

  _=>_ : Nat -> Nat -> Set
  n => m = Tm m (syn ** n)

  -- should probably generalise sel

  sel : forall {p n m} -> p <= n -> n => m -> p => m
  sel (th -^ .<>) (sg ` e) = sel th sg
  sel (th -, .<>) (sg ` e) = sel th sg ` e
  sel [] [] = []

  seliota : forall {n m}(sg : n => m) -> sel iota sg ~ sg
  seliota [] = r~
  seliota (sg ` e) = (_` e) $~ seliota sg

  sel^^ : forall {p n m l}(th : p <= n)(ph : n <= m)(sg : m => l) ->
    sel (th ^^ ph) sg ~ sel th (sel ph sg)
  sel^^ th (ph no) (sg ` e) = sel^^ th ph sg
  sel^^ (th no) (ph su) (sg ` e) = sel^^ th ph sg
  sel^^ (th su) (ph su) (sg ` e) = (_` _) $~ sel^^ th ph sg
  sel^^ [] [] [] = r~

  selnone : forall {n m}(sg : n => m) -> sel none sg ~ []
  selnone (sg ` _) = selnone sg
  selnone [] = r~

  top : forall {d n} -> Tm n (d ** ([] su)) -> Tm n d
  top (_ ` e) = e

  record ThinAlg (A : Nat -> Nat -> Set) : Set where
    field
      miss : forall {n m} -> A n m -> A n (m su)
      succ : forall {n m} -> A n m -> A (n su) (m su)
      zero : A [] []

    thin : forall {n m} -> n <= m -> A n m
    thin (th -^ x) = miss (thin th)
    thin (th -, x) = succ (thin th)
    thin [] = zero

  module _ {A}(ThA : ThinAlg A) where

    open ThinAlg ThA

    record Act : Set where
      field
        junk : forall {p n m} -> p <= n -> A n m -> A p m
        vari : forall {m} -> A ([] su) m -> Tm m syn
        junkZe : junk [] zero ~ zero
        junkNo : forall {p n m}(th : p <= n)(al : A n m) ->
          junk th (miss al) ~ miss (junk th al)
        junkNoSu : forall {p n m}(th : p <= n)(al : A n m) ->
          junk (th no) (succ al) ~ miss (junk th al)
        junkSuSu : forall {p n m}(th : p <= n)(al : A n m) ->
          junk (th su) (succ al) ~ succ (junk th al)
        junkiota : forall {n m}(al : A n m) -> junk iota al ~ al
        junk^^ : forall {p n m l}(th : p <= n)(ph : n <= m)(al : A m l) ->
          junk (th ^^ ph) al ~ junk th (junk ph al)
        succTop : forall {m}(al : A [] m) ->
          vari (succ al) ~ (# (none su))
        variThin : forall {n}(x : Fi n) ->
          vari (thin x) ~ (# x)

      act : forall {d n m} -> Tm n d -> A n m -> Tm m d
      act (! a) al = ! a
      act (pair p s t) al = pair p (act s al) (act t al)
      act (^ t) al = ^ act t (succ al)
      act [ e ] al = [ act e al ]
      act (# x) al = vari (junk x al)
      act (m / es) al = m / act es al
      act [] al = []

      selAct : forall {p n m l}(th : p <= n)(sg : n => m)(al : A m l) ->
               sel th (act sg al) ~ act (sel th sg) al
      selAct (th no) (sg ` e) al = selAct th sg al
      selAct (th su) (sg ` e) al = (_` _) $~ selAct th sg al
      selAct [] [] al = r~

      actTop : forall {n m} -> (sg : ([] su) => n)(al : A n m) ->
               act (top sg) al ~ top (act sg al)
      actTop ([] ` e) al = r~

  ThinA : ThinAlg _<=_
  ThinAlg.miss ThinA = _no
  ThinAlg.succ ThinA = _su
  ThinAlg.zero ThinA = []

  thinThin : forall {n m}(th : n <= m) ->
    ThinAlg.thin ThinA th ~ th
  thinThin (th no) = _no $~ thinThin th
  thinThin (th su) = _su $~ thinThin th
  thinThin [] = r~

  Thin : Act ThinA
  Act.junk Thin = _^^_
  Act.vari Thin = #_
  Act.junkZe Thin = r~
  Act.junkNo Thin _ _ = r~
  Act.junkNoSu Thin _ _ = r~
  Act.junkSuSu Thin _ _ = r~
  Act.junkiota Thin al = iota^^ al
  Act.junk^^ Thin th ph al = sym (thinAssoc th ph al)
  Act.succTop Thin _ = #_ $~ (_su $~ none~ _ _)
  Act.variThin Thin x = #_ $~ thinThin x

  _^Tm_ = Act.act Thin

  SbstA : ThinAlg _=>_
  ThinAlg.miss SbstA sg = sg ^Tm (iota no)
  ThinAlg.succ SbstA sg = sg ^Tm (iota no) ` (# (none su))
  ThinAlg.zero SbstA = []

  thsb : forall {n m} -> n <= m -> n => m
  thsb = ThinAlg.thin SbstA 

  Sbst : Act SbstA
  Act.junk Sbst = sel
  Act.vari Sbst = top
  Act.junkZe Sbst = r~
  Act.junkNo Sbst th sg = Act.selAct Thin th sg (iota no)
  Act.junkNoSu Sbst th sg = Act.selAct Thin th sg (iota no)
  Act.junkSuSu Sbst th sg = (_` _) $~ Act.selAct Thin th sg (iota no)
  Act.junkiota Sbst = seliota
  Act.junk^^ Sbst = sel^^
  Act.succTop Sbst _ = r~
  Act.variThin Sbst (x no) = 
    top (ThinAlg.thin SbstA x ^Tm (iota no))
      < Act.actTop Thin (ThinAlg.thin SbstA x) (iota no) ]~
    (top (ThinAlg.thin SbstA x) ^Tm (iota no))
      ~[ (_^Tm (iota no)) $~ Act.variThin Sbst x >
    ((# x) ^Tm (iota no)) ~[ #_ $~ (_no $~ (x ^^iota)) >
    (# (x no)) [QED]
  Act.variThin Sbst (x su) = #_ $~ (_su $~ none~ _ _)

  _/Tm_ = Act.act Sbst

  module ACTID
    {A : Nat -> Nat -> Set}
    {ThA : ThinAlg A}
    (ActA : Act ThA)
    (acti : forall {n} -> A n n)
    where

    open ThinAlg ThA
    open Act ActA
    
    module LAWS
      (zeroId : acti {[]} ~ zero)
      (succId : forall {n} -> acti {n su} ~ succ (acti {n}))
      where

      junkThin : forall {n m}(th : n <= m) -> junk th acti ~ thin th
      junkThin (th no) =
        junk (th no) acti ~[ junk (th no) $~ succId >
        junk (th no) (succ acti) ~[ junkNoSu th acti >
        miss (junk th acti) ~[ miss $~ junkThin th >
        thin (th no) [QED]
      junkThin (th su) = 
        junk (th su) acti ~[ junk (th su) $~ succId >
        junk (th su) (succ acti) ~[ junkSuSu th acti >
        succ (junk th acti) ~[ succ $~ junkThin th >
        thin (th su) [QED]
      junkThin [] = 
        junk [] acti ~[ junk [] $~ zeroId >
        junk [] zero ~[ junkZe >
        thin [] [QED]

      actId : forall {d n}(t : Tm n d) -> act t acti ~ t
      actId (# x) = 
        vari (junk x acti) ~[ vari $~ junkThin x >
        vari (thin x) ~[ variThin x >
        (# x) [QED]
      actId (^ t) = ^_ $~ (
        act t (succ acti) < act t $~ succId ]~
        act t acti ~[ actId t >
        t [QED])
      actId (! a) = r~
      actId (pair p s t) = pair p $~ actId s ~$~ actId t
      actId [ e ] = [_] $~ actId e
      actId (m / es) = (m /_) $~ actId es
      actId [] = r~

  module _ where
    open ACTID Thin iota
    open LAWS r~ r~
    thinId = actId

  idsb : forall {n} -> n => n
  idsb = thsb iota

  module _ where
    open ACTID Sbst idsb
    open LAWS r~ r~
    sbstId = actId

  module ACTCO
    {A B C}{ThA : ThinAlg A}{ThB : ThinAlg B}{ThC : ThinAlg C}
    (ActA : Act ThA)(ActB : Act ThB)(ActC : Act ThC)
    -- (GA : Good ActA)(GB : Good ActB)(GC : Good ActC)
    (co : forall {p n m} -> A p n -> B n m -> C p m)
    where
    open ThinAlg
    open Act
    module LAWS
      (variCo : forall {p n m}
        (x : Fi p)(a : A p n)(b : B n m) ->
        act ActB (vari ActA (junk ActA x a)) b ~
        vari ActC (junk ActC x (co a b)))
      (succCo : forall {p n m}(a : A p n)(b : B n m) ->
        (co (succ ThA a) (succ ThB b)) ~ (succ ThC (co a b)))
      where

      actCo : forall {d p n m}(t : Tm p d)
                (a : A p n)(b : B n m) ->
                act ActB (act ActA t a) b ~
                act ActC t (co a b)
      actCo (# x) a b = variCo x a b
      actCo (^ t) a b = ^_ $~ (
        act ActB (act ActA t (succ ThA a)) (succ ThB b) ~[ actCo t _ _ >
        act ActC t (co (succ ThA a) (succ ThB b)) ~[ act ActC t $~ succCo a b >
        act ActC t (succ ThC (co a b)) [QED])
      actCo (! _) a b = r~
      actCo (pair p s t) a b = pair p $~ actCo s a b ~$~ actCo t a b
      actCo [ e ] a b = [_] $~ actCo e a b
      actCo (m / es) a b = (m /_) $~ actCo es a b
      actCo [] a b = r~

  module _ {A}{ThA : ThinAlg A}(ActA : Act ThA) where
    open ThinAlg ThA
    open Act ActA
    open ACTCO Thin ActA ActA junk
    open LAWS
      (\ x a b -> vari $~ junk^^ x a b)
      junkSuSu
    thin- = actCo

  module SHOOGLE {A}{ThA : ThinAlg A}(ActA : Act ThA)
    (shoogle : forall {d n m}(t : Tm n d)(al : A n m) ->
       Act.act ActA t (ThinAlg.miss ThA al) ~
       (Act.act ActA t al ^Tm (iota no)))
    where
    open ThinAlg ThA
    open Act ActA
    open ACTCO Sbst ActA Sbst act
    open LAWS
      (\ x a b -> 
           act (top (sel x a)) b ~[ actTop (sel x a) b >
           top (act (sel x a) b) < top $~ selAct x a b ]~
           top (sel x (act a b)) [QED])
      (\ a b -> _`_
        $~  (act (a ^Tm (iota no)) (succ b) ~[ thin- ActA a (iota no) (succ b) >
             act a (junk (iota no) (succ b)) ~[ act a $~ junkNoSu iota b >
             act a (miss (junk iota b)) ~[ act a $~ (miss $~ junkiota b) >
             act a (miss b) ~[ shoogle a b >
             (act a b ^Tm (iota no)) [QED])
        ~$~ (vari (junk (none su) (succ b)) ~[ vari $~ junkSuSu none b >
             vari (succ (junk none b)) ~[ succTop _ >
             (# (none su)) [QED]))
    sbst- = actCo

  module _ where
    open ThinAlg ThinA
    open Act Thin
    open SHOOGLE Thin
      (\ t th ->
        (t ^Tm (th no)) < (t ^Tm_) $~ (_no $~ (th ^^iota)) ]~
        (t ^Tm (th ^^ iota no)) < thin- Thin t th (iota no) ]~
        ((t ^Tm th) ^Tm (iota no)) [QED])
    sbst-thin = sbst-

  module _ where
    open ThinAlg SbstA
    open Act Sbst
    open SHOOGLE Sbst
      (\ t sg -> 
         (t /Tm miss sg) < sbst-thin t sg (iota no) ]~
         ((t /Tm sg) ^Tm (iota no)) [QED])
    sbst-sbst = sbst-

  thsb/Tm : forall {n m l}(th : n <= m)(sg : m => l) ->
    (thsb th /Tm sg) ~ sel th sg
  thsb/Tm (th -^ x) (sg ` e) = 
    ((thsb th ^Tm (iota no)) /Tm (sg ` e))
      ~[ thin- Sbst (thsb th) _ _ >
    (thsb th /Tm sel (iota no) (sg ` e))
      ~[ thsb/Tm th _ >
    sel th (sel iota sg)
      ~[ sel th $~ seliota sg >
    sel th sg [QED]
  thsb/Tm (th -, x) (sg ` e) = (_` e) $~ (
    ((thsb th ^Tm (iota no)) /Tm (sg ` e))
      ~[ thin- Sbst (thsb th) _ _ >
    (thsb th /Tm sel (iota no) (sg ` e))
      ~[ thsb/Tm th _ >
    sel th (sel iota sg)
      ~[ sel th $~ seliota sg >
    sel th sg [QED])
  thsb/Tm [] [] = r~

  idsb/Tm : forall {n m}(sg : n => m) ->
    (idsb /Tm sg) ~ sg
  idsb/Tm sg =
    (idsb /Tm sg)
      ~[ thsb/Tm iota sg >
    sel iota sg
      ~[ seliota sg >
    sg
      [QED]

  _+sb_ : forall {n m p} -> n => p -> m => p -> (n +B m) => p
  sg +sb [] = sg
  sg +sb (ta ` e) = (sg +sb ta) ` e

  sel-cat-l : forall {n m p}(sg : n => p)(ta : m => p) ->
    sel thinl (sg +sb ta) ~ sg
  sel-cat-l sg (ta ` e) = sel-cat-l sg ta
  sel-cat-l sg [] = seliota sg

  sel-cat-r : forall {n m p}(sg : n => p)(ta : m => p) ->
    sel thinr (sg +sb ta) ~ ta
  sel-cat-r sg (ta ` e) = (_` _) $~ sel-cat-r sg ta
  sel-cat-r sg [] = selnone sg

  _#sb_ : forall {n0 m0 n1 m1} ->
          n0 => m0 -> n1 => m1 ->
          (n0 +B n1) => (m0 +B m1)
  sg #sb ta = (sg ^Tm thinl) +sb (ta ^Tm thinr)

  catTh : forall {n m p l}(sg : n => p)(ta : m => p)(th : p <= l) ->
    ((sg +sb ta) ^Tm th) ~ ((sg ^Tm th) +sb (ta ^Tm th))
  catTh sg (ta ` e) th = (_` _) $~ catTh sg ta th
  catTh sg [] th = r~

  catSb : forall {n m p l}(sg : n => p)(ta : m => p)(rh : p => l) ->
    ((sg +sb ta) /Tm rh) ~ ((sg /Tm rh) +sb (ta /Tm rh))
  catSb sg (ta ` e) rh = (_` _) $~ catSb sg ta rh
  catSb sg [] rh = r~

Inst : (Nat -> Set) -> (Nat -> Set) -> (Nat -> Set)
Inst M N m = forall {n} -> M n -> Tm{N} (m +B n) chk

_!Tm_ : forall {M N d n m} ->
       Tm{M} n d ->
       Inst M N m ->
       Tm{N} (m +B n) d
(w / t) !Tm pi = pi w /Tm ((idsb ^Tm thinl) +sb (t !Tm pi))
(pair p s t) !Tm pi = pair p (s !Tm pi) (t !Tm pi)
(! a) !Tm pi = ! a
(^ t) !Tm pi = ^ (t !Tm pi)
[ e ] !Tm pi = [ e !Tm pi ]
(# x) !Tm pi = # (x ^^ thinr)
[] !Tm pi = []

module INSTSTABLE {N M n m}
  (R : forall {d} l -> Tm{N} (n +B l) d -> Tm{M} (m +B l) d -> Set)
  where

  record InstStable : Set where
    field
      rePair : forall {dl dr d l s0 s1 t0 t1} ->
        (p : Pair dl dr d) ->
        R {dl} l s0 s1 -> R {dr} l t0 t1 ->
        R {d} l (pair p s0 t0) (pair p s1 t1)
      reAtom : forall a {l} -> R l (! a) (! a)
      reAbst : forall {l t0 t1} ->
        R (l su) t0 t1 -> R l (^ t0) (^ t1)
      reTurn : forall {l e0 e1} ->
        R l e0 e1 -> R l [ e0 ] [ e1 ]
      reLoca : forall {l}(x : Fi l) ->
        R l (# (x ^^ thinr)) (# (x ^^ thinr))
      reSbst : forall {k l t0 t1 es0 es1} ->
        R {chk} k t0 t1 -> R l es0 es1 ->
        R l (t0 /Tm ((idsb {_}{n} ^Tm thinl) +sb es0))
            (t1 /Tm ((idsb {_}{m} ^Tm thinl) +sb es1))
      reNull : forall {d l} -> R l ([] {d = d}) ([] {d = d})

    instStab : forall {L l d}(t : Tm{L} l d)
      (pi0 : Inst L N n)(pi1 : Inst L M m)
      (pi : forall {l}(w : L l) -> R l (pi0 w) (pi1 w)) ->
      R l (t !Tm pi0) (t !Tm pi1)
    instStab (pair p s t) pi0 pi1 pi =
      rePair p (instStab s pi0 pi1 pi) (instStab t pi0 pi1 pi)
    instStab (! a) pi0 pi1 pi = reAtom a
    instStab (^ t) pi0 pi1 pi = reAbst (instStab t pi0 pi1 pi)
    instStab [ e ] pi0 pi1 pi = reTurn (instStab e pi0 pi1 pi)
    instStab (# x) pi0 pi1 pi = reLoca x
    instStab (w / es) pi0 pi1 pi = reSbst (pi w) (instStab es pi0 pi1 pi)
    instStab [] pi0 pi1 pi = reNull

module _ {M : Nat -> Set}{n m : Nat}(sg : _=>_ {M} n m) where

  sb+ : (l : Nat) -> _=>_ {M} (n +B l) (m +B l)
  sb+ [] = sg
  sb+ (l su) = ThinAlg.succ SbstA (sb+ l)

  sb+bis : (l : Nat) -> sb+ l ~ (sg #sb idsb)
  sb+bis (l su) = _`_
    $~ ( (sb+ l ^Tm (iota no))
            ~[ (_^Tm (iota no)) $~ (sb+bis l) >
         ((sg #sb idsb) ^Tm (iota no))
            ~[ catTh (sg ^Tm thinl) (idsb ^Tm thinr) (iota no) >
         (((sg ^Tm thinl) ^Tm (iota no)) +sb ((idsb ^Tm thinr) ^Tm (iota no)))
            ~[ _+sb_
              $~ (((sg ^Tm thinl) ^Tm (iota no))
                     ~[ thin- Thin sg thinl (iota no) >
                   (sg ^Tm (thinl ^^ iota no))
                     ~[ (sg ^Tm_) $~ (_no $~ (thinl ^^iota)) >
                   (sg ^Tm thinl)
                     [QED])
              ~$~ (((idsb ^Tm thinr) ^Tm (iota no))
                    ~[ thin- Thin idsb thinr (iota no) >
                   (idsb ^Tm (thinr ^^ iota no))
                    ~[ (idsb ^Tm_) $~ (_no $~ (thinr ^^iota)) >
                   (idsb ^Tm (thinr no))
                    < (idsb ^Tm_) $~ (_no $~ (iota^^ thinr)) ]~
                   (idsb ^Tm (iota ^^ thinr no))
                    < thin- Thin idsb (iota no) (thinr su) ]~
                   ((idsb ^Tm (iota no)) ^Tm (thinr su))
                    [QED])
             >            
         ((sg ^Tm thinl) +sb ((idsb ^Tm (iota no)) ^Tm (thinr su)))
           [QED] )
    ~$~ (#_ $~ (_su $~ none~ _ _))
  sb+bis [] = sym (thinId sg)

  open INSTSTABLE {M}{M}{n}{m} (\ l s t ->
    t ~ (s /Tm sb+ l) )

  open InstStable

  sbstStable : InstStable
  rePair sbstStable p r~ r~ = r~
  reAtom sbstStable a = r~
  reAbst sbstStable r~ = r~
  reNull sbstStable = r~
  reTurn sbstStable r~ = r~
  reLoca sbstStable {l su}(x no) with ih <- (_^Tm (iota no)) $~ reLoca sbstStable x
    = (# (x ^^ thinr no)) < #_ $~ (_no $~ (_ ^^iota)) ]~
      (# (x ^^ thinr ^^ iota no)) ~[ ih >
      (top (sel (x ^^ thinr) (sb+ l)) ^Tm (iota no))
        ~[ Act.actTop Thin (sel (x ^^ thinr) (sb+ l)) (iota no) >
      top (sel (x ^^ thinr) (sb+ l) ^Tm (iota no))
        < top $~ Act.selAct Thin (x ^^ thinr) (sb+ l) (iota no) ]~
      top (sel (x ^^ thinr) (sb+ l ^Tm (iota no))) [QED]
  reLoca sbstStable (x su) = #_ $~ (_su $~ none~ _ _)
  reSbst sbstStable {k} {l} {t0} {es0 = es0} r~ r~
    rewrite sb+bis k | sb+bis l =
    ((t0 /Tm (sg #sb idsb)) /Tm ((idsb ^Tm thinl) +sb (es0 /Tm (sg #sb idsb))))
      ~[ sbst-sbst t0 _ _ >
    (t0 /Tm _) < (t0 /Tm_) $~ (
            (((idsb ^Tm thinl) +sb es0) /Tm (sg #sb idsb))
        ~[ catSb ((idsb ^Tm thinl)) es0 (sg #sb idsb) >
      (((idsb ^Tm thinl) /Tm (sg #sb idsb))
        +sb (es0 /Tm (sg #sb idsb)))
        ~[ _+sb_
           $~ (((idsb ^Tm thinl) /Tm (sg #sb idsb)) ~[ thin- Sbst idsb _ _ >
               idsb /Tm sel thinl (sg #sb idsb) ~[ idsb/Tm _ >
               sel thinl (sg #sb idsb) ~[ sel-cat-l (sg ^Tm thinl) (idsb {_}{l} ^Tm thinr) >
               (sg ^Tm thinl) < (_^Tm thinl) $~ sbstId sg ]~
               ((sg /Tm idsb) ^Tm thinl) ~[ sbst-thin sg idsb thinl >
               (sg /Tm (idsb ^Tm thinl)) < (sg /Tm_) $~ sel-cat-l _ (es0 /Tm (sg #sb idsb)) ]~
               (sg /Tm sel thinl (((idsb ^Tm thinl) +sb (es0 /Tm (sg #sb idsb)))))
               < thin- Sbst sg _ _ ]~
               ((sg ^Tm thinl) /Tm (((idsb ^Tm thinl) +sb (es0 /Tm (sg #sb idsb)))))
               [QED])
           ~$~ ((es0 /Tm (sg #sb idsb)) < sel-cat-r _ _ ]~
              sel thinr (((idsb ^Tm thinl) +sb (es0 /Tm (sg #sb idsb))))
                < idsb/Tm _ ]~
              (idsb /Tm sel thinr (((idsb ^Tm thinl) +sb (es0 /Tm (sg #sb idsb)))))
              < thin- Sbst idsb thinr _ ]~
              ((idsb ^Tm thinr) /Tm (((idsb ^Tm thinl) +sb (es0 /Tm (sg #sb idsb))))) [QED] ) >
      (((sg ^Tm thinl) /Tm (((idsb ^Tm thinl) +sb (es0 /Tm (sg #sb idsb)))))
        +sb ((idsb ^Tm thinr) /Tm (((idsb ^Tm thinl) +sb (es0 /Tm (sg #sb idsb))))))
        < catSb (sg ^Tm thinl) (idsb ^Tm thinr)
          ((idsb ^Tm thinl) +sb (es0 /Tm (sg #sb idsb)))]~
      ((sg #sb idsb) /Tm ((idsb ^Tm thinl) +sb (es0 /Tm (sg #sb idsb))))
        [QED]) ]~
    (t0 /Tm _)
      < sbst-sbst t0 _ _ ]~
    ((t0 /Tm ((idsb ^Tm thinl) +sb es0)) /Tm (sg #sb idsb))
      [QED]
