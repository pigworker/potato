module TmBis where

open import Eq
open import Thin
open import Atom
open import Basics

data Dir : Set where
  chk syn : Dir
  _**_ : Dir -> Nat -> Dir

Atomic : Dir -> Set
Atomic chk = Atom
Atomic (d ** n) = n ~ []
Atomic _ = Zero
  
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

    !_   : forall {d} -> Atomic d -> Tm n d
    ^_   : Tm (n su) chk -> Tm n chk

    [_]  : Tm n syn -> Tm n chk

    #_   : Fi n -> Tm n syn

    _/_  : forall {m} -> M m -> Tm n (syn ** m) ->
           Tm n chk

  pattern _&_  s t = pair cons s t
  pattern _$_  e s = pair elim e s
  pattern _::_ t T = pair radi t T
  pattern _`_ sg e = pair vect sg e
  infixr 4 _&_
  infixl 5 _$_
  infix 3 _::_
  infixl 2 _`_

  VTm : Nat * Dir -> Nat -> Set
  VTm (m , d) n = Tm m (d ** n)

  _=>_ : Nat -> Nat -> Set
  n => m = VTm (m , syn) n

  sel : forall {k n m} -> n <= m -> VTm k m -> VTm k n
  sel (th no) (sg ` e) = sel th sg
  sel (th su) (sg ` e) = sel th sg ` e
  sel []      (! r~)   = ! r~

  seliota : forall {k n}(sg : VTm k n) -> sel iota sg ~ sg
  seliota (! r~) = r~
  seliota (sg ` e) = (_` e) $~ seliota sg

  sel^^ : forall {k p n m}(th : p <= n)(ph : n <= m)(sg : VTm k m) ->
    sel (th ^^ ph) sg ~ sel th (sel ph sg)
  sel^^ th (ph no) (sg ` e) = sel^^ th ph sg
  sel^^ (th no) (ph su) (sg ` e) = sel^^ th ph sg
  sel^^ (th su) (ph su) (sg ` e) = (_` _) $~ sel^^ th ph sg
  sel^^ [] [] (! r~) = r~

  selnone : forall {k n}(sg : VTm k n) -> sel none sg ~ (! r~)
  selnone (sg ` _) = selnone sg
  selnone (! r~) = r~

  top : forall {n d} -> VTm (n , d) ([] su) -> Tm n d
  top (_ ` e) = e

  record Act (A : Nat -> Nat -> Set) : Set where
    field
      vari : forall {n m} -> Fi n -> A n m -> Tm m syn
      succ : forall {n m} -> A n m -> A (n su) (m su)
    act : forall {d n m} -> Tm n d -> A n m -> Tm m d
    act (pair p s t) al = pair p (act s al) (act t al)
    act (! a) al = ! a
    act (^ t) al = ^ act t (succ al)
    act [ e ] al = [ act e al ]
    act (# x) al = vari x al
    act (w / t) al = w / act t al

    sel-act : forall {d r p n m}
      (th : n <= m)(sg : VTm (p , d) m)(al : A p r) ->
      sel th (act sg al) ~ act (sel th sg) al
    sel-act (th no) (sg ` t) al = sel-act th sg al
    sel-act (th su) (sg ` t) al = (_` _) $~ sel-act th sg al
    sel-act [] (! r~) al = r~

    top-act : forall {d r p}
      (sg : VTm (p , d) ([] su))(al : A p r) ->
      top (act sg al) ~ act (top sg) al
    top-act ((! r~) ` t) al = r~

  Thin : Act _<=_
  Act.vari Thin x th = # (x ^^ th)
  Act.succ Thin th = th su

  _^Tm_ = Act.act Thin

  Sbst : Act _=>_
  Act.vari Sbst x sg = top (sel x sg)
  Act.succ Sbst sg = (sg ^Tm (iota no)) ` (# (none su))

  _/Tm_ = Act.act Sbst
  
  thsb : forall {n m} -> n <= m -> n => m
  thsb (th no) = thsb th ^Tm (iota no)
  thsb (th su) = (thsb th ^Tm (iota no)) ` (# (none su))
  thsb []      = ! r~

  data Ty' : Set where
    _<='_ : Nat -> Nat -> Ty'
    Tm' : Nat -> Dir -> Ty'

  Eval : Ty' -> Set
  Eval (n <=' m) = n <= m
  Eval (Tm' n d) = Tm n d

  data Quo : Ty' -> Set where
    <_>   : forall {T} -> Eval T -> Quo T
    _no'  : forall {n m} -> Quo (n <=' m) -> Quo (n <=' (m su))
    _su'  : forall {n m} -> Quo (n <=' m) -> Quo ((n su) <=' (m su))
    iota' : forall {n} -> Quo (n <=' n)
    _^^'_ : forall {p n m} -> Quo (p <=' n) -> Quo (n <=' m) ->
             Quo (p <=' m)
    none' : forall {n} -> Quo ([] <=' n)

    pair : forall {n dl dr dp} -> Pair dl dr dp ->
           Quo (Tm' n dl) -> Quo (Tm' n dr) -> Quo (Tm' n dp)
    !_   : forall {n d} -> Atomic d -> Quo (Tm' n d)
    ^_   : forall {n} -> Quo (Tm' (n su) chk) -> Quo (Tm' n chk)
    [_]  : forall {n} -> Quo (Tm' n syn) -> Quo (Tm' n chk)
    #_   : forall {n} -> Quo (([] su) <=' n) -> Quo (Tm' n syn)
    _/_  : forall {n m} -> M m -> Quo (Tm' n (syn ** m)) ->
           Quo (Tm' n chk)

    thsb' : forall {n m} -> Quo (n <=' m) -> Quo (Tm' m (syn ** n))
    sel'  : forall {d p n m} -> Quo (n <=' m) -> Quo (Tm' p (d ** m)) ->
              Quo (Tm' p (d ** n))
    top'  : forall {d p} -> Quo (Tm' p (d ** ([] su))) ->
              Quo (Tm' p d)
    _^Tm'_ : forall {d n m} -> Quo (Tm' n d) -> Quo (n <=' m) ->
              Quo (Tm' m d)
    _/Tm'_ : forall {d n m} -> Quo (Tm' n d) -> Quo (Tm' m (syn ** n)) ->
              Quo (Tm' m d)

  eval : forall {T} -> Quo T -> Eval T
  eval < t > = t
  eval (t' no') = eval t' no
  eval (t' su') = eval t' su
  eval iota' = iota
  eval (th ^^' ph) = eval th ^^ eval ph
  eval none' = none
  eval (pair p s' t') = pair p (eval s') (eval t')
  eval (! a) = ! a
  eval (^ t') = ^ eval t'
  eval [ e' ] = [ eval e' ]
  eval (# x') = # eval x'
  eval (w / t') = w / eval t'
  eval (thsb' th') = thsb (eval th')
  eval (sel' th' ts') = sel (eval th') (eval ts')
  eval (top' ts') = top (eval ts')
  eval (t' ^Tm' th') = eval t' ^Tm eval th'
  eval (t' /Tm' sg') = eval t' /Tm eval sg'

  record _~'_ {T : Ty'}(s' t' : Quo T) : Set where
    constructor pack
    field
      unpack : eval s' ~ eval t'
  open _~'_ public

  _~'[_>_ : forall {T}(x : Quo T){y z} -> x ~' y -> y ~' z -> x ~' z
  unpack (x ~'[ pack q0 > pack q1) = eval x ~[ q0 > q1

  _<_]~'_ : forall {T}(x : Quo T){y z} -> y ~' x -> y ~' z -> x ~' z
  unpack (x < pack q0 ]~' pack q1) = eval x < q0 ]~ q1

  _[QED]' : forall {T}(x : Quo T) -> x ~' x
  _ [QED]' = pack r~

  infixr 1 _~'[_>_ _<_]~'_
  infixr 2 _[QED]'

  record Solver : Set where
    field
      no!=   : forall {n m}(th : Quo (n <=' m)) ->
             Quo (n <=' (m su)) >< \ th' -> (eval th no) ~ eval th'
      su!=   : forall {n m}(th : Quo (n <=' m)) ->
             Quo ((n su) <=' (m su)) >< \ th' -> (eval th su) ~ eval th'
      iota!= : forall {n} ->
             Quo (n <=' n) >< \ io -> iota ~ eval io
      comp!= : forall {p n m}(th : Quo (p <=' n))(ph : Quo (n <=' m)) ->
             Quo (p <=' m) >< \ ps -> (eval th ^^ eval ph) ~ eval ps
      none!= : forall {n} ->
             Quo ([] <=' n) >< \ ne -> none ~ eval ne
      pair!= : forall {n dl dr dp}(p : Pair dl dr dp) ->
             (s : Quo (Tm' n dl))(t : Quo (Tm' n dr)) ->
             Quo (Tm' n dp) >< \ st -> pair p (eval s) (eval t) ~ eval st
      atom!= : forall {n d}(a : Atomic d) ->
             Quo (Tm' n d) >< \ a' -> (! a) ~ eval a'
      abst!= : forall {n}(t : Quo (Tm' (n su) chk)) ->
             Quo (Tm' n chk) >< \ t' -> (^ eval t) ~ eval t'
      embd!= : forall {n}(e : Quo (Tm' n syn)) ->
             Quo (Tm' n chk) >< \ t -> [ eval e ] ~ eval t
      var!=  : forall {n}(i : Quo (([] su) <=' n)) ->
             Quo (Tm' n syn) >< \ e -> (# eval i) ~ eval e
      meta!= : forall {n m}(w : M m)(es : Quo (Tm' n (syn ** m))) ->
             Quo (Tm' n chk) >< \ t -> (w / eval es) ~ eval t
      thsb!= : forall {n m}(th : Quo (n <=' m)) ->
             Quo (Tm' m (syn ** n)) >< \ sg -> thsb (eval th) ~ eval sg
      sel!=  : forall {d p n m}(th : Quo (n <=' m))(ts : Quo (Tm' p (d ** m))) ->
             Quo (Tm' p (d ** n)) >< \ us -> sel (eval th) (eval ts) ~ eval us
      top!=  : forall {d p}(ts : Quo (Tm' p (d ** ([] su)))) ->
             Quo (Tm' p d) >< \ t -> top (eval ts) ~ eval t
      thin!= : forall {d n m}(t : Quo (Tm' n d))(th : Quo (n <=' m)) ->
             Quo (Tm' m d) >< \ t' -> (eval t ^Tm eval th) ~ eval t'
      sbst!= : forall {d n m}(t : Quo (Tm' n d))(sg : Quo (Tm' m (syn ** n))) ->
             Quo (Tm' m d) >< \ t' -> (eval t /Tm eval sg) ~ eval t'

    norm : forall {T}(s : Quo T) -> Quo T >< \ t -> eval s ~ eval t
    norm < x > = < x > , r~
    norm (th no') with th! , th= <- norm th with x , q <- no!= th! =
      x , (_ ~[ _no $~ th= > q)
    norm (th su') with th! , th= <- norm th with x , q <- su!= th! =
      x , (_ ~[ _su $~ th= > q)
    norm iota' = iota!=
    norm (th ^^' ph) with th! , th= <- norm th | ph! , ph= <- norm ph
      with x , q <- comp!= th! ph! = x , (_ ~[ _^^_ $~ th= ~$~ ph= > q)
    norm none' = none!=
    norm (pair p s t) with s! , s= <- norm s | t! , t= <- norm t
      with x , q <- pair!= p s! t! = x , (_ ~[ pair p $~ s= ~$~ t= > q)
    norm (! a) = atom!= a
    norm (^ t) with t! , t= <- norm t with x , q <- abst!= t!
      = x , (_ ~[ ^_ $~ t= > q)
    norm [ e ] with e! , e= <- norm e with x , q <- embd!= e!
      = x , (_ ~[ [_] $~ e= > q)
    norm (# i) with i! , i= <- norm i with x , q <- var!= i!
      = x , (_ ~[ #_ $~ i= > q)
    norm (w / sg) with sg! , sg= <- norm sg with x , q <- meta!= w sg!
      = x , (_ ~[ (w /_) $~ sg= > q)
    norm (thsb' th) with th! , th= <- norm th with x , q <- thsb!= th!
      = x , (_ ~[ thsb $~ th= > q)
    norm (sel' th ts) with th! , th= <- norm th | ts! , ts= <- norm ts
      with x , q <- sel!= th! ts! = x , (_ ~[ sel $~ th= ~$~ ts= > q)
    norm (top' ts) with ts! , ts= <- norm ts with x , q <- top!= ts!
      = x , (_ ~[ top $~ ts= > q)
    norm (t ^Tm' th) with t! , t= <- norm t | th! , th= <- norm th
      with x , q <- thin!= t! th! = x , (_ ~[ _^Tm_ $~ t= ~$~ th= > q)
    norm (t /Tm' sg) with t! , t= <- norm t | sg! , sg= <- norm sg
      with x , q <- sbst!= t! sg! = x , (_ ~[ _/Tm_ $~ t= ~$~ sg= > q)

    solve : forall {T}{s t : Quo T} -> fst (norm s) ~ fst (norm t) ->
      s ~' t
    unpack (solve {T} {s} {t} q) with eval s | norm s | eval t | norm t
    unpack (solve {T} {s} {t} r~) | ._ | s! , r~ | ._ | .s! , r~ = r~

  solver0 : Solver
  solver0 = record
              { no!=   = \ th -> (th no')       , r~
              ; su!=   = \ th -> (th su')       , r~
              ; iota!= = iota'                  , r~
              ; comp!= = \ th ph -> (th ^^' ph) , r~
              ; none!= = none'                  , r~
              ; pair!= = \ p s t -> pair p s t  , r~
              ; atom!= = \ a -> (! a)           , r~
              ; abst!= = \ t -> (^ t)           , r~
              ; embd!= = \ e -> [ e ]           , r~
              ; var!=  = \ i -> (# i)           , r~
              ; meta!= = \ w sg -> (w / sg)     , r~
              ; thsb!= = \ th -> thsb' th       , r~
              ; sel!=  = \ th ts -> sel' th ts  , r~
              ; top!=  = \ ts -> top' ts        , r~
              ; thin!= = \ t th -> (t ^Tm' th)  , r~
              ; sbst!= = \ t sg -> (t /Tm' sg)  , r~
              }

  no!=1 : forall {n m}(th : Quo (n <=' m)) ->
             Quo (n <=' (m su)) >< \ th' -> (eval th no) ~ eval th'
  no!=1 none' = none' , r~
  no!=1 th    = (th no') , r~

  su!=1 : forall {n m}(th : Quo (n <=' m)) ->
             Quo ((n su) <=' (m su)) >< \ th' -> (eval th su) ~ eval th'
  su!=1 iota' = iota' , r~
  su!=1 th    = (th su') , r~

  comp!=1 : forall {p n m}(th : Quo (p <=' n))(ph : Quo (n <=' m)) ->
             Quo (p <=' m) >< \ ps -> (eval th ^^ eval ph) ~ eval ps
  comp!=1 th       (ph no') with ps , q <- comp!=1 th ph =
    (ps no') , (_no $~ q)
  comp!=1 (th no') (ph su') with ps , q <- comp!=1 th ph =
    (ps no') , (_no $~ q)
  comp!=1 (th su') (ph su') with ps , q <- comp!=1 th ph =
    (ps su') , (_su $~ q)
  comp!=1 iota'    ph       = ph , iota^^ _
  comp!=1 none'    ph       = none' , none~ _ _
  comp!=1 th iota'          = th , _ ^^iota
  comp!=1 th (ph ^^' ps)
    with ch , q0 <- comp!=1 th ph
    with om , q1 <- comp!=1 ch ps
    = om , ((eval th ^^ (eval ph ^^ eval ps))
               ~[ thinAssoc (eval th) (eval ph) (eval ps) >
            ((eval th ^^ eval ph) ^^ eval ps) ~[ (_^^ eval ps) $~ q0 >
            (eval ch ^^ eval ps) ~[ q1 >
            eval om [QED])
  comp!=1 th ph = (th ^^' ph) , r~  

  sel!=1  : forall {d p n m}(th : Quo (n <=' m))(ts : Quo (Tm' p (d ** m))) ->
             Quo (Tm' p (d ** n)) >< \ us -> sel (eval th) (eval ts) ~ eval us
  sel!=1 (th no') (pair vect ts t) = sel!=1 th ts
  sel!=1 (th su') (pair vect ts t) with us , q <- sel!=1 th ts
    = pair vect us t , ((_` _) $~ q)
  sel!=1 th       (sel' ph ts)
    with ps , q0 <- comp!=1 th ph with us , q1 <- sel!=1 ps ts
    = us , (sel (eval th) (sel (eval ph) (eval ts)) < sel^^ (eval th) (eval ph) _ ]~
            sel (eval th ^^ eval ph) (eval ts) ~[ sel $~ q0 ~$~ r~ >
            sel (eval ps) (eval ts) ~[ q1 >
            eval us [QED])
  sel!=1 th       (ts ^Tm' ph)  with us , q <- sel!=1 th ts =
    (us ^Tm' ph) ,
    (_ ~[ Act.sel-act Thin (eval th) (eval ts) (eval ph) >
      ((_^Tm (eval ph)) $~ q))
  sel!=1 th       (ts /Tm' sg)  with us , q <- sel!=1 th ts =
    (us /Tm' sg) ,
    (_ ~[ Act.sel-act Sbst (eval th) (eval ts) (eval sg) >
      ((_/Tm (eval sg)) $~ q))
  sel!=1 iota'    ts            = ts , seliota _
  sel!=1 none'    ts            = (! r~) , selnone (eval ts)
  sel!=1 th ts = sel' th ts , r~

  top!=1  : forall {d p}(ts : Quo (Tm' p (d ** ([] su)))) ->
             Quo (Tm' p d) >< \ t -> top (eval ts) ~ eval t
  top!=1 (pair vect ts t) = t , r~
  top!=1 (ts ^Tm' th) with t , q <- top!=1 ts =
    (t ^Tm' th) ,
    (_ ~[ Act.top-act Thin (eval ts) (eval th) >
        ((_^Tm (eval th)) $~ q))
  top!=1 (ts /Tm' sg) with t , q <- top!=1 ts =
    (t /Tm' sg) ,
    (_ ~[ Act.top-act Sbst (eval ts) (eval sg) >
        ((_/Tm (eval sg)) $~ q))
  top!=1 ts = top' ts , r~

  solver1 : Solver
  solver1 = record solver0
              { no!= = no!=1
              ; su!= = su!=1
              ; comp!= = comp!=1
              ; sel!= = sel!=1
              ; top!= = top!=1
              }

  module ACTID {A}(ActA : Act A)(ai : forall {n} -> A n n) where
    open Act ActA
    module LAWSID
      (varid : forall {n}(x : Fi n) -> vari x ai ~ (# x))
      (sucid : forall {n} -> succ (ai {n}) ~ ai)
      where
      actId : forall {d n}(t : Tm n d) -> act t ai ~ t
      actId (pair p s t) = pair p $~ actId s ~$~ actId t
      actId (! a) = r~
      actId (^ t) = ^_ $~
        (act t (succ ai) ~[ act t $~ sucid > act t ai ~[ actId t > t [QED])
      actId [ e ] = [_] $~ actId e
      actId (# x) = varid x
      actId (w / sg) = (w /_) $~ actId sg

  module ACTCO {A B C}(ActA : Act A)(ActB : Act B)(ActC : Act C)
    (co : forall {p n m} -> A p n -> B n m -> C p m) where
    open Act
    module LAWSCO
      (varco : forall {p n m}(x : Fi p)(al : A p n)(be : B n m) ->
        act ActB (vari ActA x al) be ~ vari ActC x (co al be))
      (succo : forall {p n m}(al : A p n)(be : B n m) ->
        co (succ ActA al) (succ ActB be) ~ succ ActC (co al be))
      where
      actCo : forall {d p n m}(t : Tm p d)(al : A p n)(be : B n m) ->
        act ActB (act ActA t al) be ~ act ActC t (co al be)
      actCo (pair p s t) al be = pair p $~ actCo s al be ~$~ actCo t al be
      actCo (! a) al be = r~
      actCo (^ t) al be = ^_ $~ (
        act ActB (act ActA t (succ ActA al)) (succ ActB be)
          ~[ actCo t _ _ >
        act ActC t (co (succ ActA al) (succ ActB be))
          ~[ act ActC t $~ succo al be >
        act ActC t (succ ActC (co al be)) [QED])
      actCo [ e ] al be = [_] $~ actCo e al be
      actCo (# x) al be = varco x al be
      actCo (w / sg) al be = (w /_) $~ actCo sg al be

  module _ where
    open Solver solver1
    open ACTID Thin iota
    open LAWSID
      (\ x -> unpack (
        (# (< x > ^^' iota')) ~'[ solve r~ > (# < x >) [QED]'))
      r~
    thinId = actId

    open ACTCO Thin Thin Thin _^^_
    open LAWSCO
      (\ x al be -> unpack (
        (# ((< x > ^^' < al >) ^^' < be >))  ~'[ solve r~ >
        (# (< x > ^^' (< al > ^^' < be >))) [QED]'))
      (\ _ _ -> r~)
    thin-thin = actCo

  thin!=2 : forall {d n m}(t : Quo (Tm' n d))(th : Quo (n <=' m)) ->
             Quo (Tm' m d) >< \ t' -> (eval t ^Tm eval th) ~ eval t'
  thin!=2 (pair p s t) th
      with s! , s= <- thin!=2 s th | t! , t= <- thin!=2 t th =
      pair p s! t! , (pair p $~ s= ~$~ t=)
  thin!=2 (! a) th = ! a , r~
  thin!=2 (^ t) th
      with th! , th= <- su!=1 th with t! , t= <- thin!=2 t th! =
      ^ t! , (^_ $~ (_ ~[ (eval t ^Tm_) $~ th= > t=))
  thin!=2 [ e ] th with e! , e= <- thin!=2 e th =
      [ e! ] , ([_] $~ e=)
  thin!=2 (# x) th with y! , y= <- comp!=1 x th
      = # y! , (#_ $~ y=)
  thin!=2 (w / sg) th with ta! , ta= <- thin!=2 sg th =
      w / ta! , ((w /_) $~ ta=)
  thin!=2 t iota' = t , thinId (eval t)
  thin!=2 (t ^Tm' th) ph with ps! , ps= <- comp!=1 th ph =
   t ^Tm' ps! , (
     ((eval t ^Tm eval th) ^Tm eval ph)
        ~[ thin-thin (eval t) (eval th) (eval ph) >
     (eval t ^Tm (eval th ^^ eval ph))
        ~[ (eval t ^Tm_) $~ ps= >
     (eval t ^Tm eval ps!) [QED])
  thin!=2 t th = t ^Tm' th , r~  

  solver2 : Solver
  solver2 = record solver1
              { thin!= = thin!=2
              }

  module _ where
    open Solver solver2

    open ACTCO Thin Sbst Sbst sel
    open LAWSCO
      (\ x al be -> unpack (
        top' (sel' (< x > ^^' < al >) < be >) ~'[ solve r~ >
        top' (sel' < x > (sel' < al > < be >)) [QED]'))
      (\ al be -> unpack (
        pair vect (sel' < al > (< be > ^Tm' (iota' no'))) (# (none' su'))
          ~'[ solve r~ >
        pair vect (sel' < al > < be > ^Tm' (iota' no')) (# (none' su')) [QED]'))
    thin-sbst = actCo

  module _ where
    open Solver solver2

    open ACTCO Sbst Thin Sbst _^Tm_
    open LAWSCO
      (\ x al be -> unpack (
        ((top' (sel' < x > < al >)) ^Tm' < be >) ~'[ solve r~ >
        top' (sel' < x > (< al > ^Tm' < be >)) [QED]') )
      (\ al be -> unpack (
        pair vect ((< al > ^Tm' (iota' no')) ^Tm' (< be > su'))
                  (# ((none' ^^' < be >) su'))
          ~'[ solve r~ >
        pair vect ((< al > ^Tm' < be >) ^Tm' (iota' no')) (# (none' su'))
          [QED]'))
    sbst-thin = actCo

  thin!=3 : forall {d n m}(t : Quo (Tm' n d))(th : Quo (n <=' m)) ->
             Quo (Tm' m d) >< \ t' -> (eval t ^Tm eval th) ~ eval t'
  thin!=3 (pair p s t) th
    with s! , s= <- thin!=3 s th | t! , t= <- thin!=3 t th =
    pair p s! t! , (pair p $~ s= ~$~ t=)
  thin!=3 (! a) th = ! a , r~
  thin!=3 (^ t) th
      with th! , th= <- su!=1 th with t! , t= <- thin!=3 t th! =
      ^ t! , (^_ $~ (_ ~[ (eval t ^Tm_) $~ th= > t=))
  thin!=3 [ e ] th with e! , e= <- thin!=3 e th =
      [ e! ] , ([_] $~ e=)
  thin!=3 (# x) th with y! , y= <- comp!=1 x th
      = # y! , (#_ $~ y=)
  thin!=3 (w / sg) th with ta! , ta= <- thin!=3 sg th =
      w / ta! , ((w /_) $~ ta=)
  thin!=3 t iota' = t , thinId (eval t)
  thin!=3 (t ^Tm' th) ph with ps! , ps= <- comp!=1 th ph =
   t ^Tm' ps! , (
     ((eval t ^Tm eval th) ^Tm eval ph)
        ~[ thin-thin (eval t) (eval th) (eval ph) >
     (eval t ^Tm (eval th ^^ eval ph))
        ~[ (eval t ^Tm_) $~ ps= >
     (eval t ^Tm eval ps!) [QED])
  thin!=3 (t /Tm' sg) ph with ta! , ta= <- thin!=3 sg ph =
   t /Tm' ta! , (
     ((eval t /Tm eval sg) ^Tm eval ph)
        ~[ sbst-thin (eval t) (eval sg) (eval ph) >
     (eval t /Tm (eval sg ^Tm eval ph))
        ~[ (eval t /Tm_) $~ ta= >
     (eval t /Tm eval ta!) [QED])
  thin!=3 t th = t ^Tm' th , r~  

  sbst!=3 : forall {d n m}(t : Quo (Tm' n d))(sg : Quo (Tm' m (syn ** n))) ->
             Quo (Tm' m d) >< \ t' -> (eval t /Tm eval sg) ~ eval t'
  sbst!=3 (pair p s t) sg
      with s! , s= <- sbst!=3 s sg | t! , t= <- sbst!=3 t sg =
      pair p s! t! , (pair p $~ s= ~$~ t=)
  sbst!=3 (! a) sg = ! a , r~
  sbst!=3 (^ t) sg
      with ta! , ta= <- thin!=3 sg (iota' no')
      with t! , t= <- sbst!=3 t (pair vect ta! (# (none' su'))) =
      ^ t! , (^_ $~ ( _ ~[ (eval t /Tm_) $~ ((_` _) $~ ta=) > t=))
  sbst!=3 [ e ] sg with e! , e= <- sbst!=3 e sg =
      [ e! ] , ([_] $~ e=)
  sbst!=3 (# x) sg
      with ts! , ts= <- sel!=1 x sg
      with t! , t= <- top!=1 ts!
      = t! , (_ ~[ top $~ ts= > t=)
  sbst!=3 (w / rh) sg with ta! , ta= <- sbst!=3 rh sg =
      w / ta! , ((w /_) $~ ta=)
  sbst!=3 (t ^Tm' th) sg with ta! , ta= <- sel!=1 th sg =
   t /Tm' ta! , (
     ((eval t ^Tm eval th) /Tm eval sg)
        ~[ thin-sbst (eval t) (eval th) (eval sg) >
     (eval t /Tm (sel (eval th) (eval sg)))
        ~[ (eval t /Tm_) $~ ta= >
     (eval t /Tm eval ta!) [QED])
  sbst!=3 t sg = t /Tm' sg , r~

  solver3 : Solver
  solver3 = record solver2
              { thin!= = thin!=3
              ; sbst!= = sbst!=3
              }

  module _ where
    open Solver solver3

    open ACTCO Sbst Sbst Sbst _/Tm_
    open LAWSCO
      (\ x al be -> unpack (
        (top' (sel' < x > < al >) /Tm' < be >) ~'[ solve r~ >
        top' (sel' < x > (< al > /Tm' < be >)) [QED]'))
      (\ al be -> unpack (
        pair vect
          ((< al > ^Tm' (iota' no')) /Tm'
           (pair vect (< be > ^Tm' (iota' no')) (# (none' su'))))
          (# (none' su'))
          ~'[ solve r~ > 
        pair vect
          ((< al > /Tm' < be >) ^Tm' (iota' no'))
          (# (none' su'))
      [QED]'))
    sbst-sbst = actCo

  module _ where
    open Solver solver3

    sel-thsb-lem : forall {p n m}(th : p <= n)(ph : n <= m) ->
      sel' < th > (thsb' < ph > ^Tm' (iota' no')) ~'
      (thsb' (< th > ^^' < ph >) ^Tm' (iota' no'))
      
    sel-thsb : forall {p n m}(th : p <= n)(ph : n <= m) ->
      sel th (thsb ph) ~ thsb (th ^^ ph)
      
    sel-thsb th (ph no) = unpack (sel-thsb-lem th ph)
    sel-thsb (th no) (ph su) = unpack (sel-thsb-lem th ph)
    sel-thsb (th su) (ph su) = (_` _) $~ unpack (sel-thsb-lem th ph)
    sel-thsb [] [] = r~

    sel-thsb-lem th ph = 
      sel' < th > (thsb' < ph > ^Tm' (iota' no')) ~'[ solve r~ >
      (sel' < th > (thsb' < ph >) ^Tm' (iota' no'))
        ~'[ pack ((_^Tm (iota no)) $~ sel-thsb th ph) >
      (thsb' (< th > ^^' < ph >) ^Tm' (iota' no')) [QED]'

    top-thsb : forall {n}(x : Fi n) -> top (thsb x) ~ (# x)
    top-thsb (x no) = unpack (
      top' (thsb' < x > ^Tm' (iota' no')) ~'[ solve r~ >
      (top' (thsb' < x >) ^Tm' (iota' no'))
           ~'[ pack ((_^Tm (iota no)) $~ top-thsb x) >
      ((# < x >) ^Tm' (iota' no')) ~'[ solve r~ >
      (# (< x > no')) [QED]')
    top-thsb (x su) = #_ $~ (_su $~ none~ _ _)

  pair!=4 : forall {n dl dr dp}(p : Pair dl dr dp) ->
             (s : Quo (Tm' n dl))(t : Quo (Tm' n dr)) ->
             Quo (Tm' n dp) >< \ st -> pair p (eval s) (eval t) ~ eval st
  pair!=4 vect (thsb' (th no')) (# (x su'))
    with ph! , ph= <- su!=1 th =
    thsb' ph! ,
    ((thsb (eval th) ^Tm (iota no) ` (# (eval x su)))
      ~[ ((thsb (eval th) ^Tm (iota no)) `_) $~ (#_ $~ (_su $~ none~ _ _)) >
    thsb (eval th su) ~[ thsb $~ ph= >
    thsb (eval ph!) [QED])
  pair!=4 vect (thsb' none') (# (x su')) =
    thsb' (none' su') , (
    ((thsb none ^Tm (iota no)) `_) $~ (#_ $~ (_su $~ none~ _ _)))
  pair!=4 p s t = pair p s t , r~

  atom!=4 : forall {n d}(a : Atomic d) ->
             Quo (Tm' n d) >< \ a' -> (! a) ~ eval a'
  atom!=4 {d = (syn ** _)} r~ = thsb' none' , help _ where
    help : forall n -> (! r~) ~ thsb (none {_}{n})
    help (n -, x) = (_^Tm (iota no)) $~ help n 
    help [] = r~
  atom!=4 a = ! a , r~
  
  sel!=4  : forall {d p n m}(th : Quo (n <=' m))(ts : Quo (Tm' p (d ** m))) ->
             Quo (Tm' p (d ** n)) >< \ us -> sel (eval th) (eval ts) ~ eval us
  sel!=4 (th no') (pair vect ts t) = sel!=4 th ts
  sel!=4 (th su') (pair vect ts t)
    with us , q0 <- sel!=4 th ts
    with vs , q1 <- pair!=4 vect us t
    = vs , (_ ~[ (_` _) $~ q0 > q1)
  sel!=4 th       (sel' ph ts)
    with ps , q0 <- comp!=1 th ph with us , q1 <- sel!=4 ps ts
    = us , (sel (eval th) (sel (eval ph) (eval ts)) < sel^^ (eval th) (eval ph) _ ]~
            sel (eval th ^^ eval ph) (eval ts) ~[ sel $~ q0 ~$~ r~ >
            sel (eval ps) (eval ts) ~[ q1 >
            eval us [QED])
  sel!=4 th       (ts ^Tm' ph)  with us , q <- sel!=4 th ts =
    (us ^Tm' ph) ,
    (_ ~[ Act.sel-act Thin (eval th) (eval ts) (eval ph) >
      ((_^Tm (eval ph)) $~ q))
  sel!=4 th       (ts /Tm' sg)  with us , q <- sel!=4 th ts =
    (us /Tm' sg) ,
    (_ ~[ Act.sel-act Sbst (eval th) (eval ts) (eval sg) >
      ((_/Tm (eval sg)) $~ q))
  sel!=4 th (thsb' ph) with ps , q <- comp!=1 th ph =
    thsb' ps , (_ ~[ sel-thsb (eval th) (eval ph) > (thsb $~ q))
  sel!=4 iota'    ts            = ts , seliota _
  sel!=4 none'    ts            = (! r~) , selnone (eval ts)
  sel!=4 th ts = sel' th ts , r~

  top!=4  : forall {d p}(ts : Quo (Tm' p (d ** ([] su)))) ->
             Quo (Tm' p d) >< \ t -> top (eval ts) ~ eval t
  top!=4 (pair vect ts t) = t , r~
  top!=4 (ts ^Tm' th) with t , q <- top!=4 ts =
    (t ^Tm' th) ,
    (_ ~[ Act.top-act Thin (eval ts) (eval th) >
        ((_^Tm (eval th)) $~ q))
  top!=4 (ts /Tm' sg) with t , q <- top!=4 ts =
    (t /Tm' sg) ,
    (_ ~[ Act.top-act Sbst (eval ts) (eval sg) >
        ((_/Tm (eval sg)) $~ q))
  top!=4 (thsb' x) = (# x) , top-thsb (eval x)
  top!=4 ts = top' ts , r~

  solver4 : Solver
  solver4 = record solver3
              { pair!= = pair!=4
              ; atom!= = atom!=4
              ; sel!= = sel!=4
              ; top!= = top!=4
              }

  module _ where
    open Solver solver4

    sbst-thsb : forall {d n m}(t : Tm n d)(th : n <= m) ->
      (t /Tm thsb th) ~ (t ^Tm th)
    sbst-thsb (pair p s t) th = pair p $~ sbst-thsb s th ~$~ sbst-thsb t th
    sbst-thsb (! a) th = r~
    sbst-thsb (^ t) th = ^_ $~ sbst-thsb t (th su)
    sbst-thsb [ e ] th = [_] $~ sbst-thsb e th
    sbst-thsb (# x) th = unpack (
      top' (sel' < x > (thsb' < th >)) ~'[ solve r~ >
      (# (< x > ^^' < th >)) [QED]' )
    sbst-thsb (w / sg) th = (w /_) $~ sbst-thsb sg th




{-
  module _ where
    open Act
    
    Iden : Act _~_
    vari Iden x r~ = # x
    succ Iden q = _su $~ q

    actIden : forall {d n}(t : Tm n d) -> act Iden t r~ ~ t
    actIden (pair p s t) = pair p $~ actIden s ~$~ actIden t
    actIden (! a)        = r~
    actIden (^ t)        = ^_ $~ actIden t
    actIden [ e ]        = [_] $~ actIden e
    actIden (# x)        = r~
    actIden (w / es)     = (w /_) $~ actIden es

  module _ {A B}(AA : Act A)(AB : Act B) where
    open Act

    Comp : Act \ p m -> _ >< \ n -> A p n * B n m
    vari Comp x (_ , al , be) = act AB (vari AA x al) be
    succ Comp (_ , al , be) = _ , succ AA al , succ AB be

    actComp : forall {d p n m}(t : Tm p d)(al : A p n)(be : B n m) ->
      act Comp t (n , al , be) ~ act AB (act AA t al) be
    actComp (pair p s t) al be = pair p $~ actComp s al be ~$~ actComp t al be
    actComp (! a) al be        = r~                               
    actComp (^ t) al be        = ^_ $~ actComp t (succ AA al) (succ AB be)
    actComp [ e ] al be        = [_] $~ actComp e al be                
    actComp (# x) al be        = r~                               
    actComp (w / es) al be     = (w /_) $~ actComp es al be             

    record Sim {n m}(al : A n m)(be : B n m) : Set where
      coinductive
      field
        variQ : forall x -> vari AA x al ~ vari AB x be
        succS : Sim (succ AA al) (succ AB be)

    actSim : forall {d n m}{al : A n m}{be : B n m}
             (t : Tm n d) -> Sim al be -> act AA t al ~ act AB t be
    actSim (pair p s t) albe = pair p $~ actSim s albe ~$~ actSim t albe
    actSim (! a) albe = r~
    actSim (^ t) albe = ^_ $~ actSim t (Sim.succS albe)
    actSim [ e ] albe = [_] $~ actSim e albe
    actSim (# x) albe = Sim.variQ albe x
    actSim (w / es) albe = (w /_) $~ actSim es albe

  su! : forall {n m} -> Quo (n <=' m) -> Quo ((n su) <=' (m su))
  su! iota' = iota'
  su! th' = th' su'

  comp! : forall {p n m} -> Quo (p <=' n) -> Quo (n <=' m) ->
            Quo (p <=' m)
  comp! th' iota' = th'
  comp! th' (ph' ^^' ps') = comp! (comp! th' ph') ps'
  comp! th' (ph' no') = comp! th' ph' no'
  comp! (th' no') (ph' su') = comp! th' ph' no'
  comp! (th' su') (ph' su') = su! (comp! th' ph')
  comp! iota' ph' = ph'
  comp! none' ph' = none'
  comp! th' ph' = th' ^^' ph'

  sel! : Nat -> forall {d p n m} -> Quo (n <=' m) -> Quo (Tm' p (d ** m)) ->
    Quo (Tm' p (d ** n))
  sel! g th' (sel' ph' ts') = sel! g (comp! th' ph') ts'
  sel! g th' (ts' ^Tm' ph') = sel! g th' ts' ^Tm' ph'
  sel! g th' (ts' /Tm' sg') = sel! g th' ts' /Tm' sg'
  sel! ([] su) th' (thsb' sg') = thsb' (comp! th' sg')
  sel! g iota' sg' = sg'
  sel! g none' sg' = ! r~
  sel! g (th' no') (pair vect ts' t') = sel! g th' ts'
  sel! g (th' su') (pair vect ts' t') = pair vect (sel! g th' ts') t'
  sel! [] th' sg' = sel' th' sg'
  sel! (g su) th' sg' = sel! g th' sg'
  

  top! : Nat -> forall {d p} -> Quo (Tm' p (d ** ([] su))) ->
              Quo (Tm' p d)
  top! g ts' = {!!}

  thin! : Nat -> forall {d n m} -> Quo (Tm' n d) -> Quo (n <=' m) ->
              Quo (Tm' m d)
  thin! g (pair p s' t') th' = pair p (thin! g s' th') (thin! g t' th')
  thin! g (! a) th' = ! a
  thin! g (^ t') th' = ^ (thin! g t' (su! th'))
  thin! g [ e' ] th' = [ thin! g e' th' ] 
  thin! g (# x') th' = # (comp! x' th')
  thin! g (e / sg') th' = e / thin! g sg' th'
  thin! ([] su) (t' ^Tm' th') ph' = thin! ([] su) t' (comp! th' ph')
  thin! ([] su su) (thsb' th') ph' = thsb' (comp! th' ph')
  thin! ([] su) th' iota' = th'
  thin! ([] su) t' th' = t' ^Tm' th'
  thin! [] t' th' = t' ^Tm' th'
  thin! (g su) t' th' = thin! g t' th'
  
  sbst! : Nat -> forall {d n m} -> Quo (Tm' n d) -> Quo (Tm' m (syn ** n)) ->
              Quo (Tm' m d)
  sbst! g t' sg' = {!!}

  norm : Nat -> forall {T} -> Quo T -> Quo T
  norm g < t > = < t >
  norm g (th' no') = norm g th' no'
  norm g (th' su') = su! (norm g th')
  norm g iota' = iota'
  norm g (th' ^^' ph') = comp! (norm g th') (norm g ph')
  norm g none' = none'
  norm g (pair p s' t') = pair p (norm g s') (norm g t')
  norm g (! a) = ! a
  norm g (^ t') = ^ norm g t'
  norm g [ e' ] = [ norm g e' ]
  norm g (# x) = # norm g x
  norm g (w / es) = w / norm g es
  norm g (thsb' th') = thsb' (norm g th')
  norm g (sel' th' ts') = sel! g (norm g th') (norm g ts')
  norm g (top' ts') = top! g (norm g ts')
  norm g (t' ^Tm' th') = thin! g (norm g t') (norm g th')
  norm g (t' /Tm' sg') = sbst! g (norm g t') (norm g sg')


  solve : (g : Nat) ->
    forall {T}{s' t' : Quo T} ->
    norm g s' ~ norm g t' ->
    s' ~' t'
  solveLemma : (g : Nat) ->
    forall {T}(t' : Quo T) -> t' ~' norm g t'

  lem-su! : forall {n m}(th' : Quo (n <=' m)) ->
    (eval th' su) ~ eval (su! th')
  lem-su! < x > = r~
  lem-su! (th' no') = r~
  lem-su! (th' su') = r~
  lem-su! iota' = r~
  lem-su! (th' ^^' ph') = r~
  lem-su! none' = r~

  lem-comp! : forall {p n m}(th' : Quo (p <=' n))(ph' : Quo (n <=' m)) ->
     (eval th' ^^ eval ph') ~ eval (comp! th' ph')
  lem-comp! th' (ph' no') = _no $~ lem-comp! th' ph'
  lem-comp! < x > (ph' su') = r~
  lem-comp! (th' no') (ph' su') = _no $~ lem-comp! th' ph'
  lem-comp! (th' su') (ph' su') = 
    (eval th' ^^ eval ph' su) ~[ _su $~ lem-comp! th' ph' >
    (eval (comp! th' ph') su) ~[ lem-su! (comp! th' ph') >
    eval (su! (comp! th' ph')) [QED]
  lem-comp! iota' (ph' su') = iota^^ _
  lem-comp! (_ ^^' _) (ph' su') = r~
  lem-comp! none' (ph' su') = none~ _ _
  lem-comp! th' iota' = _ ^^iota
  lem-comp! th' (ph' ^^' ps') = 
    (eval th' ^^ (eval ph' ^^ eval ps')) ~[ thinAssoc _ _ _ >
    ((eval th' ^^ eval ph') ^^ eval ps') ~[ (_^^ eval ps') $~ lem-comp! _ ph' >
    (eval (comp! th' ph') ^^ eval ps') ~[ lem-comp! _ ps' >
    eval (comp! (comp! th' ph') ps') [QED]
  lem-comp! < x > none' = r~
  lem-comp! iota' none' = none~ _ _
  lem-comp! (_ ^^' _) none' = r~
  lem-comp! none' none' = none~ _ _
  lem-comp! < _ > < _ > = r~
  lem-comp! (_ no') < x > = r~
  lem-comp! (_ su') < x > = r~
  lem-comp! iota' < x > = iota^^ _
  lem-comp! (_ ^^' _) < x > = r~
  lem-comp! none' < x > = none~ _ _

  lem-sel! : forall g -> forall {d p n m}(th' : Quo (n <=' m))(ts' : Quo (Tm' p (d ** m)))
    -> sel (eval th') (eval ts') ~ eval (sel! g th' ts')
  lem-sel! g (th' no') < x > = {!!} -- r~
  lem-sel! g (th' su') < x > = {!!} -- r~
  lem-sel! g iota' < x > = seliota _
  lem-sel! g (_ ^^' _) < x > = {!!} -- r~
  lem-sel! g none' < x > = selnone x
  lem-sel! g th' (sel' ph' ts') = 
    sel (eval th') (sel (eval ph') (eval ts')) < sel^^ (eval th') (eval ph') (eval ts') ]~
    sel (eval th' ^^ eval ph') (eval ts') ~[ sel $~ lem-comp! th' ph' ~$~ r~ >
    sel (eval (comp! th' ph')) (eval ts') ~[ lem-sel! g _ ts' >
    eval (sel! g (comp! th' ph') ts') [QED]
  lem-sel! g th' (ts' ^Tm' ph') = 
    sel (eval th') (eval ts' ^Tm eval ph') ~[ Act.sel-act Thin (eval th') (eval ts') (eval ph') >
    (sel (eval th') (eval ts') ^Tm eval ph') ~[ (_^Tm eval ph') $~ lem-sel! g th' ts' >
    (eval (sel! g th' ts') ^Tm eval ph') [QED]
  lem-sel! g th' (ts' /Tm' sg') =
    sel (eval th') (eval ts' /Tm eval sg') ~[ Act.sel-act Sbst (eval th') (eval ts') (eval sg') >
    (sel (eval th') (eval ts') /Tm eval sg') ~[ (_/Tm eval sg') $~ lem-sel! g th' ts' >
    (eval (sel! g th' ts') /Tm eval sg') [QED]
  lem-sel! g < x > (pair vect ts' t') = {!!} -- r~
  lem-sel! g (th' no') (pair vect ts' t') = lem-sel! g th' ts' 
  lem-sel! g (th' su') (pair vect ts' t') = (_` _) $~ lem-sel! g th' ts'
  lem-sel! g iota' (pair vect ts' t') = seliota _
  lem-sel! g (th' ^^' th'') (pair vect ts' t') = {!!} -- r~
  lem-sel! g none' (pair vect ts' t') = selnone (eval ts')
  lem-sel! g < _ > (top' ts') = {!!} -- r~
  lem-sel! g (_ no') (top' ts') = {!!} -- r~
  lem-sel! g (_ su') (top' ts') = {!!} -- r~
  lem-sel! g iota' (top' ts') = seliota _
  lem-sel! g (_ ^^' _) (top' ts') = {!!} -- r~
  lem-sel! g none' (top' ts') = selnone (top (eval ts'))
  lem-sel! g < _ > (! x) = {!!} -- r~
  lem-sel! g iota' (! x) = seliota _
  lem-sel! g (_ ^^' _) (! x) = {!!} -- r~
  lem-sel! g none' (! x) = selnone (! x)
  lem-sel! ([] su) th' (thsb' ph') = 
    sel (eval th') (thsb (eval ph')) ~[ help (eval th') (eval ph') >
    thsb (eval th' ^^ eval ph') ~[ thsb $~ lem-comp! th' ph' >
    thsb (eval (comp! th' ph')) [QED]
    where
    help : forall {p n m}(th : p <= n)(ph : n <= m) -> sel th (thsb ph) ~ thsb (th ^^ ph)
    yelp : forall {p n m}(th : p <= n)(ph : n <= m) ->
      sel' < th > (thsb' < ph > ^Tm' (iota' no')) ~' (thsb' (< th > ^^' < ph >) ^Tm' (iota' no'))
    help th (ph no) = unpack (yelp th ph)
    help (th no) (ph su) = unpack (yelp th ph)
    help (th su) (ph su) = (_` _) $~ unpack (yelp th ph)
    help [] [] = r~
    yelp th ph = 
      sel' < th > (thsb' < ph > ^Tm' (iota' no')) ~'[ solve [] r~ >
      (sel' < th > (thsb' < ph >) ^Tm' (iota' no')) ~'[ pack ((_^Tm _) $~ help th ph) >
      (thsb' (< th > ^^' < ph >) ^Tm' (iota' no')) [QED]'
  lem-sel! [] < x > (thsb' ph') = r~
  lem-sel! [] (th' no') (thsb' ph') = r~
  lem-sel! [] (th' su') (thsb' ph') = r~
  lem-sel! [] iota' (thsb' ph') = seliota _
  lem-sel! [] (_ ^^' _) (thsb' ph') = r~
  lem-sel! [] none' (thsb' ph') = selnone (thsb (eval ph'))
  lem-sel! [] < _ > < _ > = r~
  lem-sel! g th' sg' = {!!}

  lem-thin! : forall g {d n m}(t' : Quo (Tm' n d))(th' : Quo (n <=' m)) ->
    (eval t' ^Tm eval th') ~ eval (thin! g t' th')
  lem-thin! g (pair p s' t') th' = pair p $~ lem-thin! g s' th' ~$~ lem-thin! g t' th'
  lem-thin! g (! a) th' = r~
  lem-thin! g (^ t') th' = ^_ $~ (
    (eval t' ^Tm (eval th' su)) ~[ (eval t' ^Tm_) $~ lem-su! th' >
    (eval t' ^Tm eval (su! th')) ~[ lem-thin! g t' (su! th') >
    eval (thin! g t' (su! th')) [QED])
  lem-thin! g [ e' ] th' = [_] $~ lem-thin! g e' th'
  lem-thin! g (# x') th' = #_ $~ lem-comp! x' th'
  lem-thin! g (w / t') th' = (w /_) $~ lem-thin! g t' th'
  lem-thin! [] < x > th' = r~
  lem-thin! [] (thsb' t') th' = r~
  lem-thin! [] (sel' th' ts') ph' = r~
  lem-thin! [] (top' ts') th' = r~
  lem-thin! [] (t' ^Tm' th') ph' = r~
  lem-thin! [] (t' /Tm' sg') th' = r~
  lem-thin! (g su su su) (thsb' th') ph' = {!!}
  lem-thin! ([] su su) (thsb' th') ph' = 
    (thsb (eval th') ^Tm eval ph') ~[ help (eval th') (eval ph') >
    thsb (eval th' ^^ eval ph') ~[ thsb $~ lem-comp! th' ph' >
    thsb (eval (comp! th' ph')) [QED]
    where
    help : forall {p n m}(th : p <= n)(ph : n <= m) ->
      (thsb th ^Tm ph) ~ thsb (th ^^ ph)
    help th (ph no) = unpack (
      (thsb' < th > ^Tm' (< ph > no')) ~'[ solve ([] su) r~ >
      ((thsb' < th > ^Tm' < ph >) ^Tm' (iota' no')) ~'[ pack ((_^Tm (iota no)) $~ help th ph) >
      (thsb' (< th > ^^' < ph >) ^Tm' (iota' no')) [QED]')
    help (th no) (ph su) = unpack (
      ((thsb' < th > ^Tm' (iota' no')) ^Tm' (< ph > su')) ~'[ solve ([] su) r~ >
      ((thsb' < th > ^Tm' < ph >) ^Tm' (iota' no')) ~'[ pack ((_^Tm (iota no)) $~ help th ph) >
      (thsb' (< th > ^^' < ph >) ^Tm' (iota' no')) [QED]')
    help (th su) (ph su) = unpack (
      ((pair vect (thsb' < th > ^Tm' (iota' no')) (# (none' su'))) ^Tm' (< ph > su')) ~'[ solve ([] su) r~ >
      (pair vect ((thsb' < th > ^Tm' < ph >) ^Tm' (iota' no')) (# (none' su')))
        ~'[ pack ((_` _) $~ ((_^Tm (iota no)) $~ help th ph)) >
      (pair vect (thsb' (< th > ^^' < ph >) ^Tm' (iota' no')) (# (none' su'))) [QED]')
    help [] [] = r~
  lem-thin! ([] su) (thsb' t') < x > = r~
  lem-thin! ([] su) (thsb' t') (th' no') = r~
  lem-thin! ([] su) (thsb' t') (th' su') = r~
  lem-thin! ([] su) (thsb' t') iota' = {!!}
  lem-thin! ([] su) (thsb' t') (th' ^^' th'') = r~
  lem-thin! ([] su) (thsb' t') none' = r~
  lem-thin! (g su su) (t' ^Tm' th') ph' = {!!}
  lem-thin! ([] su) (t' ^Tm' th') ph' = 
    ((eval t' ^Tm eval th') ^Tm eval ph') ~[ help (eval t') (eval th') (eval ph') >
    (eval t' ^Tm (eval th' ^^ eval ph')) ~[ (eval t' ^Tm_) $~ lem-comp! th' ph' >
    (eval t' ^Tm eval (comp! th' ph')) ~[ lem-thin! ([] su) t' _ >
    eval (thin! ([] su) t' (comp! th' ph')) [QED]
    where
    help : forall {d p n m}(t : Tm p d)(th : p <= n)(ph : n <= m) ->
      ((t ^Tm th) ^Tm ph) ~ (t ^Tm (th ^^ ph))
    help t th ph =
      ((t ^Tm th) ^Tm ph) < actComp Thin Thin t th ph ]~
      (Act.act (Comp Thin Thin) t (_ , th , ph)) ~[ actSim (Comp Thin Thin) Thin t (sim th ph) >
      (t ^Tm (th ^^ ph)) [QED]
      where
      sim : forall {p n m}(th : p <= n)(ph : n <= m) ->
        Sim (Comp Thin Thin) Thin (_ , th , ph) (th ^^ ph)
      Sim.variQ (sim th ph) x = unpack (solve [] {_}
        {# ((< x > ^^' < th >) ^^' < ph >)}
        {# (< x > ^^' (< th > ^^' < ph >))}
        r~) 
      Sim.succS (sim th ph) = sim (th su) (ph su)
  lem-thin! (g su) < x > th' = {!!}
  lem-thin! (g su) (sel' th' ts') ph' = {!!}
  lem-thin! (g su) (top' ts') th' = {!!}
  lem-thin! (g su) (t' /Tm' sg') th' = {!!}

  solve g {T} {s'} {t'} q =
    s' ~'[ solveLemma g s' >
    norm g s' ~'[ pack (eval $~ q) >
    norm g t' < solveLemma g t' ]~'
    t' [QED]'
  unpack (solveLemma g < t >) = r~
  unpack (solveLemma g (th' no')) = _no $~ unpack (solveLemma g th')
  unpack (solveLemma g (th' su')) = 
    (eval th' su) ~[ _su $~ unpack (solveLemma g th') >
    (eval (norm g th') su) ~[ lem-su! (norm g th') >
    eval (su! (norm g th')) [QED]
  unpack (solveLemma g iota') = r~
  unpack (solveLemma g (th' ^^' ph')) = 
    (eval th' ^^ eval ph') ~[ _^^_ $~ unpack (solveLemma g th') ~$~ unpack (solveLemma g ph') >
    (eval (norm g th') ^^ eval (norm g ph')) ~[ lem-comp! (norm g th') (norm g ph') >
    eval (comp! (norm g th') (norm g ph')) [QED]
  unpack (solveLemma g none') = r~
  solveLemma g (pair p s' t') = {!!}
  unpack (solveLemma g (! a)) = r~
  unpack (solveLemma g (^ t')) = ^_ $~ unpack (solveLemma g t')
  unpack (solveLemma g [ e' ]) = [_] $~ unpack (solveLemma g e')
  unpack (solveLemma g (# x')) = #_ $~ unpack (solveLemma g x')
  unpack (solveLemma g (w / es')) = (w /_) $~ unpack (solveLemma g es')
  unpack (solveLemma g (thsb' th')) = thsb $~ unpack (solveLemma g th')
  unpack (solveLemma g (sel' th' ts')) = 
    sel (eval th') (eval ts') ~[ sel $~ unpack (solveLemma g th') ~$~ unpack (solveLemma g ts') >
    sel (eval (norm g th')) (eval (norm g ts')) ~[ lem-sel! g (norm g th') (norm g ts') >
    eval (sel! g (norm g th') (norm g ts')) [QED]
  solveLemma g (top' ts') = {!!}
  unpack (solveLemma g (t' ^Tm' th')) = 
    (eval t' ^Tm eval th') ~[ _^Tm_ $~ unpack (solveLemma g t') ~$~ unpack (solveLemma g th') >
    (eval (norm g t') ^Tm eval (norm g th')) ~[ lem-thin! g (norm g t') (norm g th') >    
    eval (thin! g (norm g t') (norm g th')) [QED]
  solveLemma g (t' /Tm' sg') = {!!}

{-

  _^Tm-iota : forall {d n}(t : Tm n d) -> (t ^Tm iota) ~ t
  t ^Tm-iota = 
    (t ^Tm iota) ~[ actSim Thin Iden t sim >
    Act.act Iden t r~ ~[ actIden t >
    t [QED]
    where
    sim : forall {n} -> Sim Thin Iden {n} iota r~
    Sim.variQ sim x = #_ $~ (x ^^iota)
    Sim.succS sim = sim

  thin-thin : forall {d p n m}(t : Tm p d)(th : p <= n)(ph : n <= m) ->
    ((t ^Tm th) ^Tm ph) ~ (t ^Tm (th ^^ ph))
  thin-thin t th ph = 
     ((t ^Tm th) ^Tm ph) < actComp Thin Thin t th ph ]~
     (Act.act (Comp Thin Thin) t (_ , th , ph)) ~[ actSim (Comp Thin Thin) Thin t (sim th ph) >
     (t ^Tm (th ^^ ph)) [QED]
     where
     sim : forall {p n m}(th : p <= n)(ph : n <= m) ->
       Sim (Comp Thin Thin) Thin (_ , th , ph) (th ^^ ph)
     Sim.variQ (sim th ph) x = #_ $~ sym (thinAssoc x th ph)
     Sim.succS (sim th ph) = sim (th su) (ph su)

  sel-thsb : forall {p n m}(th : p <= n)(ph : n <= m) ->
    sel th (thsb ph) ~ thsb (th ^^ ph)
  sel-thsb th (ph no) = 
    sel th (thsb ph ^Tm (iota no)) ~[ Act.sel-act Thin th (thsb ph) (iota no) >
    (sel th (thsb ph) ^Tm (iota no)) ~[ (_^Tm (iota no)) $~ sel-thsb th ph >
    (thsb (th ^^ ph) ^Tm (iota no)) [QED]
  sel-thsb (th no) (ph su) =
    sel th (thsb ph ^Tm (iota no)) ~[ Act.sel-act Thin th (thsb ph) (iota no) >
    (sel th (thsb ph) ^Tm (iota no)) ~[ (_^Tm (iota no)) $~ sel-thsb th ph >
    (thsb (th ^^ ph) ^Tm (iota no)) [QED]
  sel-thsb (th su) (ph su) = (_` _) $~ (
    sel th (thsb ph ^Tm (iota no)) ~[ Act.sel-act Thin th (thsb ph) (iota no) >
    (sel th (thsb ph) ^Tm (iota no)) ~[ (_^Tm (iota no)) $~ sel-thsb th ph >
    (thsb (th ^^ ph) ^Tm (iota no)) [QED] )
  sel-thsb [] [] = r~

  top-thsb : forall {n}(x : Fi n) -> top (thsb x) ~ (# x)
  top-thsb (x no) = 
    top (thsb x ^Tm (iota no)) ~[ Act.top-act Thin (thsb x) (iota no) >
    (top (thsb x) ^Tm (iota no)) ~[ (_^Tm (iota no)) $~ top-thsb x >
    (# (x ^^ iota no)) ~[ #_ $~ (_no $~ (x ^^iota)) >
    (# (x no)) [QED]
  top-thsb (x su) = #_ $~ (_su $~ none~ _ _)

  thsb-^Tm : forall {p n m}(th : p <= n)(ph : n <= m) ->
    (thsb th ^Tm ph) ~ thsb (th ^^ ph)
  thsb-^Tm-shoogle : forall {p n m}(th : p <= n)(ph : n <= m) ->
    ((thsb th ^Tm (iota no)) ^Tm (ph su)) ~
    (thsb (th ^^ ph) ^Tm (iota no))
    
  thsb-^Tm th (ph no) = 
    (thsb th ^Tm (ph no)) < (thsb th ^Tm_) $~ (_no $~ (ph ^^iota)) ]~
    (thsb th ^Tm (ph ^^ iota no)) < thin-thin (thsb th) ph (iota no) ]~
    ((thsb th ^Tm ph) ^Tm (iota no)) ~[ (_^Tm (iota no)) $~ thsb-^Tm th ph >
    (thsb (th ^^ ph) ^Tm (iota no)) [QED]
  thsb-^Tm (th no) (ph su) = thsb-^Tm-shoogle th ph  
  thsb-^Tm (th su) (ph su) = _`_
    $~ thsb-^Tm-shoogle th ph
    ~$~ (#_ $~ (_su $~ none~ _ _))
  thsb-^Tm [] [] = r~
  thsb-^Tm-shoogle th ph =
    ((thsb th ^Tm (iota no)) ^Tm (ph su)) ~[ thin-thin (thsb th) (iota no) (ph su) >
    (thsb th ^Tm (iota ^^ ph no)) ~[ (thsb th ^Tm_) $~ (_no $~ (
      (iota ^^ ph) ~[ iota^^ ph > ph < ph ^^iota ]~ (ph ^^ iota) [QED])) >
    (thsb th ^Tm (ph ^^ iota no)) < thin-thin (thsb th) ph (iota no) ]~
    ((thsb th ^Tm ph) ^Tm (iota no)) ~[ (_^Tm (iota no)) $~ thsb-^Tm th ph >
    (thsb (th ^^ ph) ^Tm (iota no)) [QED]
  
  _/Tm-thsb_ : forall {d n m}(t : Tm n d)(th : n <= m) ->
    (t /Tm thsb th) ~ (t ^Tm th)
  t /Tm-thsb th = actSim Sbst Thin t (sim th) where
    sim : forall {n m}(th : n <= m) -> Sim Sbst Thin (thsb th) th
    Sim.variQ (sim th) x = 
      top (sel x (thsb th)) ~[ top $~ sel-thsb x th >
      top (thsb (x ^^ th)) ~[ top-thsb (x ^^ th) >
      (# (x ^^ th)) [QED]
    Sim.succS (sim th) rewrite thsb-^Tm th (iota no) | th ^^iota = sim (th su)

  thin-sbst : forall {d p n m}(t : Tm p d)(th : p <= n)(sg : n => m) ->
    ((t ^Tm th) /Tm sg) ~ (t /Tm (sel th sg))
  thin-sbst t th sg = 
    ((t ^Tm th) /Tm sg) < actComp Thin Sbst t th sg ]~
    Act.act (Comp Thin Sbst) t (_ , th , sg) ~[ actSim _ _ t (sim th sg) >
    (t /Tm (sel th sg)) [QED]
    where
    sim : forall {p n m}(th : p <= n)(sg : n => m) ->
      Sim (Comp Thin Sbst) Sbst (_ , th , sg) (sel th sg)
    Sim.variQ (sim th sg) x = top $~ sel^^ x th sg
    Sim.succS (sim th sg)
      rewrite sym (Act.sel-act Thin th sg (iota no))
      = sim (th su) (Act.succ Sbst sg)

  sbst-thin : forall {d p n m}(t : Tm p d)(sg : p => n)(th : n <= m) ->
    ((t /Tm sg) ^Tm th) ~ (t /Tm (sg ^Tm th))
  sbst-thin t sg th = 
    ((t /Tm sg) ^Tm th) < actComp Sbst Thin t sg th ]~
    Act.act (Comp Sbst Thin) t (_ , sg , th) ~[ actSim _ _ t (sim sg th) >
    (t /Tm (sg ^Tm th)) [QED]
    where
    lem : forall {p n m}(sg : p => n)(th : n <= m) ->
            (((sg ^Tm th) ^Tm (iota no)) ` (# (none su)))
          ~ (((sg ^Tm (iota no)) ^Tm (th su)) ` (# (none ^^ th su)))
    lem sg th = _`_
      $~  (((sg ^Tm th) ^Tm (iota no)) ~[ thin-thin sg _ _ >
           (sg ^Tm (th ^^ iota no)) ~[ (sg ^Tm_) $~ (_no $~ (
              (th ^^ iota) ~[ th ^^iota > th < iota^^ th ]~ (iota ^^ th) [QED])) >
           (sg ^Tm (iota ^^ th no)) < thin-thin sg _ _ ]~
           ((sg ^Tm (iota no)) ^Tm (th su)) [QED])
      ~$~ (#_ $~ (_su $~ none~ _ _ ))
    sim : forall {p n m}(sg : p => n)(th : n <= m) ->
      Sim (Comp Sbst Thin) Sbst (_ , sg , th) (sg ^Tm th)
    Sim.variQ (sim sg th) x = 
      ((top (sel x sg)) ^Tm th) < Act.top-act Thin (sel x sg) th ]~
      top (sel x sg ^Tm th) < top $~ Act.sel-act Thin x sg th ]~
      top (sel x (sg ^Tm th)) [QED]
    Sim.succS (sim sg th) rewrite lem sg th = sim (Act.succ Sbst sg) (th su)

  sbst-sbst : forall {d p n m}(t : Tm p d)(sg : p => n)(ta : n => m) ->
    ((t /Tm sg) /Tm ta) ~ (t /Tm (sg /Tm ta))
  sbst-sbst t sg ta = 
    ((t /Tm sg) /Tm ta) < actComp Sbst Sbst t sg ta ]~
    Act.act (Comp Sbst Sbst) t (_ , sg , ta) ~[ actSim _ _ t (sim sg ta) >
    (t /Tm (sg /Tm ta)) [QED]
    where
    lem : forall {p n m}(sg : p => n)(ta : n => m) ->
            (((sg /Tm ta) ^Tm (iota no)) ` (# (none su)))
          ~ (((sg ^Tm (iota no)) /Tm (Act.succ Sbst ta)) ` (# (none su)))
    lem sg ta = (_` _) $~
      (((sg /Tm ta) ^Tm (iota no)) ~[ sbst-thin sg _ _ >
       (sg /Tm (ta ^Tm (iota no))) < (sg /Tm_) $~ seliota _ ]~
       (sg /Tm (sel (iota no) (Act.succ Sbst ta))) < thin-sbst sg _ _ ]~
       ((sg ^Tm (iota no)) /Tm Act.succ Sbst ta) [QED])
    sim : forall {p n m}(sg : p => n)(ta : n => m) ->
      Sim (Comp Sbst Sbst) Sbst (_ , sg , ta) (sg /Tm ta)
    Sim.variQ (sim sg ta) x =
      ((top (sel x sg)) /Tm ta) < Act.top-act Sbst (sel x sg) ta ]~
      top (sel x sg /Tm ta) < top $~ Act.sel-act Sbst x sg ta ]~
      top (sel x (sg /Tm ta)) [QED]
    Sim.succS (sim sg ta) rewrite lem sg ta =
      sim (Act.succ Sbst sg) (Act.succ Sbst ta)

  module _ {n m l}(th : n <= m)(sg : m => l) where

    thsb-/Tm : forall {n m l}(th : n <= m)(sg : m => l) ->
      (thsb th /Tm sg) ~ sel th sg
    thsb-/Tm-lem : forall {n m l}(th : n <= m)(sg : m => l) e ->
      ((thsb th ^Tm (iota no)) /Tm (sg ` e)) ~ sel th sg
    thsb-/Tm-lem th sg e = 
       ((thsb th ^Tm (iota no)) /Tm (sg ` e))
          ~[ thin-sbst (thsb th) _ _ >
        (thsb th /Tm sel (iota no) (sg ` e))
          ~[ thsb-/Tm th _ >
        sel th (sel iota sg)
          ~[ sel th $~ seliota sg >
        sel th sg [QED]
    
    thsb-/Tm (th no) (sg ` e) = thsb-/Tm-lem th sg e
    thsb-/Tm (th su) (sg ` e) = (_` e) $~ thsb-/Tm-lem th sg e
    thsb-/Tm [] (! r~) = r~

{-
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
-}
-}
-}
