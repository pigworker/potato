module Meta where

open import Eq
open import Tuple
open import Thin
open import Tm

data Ty' : Set where
  Tm' : Nat -> Dir -> Ty'
  _*'_ _->'_ : Ty' -> Ty' -> Ty'
  Aye' : Ty'

infixr 5 _->'_
infixr 6 _*'_

_+[_] : Nat -> Ty' -> Set
n +[ Tm' m d ]    = Tm (n +B m) d
n +[ M *' N ]     = (n +[ M ]) * (n +[ N ])
n +[ M ->' N ]    = n +[ M ] -> One + (n +[ N ])
n +[ Aye' ]       = One

Vec' : Ty' -> Nat -> Ty'
Vec' T (n su) = Vec' T n *' T
Vec' T [] = Aye'

  
infix 4 _:-_

data _:-_ (G : Bwd Ty') : Ty' -> Set where

  ?'_  : forall {T}
      -> T <- G
      -> G :- T
      
  \'_  : forall {S T}
      -> G -, S :- T
      -> G :- S ->' T
      
  _$'_ : forall {S T}
      -> G :- S ->' T
      -> G :- S
      -> G :- T
      
  aye' : G :- Aye'
  
  _,'_ : forall {S T}
      -> G :- S
      -> G :- T
      -> G :- S *' T
      
  unc' : forall {S T U}
      -> G :- S ->' T ->' U
      -> G :- S *' T ->' U

  naw' : forall {T}
      -> G :- T

  sub' : forall {n d} -> (m : Nat)
      -> G :- Tm' (n +B m) d
      -> G :- Vec' (Tm' n syn) m
      -> G :- Tm' n d

  mat' : forall {n T}
      -> (Atom -> G :- T)
      -> G :- Tm' n chk ->' Tm' n chk ->' T
      -> G :- Tm' n chk *' (Tm' (n su) chk ->' T)
      -> G :- Tm' n chk ->' T

  _/_  : forall {T}
      -> G :- Aye'
      -> G :- T
      -> G :- T

  chk' : forall {n}            -- this is a placeholder
      -> G :- Tm' n chk
      -> G :- Tm' n chk
      -> G :- Aye'

  !_   : {n : Nat} -> Atom -> G :- Tm' n chk
  _&_  : {n : Nat} -> G :- Tm' n chk -> G :- Tm' n chk -> G :- Tm' n chk
  ^_   : {n : Nat} -> G :- Tm' (n su) chk -> G :- Tm' n chk
  `_   : {n : Nat} -> G :- Tm' n syn -> G :- Tm' n chk
  #_   : {n : Nat} -> Fi n -> G :- Tm' n syn
  _$_  : {n : Nat} -> G :- Tm' n syn -> G :- Tm' n chk -> G :- Tm' n syn
  _::_ : {n : Nat} -> G :- Tm' n chk -> G :- Tm' n chk -> G :- Tm' n syn

atom' : forall {n G T}
      -> (Atom -> G :- T)
      -> G :- Tm' n chk ->' T
atom' f = mat' f naw' naw'

cons' : forall {n G T}
      -> G :- Tm' n chk ->' Tm' n chk ->' T
      -> G :- Tm' n chk ->' T
cons' f = mat' (\ _ -> naw') f naw'

abst' : forall {n G T}
      -> G :- Tm' n chk
      -> G :- Tm' (n su) chk ->' T
      -> G :- Tm' n chk ->' T
abst' S f = mat' (\ _ -> naw') naw' (S ,' f)

yer : forall {G T} -> Atom -> G :- T -> Atom -> G :- T
yer a p b with a ~Atom?~ b
yer a p b | ff , _ = naw'
yer a p b | tt , _ = p


En' : Nat -> Bwd Ty' -> Set
En' n G = forall {T} -> T <- G -> n +[ T ]

E0' : forall {n} -> En' n []
E0' ()

vecSb : forall {n p} m -> n +[ Vec' (Tm' p syn) m ] -> Sb m (n +B p)
vecSb (m su) (sg , e) (i no) = vecSb m sg i
vecSb (m su) (sg , e) (i su) = e

locSb : forall {n p} m -> Sb m (n +B p) -> Sb (n +B (p +B m)) (n +B p)
locSb (m su) sg (i no) = locSb m (\ j -> sg (j no)) i
locSb (m su) sg (i su) = sg (none su)
locSb [] sg i = # i

locSbExt : forall {n p} m (sg0 sg1 : Sb m (n +B p)) ->
           (forall i -> sg0 i ~ sg1 i) ->
           forall j -> locSb {n}{p} m sg0 j ~ locSb {n}{p} m sg1 j
locSbExt (m -, x) sg0 sg1 q (j -^ .x) = locSbExt m _ _ (\ i -> q (i no)) j
locSbExt (m -, .<>) sg0 sg1 q (j -, .<>) = q (none su)
locSbExt [] sg0 sg1 q j = r~


[_]P : forall {n G T} -> G :- T -> En' n G -> One + (n +[ T ])
match : forall {n m G T}
      -> (Atom -> G :- T)
      -> G :- Tm' m chk ->' Tm' m chk ->' T
      -> G :- Tm' m chk *' (Tm' (m su) chk ->' T)
      -> En' n G -> Tm (n +B m) chk -> One + (n +[ T ])
[ ?' i        ]P g = tt , g i
[ \' t        ]P g = tt , \ s -> [ t ]P (g -push s)
[ f $' s      ]P g = [ f ]P g >>= \ f -> [ s ]P g >>= \ s -> f s
[ aye'        ]P g = tt , <>
[ s ,' t      ]P g = [ s ]P g >>= \ s -> [ t ]P g >>= \ t -> tt , s , t
[ unc' f      ]P g = [ f ]P g >>= \ f -> tt , \ { (s , t) -> f s >>= \ f -> f t }
[ naw'        ]P g = ff , <>
[ sub' m t sg ]P g = [ t ]P g >>= \ t -> [ sg ]P g >>= \ sg -> tt , (t /Tm locSb m (vecSb m sg))
[ mat' q c l  ]P g = tt , match q c l g
[ c / t       ]P g = [ c ]P g >>= \ _ -> [ t ]P g
[ chk' T t    ]P g = [ T ]P g >>= \ T -> [ t ]P g >>= \ t -> tt , <>
[ ! a         ]P g = tt , ! a
[ s & t       ]P g = [ s ]P g >>= \ s -> [ t ]P g >>= \ t -> tt , s & t
[ ^ t         ]P g = [ t ]P g >>= \ t -> tt , ^ t
[ ` e         ]P g = [ e ]P g >>= \ e -> tt , ` e
[ # x         ]P g = tt , # (x ^^ thinr)
[ e $ s       ]P g = [ e ]P g >>= \ e -> [ s ]P g >>= \ s -> tt , e $ s
[ t :: T      ]P g = [ t ]P g >>= \ t -> [ T ]P g >>= \ T -> tt , t :: T
match q c l g (! a)   = [ q a ]P g
match q c l g (s & t) = [ c ]P g >>= \ c -> c s >>= \ d -> d t
match q c l g (^ t)   = [ l ]P g >>= \ (S , l) -> l t
match q c l g (` e)   = ff , <>

data MayLift {X Y}(L : X -> Y -> Set) : One + X -> One + Y -> Set where
  no : forall {my} -> MayLift L (ff , <>) my
  ye : forall {x y} -> L x y -> MayLift L (tt , x) (tt , y)

record REL {n0 n1}(L : forall m {d} -> Tm (n0 +B m) d -> Tm (n1 +B m) d -> Set) : Set where
  field
    localSb : forall {n m d}
              (t0 : Tm (n0 +B (n +B m)) d)(t1 : Tm (n1 +B (n +B m)) d) ->
              L (n +B m) t0 t1 ->
              (sg0 : Sb m (n0 +B n))(sg1 : Sb m (n1 +B n)) ->
              (forall i -> L n (sg0 i) (sg1 i)) ->
              L n (t0 /Tm locSb m sg0) (t1 /Tm locSb m sg1)
    atomInv : forall {m a t} -> L m (! a) t -> t ~ ! a
    consInv : forall {m s t u} -> L m (s & t) u -> (_ * _) >< \ (s' , t') -> u ~ s' & t' * L m s s' * L m t t'
    abstInv : forall {m t u} -> L m (^ t) u -> _ >< \ t' -> u ~ ^ t' * L (m su) t t'
    atomOk : forall {m} a -> L m (! a) (! a)
    consOk : forall {m s0 s1 t0 t1} -> L m s0 s1 -> L m t0 t1 -> L m (s0 & t0) (s1 & t1)
    abstOk : forall {m t0 t1} -> L (m su) t0 t1 -> L m (^ t0) (^ t1)
    embdOk : forall {m e0 e1} -> L m e0 e1 -> L m (` e0) (` e1)
    loclOk : forall {n}(x : Fi n) -> L n (# (x ^^ thinr)) (# (x ^^ thinr))
    elimOk : forall {m e0 e1 s0 s1} -> L m e0 e1 -> L m s0 s1 -> L m (e0 $ s0) (e1 $ s1)
    radiOk : forall {m t0 t1 T0 T1} -> L m t0 t1 -> L m T0 T1 -> L m (t0 :: T0) (t1 :: T1)
    
  Lift : (T : Ty') -> n0 +[ T ] -> n1 +[ T ] -> Set
  Lift (Tm' m d) t0        t1        = L m t0 t1
  Lift (S *' T)  (s0 , t0) (s1 , t1) = Lift S s0 s1 * Lift T t0 t1
  Lift (S ->' T) f0        f1        = forall s0 s1 -> Lift S s0 s1 -> MayLift (Lift T) (f0 s0) (f1 s1) 
  Lift Aye'      <>        <>        = One

  lift : forall {G T}(p : G :- T)(ga0 : En' n0 G)(ga1 : En' n1 G) ->
         (forall {S}(i : S <- G) -> Lift S (ga0 i) (ga1 i)) ->
         MayLift (Lift T) ([ p ]P ga0) ([ p ]P ga1)
  lift (?' i) ga0 ga1 ga = ye (ga i)
  lift (\' p) ga0 ga1 ga = ye \ s0 s1 s ->
    lift p (ga0 -push s0) (ga1 -push s1) \
      { (i -^ x) -> ga i
      ; (i -, x) -> s
      }
  lift (f $' a) ga0 ga1 ga with [ f ]P ga0 | [ f ]P ga1 | lift f ga0 ga1 ga
  lift (f $' a) ga0 ga1 ga | .(ff , <>) | f1 | no = no
  lift (f $' a) ga0 ga1 ga | .(tt , _) | .(tt , _) | ye fl with [ a ]P ga0 | [ a ]P ga1 | lift a ga0 ga1 ga
  lift (f $' a) ga0 ga1 ga | .(tt , _) | .(tt , _) | ye fl | .(ff , <>) | a1 | no = no
  lift (f $' a) ga0 ga1 ga | .(tt , _) | .(tt , _) | ye fl | .(tt , _) | .(tt , _) | ye al = fl _ _ al
  lift aye' ga0 ga1 ga = ye <>
  lift (s ,' t) ga0 ga1 ga with [ s ]P ga0 | [ s ]P ga1 | lift s ga0 ga1 ga | [ t ]P ga0 | [ t ]P ga1 | lift t ga0 ga1 ga
  lift (s ,' t) ga0 ga1 ga | .(ff , <>) | s1 | no | t0 | t1 | tl = no
  lift (s ,' t) ga0 ga1 ga | .(tt , _) | .(tt , _) | ye _ | .(ff , <>) | t1 | no = no
  lift (s ,' t) ga0 ga1 ga | .(tt , _) | .(tt , _) | ye sl | .(tt , _) | .(tt , _) | ye tl = ye (sl , tl)
  lift (unc' f) ga0 ga1 ga with [ f ]P ga0 | [ f ]P ga1 | lift f ga0 ga1 ga
  lift (unc' f) ga0 ga1 ga | .(ff , <>) | f1 | no = no
  lift (unc' {S}{T}{U} f) ga0 ga1 ga | (tt , f0) | (tt , f1) | ye fl = ye help where
    help : ((s0 , t0) : (n0 +[ S ]) * (n0 +[ T ]))((s1 , t1) : (n1 +[ S ]) * (n1 +[ T ])) ->
           Lift S s0 s1 * Lift T t0 t1 ->
           MayLift (Lift U) (f0 s0 >>= \ k -> k t0) (f1 s1 >>= \ k -> k t1)
    help (s0 , t0) (s1 , t1) (sl , tl) with f0 s0 | f1 s1 | fl s0 s1 sl
    help (s0 , t0) (s1 , t1) (sl , tl) | .(ff , <>) | k1 | no = no
    help (s0 , t0) (s1 , t1) (sl , tl) | .(tt , _) | .(tt , _) | ye kl = kl t0 t1 tl
  lift naw' ga0 ga1 ga = no
  lift (sub' m t sg) ga0 ga1 ga with [ t ]P ga0 | [ t ]P ga1 | lift t ga0 ga1 ga | [ sg ]P ga0 | [ sg ]P ga1 | lift sg ga0 ga1 ga
  lift (sub' m t sg) ga0 ga1 ga | .(ff , <>) | t1 | no | sg0 | sg1 | sgl = no
  lift (sub' m t sg) ga0 ga1 ga | .(tt , _) | .(tt , _) | ye _ | .(ff , <>) | sg1 | no = no
  lift (sub' m t sg) ga0 ga1 ga | .(tt , _) | .(tt , _) | ye tl | (tt , sg0) | (tt , sg1) | ye sgl =
    ye (localSb _ _ tl (vecSb m sg0) (vecSb m sg1) (help m sg0 sg1 sgl)) where
      help : forall m (sg0 : n0 +[ Vec' (Tm' _ syn) m ])
                      (sg1 : n1 +[ Vec' (Tm' _ syn) m ]) ->
         Lift (Vec' (Tm' _ syn) m) sg0 sg1 ->
         (i : [] su <= m) -> L _ (vecSb m sg0 i) (vecSb m sg1 i)
      help .(_ su) (sg0 , e0) (sg1 , e1) (sgl , el) (i no) = help _ sg0 sg1 sgl i
      help .(_ su) (sg0 , e0) (sg1 , e1) (sgl , el) (i su) = el
  lift (mat' {n}{T} q c l) ga0 ga1 ga = ye help where
    help : (s0 : Tm (n0 +B n) chk) (s1 : Tm (n1 +B n) chk) ->
           L n s0 s1 ->
           MayLift (Lift T) (match q c l ga0 s0) (match q c l ga1 s1)
    help (! a0) u1 ul with r~ <- atomInv ul = lift (q a0) ga0 ga1 ga
    help (s0 & t0) u ul with consInv ul
    ... | (s1 , t1) , r~ , sl , tl with [ c ]P ga0 | [ c ]P ga1 | lift c ga0 ga1 ga
    help (s0 & t0) .(s1 & t1) ul | (s1 , t1) , r~ , sl , tl | .(ff , <>) | c1 | no = no
    help (s0 & t0) .(s1 & t1) ul | (s1 , t1) , r~ , sl , tl | (tt , c0) | (tt , c1) | ye cl with c0 s0 | c1 s1 | cl s0 s1 sl
    help (s0 & t0) .(s1 & t1) ul | (s1 , t1) , r~ , sl , tl | tt , c0 | tt , c1 | ye cl | .(ff , <>) | d1 | no = no
    help (s0 & t0) .(s1 & t1) ul | (s1 , t1) , r~ , sl , tl | tt , c0 | tt , c1 | ye cl | .(tt , _) | .(tt , _) | ye dl = dl t0 t1 tl
    help (^ t0) u ul with abstInv ul
    ... | t1 , r~ , tl with [ l ]P ga0 | [ l ]P ga1 | lift l ga0 ga1 ga
    help (^ t0) .(^ t1) ul | t1 , r~ , tl | .(ff , <>) | l1 | no = no
    help (^ t0) .(^ t1) ul | t1 , r~ , tl | .(tt , _) | .(tt , _) | ye (Sl , ll) = ll t0 t1 tl
    help (` s0) s1 sl = no
  lift (c / p) ga0 ga1 ga with [ c ]P ga0 | [ c ]P ga1 | lift c ga0 ga1 ga
  lift (c / p) ga0 ga1 ga | .(ff , <>) | c1 | no = no
  lift (c / p) ga0 ga1 ga | .(tt , _) | .(tt , _) | ye x = lift p ga0 ga1 ga
  lift (chk' T t) ga0 ga1 ga with [ T ]P ga0 | [ T ]P ga1 | lift T ga0 ga1 ga | [ t ]P ga0 | [ t ]P ga1 | lift t ga0 ga1 ga
  lift (chk' T t) ga0 ga1 ga | .(ff , <>) | T1 | no | t0 | t1 | tl = no
  lift (chk' T t) ga0 ga1 ga | .(tt , _) | .(tt , _) | ye _ | .(ff , <>) | t1 | no = no
  lift (chk' T t) ga0 ga1 ga | .(tt , _) | .(tt , _) | ye Tl | .(tt , _) | .(tt , _) | ye tl = ye <>
  lift (! a) ga0 ga1 ga = ye (atomOk a)
  lift (s & t) ga0 ga1 ga with [ s ]P ga0 | [ s ]P ga1 | lift s ga0 ga1 ga | [ t ]P ga0 | [ t ]P ga1 | lift t ga0 ga1 ga
  lift (s & t) ga0 ga1 ga | .(ff , <>) | s1 | no | t0 | t1 | tl = no
  lift (s & t) ga0 ga1 ga | .(tt , _) | .(tt , _) | ye x | .(ff , <>) | t1 | no = no
  lift (s & t) ga0 ga1 ga | .(tt , _) | .(tt , _) | ye sl | .(tt , _) | .(tt , _) | ye tl = ye (consOk sl tl)
  lift (^ t) ga0 ga1 ga with [ t ]P ga0 | [ t ]P ga1 | lift t ga0 ga1 ga
  lift (^ t) ga0 ga1 ga | .(ff , <>) | t1 | no = no
  lift (^ t) ga0 ga1 ga | .(tt , _) | .(tt , _) | ye tl = ye (abstOk tl)
  lift (` e) ga0 ga1 ga with [ e ]P ga0 | [ e ]P ga1 | lift e ga0 ga1 ga
  lift (` e) ga0 ga1 ga | .(ff , <>) | e1 | no = no
  lift (` e) ga0 ga1 ga | .(tt , _) | .(tt , _) | ye el = ye (embdOk el)
  lift (# x) ga0 ga1 ga = ye (loclOk x)
  lift (e $ s) ga0 ga1 ga with [ e ]P ga0 | [ e ]P ga1 | lift e ga0 ga1 ga | [ s ]P ga0 | [ s ]P ga1 | lift s ga0 ga1 ga
  lift (e $ s) ga0 ga1 ga | .(ff , <>) | e1 | no | s0 | s1 | sl = no
  lift (e $ s) ga0 ga1 ga | .(tt , _) | .(tt , _) | ye x | .(ff , <>) | s1 | no = no
  lift (e $ s) ga0 ga1 ga | .(tt , _) | .(tt , _) | ye el | .(tt , _) | .(tt , _) | ye sl = ye (elimOk el sl)
  lift (t :: T) ga0 ga1 ga with [ t ]P ga0 | [ t ]P ga1 | lift t ga0 ga1 ga | [ T ]P ga0 | [ T ]P ga1 | lift T ga0 ga1 ga
  lift (t :: T) ga0 ga1 ga | .(ff , <>) | t1 | no | T0 | T1 | Tl = no
  lift (t :: T) ga0 ga1 ga | .(tt , _) | .(tt , _) | ye x | .(ff , <>) | T1 | no = no
  lift (t :: T) ga0 ga1 ga | .(tt , _) | .(tt , _) | ye tl | .(tt , _) | .(tt , _) | ye Tl = ye (radiOk tl Tl)

_+Sb_ : forall {n m} -> Sb n m -> forall p -> Sb (n +B p) (m +B p)
sg +Sb (n su) = (sg +Sb n) +1Sb
sg +Sb [] = sg

locSbKem : forall {n0 n1} n m
  (th : n0 <= n1)(sg0 : Sb m (n0 +B n))(sg1 : Sb m (n1 +B n)) ->
  ((i : [] su <= m) -> sg1 i ~ (sg0 i ^Tm (th +th n))) ->
  (x : Fi (n0 +B (n +B m))) ->
  locSb m sg1 (x ^^ (th +th (n +B m))) ~ (locSb m sg0 x ^Tm (th +th n))
locSbKem n (m su) th sg0 sg1 q (x -^ .<>) = locSbKem n m th _ _ (\ i -> q (i -^ <>)) x
locSbKem n (m su) th sg0 sg1 q (x -, .<>) = q (none su)
locSbKem n [] th sg0 sg1 q x = r~

THN : forall {n m}(th : n <= m) -> REL \ p t0 t1 -> t1 ~ (t0 ^Tm (th +th p))
REL.localSb (THN th) {n} {m} t0 _ r~ sg0 sg1 q = 
  ((t0 ^Tm (th +th (n +B m))) /Tm locSb m sg1) ~[ thinSbst t0 _ _ >
  (t0 /Tm (\ i -> locSb m sg1 (i ^^ (th +th (n +B m))))) ~[ extSb t0 _ _ (locSbKem n m th sg0 sg1 q) >
  (t0 /Tm (\ i -> locSb m sg0 i ^Tm (th +th n))) < sbstThin t0 _ _ ]~
  ((t0 /Tm locSb m sg0) ^Tm (th +th n)) [QED]

REL.atomInv (THN th) r~ = r~
REL.consInv (THN th) r~ = _ , r~ , r~ , r~
REL.abstInv (THN th) r~ = _ , r~ , r~

REL.atomOk (THN th) a = r~
REL.consOk (THN th) r~ r~ = r~
REL.abstOk (THN th) r~ = r~
REL.embdOk (THN th) r~ = r~
REL.loclOk (THN th) {n} x = #_ $~ (
  (x ^^ thinr) < (x ^^_) $~ thinrLemma th n ]~
  (x ^^ (thinr ^^ (th +th n))) ~[ thinAssoc _ _ _ >
  (x ^^ thinr ^^ (th +th n)) [QED])
REL.elimOk (THN th) r~ r~ = r~
REL.radiOk (THN th) r~ r~ = r~

locSbLem : forall {n0 n1} n m
  (sg : Sb n0 n1)(sg0 : Sb m (n0 +B n))(sg1 : Sb m (n1 +B n)) ->
  ((i : [] su <= m) -> sg1 i ~ (sg0 i /Tm (sg +Sb n))) ->
  (x : Fi (n0 +B (n +B m))) ->
  ((sg +Sb (n +B m)) x /Tm locSb m sg1) ~ (locSb m sg0 x /Tm (sg +Sb n))
locSbLem {n0}{n1} n (m su) sg sg0 sg1 q (x no) = 
  (((sg +Sb (n +B m)) x ^Tm (iota -^ <>)) /Tm locSb (m su) sg1) ~[ thinSbst ((sg +Sb (n +B m)) x) (iota -^ <>) (locSb (m su) sg1) >
  (((sg +Sb (n +B m)) x) /Tm \ j -> locSb {n1}{n} m (\ j -> sg1 (j -^ <>)) (j ^^ iota)) ~[ 
    extSb ((sg +Sb (n +B m)) x) _ _ (\ j -> locSb m (\ k -> sg1 (k -^ <>)) $~ (j ^^iota) ) >
  (((sg +Sb (n +B m)) x) /Tm locSb {n1}{n} m (\ j -> sg1 (j -^ <>))) ~[ locSbLem n m sg _ _ (\ i -> q (i -^ <>)) x >
  (locSb m (\ j -> sg0 (j -^ <>)) x /Tm (sg +Sb n)) [QED]
locSbLem n (m su) sg sg0 sg1 q (x su) = q (none su)
locSbLem n [] sg sg0 sg1 q x = (sg +Sb n) x /Tm-#

SUB : forall {n m}(sg : Sb n m) -> REL \ p t0 t1 -> t1 ~ (t0 /Tm (sg +Sb p))

REL.localSb (SUB sg) {n} {m} t0 _ r~ sg0 sg1 q = 
  ((t0 /Tm (sg +Sb (n +B m))) /Tm locSb m sg1) ~[ sbstSbst t0 _ _ >
  (t0 /Tm \ i -> (sg +Sb (n +B m)) i /Tm locSb m sg1) ~[ extSb t0 _ _ (locSbLem n m sg sg0 sg1 q) >
  (t0 /Tm \ i -> locSb m sg0 i /Tm (sg +Sb n)) < sbstSbst t0 _ _ ]~
  ((t0 /Tm locSb m sg0) /Tm (sg +Sb n)) [QED]
  
REL.atomInv (SUB sg) r~ = r~
REL.consInv (SUB sg) r~ = _ , r~ , r~ , r~
REL.abstInv (SUB sg) r~ = _ , r~ , r~

REL.atomOk (SUB sg) a = r~
REL.consOk (SUB sg) r~ r~ = r~
REL.abstOk (SUB sg) r~ = r~
REL.embdOk (SUB sg) r~ = r~
REL.loclOk (SUB sg) (_-^_ {m = m} x <>) =
  (# (x ^^ thinr -^ <>)) < #_ $~ ((_-^ <>) $~ (_ ^^iota)) ]~
  (# (((x ^^ thinr) ^^ iota) -^ <>)) ~[ (_^Tm (iota -^ <>)) $~ (REL.loclOk (SUB sg) x) >
  ((sg +Sb m) (x ^^ thinr)) ^Tm (iota -^ <>) [QED]
REL.loclOk (SUB sg) (x -, <>) = #_ $~ (_su $~ none~ _ _)
REL.elimOk (SUB sg) r~ r~ = r~
REL.radiOk (SUB sg) r~ r~ = r~
