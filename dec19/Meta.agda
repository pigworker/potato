module Meta where

open import Eq
open import Tuple
open import Thin
open import Tm

data Go (L X : Set) : Set where
  _-:_ : List L -> X -> Go L X
  abort : Go L X

logOut : forall {L X} -> Go L X -> One + X
logOut abort    = ff , <>
logOut (_ -: x) = tt , x

return : forall {L X} -> X -> Go L X
return x = [] -: x

_-:>>=_ : forall {L Y} -> List L -> Go L Y -> Go L Y
ls0 -:>>= abort = abort
ls0 -:>>= (ls1 -: y) = (ls0 ++ ls1) -: y

_>>=_ : forall {L X Y} -> Go L X -> (X -> Go L Y) -> Go L Y
abort >>= k = abort
(ls0 -: x) >>= k = ls0 -:>>= k x

_<*>_ : forall {L S T} -> Go L (S -> T) -> Go L S -> Go L T
gf <*> gs = gf >>= \ f -> gs >>= \ s -> return (f s)

_<$>_ : forall {L S T} -> (S -> T) -> Go L S -> Go L T
f <$> gs = gs >>= \ s -> return (f s)


infixl 1 _<*>_ _<$>_
infixr 1 _>>=_

_*R_ : forall
  {X0 X1 : Set}(X : X0 -> X1 -> Set)
  {Y0 Y1 : Set}(Y : Y0 -> Y1 -> Set) ->
  (X0 * Y0) -> (X1 * Y1) -> Set
(X *R Y) (x0 , y0) (x1 , y1) = X x0 x1 * Y y0 y1

_-R>_ : forall
  {X0 X1 : Set}(X : X0 -> X1 -> Set)
  {Y0 Y1 : Set}(Y : Y0 -> Y1 -> Set) ->
  (X0 -> Y0) -> (X1 -> Y1) -> Set
(X -R> Y) f0 f1 = forall {x0 x1} -> X x0 x1 -> Y (f0 x0) (f1 x1)
infixr 4 _-R>_

OneR : One -> One -> Set
OneR <> <> = One

data GoMo
  {R0 R1 X0 X1}(R : R0 -> R1 -> Set)(X : X0 -> X1 -> Set) 
  : Go R0 X0 -> Go R1 X1 -> Set where
    abort : forall {g} -> GoMo R X abort g
    _-:_  : (ListR R -R> X -R> GoMo R X) _-:_ _-:_

_-:>>>=_ : forall
  {R0 R1}{R : R0 -> R1 -> Set}
  {Y0 Y1}{Y : Y0 -> Y1 -> Set} ->
  (ListR R -R> GoMo R Y -R> GoMo R Y) _-:>>=_ _-:>>=_
ls0 -:>>>= abort = abort
ls0 -:>>>= (ls1 -: y) = (ls0 ++R ls1) -: y

_>>>=_ : forall
  {R0 R1}{R : R0 -> R1 -> Set}
  {X0 X1}{X : X0 -> X1 -> Set}
  {Y0 Y1}{Y : Y0 -> Y1 -> Set} ->
  (GoMo R X -R> (X -R> GoMo R Y) -R> GoMo R Y) _>>=_ _>>=_
abort >>>= k = abort
(ls -: x) >>>= k = ls -:>>>= k x

_<**>_ : forall
  {R0 R1}{R : R0 -> R1 -> Set}
  {X0 X1}{X : X0 -> X1 -> Set}
  {Y0 Y1}{Y : Y0 -> Y1 -> Set} ->
  (GoMo R (X -R> Y) -R> GoMo R X -R> GoMo R Y) _<*>_ _<*>_
f <**> x = f >>>= \ f -> x >>>= \ x -> [] -: f x

_<$$>_ : forall
  {R0 R1}{R : R0 -> R1 -> Set}
  {X0 X1}{X : X0 -> X1 -> Set}
  {Y0 Y1}{Y : Y0 -> Y1 -> Set} ->
  ((X -R> Y) -R> GoMo R X -R> GoMo R Y) _<$>_ _<$>_
f <$$> x = x >>>= \ x -> [] -: f x

infixl 1 _<**>_ _<$$>_
infixr 1 _>>>=_

logOutLem : forall
  {R0 R1}{R : R0 -> R1 -> Set}
  {X0 X1}{X : X0 -> X1 -> Set}
  {g0 g1}(g : GoMo R X g0 g1) ->
  forall {x0} -> logOut g0 ~ (tt , x0) ->
  X1 >< \ x1 -> logOut g1 ~ (tt , x1) * X x0 x1
logOutLem (_ -: x) r~ = _ , r~ , x

data Size' : Set where
  any : Size'
  gdd : Two -> Size'

smaller : Size' -> Size'
smaller any     = any
smaller (gdd _) = gdd tt

Chk : forall {d n} -> Tm n d -> Nat -> Size' -> Set
Chk u m any     = Tm m chk
Chk u m (gdd b) = Tm m chk >< Gdd u b

data Ty' : Set where
  Chk' : Nat -> Size' -> Ty'
  Syn' : Nat -> Ty'
  _*'_ _->'_ : Ty' -> Ty' -> Ty'
  Aye' : Ty'

infixr 5 _->'_
infixr 6 _*'_

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

  sub' : forall {n} -> (m : Nat)
      -> G :- Chk' (n +B m) any
      -> G :- Vec' (Syn' n) m
      -> G :- Chk' n any

  mat' : forall {z n T}
      -> (Atom -> G :- T)                                        -- what to do with an atom
      -> G :- Chk' n (smaller z) ->' Chk' n (smaller z) ->' T    -- what to do with the components of a cons
      -> G :- Chk' n any *' (Chk' (n su) (smaller z) ->' T)      -- what to do with the body of an abstraction, once you have chosen the type of the bound variable
      -> G :- Chk' n z ->' T     -- what to do with a *canonical* term; embeddings cause this to fail

  chk' : forall {n T} 
      -> G :- Chk' n any              -- the type the subterm should have
      -> G :- Chk' n any ->' T        -- how to continue with the subterm that you now trust
      -> G :- Chk' n (gdd tt) ->' T   -- what to do with a subterm of the subject

  clo' : forall {T}
      -> [] :- T
      -> G  :- T

  !_   : {n : Nat} -> Atom -> G :- Chk' n any
  _&_  : {n : Nat} -> G :- Chk' n any -> G :- Chk' n any -> G :- Chk' n any
  ^_   : {n : Nat} -> G :- Chk' (n su) any -> G :- Chk' n any
  `_   : {n : Nat} -> G :- Syn' n -> G :- Chk' n any
  #_   : {n : Nat} -> Fi n -> G :- Syn' n
  _$_  : {n : Nat} -> G :- Syn' n -> G :- Chk' n any -> G :- Syn' n
  _::_ : {n : Nat} -> G :- Chk' n any -> G :- Chk' n any -> G :- Syn' n

atom' : forall {n G T z}
      -> (Atom -> G :- T)
      -> G :- Chk' n z ->' T
atom' f = mat' f naw' naw'

yer : forall {G T} -> Atom -> G :- T -> Atom -> G :- T
yer a p b with a ~Atom?~ b
yer a p b | ff , _ = naw'
yer a p b | tt , _ = p

cons' : forall {n G T z}
     -> G :- Chk' n (smaller z) ->' Chk' n (smaller z) ->' T
     -> G :- Chk' n z ->' T
cons' f = mat' (\ _ -> naw') f naw'

abst' : forall {n G T z}
     -> G :- Chk' n any
     -> G :- Chk' (n su) (smaller z) ->' T
     -> G :- Chk' n z ->' T
abst' S f = mat' (\ _ -> naw') naw' (S ,' f)

module _ {un ud}(u : Tm un ud)  where

  Req : Set
  Req = Nat >< \ m -> Chk u (un +B m) any * Chk u (un +B m) (gdd tt)

  check : forall {m} -> Chk u (un +B m) any -> Chk u (un +B m) (gdd tt) -> Go Req One
  check {m} T t = ((m , T , t) ,- []) -: <>

  Sem' : Ty' -> Set
  Sem' (Chk' n z)  = Chk u (un +B n) z
  Sem' (Syn' n)    = Tm (un +B n) syn
  Sem' (S *' T)    = Sem' S * Sem' T
  Sem' (S ->' T)   = Sem' S -> Go Req (Sem' T)
  Sem' Aye'        = One

  En' : Bwd Ty' -> Set
  En' G = forall {T} -> T <- G -> Sem' T

  E0' : En' []
  E0' ()

  vecSb : forall {p} m -> Sem' (Vec' (Syn' p) m) -> Sb m (un +B p)
  vecSb (m su) (sg , e) (i no) = vecSb m sg i
  vecSb (m su) (sg , e) (i su) = e

  sem' : forall {G T} -> En' G -> G :- T -> Go Req (Sem' T)
  match : forall {n T G} z
       -> En' G
       -> (Atom -> G :- T)
       -> G :- Chk' n (smaller z) ->' Chk' n (smaller z) ->' T
       -> G :- Chk' n any *' (Chk' (n su) (smaller z) ->' T)
       -> Chk u (un +B n) z
       -> Go Req (Sem' T)
  sem' ga (?' x) = return (ga x)
  sem' ga (\' t) = return \ s -> sem' (ga -push s) t
  sem' ga (f $' a) = sem' ga f >>= \ f -> sem' ga a >>= \ a -> f a
  sem' ga aye' = return <>
  sem' ga (s ,' t) = _,_ <$> sem' ga s <*> sem' ga t
  sem' ga (unc' k) = return \ (s , t) -> sem' ga k >>= \ k -> k s >>= \ k -> k t
  sem' ga naw' = abort
  sem' ga (sub' m t sg) = (\ t sg -> t /Tm locSb m (vecSb m sg)) <$> sem' ga t <*> sem' ga sg
  sem' ga (chk' T k) = return \ tg@(t , _) -> sem' ga T >>= \ T -> sem' ga k >>= \ k ->
    check T tg >>= \ _ -> k t
  sem' ga (clo' t) = sem' E0' t
  sem' ga (! a) = return (! a)
  sem' ga (ps & pt) = _&_ <$> sem' ga ps <*> sem' ga pt
  sem' ga (^ p) = ^_ <$> sem' ga p
  sem' ga (` p) = `_ <$> sem' ga p
  sem' ga (# x) = return (# (x ^^ thinr))
  sem' ga (pe $ ps) = _$_ <$> sem' ga pe <*> sem' ga ps
  sem' ga (pt :: pT) = _::_ <$> sem' ga pt <*> sem' ga pT
  sem' ga (mat' {z} pa pst pSt) = return (match z ga pa pst pSt)

  match any ga pa pst pSt (! a)   = sem' ga (pa a)
  match any ga pa pst pSt (s & t) = sem' ga pst >>= \ k -> k s >>= \ k -> k t
  match any ga pa pst pSt (^ t)   = sem' ga pSt >>= \ (S , k) -> k t
  match any ga pa pst pSt (` t)   = abort
  match (gdd b) ga pa pst pSt (! a   , g) = sem' ga (pa a)
  match (gdd b) ga pa pst pSt (s & t , g) = sem' ga pst >>= \ k -> k (s , g -car) >>= \ k -> k (t , g -cdr)
  match (gdd b) ga pa pst pSt (^ t   , g) = sem' ga pSt >>= \ (S , k) -> k (t , g -bod: S)
  match (gdd b) ga pa pst pSt (` t   , g) = abort

module _ {un0 un1 : Nat}
 (IpOp : forall {d} n -> Tm (un0 +B n) d -> Tm (un1 +B n) d -> Set)
 (Subj : forall {d} n -> Tm (un0 +B n) d -> Tm (un1 +B n) d -> Set)
 where

 GDD : forall {d b0 b1 m0 m1} m {u0 : Tm (un0 +B m) d}{u1 : Tm (un1 +B m) d}
       (t0 : Tm m0 chk) -> Gdd u0 b0 t0 ->
       (t1 : Tm m1 chk) -> Gdd u1 b1 t1 ->
       Set
 GDD m t0 hic         t1 hic         = One
 GDD m t0 (car g0)    t1 (car g1)    = GDD m t0 g0 t1 g1
 GDD m t0 (cdr g0)    t1 (cdr g1)    = GDD m t0 g0 t1 g1
 GDD m t0 (bod S0 g0) t1 (bod S1 g1) = IpOp m S0 S1 * GDD (m su) t0 g0 t1 g1
 GDD m t0 (arg g0)    t1 (arg g1)    = GDD m t0 g0 t1 g1
 GDD m _  _           _  _           = Zero

 carG : forall {d b0 b1 m0 m1} m {u0 : Tm (un0 +B m) d}{u1 : Tm (un1 +B m) d}
       {s0 t0 : Tm m0 chk}(g0 : Gdd u0 b0 (s0 & t0)) ->
       {s1 t1 : Tm m1 chk}(g1 : Gdd u1 b1 (s1 & t1)) ->
       GDD m (s0 & t0) g0 (s1 & t1) g1 ->
       GDD m s0 (g0 -car) s1 (g1 -car)
 carG m hic hic g = <>
 carG m (car g0) (car g1) g = carG m g0 g1 g
 carG m (cdr g0) (cdr g1) g = carG m g0 g1 g
 carG m (bod S0 g0) (bod S1 g1) (S , g) = S , carG (m su) g0 g1 g
 carG m (arg g0) (arg g1) g = carG m g0 g1 g

 cdrG : forall {d b0 b1 m0 m1} m {u0 : Tm (un0 +B m) d}{u1 : Tm (un1 +B m) d}
       {s0 t0 : Tm m0 chk}(g0 : Gdd u0 b0 (s0 & t0)) ->
       {s1 t1 : Tm m1 chk}(g1 : Gdd u1 b1 (s1 & t1)) ->
       GDD m (s0 & t0) g0 (s1 & t1) g1 ->
       GDD m t0 (g0 -cdr) t1 (g1 -cdr)
 cdrG m hic hic g = <>
 cdrG m (car g0) (car g1) g = cdrG m g0 g1 g
 cdrG m (cdr g0) (cdr g1) g = cdrG m g0 g1 g
 cdrG m (bod S0 g0) (bod S1 g1) (S , g) = S , cdrG (m su) g0 g1 g
 cdrG m (arg g0) (arg g1) g = cdrG m g0 g1 g

 bodG' : forall {d b0 b1 m0 m1} m m' {u0 : Tm (un0 +B m) d}{u1 : Tm (un1 +B m) d} ->
        {t0 : Tm (m0 su) chk}(g0 : Gdd u0 b0 (^ t0)) ->
        {t1 : Tm (m1 su) chk}(g1 : Gdd u1 b1 (^ t1)) ->
       GDD m (^ t0) g0 (^ t1) g1 ->
       forall {S0 S1} ->
       (q0 : m0 ~ (un0 +B m')) -> (q1 : m1 ~ (un1 +B m')) ->
       IpOp m' (subst (\ i -> Tm i chk) q0 S0)
               (subst (\ i -> Tm i chk) q1 S1)  ->
       GDD m t0 (g0 -bod: S0) t1 (g1 -bod: S1)
 bodG : forall {d b0 b1 m'} m {u0 : Tm (un0 +B m) d}{u1 : Tm (un1 +B m) d} ->
        {t0 : Tm (un0 +B m' su) chk}(g0 : Gdd u0 b0 (^ t0)) ->
        {t1 : Tm (un1 +B m' su) chk}(g1 : Gdd u1 b1 (^ t1)) ->
       GDD m (^ t0) g0 (^ t1) g1 ->
       forall {S0 S1} -> IpOp m' S0 S1 ->
       GDD m t0 (g0 -bod: S0) t1 (g1 -bod: S1)

 bodG' m m' (car g0) (car g1) g r~ r~ S = bodG m g0 g1 g S
 bodG' m m' (cdr g0) (cdr g1) g r~ r~ S = bodG m g0 g1 g S
 bodG' m m' (bod R0 g0) (bod R1 g1) (R , g) r~ r~ S = R , bodG (m su) g0 g1 g S
 bodG' m m' (arg g0) (arg g1) g r~ r~ S = bodG m g0 g1 g S
 bodG' m m' hic hic g q0 q1 S = gaah m m' q0 q1 S , <> where
   gaah : forall m m'
         {S0 : Tm (un0 +B m) chk} {S1 : Tm (un1 +B m) chk}
         (q0 : (un0 +B m) ~ (un0 +B m')) (q1 : (un1 +B m) ~ (un1 +B m')) ->
       IpOp m' (subst (\ i -> Tm i chk) q0 S0)
               (subst (\ i -> Tm i chk) q1 S1) ->
       IpOp m S0 S1
   gaah m m' q0 q1 S with canSuffix un0 m m' q0
   gaah m .m r~ r~ S | r~ = S
 bodG m g0 g1 g S = bodG' m _ g0 g1 g r~ r~ S

 module _ {ud}(u0 : Tm un0 ud)(u1 : Tm un1 ud) where

  Ch : forall n z -> Sem' u0 (Chk' n z) -> Sem' u1 (Chk' n z) -> Set
  Sy : forall n -> Sem' u0 (Syn' n) -> Sem' u1 (Syn' n) -> Set
  Ch n any t0 t1 = IpOp n t0 t1
  Ch n (gdd b) (t0 , g0) (t1 , g1) = Subj n t0 t1 * GDD [] t0 g0 t1 g1
  Sy n e0 e1 = IpOp n e0 e1

  ReqR : Req u0 -> Req u1 -> Set
  ReqR (m0 , T0 , t0) (m1 , T1 , t1) = (m0 ~ m1) >< \ { r~ -> Ch m0 any T0 T1 * Ch m0 (gdd tt) t0 t1 }

  Stable : (T : Ty') -> Sem' u0 T -> Sem' u1 T -> Set
  Stable (Chk' n z) = Ch n z
  Stable (Syn' n) = Sy n
  Stable (S *' T) = Stable S *R Stable T
  Stable (S ->' T) = Stable S -R> GoMo ReqR (Stable T)
  Stable Aye' = OneR

  record STABLE : Set where
    field
      atomIO : forall {a n t} -> IpOp n (! a) t -> t ~ ! a
      consIO : forall {n s0 t0 t} -> IpOp n (s0 & t0) t ->
        (_ * _) >< \ (s1 , t1) -> t ~ (s1 & t1) * IpOp n s0 s1 * IpOp n t0 t1
      abstIO : forall {n t0 t} -> IpOp n (^ t0) t ->
        _ >< \ t1 -> t ~ ^ t1 * IpOp (n su) t0 t1

      consSu : forall {n s0 t0 t} -> Subj n (s0 & t0) t ->
        (_ * _) >< \ (s1 , t1) -> t ~ (s1 & t1) * Subj n s0 s1 * Subj n t0 t1
      abstSu : forall {n t0 t} -> Subj n (^ t0) t ->
        _ >< \ t1 -> t ~ ^ t1 * Subj (n su) t0 t1
      
      loclSb : forall {n} m ->
               (Ch (n +B m) any -R>
                (\ sg0 sg1 -> (i : Fi m) -> Sy n (sg0 i) (sg1 i)) -R>
                Ch n any)
               (\ t sg -> t /Tm locSb m sg)
               (\ t sg -> t /Tm locSb m sg)

      suIpOp : forall {m d} -> (Subj {d} m -R> IpOp m) id id

      atomOk : forall a {m} -> IpOp m (! a) (! a)
      consOk : forall {m} -> (IpOp m -R> IpOp m -R> IpOp m) _&_ _&_
      abstOk : forall {m} -> (IpOp (m su) -R> IpOp m) ^_ ^_
      embdOk : forall {m} -> (Sy m -R> IpOp m) `_ `_
      loclOk : forall {m}(x : Fi m) -> Sy m (# (x ^^ thinr)) (# (x ^^ thinr))
      elimOk : forall {m} -> (IpOp m -R> IpOp m -R> Sy m) _$_ _$_
      radiOk : forall {m} -> (IpOp m -R> IpOp m -R> Sy m) _::_ _::_

    stable : forall {G T}{ga0 : En' u0 G}{ga1 : En' u1 G}
          -> (forall {S}(i : S <- G) -> Stable S (ga0 i) (ga1 i))
          -> (p : G :- T)
          -> GoMo ReqR (Stable T) (sem' u0 ga0 p) (sem' u1 ga1 p)
    stable ga (?' i) = [] -: ga i
    stable ga (\' p) = [] -: \ sl ->
      stable (\ { (i -^ _) -> ga i
                ; (i -, _) -> sl
                })
        p
    stable ga (f $' s) =
      stable ga f >>>= \ fl ->
      stable ga s >>>= \ sl ->
      fl sl
    stable ga aye' = [] -: <>
    stable ga (s ,' t) = (\ {s0}{s1}s {t0}{t1}t -> s , t) <$$> stable ga s <**> stable ga t
    stable ga (unc' p) = [] -: \ (s , t) -> stable ga p >>>= \ p -> p s >>>= \ p -> p t
    stable ga naw' = abort
    stable ga (sub' m t sg) = (\ {_}{_}t {_}{_}sg -> loclSb m t (help m sg))
      <$$> stable ga t
      <**> stable ga sg
      where
        help : forall m {sg0 sg1} -> Stable (Vec' (Syn' _) m) sg0 sg1 ->
               (i : [] su <= m) -> Sy _ (vecSb u0 m sg0 i) (vecSb u1 m sg1 i)
        help (m su) (sg , e) (i no) = help m sg i
        help (m su) (sg , e) (i su) = e
    stable {G}{_}{ga0}{ga1} ga (mat' {any}{n}{T} pa pst pSt)   = [] -: \ {t0}{t1} -> help t0 t1 where
      help : (t0 : Tm (un0 +B n) chk)(t1 : Tm (un1 +B n) chk) ->
             Ch n any t0 t1 ->
             GoMo ReqR (Stable T) (match u0 any ga0 pa pst pSt t0)
             (match u1 any ga1 pa pst pSt t1)
      help (! a)     u1 u with atomIO u
      help (! a) .(! a) t | r~ = stable ga (pa a)
      help (s0 & t0) u1 u with consIO u
      ... | (s1 , t1) , r~ , s , t = stable ga pst >>>= \ k -> k s >>>= \ k -> k t
      help (^ t0)    u1 u with abstIO u
      ... | t1 , r~ , t = stable ga pSt >>>= \ (S , k) -> k t
      help (` _) _ _ = abort
    stable {G}{_}{ga0}{ga1} ga (mat' {gdd b}{n}{T} pa pst pSt) = [] -: \ { {t0 , g0}{t1 , g1} -> help t0 g0 t1 g1} where
      help : (t0 : Tm (un0 +B n) chk)(g0 : Gdd u0 b t0) (t1 : Tm (un1 +B n) chk) (g1 : Gdd u1 b t1) ->
             Ch n (gdd b) (t0 , g0) (t1 , g1) ->
             GoMo ReqR (Stable T) (match u0 (gdd b) ga0 pa pst pSt (t0 , g0))
             (match u1 (gdd b) ga1 pa pst pSt (t1 , g1))
      help (! a) g0 u1 g1 (u , g) with atomIO (suIpOp u)
      ... | r~ = stable ga (pa a)
      help (s0 & t0) g0 u1 g1 (u , g) with consSu u
      ... | (s1 , t1) , r~ , s , t =
        stable ga pst >>>= \ k ->
        k (s , carG [] g0 g1 g) >>>= \ k ->
        k (t , cdrG [] g0 g1 g)
      help (^ t0) g0 u1 g1 (u , g) with abstSu u
      ... | t1 , r~ , t =
        stable ga pSt >>>= \ (S , k) ->
        k (t , bodG [] g0 g1 g S)
      help (` _) _ _ _ _ = abort
    stable ga (chk' T k) =
      [] -: \ t ->
      stable ga T >>>= \ T ->
      stable ga k >>>= \ k ->
      ((r~ , T , t) ,- []) -:>>>= k (suIpOp (fst t))
    stable ga (clo' t) = stable (\ ()) t
    stable ga (! a)    = [] -: atomOk a
    stable ga (s & t)  = consOk <$$> stable ga s <**> stable ga t
    stable ga (^ t)    = abstOk <$$> stable ga t
    stable ga (` e)    = embdOk <$$> stable ga e
    stable ga (# x)    = [] -: loclOk x
    stable ga (e $ s)  = elimOk <$$> stable ga e <**> stable ga s
    stable ga (t :: T) = radiOk <$$> stable ga t <**> stable ga T

THN : forall {n m}(th : n <= m){d}(p : Nat) -> Tm (n +B p) d -> Tm (m +B p) d -> Set
THN th p t0 t1 = t1 ~ (t0 ^Tm (th +th p))

module _ {n m}(th : n <= m){d}(u : Tm n d) where

  STABLETHN : STABLE (THN th) (THN th) u (u ^Tm th) 
  STABLE.atomIO STABLETHN r~ = r~
  STABLE.consIO STABLETHN r~ = _ , r~ , r~ , r~
  STABLE.abstIO STABLETHN r~ = _ , r~ , r~
  STABLE.consSu STABLETHN r~ = _ , r~ , r~ , r~
  STABLE.abstSu STABLETHN r~ = _ , r~ , r~
  STABLE.loclSb STABLETHN {l} p {t} r~ {ta0} {ta1} ta = 
    ((t ^Tm (th +th (l +B p))) /Tm locSb p ta1) ~[ thinSbst t _ _ >
    (t /Tm \ x -> locSb p ta1 (x ^^ (th +th (l +B p)))) ~[ extSb t _ _ (help p {ta0}{ta1} ta) >
    (t /Tm \ x -> locSb p ta0 x ^Tm (th +th l)) < sbstThin t _ _ ]~
    ((t /Tm locSb p ta0) ^Tm (th +th l)) [QED]
    where 
    help : forall p {ta0} {ta1} ->
           ((i : [] su <= p) -> ta1 i ~ (ta0 i ^Tm (th +th l))) ->
           (x : [] su <= n +B (l +B p)) ->
           (locSb p ta1 (x ^^ (th +th (l +B p)))) ~
           (locSb p ta0 x ^Tm (th +th l))
    help (p su) {ta0}{ta1} ta (x no) = help p (\ j -> ta (j no)) x
    help (p su) ta (x su) = ta (none su)
    help [] ta x = _ /Tm-#
  STABLE.suIpOp STABLETHN = id
  STABLE.atomOk STABLETHN a = r~
  STABLE.consOk STABLETHN r~ r~ = r~
  STABLE.abstOk STABLETHN r~ = r~
  STABLE.embdOk STABLETHN r~ = r~
  STABLE.loclOk STABLETHN (_-^_ {m = m} x <>) = #_ $~ (_no $~ inj# (STABLE.loclOk STABLETHN x))
  STABLE.loclOk STABLETHN (x su) = #_ $~ (_su $~ none~ _ _)
  STABLE.elimOk STABLETHN r~ r~ = r~
  STABLE.radiOk STABLETHN r~ r~ = r~

SUB : forall {n m}(sg : Sb n m){d}(p : Nat) -> Tm (n +B p) d -> Tm (m +B p) d -> Set
SUB sg p t0 t1 = t1 ~ (t0 /Tm (sg +Sb p))

module _ {n m}(sg : Sb n m){d}(u : Tm n d) where

  STABLESUB : STABLE (SUB sg) (SUB sg) u (u /Tm sg) 
  STABLE.atomIO STABLESUB r~ = r~
  STABLE.consIO STABLESUB r~ = _ , r~ , r~ , r~
  STABLE.abstIO STABLESUB r~ = _ , r~ , r~
  STABLE.consSu STABLESUB r~ = _ , r~ , r~ , r~
  STABLE.abstSu STABLESUB r~ = _ , r~ , r~
  STABLE.loclSb STABLESUB {l} p {t} r~ {ta0} {ta1} ta = 
    ((t /Tm (sg +Sb (l +B p))) /Tm locSb p ta1) ~[ sbstSbst t _ _ >
    (t /Tm \ x -> (sg +Sb (l +B p)) x /Tm locSb p ta1) ~[ extSb t _ _ (help p ta) >
    (t /Tm \ x -> locSb p ta0 x /Tm (sg +Sb l)) < sbstSbst t _ _ ]~
    ((t /Tm locSb p ta0) /Tm (sg +Sb l)) [QED]
    where
    help : forall p {ta0} {ta1} ->
           ((i : [] su <= p) -> ta1 i ~ (ta0 i /Tm (sg +Sb l))) ->
           (x : [] su <= n +B (l +B p)) ->
           ((sg +Sb (l +B p)) x /Tm locSb p ta1) ~
           (locSb p ta0 x /Tm (sg +Sb l))
    help (p su) {ta0}{ta1} ta (x no) = 
      (((sg +Sb (l +B p)) x ^Tm (iota no)) /Tm locSb (p su) ta1) ~[ thinSbst ((sg +Sb (l +B p)) x) _ _ >
      ((sg +Sb (l +B p)) x /Tm \ y -> locSb (p su) ta1 (y ^^ (iota no))) ~[ extSb ((sg +Sb (l +B p)) x) _ _
        (\ y -> locSb p (\ j -> ta1 (j no)) $~ (y ^^iota)) >
      ((sg +Sb (l +B p)) x /Tm locSb p (\ j -> ta1 (j no))) ~[ help p (\ i -> ta (i no)) x >
      (locSb p (\ j -> ta0 (j no)) x /Tm (sg +Sb l)) [QED]
    help (p su) ta (x su) = ta (none su)
    help [] ta x = _ /Tm-#
  STABLE.suIpOp STABLESUB = id
  STABLE.atomOk STABLESUB a = r~
  STABLE.consOk STABLESUB r~ r~ = r~
  STABLE.abstOk STABLESUB r~ = r~
  STABLE.embdOk STABLESUB r~ = r~
  STABLE.loclOk STABLESUB (_-^_ {m = m} x <>) =
    (# (x ^^ thinr -^ <>)) < #_ $~ ((_-^ <>) $~ (_ ^^iota)) ]~
    (# (((x ^^ thinr) ^^ iota) -^ <>)) ~[ (_^Tm (iota -^ <>)) $~ (STABLE.loclOk STABLESUB x) >
    ((sg +Sb m) (x ^^ thinr)) ^Tm (iota -^ <>) [QED]
  STABLE.loclOk STABLESUB (x su) = #_ $~ (_su $~ none~ _ _)
  STABLE.elimOk STABLESUB r~ r~ = r~
  STABLE.radiOk STABLESUB r~ r~ = r~
  

{-
    record REL {n0 n1}(L : forall m {d} -> Tm (n0 +B m) d -> Tm (n1 +B m) d -> Set)
                      (Rq : Req n0 -> Req n1 -> Set) : Set where
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
        chkMate : forall {m T T' t t'} p p' ->
                    L m T T' -> L m t t' ->
                    gChk T t p ~ (tt , <>) -> gChk T' t' p' ~ (tt , <>)
        atomOk : forall {m} a -> L m (! a) (! a)
        consOk : forall {m s0 s1 t0 t1} -> L m s0 s1 -> L m t0 t1 -> L m (s0 & t0) (s1 & t1)
        abstOk : forall {m t0 t1} -> L (m su) t0 t1 -> L m (^ t0) (^ t1)
        embdOk : forall {m e0 e1} -> L m e0 e1 -> L m (` e0) (` e1)
        loclOk : forall {n}(x : Fi n) -> L n (# (x ^^ thinr)) (# (x ^^ thinr))
        elimOk : forall {m e0 e1 s0 s1} -> L m e0 e1 -> L m s0 s1 -> L m (e0 $ s0) (e1 $ s1)
        radiOk : forall {m t0 t1 T0 T1} -> L m t0 t1 -> L m T0 T1 -> L m (t0 :: T0) (t1 :: T1)
{-        
      Lift : (T : Ty') -> (n0 +[ T ] -> n1 +[ T ] -> Set)
      Lift (Chk' m any) t0        t1        = L m t0 t1
      Lift (Chk' m (gdd b)) (t0 , _) (t1 , _) = L m t0 t1
      Lift (Syn' m) t0        t1        = L m t0 t1
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
          help : forall m (sg0 : n0 +[ Vec' (Syn' _) m ])
                          (sg1 : n1 +[ Vec' (Syn' _) m ]) ->
             Lift (Vec' (Syn' _) m) sg0 sg1 ->
             (i : [] su <= m) -> L _ (vecSb m sg0 i) (vecSb m sg1 i)
          help .(_ su) (sg0 , e0) (sg1 , e1) (sgl , el) (i no) = help _ sg0 sg1 sgl i
          help .(_ su) (sg0 , e0) (sg1 , e1) (sgl , el) (i su) = el
      lift (mat' {any}{n}{T} q c l) ga0 ga1 ga = ye help where
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
      lift (mat' {gdd b}{n}{T} q c l) ga0 ga1 ga = ye help where
        help : (s0 : Tm (n0 +B n) chk >< Gdd b) (s1 : Tm (n1 +B n) chk >< Gdd b) ->
               L n (fst s0) (fst s1) ->
               MayLift (Lift T) (match q c l ga0 s0) (match q c l ga1 s1)
        help (! a0 , p) u1 ul with r~ <- atomInv ul = lift (q a0) ga0 ga1 ga
        help (s0 & t0 , p) u ul with consInv ul
        ... | (s1 , t1) , r~ , sl , tl with [ c ]P ga0 | [ c ]P ga1 | lift c ga0 ga1 ga
        help (s0 & t0 , p) (.(s1 & t1) , q) ul | (s1 , t1) , r~ , sl , tl | .(ff , <>) | c1 | no = no
        help (s0 & t0 , p) (.(s1 & t1) , q) ul | (s1 , t1) , r~ , sl , tl | (tt , c0) | (tt , c1) | ye cl
          with c0 (s0 , gCar s0 t0 b p) | c1 (s1 , gCar s1 t1 b q) | cl (s0 , gCar s0 t0 b p) (s1 , gCar s1 t1 b q) sl
        help (s0 & t0 , p) (.(s1 & t1) , q) ul | (s1 , t1) , r~ , sl , tl | tt , c0 | tt , c1 | ye cl | .(ff , <>) | d1 | no = no
        help (s0 & t0 , p) (.(s1 & t1) , q) ul | (s1 , t1) , r~ , sl , tl | tt , c0 | tt , c1 | ye cl | .(tt , _) | .(tt , _) | ye dl =
          dl (t0 , gCdr s0 t0 b p) (t1 , gCdr s1 t1 b q) tl
        help (^ t0 , p) u ul with abstInv ul
        ... | t1 , r~ , tl with [ l ]P ga0 | [ l ]P ga1 | lift l ga0 ga1 ga
        help (^ t0 , p) (.(^ t1) , q) ul | t1 , r~ , tl | .(ff , <>) | l1 | no = no
        help (^ t0 , p) (.(^ t1) , q) ul | t1 , r~ , tl | tt , S0 , _ | tt , S1 , _ | ye (Sl , ll) = ll (t0 , gBod S0 t0 b p) (t1 , gBod S1 t1 b q) tl
        help (` s0 , p) s1 sl = no
      lift (chk' T k) ga0 ga1 ga = ye help where
        help : ((t0 , p0) : Tm (n0 +B _) chk >< Gdd tt)((t1 , p1) : Tm (n1 +B _) chk >< Gdd tt) ->
               L _ t0 t1 ->
               MayLift (Lift _)
                ([ T ]P ga0 >>= \ T -> [ k ]P ga0 >>= \ k -> gChk T t0 p0 >>= \ _ -> k t0)
                ([ T ]P ga1 >>= \ T -> [ k ]P ga1 >>= \ k -> gChk T t1 p1 >>= \ _ -> k t1)
        help (t0 , p0) (t1 , p1) tl
          with [ T ]P ga0 | [ T ]P ga1 | lift T ga0 ga1 ga
             | [ k ]P ga0 | [ k ]P ga1 | lift k ga0 ga1 ga
        help (t0 , p0) (t1 , p1) tl | .(ff , <>) | T1 | no | k0 | k1 | kl = no
        help (t0 , p0) (t1 , p1) tl | .(tt , _) | .(tt , _) | ye _ | .(ff , <>) | k1 | no = no
        help (t0 , p0) (t1 , p1) tl | tt , T0 | tt , T1 | ye Tl | tt , k0 | tt , k1 | ye kl
          with gChk T0 t0 p0 | gChk T1 t1 p1 | chkMate p0 p1 Tl tl
        ... | ff , _ | b1 , _ | q = no
        ... | tt , _ | b1 , _ | q with r~ <- q r~ = kl _ _ tl
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

    locSbKem : forall {n0 n1} n m
      (th : n0 <= n1)(sg0 : Sb m (n0 +B n))(sg1 : Sb m (n1 +B n)) ->
      ((i : [] su <= m) -> sg1 i ~ (sg0 i ^Tm (th +th n))) ->
      (x : Fi (n0 +B (n +B m))) ->
      locSb m sg1 (x ^^ (th +th (n +B m))) ~ (locSb m sg0 x ^Tm (th +th n))
    locSbKem n (m su) th sg0 sg1 q (x -^ .<>) = locSbKem n m th _ _ (\ i -> q (i -^ <>)) x
    locSbKem n (m su) th sg0 sg1 q (x -, .<>) = q (none su)
    locSbKem n [] th sg0 sg1 q x = r~

    module RELTHN {n m}(th : n <= m)
      (gChkTh : forall k -> (T t : Tm (n +B k) chk) (p0 : Gdd tt t)(p1 : Gdd tt (t ^Tm (th +th k)))
             -> gChk T t p0 ~ (tt , <>)
             -> gChk (T ^Tm (th +th k)) (t ^Tm (th +th k)) p1 ~ (tt , <>))
      where

      THN : REL \ p t0 t1 -> t1 ~ (t0 ^Tm (th +th p))
      REL.localSb THN {n} {m} t0 _ r~ sg0 sg1 q = 
        ((t0 ^Tm (th +th (n +B m))) /Tm locSb m sg1) ~[ thinSbst t0 _ _ >
        (t0 /Tm (\ i -> locSb m sg1 (i ^^ (th +th (n +B m))))) ~[ extSb t0 _ _ (locSbKem n m th sg0 sg1 q) >
        (t0 /Tm (\ i -> locSb m sg0 i ^Tm (th +th n))) < sbstThin t0 _ _ ]~
        ((t0 /Tm locSb m sg0) ^Tm (th +th n)) [QED]
    
      REL.atomInv THN r~ = r~
      REL.consInv THN r~ = _ , r~ , r~ , r~
      REL.abstInv THN r~ = _ , r~ , r~

      REL.chkMate THN p p' r~ r~ q = gChkTh _ _ _ p p' q

      REL.atomOk THN a = r~
      REL.consOk THN r~ r~ = r~
      REL.abstOk THN r~ = r~
      REL.embdOk THN r~ = r~
      REL.loclOk THN {n} x = #_ $~ (
        (x ^^ thinr) < (x ^^_) $~ thinrLemma th n ]~
        (x ^^ (thinr ^^ (th +th n))) ~[ thinAssoc _ _ _ >
        (x ^^ thinr ^^ (th +th n)) [QED])
      REL.elimOk THN r~ r~ = r~
      REL.radiOk THN r~ r~ = r~


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

    module RELSUB {n m}(sg : Sb n m)
      (gChkSb : forall k -> (T t : Tm (n +B k) chk) (p0 : Gdd tt t)(p1 : Gdd tt (t /Tm (sg +Sb k)))
             -> gChk T t p0 ~ (tt , <>)
             -> gChk (T /Tm (sg +Sb k)) (t /Tm (sg +Sb k)) p1 ~ (tt , <>))
      where

      SUB : REL \ p t0 t1 -> t1 ~ (t0 /Tm (sg +Sb p))
      
      REL.localSb SUB {n} {m} t0 _ r~ sg0 sg1 q = 
        ((t0 /Tm (sg +Sb (n +B m))) /Tm locSb m sg1) ~[ sbstSbst t0 _ _ >
        (t0 /Tm \ i -> (sg +Sb (n +B m)) i /Tm locSb m sg1) ~[ extSb t0 _ _ (locSbLem n m sg sg0 sg1 q) >
        (t0 /Tm \ i -> locSb m sg0 i /Tm (sg +Sb n)) < sbstSbst t0 _ _ ]~
        ((t0 /Tm locSb m sg0) /Tm (sg +Sb n)) [QED]
        
      REL.atomInv SUB r~ = r~
      REL.consInv SUB r~ = _ , r~ , r~ , r~
      REL.abstInv SUB r~ = _ , r~ , r~
  
      REL.chkMate SUB p p' r~ r~ q = gChkSb _ _ _ p p' q
  
      REL.atomOk SUB a = r~
      REL.consOk SUB r~ r~ = r~
      REL.abstOk SUB r~ = r~
      REL.embdOk SUB r~ = r~
      REL.loclOk SUB (_-^_ {m = m} x <>) =
        (# (x ^^ thinr -^ <>)) < #_ $~ ((_-^ <>) $~ (_ ^^iota)) ]~
        (# (((x ^^ thinr) ^^ iota) -^ <>)) ~[ (_^Tm (iota -^ <>)) $~ (REL.loclOk SUB x) >
        ((sg +Sb m) (x ^^ thinr)) ^Tm (iota -^ <>) [QED]
      REL.loclOk SUB (x -, <>) = #_ $~ (_su $~ none~ _ _)
      REL.elimOk SUB r~ r~ = r~
      REL.radiOk SUB r~ r~ = r~
-}
-}
