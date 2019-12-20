module Red where

open import Eq
open import Tuple
open import Thin
open import Tm
open import Meta

infixr 19 _SU _NO
pattern _SU X = X -, _
pattern _NO X = X -^ _

ElimBeta' : Ty'
ElimBeta' = Chk' [] any                    -- target type
        ->' Chk' [] (gdd tt)               -- eliminator (s is guarded in e $ s)
        ->' (Syn' [] ->' Chk' [] any)      -- result type in the abstract
         *' (Chk' [] any ->' Chk' [] any)  -- result value, concretely

module RED (eb' : forall {G} -> G :- ElimBeta') where

  Contract' : Ty'
  Contract' = Chk' [] any      -- target type
           *' Chk' [] (gdd tt) -- eliminator
           *' Chk' [] any -- target intro
          ->' Chk' [] any -- result value
           *' Chk' [] any -- result type

  contract' : [] :- Contract'
  contract' = unc' (\'{-T-} unc' (\'{-s-} (\'{-t-} (unc' (\'{-R-} (\'{-r-} (
       ((?'{-r-} (none SU)) $'
            (?'{-t-} (none SU NO NO)))
      ,' ((?'{-R-} (none SU NO)) $'
            ((?'{-t-} (none SU NO NO)) :: (?'{-T-} (none SU NO NO NO NO)))))))
    $' ((eb' $' (?'{-T-} (none SU NO NO))) $' (?'{-s-} (none SU NO)))))))

  contract : forall {n}
    -> Tm n chk {-t-}
    -> Tm n chk {-T-}
    -> Tm n chk {-s-}
    -> One + (Tm n chk{-t'-} * Tm n chk{-T-})
  contract t T s = logOut (sem' ((t :: T) $ s) (E0' _) contract' >>= \ f -> f (T , (s , arg hic) , t))

  module _ {un0}{un1}
    (IpOp : forall {d} n -> Tm (un0 +B n) d -> Tm (un1 +B n) d -> Set)
    (Subj : forall {d} n -> Tm (un0 +B n) d -> Tm (un1 +B n) d -> Set)
    (t0 : Tm un0 chk)(t1 : Tm un1 chk)
    (T0 : Tm un0 chk)(T1 : Tm un1 chk)
    (s0 : Tm un0 chk)(s1 : Tm un1 chk)
    (Stab : STABLE IpOp Subj ((t0 :: T0) $ s0) ((t1 :: T1) $ s1))
    where
    contractStable  
       : IpOp [] t0 t1
      -> IpOp [] T0 T1
      -> Subj [] s0 s1
      -> (v0 V0 : Tm un0 chk)
      -> contract t0 T0 s0 ~ (tt , v0 , V0)
      -> (_ * _) >< \ (v1 , V1) ->
         contract t1 T1 s1 ~ (tt , v1 , V1) * IpOp [] v0 v1 * IpOp [] V0 V1
    contractStable t T s v0 V0 q =
      logOutLem (stable {[]}{Contract'}{E0' _}{E0' _}(\ ()) contract'
                 >>>= \ fl -> fl {T0 , (s0 , arg hic) , t0}
                                 {T1 , (s1 , arg hic) , t1}
                                 (T , (s , <>) , t))
        q
      where open STABLE Stab

  contractStableTh : forall {n m}(th : n <= m)
    -> (t : Tm n chk)(T : Tm n chk)(s : Tm n chk)
    -> (t' T' : Tm n chk)
    -> contract t T s ~ (tt , t' , T')
    -> contract (t ^Tm th) (T ^Tm th) (s ^Tm th) ~ (tt , t' ^Tm th , T' ^Tm th)
  contractStableTh th t T s t' T' q
    with contractStable (THN th) (THN th) t _ T _ s _
           (STABLETHN th ((t :: T) $ s))
           r~ r~ r~ _ _ q
  ... | _ , q' , r~ , r~ = q'    
    
  contractStableSb : forall {n m}(sg : Sb n m)
    -> (t : Tm n chk)(T : Tm n chk)(s : Tm n chk)
    -> (t' T' : Tm n chk)
    -> contract t T s ~ (tt , t' , T')
    -> contract (t /Tm sg) (T /Tm sg) (s /Tm sg) ~ (tt , t' /Tm sg , T' /Tm sg)
  contractStableSb sg t T s t' T' q
    with contractStable (SUB sg) (SUB sg) t _ T _ s _
           (STABLESUB sg ((t :: T) $ s))
           r~ r~ r~ _ _ q
  ... | _ , q' , r~ , r~ = q'    
    
  data _=>_ {n} : forall {d} -> Tm n d -> Tm n d -> Set where
    beta : forall {t t' T T' s s' r r' R R'} ->
           contract t T s ~ (tt , r , R) ->
           t => t' -> T => T' -> s => s' ->
           contract t' T' s' ~ (tt , r' , R') ->
           ((t :: T) $ s) => (r' :: R')
    upsi : forall {t t' T} -> t => t' -> (` (t :: T)) => t'
    !_   : forall a -> (! a) => (! a)
    _&_  : forall {s s' t t'} -> s => s' -> t => t' -> (s & t) => (s' & t')
    ^_   : forall {t t'} -> t => t' -> (^ t) => (^ t')
    `_   : forall {e e'} -> e => e' -> (` e) => (` e')
    #_   : forall x -> (# x) => (# x)
    _$_  : forall {e e' s s'} -> e => e' -> s => s' -> (e $ s) => (e' $ s')
    _::_ : forall {t t' T T'} -> t => t' -> T => T' -> (t :: T) => (t' :: T')

  parTh : forall {n d}{t0 t1 : Tm n d} -> t0 => t1 ->
          forall {m}(th : n <= m) ->
          (t0 ^Tm th) => (t1 ^Tm th)
  parTh (beta q0 t T s q1) th = beta (contractStableTh th _ _ _ _ _ q0) (parTh t th) (parTh T th) (parTh s th) (contractStableTh th _ _ _ _ _ q1)
  parTh (upsi t) th = upsi (parTh t th)
  parTh (! a) th = ! a
  parTh (s & t) th = parTh s th & parTh t th
  parTh (^ t) th = ^ parTh t (th su)
  parTh (` e) th = ` parTh e th
  parTh (# x) th = # _
  parTh (e $ s) th = parTh e th $ parTh s th
  parTh (t :: T) th = parTh t th :: parTh T th 
          
  parSb : forall {n d}{t0 t1 : Tm n d} -> t0 => t1 ->
          forall {m}(sg0 sg1 : Sb n m) -> (forall i -> sg0 i => sg1 i) ->
          (t0 /Tm sg0) => (t1 /Tm sg1)
  parSb (beta q0 t T s q1) sg0 sg1 sg =
    beta (contractStableSb sg0 _ _ _ _ _ q0)
         (parSb t sg0 sg1 sg) (parSb T sg0 sg1 sg) (parSb s sg0 sg1 sg)
         (contractStableSb sg1 _ _ _ _ _ q1)
  parSb (upsi t) sg0 sg1 sg = upsi (parSb t sg0 sg1 sg)
  parSb (! a) sg0 sg1 sg = ! a
  parSb (s & t) sg0 sg1 sg = parSb s sg0 sg1 sg & parSb t sg0 sg1 sg
  parSb (^ t) sg0 sg1 sg = ^ parSb t (sg0 +1Sb) (sg1 +1Sb) \
    { (x no) -> parTh (sg x) (iota -^ <>) 
    ; (x su) -> # _
    }
  parSb (` e) sg0 sg1 sg = ` parSb e sg0 sg1 sg
  parSb (# x) sg0 sg1 sg = sg x
  parSb (e $ s) sg0 sg1 sg = parSb e sg0 sg1 sg $ parSb s sg0 sg1 sg
  parSb (t :: T) sg0 sg1 sg = parSb t sg0 sg1 sg :: parSb T sg0 sg1 sg

  PAR : forall {n}{d}{u0 u1 : Tm n d} -> u0 => u1 ->
        STABLE (\ m -> _=>_ {n +B m}) (\ m -> _=>_ {n +B m}) u0 u1
  STABLE.atomIO (PAR u) (! a) = r~
  STABLE.consIO (PAR u) (s & t) = _ , r~ , s , t
  STABLE.abstIO (PAR u) (^ t) = _ , r~ , t
  STABLE.consSu (PAR u) (s & t) = _ , r~ , s , t
  STABLE.abstSu (PAR u) (^ t) = _ , r~ , t
  STABLE.loclSb (PAR {n} u) {p} m t {sg0}{sg1} sg =
    parSb t (locSb m sg0) (locSb m sg1) (help n p m sg0 sg1 sg) where
    help : forall n p m (sg0 sg1 : Sb m (n +B p))(sg : forall i -> sg0 i => sg1 i) ->
           forall i -> locSb {n}{p} m sg0 i => locSb {n}{p} m sg1 i
    help n p (m -, x) sg0 sg1 sg (i -^ .x) = help n p m _ _ (\ i -> sg (i -^ _)) i
    help n p (m -, .<>) sg0 sg1 sg (i -, .<>) = sg (none su)
    help n p [] sg0 sg1 r i = # i
  STABLE.suIpOp (PAR u) = id
  STABLE.atomOk (PAR u) a = ! a
  STABLE.consOk (PAR u) s t = s & t
  STABLE.abstOk (PAR u) t = ^ t
  STABLE.embdOk (PAR u) e = ` e
  STABLE.loclOk (PAR u) x = # _
  STABLE.elimOk (PAR u) e s = e $ s
  STABLE.radiOk (PAR u) t T = t :: T

  contractStablePar : forall {n}
    -> {t0 t1 : Tm n chk} -> t0 => t1
    -> {T0 T1 : Tm n chk} -> T0 => T1
    -> {s0 s1 : Tm n chk} -> s0 => s1
    -> {t'0 T'0 : Tm n chk}
    -> contract t0 T0 s0 ~ (tt , t'0 , T'0)
    -> (_ * _) >< \ (t'1 , T'1)
    -> contract t1 T1 s1 ~ (tt , t'1 , T'1) * (t'0 => t'1) * (T'0 => T'1)
  contractStablePar {n} {t0}{t1} t {T0}{T1} T {s0}{s1} s {t'0}{T'0} =
    contractStable (\ m -> _=>_ {n +B m}) (\ m -> _=>_ {n +B m}) _ _ _ _ _ _
       (PAR ((t :: T) $ s)) t T s t'0 T'0
  
  develop : forall {n d}(t : Tm n d) -> Tm n d
  develop (! a) = ! a
  develop (s & t) = develop s & develop t
  develop (^ t) = ^ develop t
  develop (` (t :: T)) = develop t
  develop (` e) = ` develop e
  develop (# x) = # x
  develop ((t :: T) $ s) with contract t T s | develop t | develop T | develop s
  ... | ff , _ | t' | T' | s' = (t' :: T') $ s'
  ... | tt , _ | t' | T' | s' with contract t' T' s'
  ... | tt , r' , R' = r' :: R'
  ... | ff , <> = (t' :: T') $ s' -- never happens, we know
  develop (e $ s) = develop e $ develop s
  develop (t :: T) = develop t :: develop T

  developLemma : forall {n d}(t0 t1 : Tm n d) ->
    t0 => t1 -> t1 => develop t0
  developLemma .((_ :: _) $ _) .(_ :: _) (beta {t}{t'}{T}{T'}{s}{s'} q0 tr Tr sr q1)
    with contract t T s | develop t | develop T | develop s | developLemma _ _ tr | developLemma _ _ Tr | developLemma _ _ sr
  ... | a | td | Td | sd | th | Th | sh with contractStablePar th Th sh q1
  developLemma .((t :: T) $ s) .(_ :: _) (beta {t} {t'} {T} {T'} {s} {s'} r~ tr Tr sr q1)
    | .(tt , _ , _) | td | Td | sd | th | Th | sh | (r' , R') , q2 , rd , Rd
    rewrite q2 = rd :: Rd
  developLemma .(` (_ :: _)) t1 (upsi t) = developLemma _ _ t
  developLemma .(! a) .(! a) (! a) = ! a
  developLemma .(_ & _) .(_ & _) (s & t) = developLemma _ _ s & developLemma _ _ t
  developLemma .(^ _) .(^ _) (^ t) = ^ developLemma _ _ t
  developLemma (` e0) (` e1) (` e) with developLemma _ _ e
  developLemma (` # x) (` e1) (` e) | r = ` r
  developLemma (` e0 $ e2) (` e1) (` e) | r = ` r
  developLemma (` (e0 :: e2)) (` .(_ :: _)) (` (t :: T)) | t' :: T' = upsi t'
  developLemma .(# x) .(# x) (# x) = # x
  developLemma (# x $ s0) (e1 $ s1) (e $ s) = developLemma _ _ e $ developLemma _ _ s
  developLemma (e0 $ e2 $ s0) (e1 $ s1) (e $ s) = developLemma _ _ e $ developLemma _ _ s
  developLemma ((t0 :: T0) $ s0) (e1 $ s1) ((t :: T) $ s)
    with contract t0 T0 s0
       | develop t0 | developLemma _ _ t | develop T0 | developLemma _ _ T | develop s0 | developLemma _ _ s
       | contractStablePar t T s
  developLemma ((t0 :: T0) $ s0) (.(_ :: _) $ s1) (e $ s) | ff , <> | td | th | Td | Th | sd | sh | g = (th :: Th) $ sh
  developLemma ((t0 :: T0) $ s0) (.(_ :: _) $ s1) (e $ s) | tt , z | td | th | Td | Th | sd | sh | g with g r~
  ... | (t'1 , T'1) , q , r , R  with contractStablePar th Th sh q
  ... | (rd , Rd) , qd , x , y
      rewrite qd = beta q th Th sh qd
  developLemma .(_ :: _) .(_ :: _) (t :: T) = developLemma _ _ t :: developLemma _ _ T

  mkBeta : forall {n}{t t' T T' s s' : Tm n chk} -> t => t' -> T => T' -> s => s' ->
    One ->
    forall {r r' R R'} ->
    contract t T s ~ (tt , r , R) ->
    contract t' T' s' ~ (tt , r' , R') ->
    ((t :: T) $ s) => (r' :: R')
  mkBeta t T s <> q0 q1 = beta q0 t T s q1

  developPar : forall {d n}(t : Tm n d) -> t => develop t
  developPar (! a) = ! a
  developPar (s & t) = developPar s & developPar t
  developPar (^ t) = ^ developPar t
  developPar (` (t :: T)) = upsi (developPar t)
  developPar (` # x) = ` # x
  developPar (` e $ s) = ` developPar (e $ s)
  developPar (# x) = # x
  developPar ((t :: T) $ s)
    with develop t | developPar t | develop T | developPar T | develop s | developPar s
  ... | t' | th | T' | Th | s' | sh with contract t T s | mkBeta th Th sh
  ... | ff , c0 | _ = (th :: Th) $ sh
  ... | tt , c0 | be with contract t' T' s'
  ... | ff , c1 = (th :: Th) $ sh
  ... | tt , r , R = be <> r~ r~
  developPar (# x $ s)   = # x $ developPar s
  developPar (e $ r $ s) = developPar (e $ r) $ developPar s
  developPar (t :: T) = developPar t :: developPar T

  diamond : forall {n d}{s p q : Tm n d} -> s => p -> s => q ->
            _ >< \ r -> p => r * q => r
  diamond sp sq = _ , developLemma _ _ sp , developLemma _ _ sq

  strip : forall {n d}{s p q : Tm n d} -> s => p -> Star _=>_ s q ->
          _ >< \ r -> Star _=>_ p r * q => r
  strip sp [] = _ , [] , sp
  strip sp (sa ,- aq) with _ , pb , ab <- diamond sp sa | _ , br , qr <- strip ab aq = _ , (pb ,- br) , qr

  parallelogram : forall {n d}{s p q : Tm n d} -> Star _=>_ s p -> Star _=>_ s q ->
              _ >< \ r -> Star _=>_ p r * Star _=>_ q r
  parallelogram [] sq = _ , sq , []
  parallelogram (sa ,- ap) sq with _ , ab , qb <- strip sa sq | _ , pr , br <- parallelogram ap ab = _ , pr , (qb ,- br)

  parRefl : forall {n d}(t : Tm n d) -> t => t
  parRefl (! a) = ! a
  parRefl (s & t) = parRefl s & parRefl t
  parRefl (^ t) = ^ parRefl t
  parRefl (` e) = ` parRefl e
  parRefl (# x) = # x
  parRefl (e $ s) = parRefl e $ parRefl s
  parRefl (t :: T) = parRefl t :: parRefl T

  data _~>_ {n} : forall {d} -> Tm n d -> Tm n d -> Set where
    beta : forall {t T s r R} ->
           contract t T s ~ (tt , r , R) ->
           ((t :: T) $ s) ~> (r :: R)
    upsi : forall {t T} -> (` (t :: T)) ~> t
    _<&_ : forall {s s'} -> s ~> s' -> forall t -> (s & t) ~> (s' & t)
    _&>_ : forall s {t t'} -> t ~> t' -> (s & t) ~> (s & t')
    ^_ : forall {t t'} -> t ~> t' -> (^ t) ~> (^ t')
    `_ : forall {e e'} -> e ~> e' -> (` e) ~> (` e')
    _<$_ : forall {e e'} -> e ~> e' -> forall s -> (e $ s) ~> (e' $ s)
    _$>_ : forall e {s s'} -> s ~> s' -> (e $ s) ~> (e $ s')
    _<::_ : forall {t t'} -> t ~> t' -> forall T -> (t :: T) ~> (t' :: T)
    _::>_ : forall t {T T'} -> T ~> T' -> (t :: T) ~> (t :: T')

  stepPar : forall {n d}{t t' : Tm n d} -> t ~> t' -> t => t'
  stepPar (beta q) = beta q (parRefl _) (parRefl _) (parRefl _) q
  stepPar upsi = upsi (parRefl _)
  stepPar (s <& t) = stepPar s & parRefl t
  stepPar (s &> t) = parRefl s & stepPar t
  stepPar (^ t) = ^ stepPar t
  stepPar (` e) = ` stepPar e
  stepPar (e <$ s) = stepPar e $ parRefl s
  stepPar (e $> s) = parRefl e $ stepPar s
  stepPar (t <:: T) = stepPar t :: parRefl T
  stepPar (t ::> T) = parRefl t :: stepPar T

  parSteps : forall {n d}{t t' : Tm n d} -> t => t' -> Star _~>_ t t'
  parSteps (beta q0 t T s q1)
    =  star (_$ _) (_<$ _)
        (  star (_:: _) (_<:: _) (parSteps t)
        ++ star (_ ::_) (_ ::>_) (parSteps T))
    ++ star (_ $_) (_ $>_) (parSteps s)
    ++ (beta q1 ,- [])
  parSteps (upsi t) = upsi ,- parSteps t
  parSteps (! a) = []
  parSteps (s & t) = star (_& _) (_<& _) (parSteps s) ++ star (_ &_) (_ &>_) (parSteps t)
  parSteps (^ t) = star ^_ ^_ (parSteps t)
  parSteps (` e) = star `_ `_ (parSteps e)
  parSteps (# x) = []
  parSteps (e $ s) = star (_$ _) (_<$ _) (parSteps e) ++ star (_ $_) (_ $>_) (parSteps s)
  parSteps (t :: T) = star (_:: _) (_<:: _) (parSteps t) ++ star (_ ::_) (_ ::>_) (parSteps T)

  confluence : forall {n d}{s p q : Tm n d} -> Star _~>_ s p -> Star _~>_ s q ->
              _ >< \ r -> Star _~>_ p r * Star _~>_ q r
  confluence sp sq
      with _ , pr , qr <- parallelogram (star (\ x -> x) stepPar sp) (star (\ x -> x) stepPar sq)
         = _ , starB (\ x -> x) parSteps pr , starB (\ x -> x) parSteps qr

  developSteps : forall {n d}(t : Tm n d) -> Star _~>_ t (develop t)
  developSteps t = parSteps (developPar t)

  stepSb : forall {n d}{t0 t1 : Tm n d} -> t0 ~> t1 ->
           forall {m}(sg : Sb n m) -> (t0 /Tm sg) ~> (t1 /Tm sg)
  stepSb (beta {t} {T} {s} {r} {R} q) sg = beta (contractStableSb sg t T s r R q)
  stepSb upsi sg = upsi
  stepSb (s <& t) sg = stepSb s sg <& _
  stepSb (s &> t) sg = _ &> stepSb t sg
  stepSb (^ t) sg = ^ stepSb t (sg +1Sb)
  stepSb (` e) sg = ` stepSb e sg
  stepSb (e <$ s) sg = stepSb e sg <$ _
  stepSb (e $> s) sg = _ $> stepSb s sg
  stepSb (t <:: T) sg = stepSb t sg <:: _ 
  stepSb (t ::> T) sg = _ ::> stepSb T sg

  stepTh : forall {n d}{t0 t1 : Tm n d} -> t0 ~> t1 ->
           forall {m}(th : n <= m) ->
           (t0 ^Tm th) ~> (t1 ^Tm th)
  stepTh (beta {t} {T} {s} {r} {R} q) th = beta (contractStableTh th t T s r R q)
  stepTh upsi th = upsi
  stepTh (s <& t) th = stepTh s th <& _
  stepTh (s &> t) th = _ &> stepTh t th
  stepTh (^ t) th = ^ stepTh t (th su)
  stepTh (` e) th = ` stepTh e th
  stepTh (e <$ s) th = stepTh e th <$ _
  stepTh (e $> s) th = _ $> stepTh s th
  stepTh (t <:: T) th = stepTh t th <:: _ 
  stepTh (t ::> T) th = _ ::> stepTh T th

  sbSteps : forall {n d}(t : Tm n d) ->
            forall {m}{sg0 sg1 : Sb n m} ->
            (sg : forall i -> Star _~>_ (sg0 i) (sg1 i)) ->
            Star _~>_ (t /Tm sg0) (t /Tm sg1)
  sbSteps (! a) sg = []
  sbSteps (s & t) sg = star (_& _) (_<& _) (sbSteps s sg) ++ star (_ &_) (_ &>_) (sbSteps t sg)
  sbSteps (^ t) sg = star ^_ ^_ (sbSteps t \
    { (x no) -> star (_^Tm (iota no)) (\ t -> stepTh t (iota no)) (sg x)
    ; (x su) -> []
    })
  sbSteps (` e) sg = star `_ `_ (sbSteps e sg)
  sbSteps (# x) sg = sg x
  sbSteps (e $ s) sg = star (_$ _) (_<$ _) (sbSteps e sg) ++ star (_ $_) (_ $>_) (sbSteps s sg)
  sbSteps (t :: T) sg = star (_:: _) (_<:: _) (sbSteps t sg) ++ star (_ ::_) (_ ::>_) (sbSteps T sg)

  JOY : forall {n}{d}{u0 u1 : Tm n d} -> u0 => u1 ->
        STABLE (\ {d} m -> Star _~>_) (\ m -> _=>_ {n +B m}) u0 u1
  STABLE.atomIO (JOY u) [] = r~
  STABLE.consIO (JOY u) [] = _ , r~ , [] , [] 
  STABLE.consIO (JOY u) ((s <& t) ,- rs) with STABLE.consIO (JOY u) rs
  ... | _ , r~ , ss , ts = _ , r~ , (s ,- ss) , ts
  STABLE.consIO (JOY u) ((s &> t) ,- rs) with STABLE.consIO (JOY u) rs
  ... | _ , r~ , ss , ts = _ , r~ , ss , (t ,- ts)
  STABLE.abstIO (JOY u) [] = _ , r~ , []
  STABLE.abstIO (JOY u) ((^ r) ,- rs) with STABLE.abstIO (JOY u) rs
  ... | _ , r~ , rs' = _ , r~ , r ,- rs'
  STABLE.consSu (JOY u) (s & t) = _ , r~ , s , t
  STABLE.abstSu (JOY u) (^ t) = _ , r~ , t
  STABLE.loclSb (JOY u) m {x0} [] {sg0}{sg1} sg = sbSteps x0 (help m sg) where
    help : forall m {sg0 sg1 : Sb m _} ->
       ((i : [] su <= m) -> Star _~>_ (sg0 i) (sg1 i)) ->
       (i : [] su <= _ +B (_ +B m)) ->
       Star _~>_ (locSb m sg0 i) (locSb m sg1 i)
    help (m su) sg (i no) = help m (\ i -> sg (i no)) i
    help (m su) sg (i su) = sg (none su)
    help [] sg i = []
  STABLE.loclSb (JOY u) m (t ,- ts) sg with STABLE.loclSb (JOY u) m ts sg
  ... | us = stepSb t _ ,- us
  STABLE.suIpOp (JOY u) = parSteps
  STABLE.atomOk (JOY u) a = []
  STABLE.consOk (JOY u) s t = star (_& _) (_<& _) s ++ star (_ &_) (_ &>_) t
  STABLE.abstOk (JOY u) t = star ^_ ^_ t
  STABLE.embdOk (JOY u) e = star `_ `_ e
  STABLE.loclOk (JOY u) x = []
  STABLE.elimOk (JOY u) e s = star (_$ _) (_<$ _) e ++ star (_ $_) (_ $>_) s
  STABLE.radiOk (JOY u) t T = star (_:: _) (_<:: _) t ++ star (_ ::_) (_ ::>_) T

  _&&_ : Two -> Two -> Two
  tt && b = b
  ff && b = ff
  infixr 4 _&&_

  not : Two -> Two
  not tt = ff
  not ff = tt
  
  done? : forall {n d} -> Tm n d -> Two
  done? (! a)    = tt
  done? (s & t)  = done? s && done? t
  done? (^ t)    = done? t
  done? (` (t :: T)) = ff
  done? (` e)        = done? e
  done? (# x)    = tt
  done? ((t :: T) $ s) = done? t && done? T && done? s && not (fst (contract t T s))
  done? (e $ s)  = done? e && done? s
  done? (t :: T) = done? t && done? T

  gasRed : Nat -> forall {n d} -> Tm n d -> Tm n d
  gasRed [] t = t
  gasRed (z su) t with done? t
  ... | tt = t
  ... | ff = gasRed z (develop t)

  gasRedSound : forall z {n d} (t : Tm n d) -> Star _~>_ t (gasRed z t)
  gasRedSound (z su) t with done? t
  gasRedSound (z su) t | ff with develop t | developSteps t
  ... | t' | r = r ++ gasRedSound z t'
  gasRedSound (z su) t | tt = []
  gasRedSound [] t = []
