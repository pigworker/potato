module Red where

open import Eq
open import Tuple
open import Thin
open import Tm
open import Meta

ElimSyn : Ty'
ElimSyn = Tm' [] syn -- target
      ->' Tm' [] chk -- target type
      ->' Tm' [] chk -- eliminator
      ->' Tm' [] chk -- result type

KiplingElimSyn : forall {G} -> G :- ElimSyn
{-
(e :: ! A0) $ T <: T
(e :: ! A2) $ (! TY & F & T) <: ! TY
(e :: ! A2) $ ((^ P) & f & t) <: P / e
(e :: (! PI & S & ^ T)) $ s <: T / (s :: S)
(e :: (! SG & S & ^ T)) $ ! A0 <: S
(e :: (! SG & S & ^ T)) $ ! A1 <: T / (e $ ! A0)
-}
KiplingElimSyn = \' mat'
  (\ { A0 -> \' (?' (none -, _))
     ; A2 -> cons' (mat' (yer TY (cons' (\' (\' (! TY)))))
                      naw'
                      (\' cons' (\' (\' sub' ([] su) (?' (none -, _ -^ _ -^ _)) (aye' ,' (?' (none -, _ -^ _ -^ _ -^ _)))))))
     ; _ -> naw' })
  (atom' (\ { PI -> cons' (\' abst' (\' (\' sub' ([] su) (?' (none -, _ -^ _)) (aye' ,' ((?' (none -, _)) :: (?' (none -, _ -^ _ -^ _)))))) )
            ; SG -> cons' (\' abst' (\' atom' \ { A0 -> ?' (none -, _ -^ _)
                                                ; A1 -> sub' ([] su) (?' (none -, _)) (aye' ,' ((?' (none -, _ -^ _ -^ _)) $ ! A0))
                                                ; _ -> naw' }))
            ; _ -> naw' }))
  naw'

BetaVal : Ty'
BetaVal = Tm' [] chk -- target type
      ->' Tm' [] chk -- eliminator
      ->' Tm' [] chk -- intro
      ->' Tm' [] chk -- return value

KiplingBetaVal : forall {G} -> G :- BetaVal
{-
(! A0 :: ! A2) $ (! TY & F * T) ~> F
(! A0 :: ! A2) $ ((^ P) & f & t) ~> f
(! A1 :: ! A2) $ (! TY & F * T) ~> T
(! A1 :: ! A2) $ ((^ P) & f & t) ~> t
(^ t :: ! PI & S & ^ T) $ s ~> t / (s :: S)
(s & t :: ! SG & S & T) $ ! A0 ~> s
(s & t :: ! SG & S & T) $ ! A1 ~> t
-}
KiplingBetaVal = mat'
  (yer A2 (cons' (mat' (yer TY (cons' (\' (\' atom' \ { A0 -> ?' (none -, _ -^ _) ; A1 -> ?' (none -, _) ; _ -> naw' }) )))
                       naw'
                       (\' cons' (\' (\' atom' \ { A0 -> ?' (none -, _ -^ _) ; A1 -> ?' (none -, _) ; _ -> naw' }))))))
  (atom' (\ { PI -> cons' (\' abst' (\' (\' abst' (\' sub' ([] su) (?' (none -, _)) (aye' ,' ((?' (none -, _ -^ _)) :: (?' (none -, _ -^ _ -^ _ -^ _))))))))
            ; SG -> cons' (\' abst' (\' atom' \ { A0 -> cons' (\' (\' (?' (none -, _ -^ _))))
                                                ; A1 -> cons' (\' (\' (?' (none -, _))))
                                                ; _ -> naw' }))
            ; _ -> naw' }))
  naw'


{-
BetaStep : Set
BetaStep = forall {n} -> Pat n (Pat n (Pat n (Ex n chk)))  -- type, elim, intro -> term

KiplingElim : forall {n} -> Pat n (Pat n (Tm n syn -> Ex n chk))  -- type, elim -> result type
KiplingElim = split
  (yer A2 (pair (split (yer TY (pair (eat \ f -> eat \ t -> \ _ -> ! TY)))
                       fail
                       (eat \ P -> pair (eat \ f -> eat \ t -> \ e -> [ P ] // [ e ])))))
  (atom (\ { PI -> tt , pair (eat \ S -> abst (eat \ T -> eat \ s -> \ _ -> [ T ] // ([ s ] :: [ S ])))
           ; SG -> tt , pair (eat \ S -> abst (eat \ T -> atom \ { A0 -> tt , \ _ -> [ S ]
                                                                 ; A1 -> tt , \ e -> [ T ] // ([ e ] $ ! A0)
                                                                 ; _ -> ff , <> }))
           ; _  -> ff , <> }))
  fail


KiplingBeta : BetaStep
KiplingBeta = split
  (yer A2 (pair (split (yer TY (pair (eat \ f -> eat \ t -> atom \ { A0 -> tt , [ f ] ; A1 -> tt , [ t ] ; _ -> ff , <> })))
                       fail
                       (eat \ P -> pair (eat \ f -> eat \ t -> atom \ { A0 -> tt , [ f ] ; A1 -> tt , [ t ] ; _ -> ff , <> })))))
  (atom (\ { PI -> tt , pair (eat \ S -> abst (eat \ T -> eat \ s -> abst (eat \ t -> [ t ] // ([ s ] :: [ S ]))))
           ; SG -> tt , pair (eat \ S -> abst (eat \ T -> atom \ { A0 -> tt , pair (eat \ s -> eat \ t -> [ s ])
                                                                 ; A1 -> tt , pair (eat \ s -> eat \ t -> [ t ])
                                                                 ; _ -> ff , <> }))
           ; _  -> ff , <> }))
  fail


BetaStep : Set
BetaStep = forall {n} -> Tm n chk -> Tm n chk -> Tm n chk ->
                  One + (Tm n chk * Tm n chk)

StableBeta : BetaStep -> Set
StableBeta step = forall {n}(t T s : Tm n chk){r R} ->
  step t T s ~ (tt , r , R) ->
  forall {m}(sg : Sb n m) ->
  step (t /Tm sg) (T /Tm sg) (s /Tm sg) ~ (tt , r /Tm sg , R /Tm sg)

module RED
  (step : BetaStep)
  (stepSb : StableBeta step)
  where

  stepTh : forall {n}(t T s : Tm n chk){r R} ->
    step t T s ~ (tt , r , R) ->
    forall {m}(th : n <= m) ->
    step (t ^Tm th) (T ^Tm th) (s ^Tm th) ~ (tt , r ^Tm th , R ^Tm th)
  stepTh t T s {r} {R} q th
    rewrite thSb t th | thSb T th | thSb s th | thSb r th | thSb R th
    = stepSb t T s q (\ x -> # (x ^^ th))


  data _~>_ {n} : forall {d} -> Tm n d -> Tm n d -> Set where
    beta : forall {t T s r R} ->
           step t T s ~ (tt , r , R) ->
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

  data _=>_ {n} : forall {d} -> Tm n d -> Tm n d -> Set where
    beta : forall {t t' T T' s s' r r' R R'} ->
           step t T s ~ (tt , r , R) ->
           t => t' -> T => T' -> s => s' ->
           step t' T' s' ~ (tt , r' , R') ->
           ((t :: T) $ s) => (r' :: R')
    upsi : forall {t t' T} -> t => t' -> (` (t :: T)) => t'
    !_  : forall a -> (! a) => (! a)
    _&_ : forall {s s' t t'} -> s => s' -> t => t' -> (s & t) => (s' & t')
    ^_ : forall {t t'} -> t => t' -> (^ t) => (^ t')
    `_ : forall {e e'} -> e => e' -> (` e) => (` e')
    #_ : forall x -> (# x) => (# x)
    _$_ : forall {e e' s s'} -> e => e' -> s => s' -> (e $ s) => (e' $ s')
    _::_ : forall {t t' T T'} -> t => t' -> T => T' -> (t :: T) => (t' :: T')


  parRefl : forall {n d}(t : Tm n d) -> t => t
  parRefl (! a) = ! a
  parRefl (s & t) = parRefl s & parRefl t
  parRefl (^ t) = ^ parRefl t
  parRefl (` e) = ` parRefl e
  parRefl (# x) = # x
  parRefl (e $ s) = parRefl e $ parRefl s
  parRefl (t :: T) = parRefl t :: parRefl T

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

  parTh : forall {n m d}{t t' : Tm n d} -> t => t' ->
            (th : n <= m) ->
            (t ^Tm th) => (t' ^Tm th)
  parTh (beta q0 t T s q1) th = beta (stepTh _ _ _ q0 th) (parTh t th) (parTh T th) (parTh s th) (stepTh _ _ _ q1 th)
  parTh (upsi t) th = upsi (parTh t th)
  parTh (! a) th = ! a
  parTh (s & t) th = parTh s th & parTh t th
  parTh (^ t) th = ^ parTh t (th su)
  parTh (` e) th = ` parTh e th
  parTh (# x) th = # _
  parTh (e $ s) th = parTh e th $ parTh s th
  parTh (t :: T) th = parTh t th :: parTh T th

  parSb : forall {n m d}{t t' : Tm n d} -> t => t' ->
            (sg sg' : Sb n m) ->
            (forall x -> sg x => sg' x) ->
            (t /Tm sg) => (t' /Tm sg')
  parSb (beta q0 t T s q1) sg sg' rs =
    beta (stepSb _ _ _ q0 sg) (parSb t sg sg' rs) (parSb T sg sg' rs) (parSb s sg sg' rs) (stepSb _ _ _ q1 sg')
  parSb (upsi t) sg sg' rs = upsi (parSb t sg sg' rs)
  parSb (! a) sg sg' rs = ! a
  parSb (s & t) sg sg' rs = parSb s sg sg' rs & parSb t sg sg' rs
  parSb (^ t) sg sg' rs = ^ parSb t (sg +1Sb) (sg' +1Sb) \
    { (x no) -> parTh (rs x) (iota no) 
    ; (x su) -> # _
    }
  parSb (` e) sg sg' rs = ` parSb e sg sg' rs
  parSb (# x) sg sg' rs = rs x
  parSb (e $ s) sg sg' rs = parSb e sg sg' rs $ parSb s sg sg' rs
  parSb (t :: T) sg sg' rs = parSb t sg sg' rs :: parSb T sg sg' rs

  develop : forall {n d}(t : Tm n d) -> Tm n d
  develop (! a) = ! a
  develop (s & t) = develop s & develop t
  develop (^ t) = ^ develop t
  develop (` (t :: T)) = develop t
  develop (` e) = ` develop e
  develop (# x) = # x
  develop ((t :: T) $ s) with step t T s | develop t | develop T | develop s
  ... | ff , _ | t' | T' | s' = (t' :: T') $ s'
  ... | tt , _ | t' | T' | s' with step t' T' s'
  ... | tt , r , R = r :: R
  ... | ff , <> = (t' :: T') $ s' -- never happens, we hope
  develop (e $ s) = develop e $ develop s
  develop (t :: T) = develop t :: develop T

  module GOOD
    (good : forall {n}{t T s t' T' s' r R : Tm n chk} ->
            t => t' -> T => T' -> s => s' ->
            step t T s ~ (tt , r , R) ->
            _ >< \ x ->
            step t' T' s' ~ (tt , x) * r => fst x * R => snd x)
    where

    developLemma : forall {n d}(t0 t1 : Tm n d) ->
      t0 => t1 -> t1 => develop t0
    developLemma .((_ :: _) $ _) .(_ :: _) (beta {t}{t'}{T}{T'}{s}{s'} q0 tr Tr sr q1)
      with step t T s | develop t | develop T | develop s | developLemma _ _ tr | developLemma _ _ Tr | developLemma _ _ sr
    ... | a | td | Td | sd | th | Th | sh with good th Th sh q1
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
      with step t0 T0 s0
         | develop t0 | developLemma _ _ t | develop T0 | developLemma _ _ T | develop s0 | developLemma _ _ s
         | good {_}{t0}{T0}{s0}
    developLemma ((t0 :: T0) $ s0) (.(_ :: _) $ s1) (e $ s) | ff , <> | td | th | Td | Th | sd | sh | g = (th :: Th) $ sh
    developLemma ((t0 :: T0) $ s0) (.(_ :: _) $ s1) ((t :: T) $ s) | tt , r0 , R0 | td | th | Td | Th | sd | sh | g with g t T s r~
    ... | (r , R) , q , rr , Rr with good th Th sh q
    ... | (rd , Rd) , qd , x , y
      rewrite qd = beta q th Th sh qd
    developLemma .(_ :: _) .(_ :: _) (t :: T) = developLemma _ _ t :: developLemma _ _ T

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

    confluence : forall {n d}{s p q : Tm n d} -> Star _~>_ s p -> Star _~>_ s q ->
              _ >< \ r -> Star _~>_ p r * Star _~>_ q r
    confluence sp sq
      with _ , pr , qr <- parallelogram (star (\ x -> x) stepPar sp) (star (\ x -> x) stepPar sq)
         = _ , starB (\ x -> x) parSteps pr , starB (\ x -> x) parSteps qr


KiplingBeta : BetaStep
KiplingBeta (^ t)   (! PI & S & ^ T) s      = tt , (t /0 (s :: S) , T /0 (s :: S))
KiplingBeta (s & t) (! SG & S & ^ T) (! A0) = tt , s , S
KiplingBeta (s & t) (! SG & S & ^ T) (! A1) = tt , t , T /0 (s :: S)
KiplingBeta (! A0)  (! A2) (! TY & F & T)   = tt , F , ! TY
KiplingBeta (! A1)  (! A2) (! TY & F & T)   = tt , T , ! TY
KiplingBeta (! A0)  (! A2) ((^ P) & f & t)  = tt , f , P /0 (! A0 :: ! A2)
KiplingBeta (! A1)  (! A2) ((^ P) & f & t)  = tt , t , P /0 (! A1 :: ! A2)
KiplingBeta t T s = ff , <>

KiplingBetaStab : StableBeta KiplingBeta
KiplingBetaStab (^ t)   (! PI & S & ^ T) s      r~ sg rewrite stabSb0 t (s :: S) sg | stabSb0 T (s :: S) sg = r~
KiplingBetaStab (s & t) (! SG & S & ^ T) (! A0) r~ sg = r~
KiplingBetaStab (s & t) (! SG & S & ^ T) (! A1) r~ sg rewrite stabSb0 T (s :: S) sg = r~
KiplingBetaStab (! A0)  (! A2) (! TY & F & T)   r~ sg = r~
KiplingBetaStab (! A1)  (! A2) (! TY & F & T)   r~ sg = r~
KiplingBetaStab (! A0)  (! A2) ((^ P) & f & t)  r~ sg rewrite stabSb0 P (! A0 :: ! A2) sg = r~
KiplingBetaStab (! A1)  (! A2) ((^ P) & f & t)  r~ sg rewrite stabSb0 P (! A1 :: ! A2) sg = r~

open RED KiplingBeta KiplingBetaStab public

KiplingBetaGood : forall {n}{t T s t' T' s' r R : Tm n chk} ->
            t => t' -> T => T' -> s => s' ->
            KiplingBeta t T s ~ (tt , r , R) ->
            _ >< \ x ->
            KiplingBeta t' T' s' ~ (tt , x) * r => fst x * R => snd x
KiplingBetaGood (RED.! A0) (RED.! A2) ((RED.! TY) RED.& (F RED.& T)) r~ = _ , r~ , F , ! TY
KiplingBetaGood (RED.! A0) (RED.! A2) ((RED.^ P) RED.& (f RED.& t)) r~ =
  _ , r~ , f , parSb P _ _ \
    { (x no) -> # _
    ; (x su) -> ! A0 :: ! A2
    }
KiplingBetaGood (RED.! A1) (RED.! A2) ((RED.! TY) RED.& (F RED.& T)) r~ = _ , r~ , T , ! TY
KiplingBetaGood (RED.! A1) (RED.! A2) ((RED.^ P) RED.& (f RED.& t)) r~ =
  _ , r~ , t , parSb P _ _ \
    { (x no) -> # _
    ; (x su) -> ! A1 :: ! A2
    }
KiplingBetaGood (s RED.& t) ((RED.! SG) RED.& (S RED.& (RED.^ T))) (RED.! A0) r~ =
  _ , r~ , s , S
KiplingBetaGood (s RED.& t) ((RED.! SG) RED.& (S RED.& (RED.^ T))) (RED.! A1) r~ =
  _ , r~ , t , parSb T _ _ \
    { (x no) -> # _
    ; (x su) -> s :: S
    }
KiplingBetaGood (RED.^ t) ((RED.! PI) RED.& (S RED.& (RED.^ T))) s r~ =
  _ , r~
  , (parSb t _ _ \
    { (x no) -> # _
    ; (x su) -> s :: S
    })
  , (parSb T _ _ \
    { (x no) -> # _
    ; (x su) -> s :: S
    })

open GOOD KiplingBetaGood
-}
