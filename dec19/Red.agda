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
ElimBeta' = Tm' [] chk -- target type
        ->' Tm' [] chk -- eliminator
        ->' (Tm' [] syn ->' Tm' [] chk)  -- result type in the abstract
         *' (Tm' [] chk ->' Tm' [] chk)  -- result value, concretely

module RED (eb' : forall {G} -> G :- ElimBeta') where

  Contract' : Ty'
  Contract' = Tm' [] chk -- target type
           *' Tm' [] chk -- eliminator
           *' Tm' [] chk -- target intro
          ->' Tm' [] chk -- result value
           *' Tm' [] chk -- result type

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
  contract t T s = [ contract' ]P E0' >>= \ f -> f (T , s , t)

  contractStableSb : forall {n m}(sg : Sb n m)
    -> (t : Tm n chk)(T : Tm n chk)(s : Tm n chk)
    -> (t' T' : Tm n chk)
    -> contract t T s ~ (tt , t' , T')
    -> contract (t /Tm sg) (T /Tm sg) (s /Tm sg) ~ (tt , t' /Tm sg , T' /Tm sg)
  contractStableSb {n}{m} sg t T s t' T' = help where
    open REL (SUB sg)
    help : contract t T s ~ (tt , t' , T')
        -> contract (t /Tm sg) (T /Tm sg) (s /Tm sg) ~ (tt , t' /Tm sg , T' /Tm sg)
    help = yelp ([ contract' ]P E0') ([ contract' ]P E0') (lift contract' E0' E0' (\ ())) where
      yelp : (f0 : One + (n +[ Contract' ]))(f1 : One + (m +[ Contract' ]))(fl : MayLift (Lift Contract') f0 f1) ->
             (f0 >>= \ f -> f (T , s , t)) ~ (tt , t' , T') ->
             (f1 >>= \ f -> f (T /Tm sg , s /Tm sg , t /Tm sg)) ~ (tt , t' /Tm sg , T' /Tm sg)
      yelp (tt , f0) (tt , f1) (ye fl) q with f0 (T , s , t) | f1 (T /Tm sg , s /Tm sg , t /Tm sg) | fl (T , s , t) _ (r~ , r~ , r~)
      yelp (tt , f0) (tt , f1) (ye fl) r~ | .(tt , _ , _) | .(tt , _) | ye (r~ , r~) = r~
    
  contractStableTh : forall {n m}(th : n <= m)
    -> (t : Tm n chk)(T : Tm n chk)(s : Tm n chk)
    -> (t' T' : Tm n chk)
    -> contract t T s ~ (tt , t' , T')
    -> contract (t ^Tm th) (T ^Tm th) (s ^Tm th) ~ (tt , t' ^Tm th , T' ^Tm th)
  contractStableTh {n}{m} th t T s t' T' = help where
    open REL (THN th)
    help : contract t T s ~ (tt , t' , T')
        -> contract (t ^Tm th) (T ^Tm th) (s ^Tm th) ~ (tt , t' ^Tm th , T' ^Tm th)
    help = yelp ([ contract' ]P E0') ([ contract' ]P E0') (lift contract' E0' E0' (\ ())) where
      yelp : (f0 : One + (n +[ Contract' ]))(f1 : One + (m +[ Contract' ]))(fl : MayLift (Lift Contract') f0 f1) ->
             (f0 >>= \ f -> f (T , s , t)) ~ (tt , t' , T') ->
             (f1 >>= \ f -> f (T ^Tm th , s ^Tm th , t ^Tm th)) ~ (tt , t' ^Tm th , T' ^Tm th)
      yelp (tt , f0) (tt , f1) (ye fl) q with f0 (T , s , t) | f1 (T ^Tm th , s ^Tm th , t ^Tm th) | fl (T , s , t) _ (r~ , r~ , r~)
      yelp (tt , f0) (tt , f1) (ye fl) r~ | .(tt , _ , _) | .(tt , _) | ye (r~ , r~) = r~
    
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

  PAR : forall {n} -> REL \ m -> _=>_ {n +B m}
  REL.localSb (PAR {n}) {p} {m} t0 t1 t sg0 sg1 r =
    parSb t (locSb m sg0) (locSb m sg1) (help n p m sg0 sg1 r) where
    help : forall n p m (sg0 sg1 : Sb m (n +B p))(r : forall i -> sg0 i => sg1 i) ->
           forall i -> locSb {n}{p} m sg0 i => locSb {n}{p} m sg1 i
    help n p (m -, x) sg0 sg1 r (i -^ .x) = help n p m _ _ (\ i -> r (i -^ _)) i
    help n p (m -, .<>) sg0 sg1 r (i -, .<>) = r (none su)
    help n p [] sg0 sg1 r i = # i
  REL.atomInv PAR (! a) = r~
  REL.consInv PAR (s & t) = _ , r~ , s , t
  REL.abstInv PAR (^ t) = _ , r~ , t
  REL.atomOk PAR = !_
  REL.consOk PAR = _&_
  REL.abstOk PAR = ^_
  REL.embdOk PAR = `_
  REL.loclOk PAR x = # (x ^^ thinr)
  REL.elimOk PAR = _$_
  REL.radiOk PAR = _::_

  contractStablePar : forall {n}
    -> {t0 t1 : Tm n chk} -> t0 => t1
    -> {T0 T1 : Tm n chk} -> T0 => T1
    -> {s0 s1 : Tm n chk} -> s0 => s1
    -> {t'0 T'0 : Tm n chk}
    -> contract t0 T0 s0 ~ (tt , t'0 , T'0)
    -> (_ * _) >< \ (t'1 , T'1)
    -> (t'0 => t'1) * (T'0 => T'1) * contract t1 T1 s1 ~ (tt , t'1 , T'1)
  contractStablePar {n} {t0}{t1} t {T0}{T1} T {s0}{s1} s {t'0}{T'0} = help where
    open REL (PAR {n})
    help : contract t0 T0 s0 ~ (tt , t'0 , T'0)
        -> (_ * _) >< \ (t'1 , T'1)
        -> (t'0 => t'1) * (T'0 => T'1) * contract t1 T1 s1 ~ (tt , t'1 , T'1)
    help = yelp ([ contract' ]P E0') ([ contract' ]P E0') (lift contract' E0' E0' (\ ())) where
      yelp : (f0 : One + (n +[ Contract' ]))(f1 : One + (n +[ Contract' ]))(fl : MayLift (Lift Contract') f0 f1) ->
             (f0 >>= \ f -> f (T0 , s0 , t0)) ~ (tt , t'0 , T'0) -> (_ * _) >< \ (t'1 , T'1)
        ->   (t'0 => t'1) * (T'0 => T'1) * (f1 >>= \ f -> f (T1 , s1 , t1)) ~ (tt , t'1 , T'1)
      yelp (tt , f0) (tt , f1) (ye fl) q with f0 (T0 , s0 , t0) | f1 (T1 , s1 , t1) | fl _ _ (T , s , t)
      yelp (tt , f0) (tt , f1) (ye fl) r~ | .(tt , _ , _) | .(tt , _) | ye (t' , T') = _ , t' , T' , r~

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
  ... | tt , r , R = r :: R
  ... | ff , <> = (t' :: T') $ s' -- never happens, we know
  develop (e $ s) = develop e $ develop s
  develop (t :: T) = develop t :: develop T

  developLemma : forall {n d}(t0 t1 : Tm n d) ->
    t0 => t1 -> t1 => develop t0
  developLemma .((_ :: _) $ _) .(_ :: _) (beta {t}{t'}{T}{T'}{s}{s'} q0 tr Tr sr q1)
    with contract t T s | develop t | develop T | develop s | developLemma _ _ tr | developLemma _ _ Tr | developLemma _ _ sr
  ... | a | td | Td | sd | th | Th | sh with contractStablePar th Th sh q1
  developLemma .((t :: T) $ s) .(_ :: _) (beta {t} {t'} {T} {T'} {s} {s'} r~ tr Tr sr q1)
    | .(tt , _ , _) | td | Td | sd | th | Th | sh | (r' , R') , rd , Rd , q2
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
  ... | (t'1 , T'1) , r , R , q  with contractStablePar th Th sh q
  ... | (rd , Rd) , x , y , qd
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


KiplingElimBeta : forall {G} -> G :- ElimBeta'
KiplingElimBeta = mat'
  (\ { A0 -> \'{-P-} (chk' (! TY) (?' (none SU)) /    -- any type you ask for
             (  (\' (?'{-P-} (none SU NO)))           -- 0-elim gives you but
             ,' (\' naw')                        -- it does not compute
             ))
     ; A2 -> cons' (mat'
               (yer TY (cons' (\'{-F-} (chk' (! TY) (?'{-F-} (none SU)) /
                               (\'{-T-} (chk' (! TY) (?'{-T-} (none SU)) /
                               (  (\' (! TY))    -- Big If makes types
                               ,' atom' \ { A0 -> (?'{-F-} (none SU NO))
                                          ; A1 -> (?'{-T-} (none SU))
                                          ; _ -> naw' }
                               )))))))
               naw'
               ({-b-} ! A2 ,' (\'{-P-} (chk' (! TY) (?'{-P-} (none SU)) /
                    cons' (\'{-f-} (chk' (sub' ([] su) (?'{-P-} (none SU NO)) (aye' ,' (! A0 :: ! A2))) (?'{-f-} (none SU)) /
                           (\'{-t-} (chk' (sub' ([] su) (?'{-P-} (none SU NO NO)) (aye' ,' (! A1 :: ! A2))) (?'{-t-} (none SU)) /
                             (  (\'{-e-} sub' ([] su) (?'{-P-} (none SU NO NO NO)) (aye' ,' (?'{-e-} (none SU))))
                             ,' atom' \ { A0 -> (?'{-f-} (none SU NO))
                                        ; A1 -> (?'{-t-} (none SU))
                                        ; _ -> naw' }
                             ))) ))))))
     ; _ -> naw' })
  (atom' \ { PI -> cons' (\'{-S-} (abst' (?'{-S-} (none SU)) (\'{-T-} (
                       (\'{-s-} (chk' (?'{-S-} (none SU NO NO)) (?'{-s-} (none SU)) /
                         (  (\'{-f-} sub' ([] su) (?'{-T-} (none SU NO NO)) (aye' ,' ((?'{-s-} (none SU NO)) :: (?'{-S-} (none SU NO NO NO)))))
                         ,' abst' (?'{-S-} (none SU NO NO)) (\'{-t-} sub' ([] su) (?'{-t-} (none SU)) (aye' ,' ((?'{-s-} (none SU NO)) :: (?'{-S-} (none SU NO NO NO)))))
                         )))))))
           ; SG -> cons' (\'{-S-} (abst' (?'{-S-} (none SU)) (\'{-T-}
                       atom' \ { A0 -> (\'{-e-} (?'{-S-} (none SU NO NO)))
                                    ,' cons' (\'{-s-} (\'{-t-} (?'{-s-} (none SU NO))))
                               ; A1 -> (\'{-e-} sub' ([] su) (?'{-T-} (none SU NO)) (aye' ,' ((?'{-e-} (none SU)) $ ! A0)))
                                    ,' cons' (\'{-s-} (\'{-t-} (?'{-t-} (none SU))))
                               ; _ -> naw' })))
           ; _ -> naw' })
  naw'

open RED KiplingElimBeta

testLAPI : forall {n} -> (t : Tm (n su) chk)(S : Tm n chk)(T : Tm (n su) chk)(s : Tm n chk) -> One + (Tm n chk * Tm n chk)
testLAPI t S T s = contract (^ t) (! PI & S & ^ T) s

