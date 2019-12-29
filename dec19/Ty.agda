module Ty where

open import Eq
open import Tuple
open import Thin
open import Tm
open import Meta
open import Red


All : forall {X} -> (X -> Set) -> List X -> Set
All P [] = One
All P (x ,- xs) = P x * All P xs

FormIntro' : Ty'
FormIntro' = Chk' [] any *' Chk' [] (gdd ff) ->' Aye'

module RULES
  (formIntro' : [] :- FormIntro')
  (elimBeta'  : [] :- ElimBeta')
  where
  open RED elimBeta'

  formIntro : forall {n}(T : Tm n chk)(t : Tm n chk) -> Go (Req t) One
  formIntro T t =
    sem' t (E0' _) formIntro' >>= \ k ->
    k (T , t , hic)

  elimTyTy' : Ty'
  elimTyTy' = Syn' [] *' Chk' [] any *' Chk' [] (gdd tt)
          ->' Chk' [] any

  elimTy' : [] :- elimTyTy'
  elimTy' =
    unc' (\'{-e-} unc' (\'{-S-} (\'{-s-} (
    unc' (\'{-R-} (\'{-r-} ((?'{-R-} (none SU NO)) $' (?'{-e-} (none SU NO NO NO NO)))))
    $' ((clo' elimBeta'
         $' (?'{-S-} (none SU NO)))
         $' (?'{-s-} (none SU))))
    )))

  elimTy : forall {n}(e : Tm n syn)(S : Tm n chk)(s : Tm n chk) ->
           Go (Req (e $ s)) (Tm n chk)
  elimTy e S s = 
    sem' (e $ s) (E0' _) elimTy' >>= \ k ->
    k (e , S , s , arg hic)

  data _|-_:>_ {n} (G : Cx n) : Tm n chk -> Tm n chk -> Set
  data _|-_<:_ {n} (G : Cx n) : Tm n syn -> Tm n chk -> Set

  Judge : forall {d n}(u : Tm n d) -> Cx n -> Req u -> Set
  Judge u G (m , T , t , g) = (G +Cx g) |- T :> t

  data _|-_:>_ {n} G where

    embed : forall {e S T} ->
           G |- e <: S ->
           S ~ T ->
           G |- T :> ` e

    intro : forall {T t rs} ->
            formIntro T t ~ (rs -: <>) ->
            All (Judge t G) rs ->
            G |- T :> t

    pre : forall {T T' t} ->
           T ~> T' ->
           G |- T' :> t ->
           G |- T :> t

  data _|-_<:_ {n} G where

    #_ : (x : Fi n) -> G |- # x <: G x

    rad : forall {t T} ->
            G |- ! TY :> T ->
            G |- T :> t ->
            G |- t :: T <: T
            
    elim : forall {e S s rs S'} ->
            G |- e <: S ->
            elimTy e S s ~ (rs -: S') ->
            All (Judge (e $ s) G) rs ->
            G |- e $ s <: S'

    post : forall {e S S'} ->
            G |- e <: S ->
            S ~> S' ->
            G |- e <: S'

  mkIntro : forall {n}(G : Cx n) T t -> One -> forall {rs} ->
    formIntro T t ~ (rs -: <>) ->
    All (Judge t G) rs ->
    G |- T :> t
  mkIntro G T t <> q hs = intro q hs

  mkElim : forall {n}(G : Cx n){e S} ->
           G |- e <: S -> forall s ->
           One -> forall {rs S'} ->
           elimTy e S s ~ (rs -: S') ->
           All (Judge (e $ s) G) rs ->
           G |- e $ s <: S'
  mkElim G eS s <> q Tts = elim eS q Tts

  preSteps : forall {n}{G : Cx n}{T T' t} ->
    Star _~>_ T T' -> G |- T' :> t -> G |- T :> t
  preSteps [] Tt = Tt
  preSteps (r ,- rs) Tt = pre r (preSteps rs Tt)

  postSteps : forall {n}{G : Cx n}{e S S'} ->
    G |- e <: S -> Star _~>_ S S' -> G |- e <: S'
  postSteps eS [] = eS
  postSteps eS (r ,- rs) = postSteps (post eS r) rs

  module CHECKER
    (redTy      : forall {n} -> Cx n -> Tm n chk -> Tm n chk)
    (redTySound : forall {n}(G : Cx n)(T : Tm n chk) -> Star _~>_ T (redTy G T))
    where

    eqTest : forall {n} -> Tm n chk -> Tm n chk -> Go Zero One
    eqTest S T with S ~Tm?~ T
    eqTest S T | ff , _ = abort
    eqTest S T | tt , _ = [] -: <>

    typeCheckRec : forall {n} -> Cx n -> Tm n chk -> (t : Tm n chk) -> TmRec t -> Go Zero One
    synthTypeRec : forall {n} -> Cx n ->             (e : Tm n syn) -> TmRec e -> Go Zero (Tm n chk)
    premises : forall {n}{d}(G : Cx n)
               (u : Tm n d)(ug : {m : Nat} {t : Tm m chk} -> Gdd u tt t -> TmRec t)
               (rs : List (Req u)) -> Go Zero One

    typeCheckRec G T t tr with redTy G T
    typeCheckRec G T t (can _ tg) | T' with formIntro T t
    typeCheckRec G T t (can _ tg) | T' | abort = abort
    typeCheckRec G T t (can _ tg) | T' | rs -: <> = premises G t tg rs
    typeCheckRec G T (` e) (emb er) | T' = 
      synthTypeRec G e er >>= \ S ->
      eqTest S T'

    premises G u ug [] = [] -: <>
    premises G u ug ((_ , T , t , g) ,- rs) = 
      typeCheckRec (G +Cx g) T t (ug g) >>= \ _ ->
      premises G u ug rs

    synthTypeRec G .(# x)   (var x)     = [] -: redTy G (G x)
    synthTypeRec G (e $ s)  (eli er sg) with synthTypeRec G e er
    ... | abort = abort
    ... | [] -: S with elimTy e S s
    ... | abort = abort
    ... | rs -: S' = premises G (e $ s) sg rs >>= \ _ -> [] -: redTy G S'
    synthTypeRec G (t :: T) (rad tr Tr) = 
      typeCheckRec G (! TY) T Tr >>= \ _ ->
      typeCheckRec G T t tr >>= \ _ ->
      [] -: redTy G T

    typeCheck : forall {n} -> Cx n -> Tm n chk -> Tm n chk -> Go Zero One
    typeCheck G T t = typeCheckRec G T t (tmRec t)
    synthType : forall {n} -> Cx n -> Tm n syn -> Go Zero (Tm n chk)
    synthType G e = synthTypeRec G e (tmRec e)

    typeCheckRecSound : forall {n}(G : Cx n)(T t : Tm n chk)(tr : TmRec t) ->
      typeCheckRec G T t tr ~ ([] -: <>) ->
      G |- T :> t

    synthTypeRecSound : forall {n}(G : Cx n)(e : Tm n syn)(er : TmRec e)
      (S : Tm n chk) -> synthTypeRec G e er ~ ([] -: S) ->
      G |- e <: S

    premisesSound : forall {n d}(G : Cx n)
      (u : Tm n d)(ug : {m : Nat} {t : Tm m chk} -> Gdd u tt t -> TmRec t)
      (rs : List (Req u)) ->
      premises G u ug rs ~ ([] -: <>) ->
      All (Judge u G) rs 

    typeCheckRecSound G T t tr q with redTy G T | redTySound G T
    typeCheckRecSound G T t (can _ tg) q | T' | TT' with formIntro T t | mkIntro G T t
    typeCheckRecSound G T t (can _ tg) q | T' | TT' | rs -: <> | mki
      with premises G t tg rs | premisesSound G t tg rs
    ... | [] -: <> | Tts = mki <> r~ (Tts r~)
    typeCheckRecSound G T (` e) (emb er) q | T' | TT'
      with synthTypeRec G e er | synthTypeRecSound G e er
    typeCheckRecSound G T (` e) (emb er) q | T' | TT' | [] -: S | eSok
      with eSok _ r~ | S ~Tm?~ T'
    typeCheckRecSound G T (` e) (emb er) q | .S | TT' | [] -: S | eSok | eS | tt , r~ =
      preSteps TT' (embed eS r~)

    synthTypeRecSound G .(# x) (var x) S q with redTy G (G x) | redTySound G (G x)
    synthTypeRecSound G .(# x) (var x) .S' r~ | S' | SS' = postSteps (# x) SS'
    synthTypeRecSound G (e $ s) (eli er sg) S q
      with synthTypeRec G e er | synthTypeRecSound G e er
    ... | [] -: R | eS0
      with elimTy e R s | mkElim G (eS0 _ r~) s
    ... | rs -: S0 | mke
      with premises G (e $ s) sg rs | premisesSound G (e $ s) sg rs
    ... | [] -: <> | Tts
      with redTy G S0 | redTySound G S0
    synthTypeRecSound G (e $ s) (eli er sg) .S1 r~
      | [] -: R | eS0 | rs -: S0 | mke | [] -: <> | Tts | S1 | S0S1
      = postSteps (mke <> r~ (Tts r~)) S0S1
    synthTypeRecSound G (t :: T) (rad tr Tr) S q
      with typeCheckRec G (! TY) T Tr | typeCheckRecSound G (! TY) T Tr
    ... | [] -: <> | TyT
      with typeCheckRec G T t tr | typeCheckRecSound G T t tr
    ... | [] -: <> | Tt
      with redTy G T | redTySound G T
    synthTypeRecSound G (t :: T) (rad tr Tr) .T' r~
      | [] -: <> | TyT | [] -: <> | Tt | T' | TT'
      = postSteps (rad (TyT r~) (Tt r~)) TT'

    premisesSound G u ug [] q = <>
    premisesSound G u ug ((_ , T , t , g) ,- rs) q
      with typeCheckRec (G +Cx g) T t (ug g) | typeCheckRecSound (G +Cx g) T t (ug g)
    premisesSound G u ug ((_ , T , t , g) ,- rs) q | [] -: <> | Tt
      with premises G u ug rs | premisesSound G u ug rs
    ... | [] -: <> | Tts = Tt r~ , Tts r~

    typeCheckSound : forall {n}(G : Cx n)(T t : Tm n chk)->
      typeCheck G T t ~ ([] -: <>) ->
      G |- T :> t
    typeCheckSound G T t = typeCheckRecSound G T t (tmRec t)

    synthTypeSound : forall {n}(G : Cx n)(e : Tm n syn)
      (S : Tm n chk) -> synthType G e ~ ([] -: S) ->
      G |- e <: S
    synthTypeSound G e = synthTypeRecSound G e (tmRec e)


  module GASCHECKER (z : Nat) = CHECKER (\ G -> gasRed z) (\ G -> gasRedSound z)

  module PRES
    (betaSound :
      forall {n}{G : Cx n}{t T T' s r R R' : Tm n chk}{rs} ->
        Star _~>_ T T' -> Star _~>_ R R' ->
        elimTy (t :: T) T' s ~ (rs -: R') ->
        contract t T s ~ (tt , r , R) ->
        G |- ! TY :> T ->
        G |- T :> t ->
        All (Judge ((t :: T) $ s) G) rs ->
        G |- ! TY :> R * G |- R :> r)
    -- or something like that
    where

    module _ {n}{T0 T1 t0 t1 : Tm n chk}{rs0 : List (Req t0)}
      (Tr : Star _~>_ T0 T1)
      (tr : t0 => t1)
      where

      open STABLE (JOY tr)

      formIntroLem :
        formIntro T0 t0 ~ (rs0 -: <>) ->
        _ >< \ rs1 ->
          formIntro T1 t1 ~ (rs1 -: <>)
        * ListR (ReqR (\ _ -> Star _~>_) (\ _ -> _=>_) t0 t1) rs0 rs1
      formIntroLem
        with sem' t0 (E0' t0) formIntro'
           | sem' t1 (E0' t1) formIntro'
           | stable {ga0 = E0' _}{ga1 = E0' _} (\ ()) formIntro'
      formIntroLem | .abort | k1 | abort = \ ()
      formIntroLem | .(_ -: k0) | .(_ -: k1) | _-:_ rs {k0} {k1} K
        with k0 (T0 , t0 , hic)
           | k1 (T1 , t1 , hic)
           | K {T0 , t0 , hic} {T1 , t1 , hic} (Tr , tr , <>)
      ...  | .abort | l1 | abort = \ ()
      ...  | .(_ -: _) | .(_ -: _) | rs' -: L = \ { r~ ->
         _ , r~ , (rs ++R rs') }

    module _ {n}(t T T' s r R : Tm n chk) where

      redex : Tm n syn
      redex = (t :: T) $ s

      open STABLE (JOY (parRefl redex))

      contractLem :
        contract t T s ~ (tt , r , R) -> Star _~>_ T T' ->
        _ >< \ rs -> _ >< \ R' ->
        elimTy (t :: T) T' s ~ (rs -: R') * Star _~>_ R R'
      contractLem
        with sem' redex (E0' redex) elimBeta'
           | stable {ga0 = E0' redex}{ga1 = E0' redex}(\ ())
               elimBeta'
      contractLem | .abort | abort = \ ()
      contractLem | (x -: f) | rs0 -: F = \ q TT' -> help (f T) (f T') (F TT') q where
        HTy' = Chk' [] (gdd tt)
           ->' (Syn' [] ->' Chk' [] any)
           *' (Chk' [] any ->' Chk' [] any)
        help : (g g' : Go (Req redex) (Sem' redex HTy')) ->
               GoMo (ReqR (\ _ -> Star _~>_) (\ _ -> _=>_) redex redex)
                    (Stable (\ _ -> Star _~>_) (\ _ -> _=>_) redex redex
                       HTy') g g' -> 
               logOut ([] -:>>= ([] -:>>= ([] -:>>= ([] -:>>= ([] -:>>= ([] -:>>=
                 (((x -:>>= ([] -:>>= g)) >>= (λ k → [] -:>>= k (s , arg hic)))
                   >>=
                (\ (K , k) ->
                  [] -:>>= ([] -:>>= ((([] -:>>= ([] -:>>= k t)) >>=
                     (\ a -> [] -: _,_ a))
                     >>=
                    (\ b ->
                       ([] -:>>= ([] -:>>= K (t :: T))) >>=
                       (\ a -> [] -: b a))))))))))))
                 ~ (tt , r , R)
               -> _ >< \ rs -> _ >< \ R' ->
                ([] -:>>= ([] -:>>= ([] -:>>= ([] -:>>= ([] -:>>= ([] -:>>=
               (((x -:>>= ([] -:>>= g')) >>= (\ k -> [] -:>>= k (s , arg hic)))
                >>=
                (\ (K , k) -> [] -:>>= ([] -:>>=
                    ([] -:>>= ([] -:>>= K (t :: T))))))))))))
                ~ (rs -: R')
                * Star _~>_ R R'
        help (_ -: g) (_ -: g') (y -: G) q
          with g (s , arg hic) | g' (s , arg hic)
             | G {s , arg hic}{s , arg hic} (parRefl s , <>)
        ... | (_ -: (h , i)) | (_ -: (h' , i')) | z -: (H , I)
          with h (t :: T) | h' (t :: T) | H {t :: T} [] | i t
        help (_ -: g) (_ -: g') (y -: G) r~
           | _ -: (h , i) | _ -: (h' , i') | z -: (H , I)
           | .(_ -: _) | .(_ -: _) | _ -: RR' | _ -: _
           = _ , _ , r~ , RR'
               
    module _ {n}{e e' : Tm n syn}{R R' s s' S : Tm n chk}
           {rs : List (Req (e $ s))}
           (er : e => e')
           (Rr : Star _~>_ R R')
           (sr : s => s')
      where

      open STABLE (JOY (er $ sr))

      elimTyLem : 
        elimTy e R s ~ (rs -: S) ->
        
        _ >< \ rs' -> _ >< \ S' ->
          elimTy e' R' s' ~ (rs' -: S')
        * ListR (ReqR (\ _ -> Star _~>_) (\ _ -> _=>_) (e $ s) (e' $ s')) rs rs'
        * Star _~>_ S S' 

      elimTyLem = help
             (sem' (e $ s) (E0' _) elimTy')
             (sem' (e' $ s') (E0' _) elimTy')
             (stable {ga0 = E0' _}{ga1 = E0' _} (\ ()) elimTy')
        where
        help :
          (k0 : Go (Req (e $ s)) (Sem' (e $ s) elimTyTy'))
          (k1 : Go (Req (e' $ s')) (Sem' (e' $ s') elimTyTy')) ->
          GoMo
            (ReqR (\ _ -> Star _~>_) (\ _ -> _=>_) (e $ s) (e' $ s'))
            (Stable (\ _ -> Star _~>_) (\ _ -> _=>_)
              (e $ s) (e' $ s') elimTyTy')
            k0 k1 ->
          (k0 >>= \ k -> k (e , R , s , arg hic)) ~ (rs -: S) ->
          _ >< \ rs' -> _ >< \ S' ->
          (k1 >>= \ k -> k (e' , R' , s' , arg hic)) ~ (rs' -: S')
          * ListR (ReqR (\ _ -> Star _~>_) (\ _ -> _=>_) (e $ s) (e' $ s')) rs rs'
          * Star _~>_ S S'
        help (rs0 -: k0) (rs1 -: k1) (rss -: K)
          with k0 (e , R , s , arg hic)
             | k1 (e' , R' , s' , arg hic)
             | K {e , R , s , arg hic} {e' , R' , s' , arg hic}
                 (parSteps er , Rr , sr , <>)
        help (rs0 -: k0) (rs1 -: k1) (rss -: K)
          | .abort | l1 | abort = \ ()
        help (rs0 -: k0) (rs1 -: k1) (rss -: K)
          | .(_ -: _) | .(_ -: _) | rss' -: Sr = \ { r~ ->
          _ , _ , r~ , (rss ++R rss') , Sr }

    presChk : forall {n}{G G' : Cx n}{T T' t t' : Tm n chk} ->
      G |- T :> t ->
      (forall i -> Star _~>_ (G i) (G' i)) ->
      Star _~>_ T T' ->
      t => t' ->
      G' |- T' :> t'
    presSyn : forall {n}{G G' : Cx n}{e e' : Tm n syn}{S : Tm n chk} ->
      G |- e <: S ->
      (forall i -> Star _~>_ (G i) (G' i)) ->
      e => e' ->
      _ >< \ S' ->
          Star _~>_ S S'
        * G' |- e' <: S'
    presPrem : forall {n ud}{u0 u1 : Tm n ud}{G0 G1 : Cx n}{rs0 rs1} ->
      (forall i -> Star _~>_ (G0 i) (G1 i)) ->
      ListR (ReqR (\ _ -> Star _~>_) (\ _ -> _=>_) u0 u1) rs0 rs1 ->
      All (Judge u0 G0) rs0 ->
      All (Judge u1 G1) rs1

    presPrem G [] <> = <>
    presPrem {n}{ud}{u0}{u1}{G0}{G1}
      {(_ , T0 , t0 , g0) ,- rs0}{(_ , T1 , t1 , g1) ,- rs1}
      G ((r~ , T , t , g) ,- rs) (J , Js) =
      presChk J (help [] _ tt G0 u0 t0 g0 tt G1 u1 t1 g1 G g) T t , presPrem G rs Js
      where
        help : forall p m {ud}
               b0
               (G0 : Cx (n +B p))
               (u0 : Tm (n +B p) ud)
               (t0 : Tm m chk)
               (g0 : Gdd u0 b0 t0)
               b1
               (G1 : Cx (n +B p))
               (u1 : Tm (n +B p) ud)
               (t1 : Tm m chk)
               (g1 : Gdd u1 b1 t1)
               ->
               (forall i -> Star _~>_ (G0 i) (G1 i)) ->
               GDD (\ _ -> Star _~>_) (\ _ -> _=>_) p t0 g0 t1 g1 ->
               forall i -> Star _~>_ ((G0 +Cx g0) i) ((G1 +Cx g1) i)
        help p m .ff G0 u0 .u0 hic .ff G1 u1 .u1 hic G g = G
        help p m .tt G0 .(_ & _) t0 (car g0) .tt G1 .(_ & _) t1 (car g1) G g =
          help p m _ G0 _ t0 g0 _ G1 _ t1 g1 G g
        help p m .tt G0 .(_ & _) t0 (cdr g0) .tt G1 .(_ & _) t1 (cdr g1) G g =
          help p m _ G0 _ t0 g0 _ G1 _ t1 g1 G g
        help p m .tt G0 .(^ _) t0 (bod S0 g0) .tt G1 .(^ _) t1 (bod S1 g1) G (S , g) =
          help _ _ _ (G0 ,^ S0) _ t0 g0 _ (G1 ,^ S1) _ t1 g1 (
            \ { (i -^ .<>) -> star (_^Tm (iota no)) (\ r -> stepTh r (iota no)) (G i)
              ; (i -, .<>) -> star (_^Tm (iota no)) (\ r -> stepTh r (iota no)) S
              })
            g
        help p m .tt G0 .(_ $ _) t0 (arg g0) .tt G1 .(_ $ _) t1 (arg g1) G g =
          help p m _ G0 _ t0 g0 _ G1 _ t1 g1 G g

    presChk (embed J r~) G T (` e)
      with _ , S , J' <- presSyn J G e
         | _ , S' , T' <- confluence S T
      = preSteps T' (embed (postSteps J' S') r~)
    presChk {n} {G0} {G1} {T0} {T1} {.(` (t0 :: T2))} {t1} (embed J r~) G T
      (upsi {t0} {T = T2} t) = help J T where
      help : forall {T0 T1 T2} ->
        G0 |- t0 :: T2 <: T0 ->
        Star _~>_ T0 T1 ->
        G1 |- T1 :> t1
      help (rad _ J) T = presChk J G T t
      help (post J T') T = help J (T' ,- T)
    presChk (intro q Js) G T t
      with rs1 , q' , rs <- formIntroLem T t q
      = intro q' (presPrem G rs Js)
    presChk (pre T0 J) G T t
      with T' , T2 , T3 <- confluence (T0 ,- []) T
      = preSteps T3 (presChk J G T2 t)
    presSyn (post J S0) G e
      with S' , S1 , J' <- presSyn J G e
         | S'' , S2 , S3 <- confluence (S0 ,- []) S1
         = S'' , S2 , postSteps J' S3
    presSyn {G = G0}{G1}{S = S0} (elim {S = R0} {s0} J q2 Js) G
      (beta {t0} {T = T0} q0 t T s q1) = help J []
      where
      help : forall {Q0} ->
             G0 |- t0 :: T0 <: Q0 -> Star _~>_ Q0 R0 ->
             _ >< \ S1 -> Star _~>_ S0 S1 * (G1 |- _ <: S1)
      help (rad J j) R
       with J' <- presChk J G [] T
          | j' <- presChk j G (parSteps T) t
          | rs , X , q3 , Xr <- contractLem t0 T0 R0 s0 _ _ q0 R
          | r~ <- _ < q2 ]~ q3
          | T1 , r0 , r1 <- confluence (parSteps T) R
          | rs' , X' , q4 , RS , XX' <- elimTyLem (t :: T) r1 s q2
          | rs'' , R'' , q5 , RR <- contractLem _ _ _ _ _ _ q1 r0
          | r~ <- _ < q4 ]~ q5
          | Rok , rok <- betaSound r0 RR q4 q1 J' j' (presPrem G RS Js)
          = _ , XX' , postSteps (rad Rok rok) RR
      help (post J x) R = help J (x ,- R)
    presSyn (# .x) G (# x) = _ , G x , # x
    presSyn {S = S0} (elim {e0} {R0} {s0} {rs0} J q js) G (e $ s)
      with R1 , Rr , J' <- presSyn J G e
         | rs1 , S1 , q' , rs , S <- elimTyLem e Rr s q
         = _ , S , elim J' q' (presPrem G rs js)
    presSyn (rad J j) G (t :: T)
      = _
      , T'
      , rad (presChk J G [] T) (presChk j G T' t)
      where T' = parSteps T
