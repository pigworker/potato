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
  (formIntro' : forall {G} -> G :- FormIntro')
  (elimBeta'  : forall {G} -> G :- ElimBeta')
  where
  open RED elimBeta'

  formIntro : forall {n}(T : Tm n chk)(t : Tm n chk) -> Go (Req t) One
  formIntro T t =
    sem' t (E0' _) formIntro' >>= \ k ->
    k (T , t , hic)

  elimTy' : [] :- Syn' [] *' Chk' [] any *' Chk' [] (gdd tt)
        ->' Chk' [] any
  elimTy' =
    unc' (\'{-e-} unc' (\'{-S-} (\'{-s-} (
    unc' (\'{-R-} (\'{-r-} ((?'{-R-} (none SU NO)) $' (?'{-e-} (none SU NO NO NO NO)))))
    $' ((elimBeta' $' (?'{-S-} (none SU NO)))
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

    preSteps : forall {n}{G : Cx n}{T T' t} ->
      Star _~>_ T T' -> G |- T' :> t -> G |- T :> t
    preSteps [] Tt = Tt
    preSteps (r ,- rs) Tt = pre r (preSteps rs Tt)

    postSteps : forall {n}{G : Cx n}{e S S'} ->
      G |- e <: S -> Star _~>_ S S' -> G |- e <: S'
    postSteps eS [] = eS
    postSteps eS (r ,- rs) = postSteps (post eS r) rs

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
