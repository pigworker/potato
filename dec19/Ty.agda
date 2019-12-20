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

    typeCheckRec G T t tr with redTy G T
    typeCheckRec G T t (can _ tg) | T' with formIntro T t
    typeCheckRec G T t (can _ tg) | T' | abort = abort
    typeCheckRec G T t (can _ tg) | T' | rs -: <> = rec rs where
      rec : List (Req t) -> Go Zero One
      rec []                      = [] -: <>
      rec ((_ , T , t , g) ,- rs) = 
        typeCheckRec (G +Cx g) T t (tg g) >>= \ _ ->
        rec rs
    typeCheckRec G T (` e) (emb er) | T' = 
      synthTypeRec G e er >>= \ S ->
      eqTest S T'

    synthTypeRec G .(# x)   (var x)     = [] -: redTy G (G x)
    synthTypeRec G (e $ s)  (eli er sg) with synthTypeRec G e er
    ... | abort = abort
    ... | [] -: S with elimTy e S s
    ... | abort = abort
    ... | rs -: S' = rec rs >>= \ _ -> [] -: redTy G S'
      where
      rec : List (Req (e $ s)) -> Go Zero One
      rec []                      = [] -: <>
      rec ((_ , T , t , g) ,- rs) = 
        typeCheckRec (G +Cx g) T t (sg g) >>= \ _ ->
        rec rs
    synthTypeRec G (t :: T) (rad tr Tr) = 
      typeCheckRec G (! TY) T Tr >>= \ _ ->
      typeCheckRec G T t tr >>= \ _ ->
      [] -: redTy G T
    
    typeCheck : forall {n} -> Cx n -> Tm n chk -> Tm n chk -> Go Zero One
    typeCheck G T t = typeCheckRec G T t (tmRec t)
    synthType : forall {n} -> Cx n -> Tm n syn -> Go Zero (Tm n chk)
    synthType G e = synthTypeRec G e (tmRec e)
