module Kipling where

open import Tuple
open import Thin
open import Tm
open import Meta
open import Red
open import Ty

KiplingFormIntro : [] :- FormIntro'
KiplingFormIntro = unc' (mat'
  (\ { TY -> mat'
         (\ { A0 -> aye' ; A1 -> aye' ; A2 -> aye' ; _ -> naw' })
         (atom' \ { PI -> cons' (chk' (! TY) (\'{-S-}
                                abst' (?'{-S-} (none SU)) (chk' (! TY) (\'{-T-}
                                aye'))))
                  ; SG -> cons' (chk' (! TY) (\'{-S-}
                                abst' (?'{-S-} (none SU)) (chk' (! TY) (\'{-T-}
                                aye'))))
                  ; _  -> naw' })
         naw'
     ; A1 -> atom' (yer A0 aye')
     ; A2 -> atom' \ { A0 -> aye' ; A1 -> aye' ; _ -> naw' }
     ; _ -> naw' })
  (atom' \ { PI -> cons' (\'{-S-} abst' (?'{-S-} (none SU)) (\'{-T-}
               abst' (?'{-S-} (none SU NO)) (chk' (?'{-T-} (none SU)) (\'{-t-}
               aye'))))
           ; SG -> cons' (\'{-S-} abst' (?'{-S-} (none SU)) (\'{-T-}
              cons' (chk' (?'{-S-} (none SU NO)) (\'{-s-}
                     chk' (sub' ([] su) (?'{-T-} (none SU NO)) (aye' ,' ((?'{-s-} (none SU)) :: (?'{-S-} (none SU NO NO))))) (\'{-t-}
                     aye')))))
           ; _ -> naw' })
  naw')

KiplingElimBeta : [] :- ElimBeta'
KiplingElimBeta = mat'
  (\ { A0 -> chk' (! TY) (\'{-P-}             -- any type you ask for
             (  (\' (?'{-P-} (none SU NO)))   -- 0-elim gives you but
             ,' (\' naw')                     -- it does not compute
             ))
     ; A2 -> cons' (mat'
               (yer TY (cons' (chk' (! TY) (\'{-F-} 
                               (chk' (! TY) (\'{-T-} 
                               (  (\' (! TY))    -- Big If makes types
                               ,' atom' \ { A0 -> ?'{-F-} (none SU NO)
                                          ; A1 -> ?'{-T-} (none SU)
                                          ; _ -> naw' }
                               )))))))
               naw'
               ({-b-} ! A2 ,' (chk' (! TY) (\'{-P-} 
                    cons' (chk' (sub' ([] su) (?'{-P-} (none SU)) (aye' ,' (! A0 :: ! A2))) (\'{-f-} 
                           (chk' (sub' ([] su) (?'{-P-} (none SU NO)) (aye' ,' (! A1 :: ! A2))) (\'{-t-} 
                             (  (\'{-e-} sub' ([] su) (?'{-P-} (none SU NO NO NO)) (aye' ,' (?'{-e-} (none SU))))
                             ,' atom' \ { A0 -> ?'{-f-} (none SU NO)
                                        ; A1 -> ?'{-t-} (none SU)
                                        ; _ -> naw' }
                             ))) ))))))
     ; _ -> naw' })
  (atom' \ { PI -> cons' (\'{-S-} (abst' (?'{-S-} (none SU)) (\'{-T-} (
                       (chk' (?'{-S-} (none SU NO)) (\'{-s-} 
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

open RULES KiplingFormIntro KiplingElimBeta

open GASCHECKER

test0 : Go Zero One
test0 = typeCheck [] {[]} (\ ()) (! TY) (! PI & ! A2 & ^ ! A2)

test1 : Go Zero One
test1 = typeCheck [] {[]} (\ ()) (! PI & ! A2 & ^ ! A2)
  (^ ` # (none su) $ ((^ ! A2) & ! A1 & ! A0))
