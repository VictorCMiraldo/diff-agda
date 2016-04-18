open import Prelude
open import Diffing.Universe
open import Diffing.Universe.Lab

open import Diffing.Patches.Diff.D
open import Diffing.Patches.Diff.Cost
open import Diffing.Patches.Diff top-down-cost

module Diffing.Patches.Lab where

  δ : {n i j : ℕ}{t : T n}{ty : U (suc n)}
    → Dμ ⊥ₚ t ty i j → List ((ℕ × ℕ) × (ℕ × ℕ))
  δ (Dμ-A () p)
  δ Dμ-end = []
  δ {i = .(suc pi)} {.(suc pj)} (Dμ-dwn {i = pi} {pj} a b p) 
    = ((suc pi , suc pj) , pi , pj) ∷ δ p
  δ {i = .(suc pi)} {.pj}       (Dμ-del {i = pi} {pj} a p) 
    = ((suc pi , pj) , pi , pj) ∷ δ p
  δ {i = .pi} {.(suc pj)}       (Dμ-ins {i = pi} {pj} a p) 
    = ((pi , suc pj) , pi , pj) ∷ δ p

  module LIST-test where
    l1 l2 l3 : ElU LIST (BOOL ∷ [])

    l1 = CONS TT NIL

    l2 = CONS FF (CONS TT NIL)

    l3 = CONS FF NIL

    d12 d13 : D ⊥ₚ (BOOL ∷ []) LIST
    d12 = gdiff l1 l2
    d13 = gdiff l1 l3


  module FS-test where

    t1 t2 t3 : ElU FS (BOOL ∷ [])
    t1 = FS2 TT (FS2 FF FS0 FS0) FS0

    t2 = FS2 TT (FS1 TT (FS2 FF FS0 FS0)) FS0

    t3 = FS1 FF (FS2 TT FS0 (FS2 FF FS0 FS0))

    d12 d13 d12-nf d13-nf : D ⊥ₚ (BOOL ∷ []) FS
    d12 = gdiff t1 t2
    d13 = gdiff t1 t3

    d12-nf = D-mu
      (Dμ-dwn {i = 0} {0} 
        (inr (inl (_,_ (pop (top (inl (unit  )))) 
                  (_,_ (top (unit  )) (top (unit  )))))) 
        (inr (inl (_,_ (pop (top (inl (unit  )))) 
                  (_,_ (top (unit  )) (top (unit  ))))))
      (Dμ-ins {i = 2} {1} 
        (inr (inr (_,_ (pop (top (inl (unit  )))) (top (unit  ))))) 
      (Dμ-dwn {i = 1} {1} 
        (inr (inl (_,_ (pop (top (inr (unit  )))) 
                  (_,_ (top (unit  )) (top (unit  )))))) 
        (inr (inl (_,_ (pop (top (inr (unit  )))) 
                  (_,_ (top (unit  )) (top (unit  )))))) 
      (Dμ-dwn {i = 2} {2} (inl (unit )) (inl (unit )) 
      (Dμ-dwn {i = 1} {1} (inl (unit )) (inl (unit )) 
      (Dμ-dwn {i = 0} {0} (inl (unit )) (inl (unit ))
      Dμ-end))))))
    

    d13-1 : Dμ ⊥ₚ (BOOL ∷ []) FORKSEQ-sop 1 1
    d13-2 : Dμ ⊥ₚ (BOOL ∷ []) FORKSEQ-sop 1 1
    d13-3 : Dμ ⊥ₚ (BOOL ∷ []) FORKSEQ-sop 2 2
    d13-4 : Dμ ⊥ₚ (BOOL ∷ []) FORKSEQ-sop 2 1
    d13-5 : Dμ ⊥ₚ (BOOL ∷ []) FORKSEQ-sop 3 2
    d13-6 : Dμ ⊥ₚ (BOOL ∷ []) FORKSEQ-sop 2 2
    d13-7 : Dμ ⊥ₚ (BOOL ∷ []) FORKSEQ-sop 1 1

    d13-1 = Dμ-ins {i = 1} {0} (inr (inr (pop (top (inr unit)) , top unit)))
              d13-2
    d13-2 = Dμ-dwn {i = 0} {0}
              (inr (inl (pop (top (inl unit)) , top unit , top unit)))
              (inr (inl (pop (top (inl unit)) , top unit , top unit))) d13-3
    d13-3 = Dμ-ins {i = 2} {1} (inl unit) d13-4
    d13-4 = Dμ-dwn {i = 1} {0}
              (inr (inl (pop (top (inr unit)) , top unit , top unit)))
              (inr (inl (pop (top (inr unit)) , top unit , top unit))) d13-5
    d13-5 = Dμ-del {i = 2} {2} (inl unit) d13-6
    d13-6 = Dμ-dwn {i = 1} {1} (inl unit) (inl unit) d13-7
    d13-7 = Dμ-dwn {i = 0} {0} (inl unit) (inl unit) Dμ-end

    d13-nf = D-mu 
      (Dμ-ins {i = 1} {0} (inr (inr (_,_ (pop (top (inr (unit )))) (top (unit )))))
      (Dμ-dwn {i = 0} {0} 
             (inr (inl (_,_ 
               (pop (top (inl (unit )))) 
               (_,_ (top (unit ))
                    (top (unit )))
             ))) 
             (inr (inl (_,_ 
               (pop (top (inl (unit  ))))
               (_,_ (top (unit ))
                    (top (unit )))
             )))
      (Dμ-ins {i = 2} {1} (inl (unit ))
      (Dμ-dwn {i = 1} {0} 
              (inr (inl (_,_ 
                   (pop (top (inr (unit ))))
                   (_,_ (top (unit ))
                        (top (unit )))
              )))
              (inr (inl (_,_ 
                   (pop (top (inr (unit )))) 
                   (_,_ (top (unit )) 
                        (top (unit )))
              )))
      (Dμ-del {i = 2} {2} (inl (unit ))
      (Dμ-dwn {i = 1} {1}
              (inl (unit )) 
              (inl (unit ))
      (Dμ-dwn {i = 0} {0} (inl (unit ))
              (inl (unit )) 
      Dμ-end)))))))

    
    both : D ⊥ₚ (BOOL ∷ []) FS × D ⊥ₚ (BOOL ∷ []) FS
    both = d12 , d13

    


  module RT-test where

    rt1 rt2 rt3 : ElU RTREE (BOOL ∷ [])

    rt1 = RT TT (CONS (RT-leaf TT) (CONS (RT-leaf TT) (CONS (RT-leaf TT) NIL)))
    rt3 = RT FF NIL
    rt2 = RT TT (CONS (RT-leaf TT) NIL)

    d12 d13 d12-nf d13-nf : D ⊥ₚ (BOOL ∷ []) RTREE
    d12 = gdiff rt1 rt2
    d13 = gdiff rt1 rt3

    d13-nf = D-mu
      (Dμ-del {i = 0} {1}
       (pop (top (inl unit)) ,
        red
        (pop
         (mu
          (inr
           (pop (top unit) ,
            top
            (mu
             (inr
              (pop (top unit) ,
               top (mu (inr (pop (top unit) , top (mu (inl unit)))))))))))))
       (Dμ-del {i = 2} {1} (pop (top (inl unit)) , red (pop (mu (inl unit))))
        (Dμ-del {i = 1} {1} (pop (top (inl unit)) , red (pop (mu (inl unit))))
         (Dμ-dwn {i = 0} {0} 
           (pop (top TT) , red (pop (mu (inl unit))))
           (pop (top FF) , red (pop (mu (inl unit)))) 
         Dμ-end))))

    d12-nf = D-mu
      (Dμ-dwn {i = 0} {0}
       (pop (top (inl unit)) ,
        red
        (pop
         (mu
          (inr
           (pop (top unit) ,
            top
            (mu
             (inr
              (pop (top unit) ,
               top (mu (inr (pop (top unit) , top (mu (inl unit)))))))))))))
       (pop (top (inl unit)) ,
        red (pop (mu (inr (pop (top unit) , top (mu (inl unit)))))))
       (Dμ-del {i = 2} {1} (pop (top (inl unit)) , red (pop (mu (inl unit))))
        (Dμ-del {i = 1} {1} (pop (top (inl unit)) , red (pop (mu (inl unit))))
         (Dμ-dwn {i = 0} {0} 
                 (pop (top (inl unit)) , red (pop (mu (inl unit))))
                 (pop (top (inl unit)) , red (pop (mu (inl unit)))) 
        Dμ-end))))
