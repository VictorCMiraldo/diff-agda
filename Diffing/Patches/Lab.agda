open import Prelude
open import Diffing.Universe
open import Diffing.Universe.Lab

open import Diffing.Patches.Diff.D
open import Diffing.Patches.Diff.Cost
open import Diffing.Patches.Diff top-down-cost

module Diffing.Patches.Lab where

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
