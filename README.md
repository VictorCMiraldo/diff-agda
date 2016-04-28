Generic Diffing Formalization in Agda
=====================================

MASTER2:
--------

  We're starting from scratch here.
  Although we managed to encode our linear diff
  in a type safe fashion, the indices didn't let us calculate
  interesting things with it. The latest development
  on that is in iss4NoFinRedundant branch.
  
  Instead of doing things linearly, we can also
  change the fix-point operator. In the lines of
  
  ```haskell
  data Color (f :: * -> *)
    = Cpy (f (Color f))
    | Add (Ctx f) (Color f)
    | Rm  (Ctx f) (Color f)
  
  Patch (Fix f) = Color (Patch f)
  ```
  
  Where *Ctx f* represents the derivative of *f x* on *x*;
  or, the type of contexts of f with one hole.
