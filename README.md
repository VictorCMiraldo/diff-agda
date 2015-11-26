Generic Diffing Formalization in Agda
=====================================

ISSUE 4: changelog
------------------
  1. Conflicts are now indexed by a datatype. This allows a usefull
     monadic-like multiplication operation (D (D 0) t ty) -> D 0 t ty
     where 0 represents (const (const Void)).
  2. Obviously, this introduces even more theoretical questions...
  
  

This repository contains the Agda formalization
of our diff algorithm.

Agda code is inside the *Diffing* folder; Directory structure is as follows:

* **Patches/** , Everything related to patches.
    * **Diff/** , Properties and specifics of diffs.
        * **Correctness.agda** , correctness proof.
        * **Functor.agda** , functorial aspects.
    * **Diff.lagda** , The actual diff algorithm and correspondent apply function.
    * **Residual/**
        * **Symmetry.lagda** , residuals are symmetric modulo some operation.
        * **SymmetryConflict.lagda** , proves that this operation does NOT 
                                       introduce any new conflicts.
    * **Residual.lagda** , Defines the notion of a residual over patches.
    * **Conflicts/** , Conflict solvers
        * **Grow.lagda** ,  Solving some grow conflicts automatically.
    * **Conflicts.lagda** , Definition of conflicts
    * **Merging/** , Merging specific properties.
        * **Grow.lagda** , Proves merging of disjoint patches is ok.
    * **Overlap.lagda** , defines a notion of disjoint patches
* **Universe/** , universe specific definitions.
    * **Syntax.lagad** , Defines the syntax of types and their elements.
    * **Equality.lagda** , gives us a notion of generic element equality.
    * **Map.lagda** , gives us a notion of generic mapping, in different flavors.
    * **MuUtils.lagda** , provides some utilities for working with fixed points.
* **Utils/** , Utility modules.
    * **Monads.agda** , easier to use than the Monads in agda's std-lib.
    * **Propositions.agda** , a bunch of propositions for rewriting things here and there.
