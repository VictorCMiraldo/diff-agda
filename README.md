Generic Diffing Formalization in Agda
=====================================

This repository contains the Agda formalization
of our diff algorithm.

Directory structure is as follows:

* **Universe/** , universe specific definitions.
    * **Syntax.lagad** , Defines the syntax of types and their elements.
    * **Equality.lagda** , gives us a notion of generic element equality.
    * **Map.lagda** , gives us a notion of generic mapping, in different flavors.
    * **MuUtils.lagda** , provides some utilities for working with fixed points.
* **Utils/** , Utility modules.
    * **Monads.agda** , easier to use than the Monads in agda's std-lib.
    * **Propositions.agda** , a bunch of propositions for rewriting things here and there.
* **Diff.lagda** , The actual diff algorithm and correspondent apply function.
* **DiffCorrect.agda** , Correctness proof of the above. WARNING: typecheck takes 20 minutes.
