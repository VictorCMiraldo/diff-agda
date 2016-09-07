Generic Diffing Formalization in Agda
=====================================

This repo is divided in 4 main branches, which encode
four different encodings of the *D* datatype.

The goal is to have type-safe patches. For non-recursive types
that is trivial to accomplish. Fixpoints introduce a problem.

We found two ways of handling fixpoints, one is linearly, the other is
following its branching structure.

# Linear

## linearUntyped

Here, we handle fixpoints in a "serialized" fashion.
Take the fixpoint of a functor `Fix F`, and functions `hd : Fix F -> F 1`
and `ch : Fix F -> [Fix F]`, we can serialize any `Fix F` as:

`serialize x = hd x : concat (map serialize (ch x))`

This gives a list of constructors as seen in a pre-order traversal of 
a value of type `Fix F`.

Patches over fixpoints are then just patches over lists.

Deserialization is inherently partial in this approach, as we can never be
sure we have the right amount of **ch**ildren.

Since our patches are type-unsafe, we resort to a WF (Well-formed) predicate
and use the type `\Sigma WF Patch` to rule out pathological patches.

## linearTyped

We can annotate the patches with two **Nat** indexes, hence, a patch `p : Dmu m n`
isa patch that expects a vector of `m` values and returns a vector of `n` fixpoints.

We can have a total `apply` function here, but defining residuals is extremely complicated.
Not to mention we have to constantly fight Agda to rewrite these indexes correctly.

# Branching

Another option is to resort to derivatives of datatypes
and follow the functor's branching structure.

Take the following type as the patches for `Fix F`:

`Gix F = Mod (F 1) [Gix F]`
`      | Add (Ctx F) (Gix F)`
`      | Del (Ctx F) (Gix F)`

The one-hole contexts (derivatives of F) provide a nice way to make sure
we have only one place to keep diffing after inserting or deleting, the `Mod`ify
constructor, however, has a list of recursive children. If this list does **not**
contain the correct number of children, we have to fail. (this is encoded in the **treeUntyped** branch).

We can always substitute that list for a vector with the correct length,
and we gain type-safe patches again, this is done in **treeTyped**. 
Nevertheless, we still have to fight the typechecker for indicies rewriting here.
