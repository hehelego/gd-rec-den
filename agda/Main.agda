{-
A nearly complete guarded cubical agda formalization of chapter 2 of Marco Paviotti's PhD dissertation.

All proofs are closed with no axiom dependency.

agda version: 2.8.0
cubical agda standard library version: 0.9
agda flags: --cubical --guarded --guardedness -WnoUnsupportedIndexedMatch

@article{paviotti2015model,
  title={A model of PCF in guarded type theory},
  author={Paviotti, Marco and M{\o}gelberg, Rasmus Ejlers and Birkedal, Lars},
  journal={Electronic Notes in Theoretical Computer Science},
  volume={319},
  pages={333--349},
  year={2015},
  publisher={Elsevier}
}

-}
module Main where

{- Syntax and static semantics of PCF, the object language
   Intrinsically typed de Bruijn Representation
-}
module Syntax-and-Statics where
  open import Term public

open Syntax-and-Statics


{- Renaming and Substitution algebra
   Substitution and renaming maps are composable
-}
module Substitution-Infrastructure where
  open import Renaming.Base public
  open import Renaming.Properties public

  open import Substitution.Base public
  open import Substitution.Properties public

open Substitution-Infrastructure


{- Operational semantics of the object language
   Only small-step operational semantics is formalized

   The step-indexing big-step operational semantics with value predicate defined in the _A Model of PCF in Guarded Type Theory_ paper appears to be non-wellfounded and cannot be easily fixed.
-}
module Operational-Semantics where
  open import OpSem.SmallStep public
  open import OpSem.SProperties public

open Operational-Semantics


{- Free later algebre domain
   Interpretation of types and context
   Denotation of (well-typed) terms

   Soundness of the denotation semantics with respect to the small-step operational semantics.
   Proof strategy: 
   (1) unfold-free reduction preserves the denotation while unfold of the fixed point combinator generates a delay credit
   (2) induction on multi-step reduction

   Computational Adequacy of the denotation semantics with respect to the small-step operational semantics
   Proof strategy:
   (1) a logical relation linking closed-terms and the semantics domain
   (2) subject reduction lemmas
   (3) subject expansion lemmas
   (4) typing compatibility and fundamental lemma
   (5) use guarded recursion to eliminate the witness of a term and a semantics domain object to construct a multi-step reduction
-}
module Denotational-Semantics where
  open import Denotation.LaterAlgebra public
  open import Denotation.Interpretation public
  open import Denotation.RenSub public
  open import Denotation.Soundness public
  open import Denotation.Adequacy public

open Denotational-Semantics
