module Diff3.Embedding where

open import Data.DTree hiding ([_])
open import EditScript.Embedding
open import EditScript.Mapping
open import Diff.Embedding
open import Diff.Safety
open import Diff3.Safety

open import Data.List
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Data.Empty using (⊥-elim)

-- Successful merges are order preserving with respect to edits that perform changes.
-- This restriction is needed because the semantics of the merger may overwrite
-- identity edits. The merged edit script does not actually need to be well-typed,
-- but just conflictless, however that would require to redefine  _⊢ₑ_⊏_ for ES₃.
diff3-⊏₁ : ∀ {as bs cs ds es fs gs hs xs ys zs ws} {u : Val as bs} {v : Val cs ds} {w : Val es fs} {z : Val gs hs}
            {f : u ~> v} {g : w ~> z} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} -> 
            {{c₁ : Change f}} {{c₂ : Change g}} -> e₁ ⊢ₑ f ⊏ g -> Merged₃ e₁ e₂ e₃ -> e₃ ⊢ₑ f ⊏ g
diff3-⊏₁ {{c₁ = IsChange v≠w}} (here f o) (cons (Id₁ .f g) q) = ⊥-elim (v≠w refl)
diff3-⊏₁ (here f o) (cons (Id₂ .f g) q) = here f (noBackOutChangesMerged₁ q o)
diff3-⊏₁ (here f o) (cons (Idem .f) q) = here f (noBackOutChangesMerged₁ q o)
diff3-⊏₁ (there a p) (cons m q) = there _ (diff3-⊏₁ p q)

-- Similar result for changes from the second edit script.
diff3-⊏₂ : ∀ {as bs cs ds es fs gs hs xs ys zs ws} {u : Val as bs} {v : Val cs ds} {w : Val es fs} {z : Val gs hs}
            {f : u ~> v} {g : w ~> z} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} -> 
            {{c₁ : Change f}} {{c₂ : Change g}} -> e₂ ⊢ₑ f ⊏ g -> Merged₃ e₁ e₂ e₃ -> e₃ ⊢ₑ f ⊏ g
diff3-⊏₂ p d = diff3-⊏₁ p (Merged₃-sym d)

--------------------------------------------------------------------------------
-- Corollaries: Merged₃ preserves structural invariants.

Merged₃↦ : ∀ {xs ys zs ws as bs a b} {x : DList xs} {y : DList ys} {z : DList zs}
           {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} {α : View as a} {β : View bs b} ->
           Diff x y e₁ -> Diff x z e₂ -> Merged₃ e₁ e₂ e₃ -> x ⊢ α ⊏ β -> e₃ ↦ α ⊏ β
Merged₃↦ {e₃ = e₃} d₁ d₂ d₃ p rewrite
  trans mkDiff⟪ d₁ ⟫ Merged₃⟪ d₃ ⟫ = Diff↦ (mkDiff e₃) p

-- Since e₃ is maximal, it includes all the changes from e₁ and e₂ therefore e₃ ↤ α ⊏ β 
-- holds as the inserts cases cover when α and β comes from e₁ or e₂. 
Merged₃↤ : ∀ {xs ys zs ws as bs a b} {x : DList xs} {y : DList ys} {z : DList zs}
           {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} {α : View as a} {β : View bs b} ->
           Diff x y e₁ -> Diff x z e₂ -> Merged₃ e₁ e₂ e₃ -> ⟦ e₃ ⟧ ⊢ α ⊏ β -> e₃ ↤ α ⊏ β 
Merged₃↤ {e₃ = e₃} d₁ d₂ d₃ p = Diff↤ (mkDiff e₃) p
