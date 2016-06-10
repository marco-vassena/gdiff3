module EditScript.Mapping where

open import EditScript.Core public
open import Data.DTree

open import Data.List

-- e ⊢ₑ v ~> w is the proof that some value v is mapped to w in e.
data _⊢ₑ_~>_  {xs ys} (e : ES xs ys) : ∀ {as bs cs ds} -> Val as bs -> Val cs ds -> Set₁ where
  Upd : ∀ {as bs a} (α : View as a) (β : View bs a) -> Upd α β ∈ₑ e -> e ⊢ₑ ⟨ α ⟩ ~> ⟨ β ⟩ 
  Del : ∀ {as a} (α : View as a) -> Del α ∈ₑ e -> e ⊢ₑ ⟨ α ⟩ ~> ⊥
  Ins : ∀ {as a} (α : View as a) -> Ins α ∈ₑ e -> e ⊢ₑ ⊥ ~> ⟨ α ⟩
  Nop : Nop ∈ₑ e -> e ⊢ₑ ⊥ ~> ⊥

infixr 3 _⊢ₑ_~>_

-- Auxiliary function that appends an additional edit to a proof e ⊢ₑ v ~> w
there~> : ∀ {xs ys as bs cs ds es fs gs hs} {v₁ : Val es fs} {v₂ : Val gs hs} 
            {v : Val as bs} {w : Val cs ds} (c : v ~> w) {e : ES (as ++ xs) (cs ++ ys)} -> 
            e ⊢ₑ v₁ ~> v₂ -> c ∷ e ⊢ₑ v₁ ~> v₂
there~> c (Upd α β x) = Upd α β (there c x)
there~> c (Del α x) = Del α (there c x)
there~> c (Ins α x) = Ins α (there c x)
there~> c (Nop x) = Nop (there c x)

--------------------------------------------------------------------------------
-- Structural invariants

-- Proof that edit scripts preserve the ⊏ relation with respect to the target object
data _↦_⊏_ {xs ys as a bs b} (e : ES xs ys) (α : View as a) (β : View bs b) : Set₁ where
  Del₁ : e ⊢ₑ ⟨ α ⟩ ~> ⊥ -> e ↦ α ⊏ β
  Del₂ : e ⊢ₑ ⟨ β ⟩ ~> ⊥ -> e ↦ α ⊏ β
  Map₂ : ∀ {cs ds c d} {γ : View cs c} {φ : View ds d} 
             -> e ⊢ₑ ⟨ α ⟩ ~> ⟨ γ ⟩ -> e ⊢ₑ ⟨ β ⟩ ~> ⟨ φ ⟩ -> ⟦ e ⟧ ⊢ γ ⊏ φ -> e ↦ α ⊏ β
 
-- The symmetric statement
-- Proof that edit scripts preserve the ⊏ relation with respect to the source object
data _↤_⊏_ {xs ys as a bs b} (e : ES xs ys) (α : View as a) (β : View bs b) : Set₁ where
  Ins₁ : e ⊢ₑ ⊥ ~> ⟨ α ⟩ -> e ↤ α ⊏ β
  Ins₂ : e ⊢ₑ ⊥ ~> ⟨ β ⟩ -> e ↤ α ⊏ β
  Map₂ : ∀ {cs ds c d} {γ : View cs c} {φ : View ds d} 
             -> e ⊢ₑ ⟨ γ ⟩ ~> ⟨ α ⟩ -> e ⊢ₑ ⟨ φ ⟩ ~> ⟨ β ⟩ -> ⟪ e ⟫ ⊢ γ ⊏ φ -> e ↤ α ⊏ β
