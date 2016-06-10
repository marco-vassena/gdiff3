module Diff.Embedding where

open import Data.DTree hiding ([_])
open import EditScript.Embedding
open import EditScript.Mapping
open import Diff.Safety

open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

-- e ⊢ˢ α ⊏ β means that in e there are two edits f with source ⟨ α ⟩ and g with source ⟨ β ⟩
-- such that e ⊢ f ⊏ g.
data _⊢ˢ_⊏_ {xs ys as bs a b} (e : ES xs ys) (α : View as a) (β : View bs b) : Set₁ where
  source-⊏ : ∀ {cs ds es fs} {v : Val cs ds} {w : Val es fs} 
               {f : ⟨ α ⟩ ~> v} {g : ⟨ β ⟩ ~> w} -> e ⊢ₑ f ⊏ g -> e ⊢ˢ α ⊏ β 

-- Edit script preserve the ordering of nodes in the source object  
diff-⊏ˢ : ∀ {xs ys as bs a b} {α : View as a} {β : View bs b} {x : DList xs} {y : DList ys} {e : ES xs ys} 
        -> Diff x y e -> x ⊢ α ⊏ β -> e ⊢ˢ α ⊏ β
diff-⊏ˢ (Del α p) (here .α q) with noEraseˢ p q
diff-⊏ˢ (Del α p) (here .α q) | source-∈ x = source-⊏ (here (Del α) x)
diff-⊏ˢ (Upd α β p) (here .α q) with noEraseˢ p q
diff-⊏ˢ (Upd α β p) (here .α q) | source-∈ x = source-⊏ (here (Upd α β) x)
diff-⊏ˢ (Ins β p) (here α q) with diff-⊏ˢ p (here α q)
diff-⊏ˢ (Ins β p) (here α q) | source-⊏ x = source-⊏ (there (Ins β) x)
diff-⊏ˢ (Nop p) (here α q) with diff-⊏ˢ p (here α q)
diff-⊏ˢ (Nop p) (here α q) | source-⊏ x = source-⊏ (there Nop x)
diff-⊏ˢ (Del z p) (there q) with diff-⊏ˢ p q
diff-⊏ˢ (Del z p) (there q) | source-⊏ x = source-⊏ (there (Del z) x)
diff-⊏ˢ (Upd α β p) (there q) with diff-⊏ˢ p q
diff-⊏ˢ (Upd α β p) (there q) | source-⊏ x = source-⊏ (there (Upd α β) x)
diff-⊏ˢ (Ins β p) (there q) with diff-⊏ˢ p (there q)
diff-⊏ˢ (Ins β p) (there q) | source-⊏ x = source-⊏ (there (Ins β) x)
diff-⊏ˢ (Nop p) (there q) with diff-⊏ˢ p (there q)
diff-⊏ˢ (Nop p) (there q) | source-⊏ x = source-⊏ (there Nop x)

--------------------------------------------------------------------------------

-- e ⊢ᵗ α ⊏ β means that in e there are two edits f with target ⟨ α ⟩ and g with target ⟨ β ⟩
-- such that e ⊢ f ⊏ g.
data _⊢ᵗ_⊏_ {xs ys as bs a b} (e : ES xs ys) (α : View as a) (β : View bs b) : Set₁ where
  target-⊏ : ∀ {cs ds es fs} {v : Val cs ds} {w : Val es fs} {f : v ~> ⟨ α ⟩} {g : w ~> ⟨ β ⟩} -> 
               e ⊢ₑ f ⊏ g -> e ⊢ᵗ α ⊏ β

infixr 3 _⊢ᵗ_⊏_

-- Edit script preserve the ordering of nodes in the target object  
-- TODO rename o to t
diff-⊏ₒ : ∀ {xs ys as bs a b} {α : View as a} {β : View bs b} {x : DList xs} {y : DList ys} {e : ES xs ys} -> 
            Diff x y e -> y ⊢ α ⊏ β -> e ⊢ᵗ α ⊏ β
diff-⊏ₒ (Del β p) (here α q) with diff-⊏ₒ p (here α q)
diff-⊏ₒ (Del β p) (here α q) | target-⊏ x = target-⊏ (there (Del β) x)
diff-⊏ₒ (Upd α β p) (here .β q) with noEraseₒ p q
diff-⊏ₒ (Upd α β p) (here .β q) | target-∈ x = target-⊏ (here (Upd α β) x)
diff-⊏ₒ (Ins α p) (here .α q) with noEraseₒ p q
diff-⊏ₒ (Ins α p) (here .α q) | target-∈ x = target-⊏ (here (Ins α) x)
diff-⊏ₒ (Nop p) (here α q) with diff-⊏ₒ p (here α q)
diff-⊏ₒ (Nop p) (here α q) | target-⊏ x = target-⊏ (there Nop x)
diff-⊏ₒ (Del α p) (there q) with diff-⊏ₒ p (there q)
diff-⊏ₒ (Del α p) (there q) | target-⊏ x = target-⊏ (there (Del α) x)
diff-⊏ₒ (Upd α β p) (there q) with diff-⊏ₒ p q
diff-⊏ₒ (Upd α β p) (there q) | target-⊏ x = target-⊏ (there (Upd α β) x)
diff-⊏ₒ (Ins α p) (there q) with diff-⊏ₒ p q
diff-⊏ₒ (Ins α p) (there q) | target-⊏ x = target-⊏ (there (Ins α) x)
diff-⊏ₒ (Nop p) (there q) with diff-⊏ₒ p (there q)
diff-⊏ₒ (Nop p) (there q) | target-⊏ x = target-⊏ (there Nop x)

--------------------------------------------------------------------------------
-- Theorems that show that sturctural invariants are preserved by an edit script


-- If ⟪ e ⟫ ⊢ α ⊏ β then e ↦ α ⊏ β, which means that either:  
--   1) α is deleted
--   2) β is deleted
--   3) ∃ γ , φ . e ⊢ₑ ⟨ α ⟩ ~> ⟨ γ ⟩ and e ⊢ₑ ⟨ β ⟩ ~> ⟨ φ ⟩ and ⟦ e ⟧ ⊢ γ ⊏ φ 
preserve-↦ : ∀ {xs ys as bs a b} {e : ES xs ys} {α : View as a} {β : View bs b}
              (p : ⟪ e ⟫ ⊢ α ⊏ β) -> e ↦ α ⊏ β
preserve-↦ {e = e} p with diff-⊏ˢ (mkDiff e) p
preserve-↦ p | source-⊏ {f = Del α} x = Del₁ (Del α (⊏ₑ-∈₁ x))
preserve-↦ p | source-⊏ {f = Upd _ _} {Del β} x = Del₂ (Del β (⊏ₑ-∈₂ x))
preserve-↦ p | source-⊏ {f = Upd α γ} {Upd β φ} x = Map₂ (Upd α γ (⊏ₑ-∈₁ x)) (Upd β φ (⊏ₑ-∈₂ x)) (⟦⟧-⊏ (Upd α γ) (Upd β φ) x)

-- If ⟦ e ⟧ ⊢ α ⊏ β then e ↤ α ⊏ β, which means that either:  
--   1) α is inserted
--   2) β is inserted
--   3) ∃ γ , φ . e ⊢ₑ ⟨ γ ⟩ ~> ⟨ α ⟩ and e ⊢ₑ ⟨ φ ⟩ ~> ⟨ β ⟩ and ⟪ e ⟫ ⊢ γ ⊏ φ 
preserve-↤ : ∀ {xs ys as bs a b} {e : ES xs ys} {α : View as a} {β : View bs b}
              (p : ⟦ e ⟧ ⊢ α ⊏ β) -> e ↤ α ⊏ β 
preserve-↤ {e = e} p with diff-⊏ₒ (mkDiff e) p
preserve-↤ p | target-⊏ {f = Ins α} x = Ins₁ (Ins α (⊏ₑ-∈₁ x))
preserve-↤ p | target-⊏ {f = Upd _ _} {Ins β} x = Ins₂ (Ins β (⊏ₑ-∈₂ x))
preserve-↤ p | target-⊏ {f = Upd α γ} {Upd β φ} x = Map₂ (Upd α γ (⊏ₑ-∈₁ x)) (Upd β φ (⊏ₑ-∈₂ x)) (⟪⟫-⊏ (Upd α γ) (Upd β φ) x) 

--------------------------------------------------------------------------------
-- Corollaries: Diff preserves structural invariants

Diff↦ :  ∀ {xs ys as bs a b} {x : DList xs} {y : DList ys} {e : ES xs ys} {α : View as a} {β : View bs b}
            -> Diff x y e -> x ⊢ α ⊏ β -> e ↦ α ⊏ β
Diff↦ d p rewrite mkDiff⟪ d ⟫ = preserve-↦ p

Diff↤ :  ∀ {xs ys as bs a b} {x : DList xs} {y : DList ys} {e : ES xs ys} {α : View as a} {β : View bs b}
            -> Diff x y e -> y ⊢ α ⊏ β -> e ↤ α ⊏ β
Diff↤ d p rewrite mkDiff⟦ d ⟧ = preserve-↤ p
