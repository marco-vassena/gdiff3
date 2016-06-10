-- This module proves some structural invariants between edit scripts
-- and their corresponding source and target objects.
-- Note that these properties follow from the definition of ES
-- and the source and target values and not from the diff algorithm 
-- used to generate the script.

module EditScript.Embedding where

open import EditScript.Core public
open import EditScript.Safety
open import Data.DTree

open import Data.List
open import Data.Product

⟦⟧-lemma : ∀ {{ys}} {{zs}} {as bs a b xs} {α : View as a} {β : View bs b} (e : ES xs (ys ++ zs))
              -> ⟦ e ⟧ ⊢ α ⊏ β ->
             let ds₁ , ds₂ = dsplit ⟦ e ⟧ in ds₁ +++ ds₂ ⊢ α ⊏ β
⟦⟧-lemma e q rewrite dsplit-lemma ⟦ e ⟧ = q

-- The ⊏ relation for edits is preserved in the target object
⟦⟧-⊏ : ∀ {as bs cs ds es fs a b xs ys} {e : ES xs ys} {α : View as a} {β : View bs b} {v : Val cs ds} {w : Val es fs}
              (f : v ~> ⟨ α ⟩) (g : w ~> ⟨ β ⟩) 
              -> e ⊢ₑ f ⊏ g -> ⟦ e ⟧ ⊢ α ⊏ β
⟦⟧-⊏ (Ins α) g (here .(Ins α) o) = here α (∈-dsplit _ (∈-⟦⟧ o))
⟦⟧-⊏ (Upd α β) g (here .(Upd α β) o) = here β (∈-dsplit _ (∈-⟦⟧ o))
⟦⟧-⊏ f g (there {e = e} (Ins α) p) = there (⟦⟧-lemma e (⟦⟧-⊏ f g p))
⟦⟧-⊏ f g (there (Del α) p) = ⟦⟧-⊏ f g p
⟦⟧-⊏ f g (there {e = e} (Upd α β) p) = there (⟦⟧-lemma e (⟦⟧-⊏ f g p))
⟦⟧-⊏ f g (there Nop p) = ⟦⟧-⊏ f g p

--------------------------------------------------------------------------------
-- Similar lemmas for ⟪⟫

⟪⟫-lemma : ∀ {{xs}} {{ys}} {as bs a b zs} {α : View as a} {β : View bs b} (e : ES (xs ++ ys) zs)
              -> ⟪ e ⟫ ⊢ α ⊏ β ->
             let ds₁ , ds₂ = dsplit ⟪ e ⟫ in ds₁ +++ ds₂ ⊢ α ⊏ β
⟪⟫-lemma e q rewrite dsplit-lemma ⟪ e ⟫ = q

-- The ⊏ relation for edits is preserved in the source object
⟪⟫-⊏ : ∀ {as bs cs ds es fs a b xs ys} {e : ES xs ys} {α : View as a} {β : View bs b} {v : Val cs ds} {w : Val es fs}
              (f : ⟨ α ⟩ ~> v) (g : ⟨ β ⟩ ~> w) 
              -> e ⊢ₑ f ⊏ g -> ⟪ e ⟫ ⊢ α ⊏ β
⟪⟫-⊏ (Del α) g (here .(Del α) o) = here α (∈-dsplit _ (∈-⟪⟫ o))
⟪⟫-⊏ (Upd α β) g (here .(Upd α β) o) = here α (∈-dsplit _ (∈-⟪⟫ o))
⟪⟫-⊏ f g (there (Ins α) p) = ⟪⟫-⊏ f g p
⟪⟫-⊏ f g (there {e = e} (Del α) p) = there (⟪⟫-lemma e (⟪⟫-⊏ f g p))
⟪⟫-⊏ f g (there {e = e} (Upd α β) p) = there (⟪⟫-lemma e (⟪⟫-⊏ f g p))
⟪⟫-⊏ f g (there Nop p) = ⟪⟫-⊏ f g p

--------------------------------------------------------------------------------
