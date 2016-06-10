module Diff.Safety where

open import Diff.Core public
open import EditScript.Safety
open import Data.DTree
open import Lemmas

open import Function
open import Data.Product
open import Data.List
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding ([_])

--------------------------------------------------------------------------------
-- Safety properties
--------------------------------------------------------------------------------

-- High level statements using Mapping

open import EditScript.Mapping 
import Data.Product as P

-- Let e be the edit script that maps the source tree x in the target tree y (Diff x y e).
-- If some value v is mapped to α in e, then α is a node present in the target tree y.
noTargetMadeUp : ∀ {xs ys as a bs cs} {v : Val bs cs} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys}
            -> e ⊢ₑ v ~> ⟨ α ⟩ -> Diff x y e -> α ∈ y 
noTargetMadeUp p q rewrite mkDiff⟦ q ⟧ = targetOrigin p

-- Inverse of noTargetMadeUp.
-- Let e be the edit script that maps the source tree x in the target tree y (Diff x y e).
-- If a node α is present in the target tree y, than there is a value v which is mapped to α
  -- in e.
noTargetErase : ∀ {xs ys as a} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys}
            -> Diff x y e -> α ∈ y -> ∃ⱽ (λ v → e ⊢ₑ v ~> ⟨ α ⟩) 
noTargetErase (Del β d) (∈-here α) = map∃ⱽ (there~> (Del β)) (noTargetErase d (∈-here α))
noTargetErase (Upd α β d) (∈-here .β) = ⟨ α ⟩ , Upd α β (here (Upd α β))
noTargetErase (Ins α d) (∈-here .α) = ⊥ , Ins α (here (Ins α))
noTargetErase (Nop d) (∈-here α) = map∃ⱽ (there~> Nop) (noTargetErase d (∈-here α))
noTargetErase (Del α d) (∈-there p) = map∃ⱽ (there~> (Del α)) (noTargetErase d (∈-there p))
noTargetErase (Upd α y d) (∈-there p) = map∃ⱽ (there~> (Upd α y)) (noTargetErase d p)
noTargetErase (Ins β d) (∈-there p) = map∃ⱽ (there~> (Ins β)) (noTargetErase d p)
noTargetErase (Nop d) (∈-there p) = map∃ⱽ (there~> Nop) (noTargetErase d (∈-there p))

--------------------------------------------------------------------------------

-- Let e be the edit script that maps the source tree x in the target tree y (Diff x y e).
-- If α is is mapped to some value v e, then α is a node present in the source tree x.
noSourceMadeUp : ∀ {xs ys as a bs cs} {α : View as a} {v : Val bs cs} {x : DList xs} {y : DList ys} {e : ES xs ys}
               -> e ⊢ₑ ⟨ α ⟩ ~> v -> Diff x y e -> α ∈ x 
noSourceMadeUp p q rewrite mkDiff⟪ q ⟫ = sourceOrigin p

-- Inverse of noSourceMadeUp.
-- Let e be the edit script that maps the source tree x in the target tree y (Diff x y e).
-- If a node α is present in the source tree x, than there is a value v that is mapped to α
-- in e.
noSourceErase : ∀ {xs ys as a} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys} -> 
                  Diff x y e -> α ∈ x -> ∃ⱽ λ v -> e ⊢ₑ ⟨ α ⟩ ~> v
noSourceErase (Del α d) (∈-here .α) = ⊥ , Del α (here (Del α))
noSourceErase (Upd α β d) (∈-here .α) = ⟨ β ⟩ , Upd α β (here (Upd α β))
noSourceErase (Ins β d) (∈-here α) = map∃ⱽ (there~> (Ins β)) (noSourceErase d (∈-here α))
noSourceErase (Nop d) (∈-here α) = map∃ⱽ (there~> Nop) (noSourceErase d (∈-here α))
noSourceErase (Del α d) (∈-there p) = map∃ⱽ (there~> (Del α)) (noSourceErase d p)
noSourceErase (Upd α β d) (∈-there p) = map∃ⱽ (there~> (Upd α β)) (noSourceErase d p)
noSourceErase (Ins β d) (∈-there p) = map∃ⱽ (there~> (Ins β)) (noSourceErase d (∈-there p))
noSourceErase (Nop d) (∈-there p) = map∃ⱽ (there~> Nop) (noSourceErase d (∈-there p))

--------------------------------------------------------------------------------
-- The same lemmas are proved using specific data-types.
-- This are more convienient to work with, when considering Embedding properties.

-- Source node present in an edit script
data _∈ˢ_ {xs ys as a} (α : View as a) (e : ES xs ys) : Set₁ where
  source-∈ : ∀ {bs cs} {v : Val bs cs} {c : ⟨ α ⟩ ~> v} -> c ∈ₑ e -> α ∈ˢ e 

-- Every term in the input tree is found as source in the edit script
noEraseˢ : ∀ {xs ys as a} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys}
            -> Diff x y e -> α ∈ x -> α ∈ˢ e
noEraseˢ p q with noSourceErase p q
noEraseˢ p q | .(⟨ β ⟩) , Upd α β x = source-∈ x
noEraseˢ p q | .⊥ , Del α x = source-∈ x

-- Inverse of noErase
-- If a node α is a source in e, then α belongs to the the source of e. 
noMadeUpˢ : ∀ {xs ys as a} {t₀ : DList xs} {t₁ : DList ys} {e : ES xs ys}
              {α : View as a} -> α ∈ˢ e -> Diff t₀ t₁ e -> α ∈ t₀
noMadeUpˢ (source-∈ x) q rewrite mkDiff⟪ q ⟫ = ∈-⟪⟫ x

--------------------------------------------------------------------------------

-- Target node present in edit script
data _∈ₒ_ {xs ys as a} (α : View as a) (e : ES xs ys) : Set₁ where
  target-∈ : ∀ {bs cs} {v : Val bs cs} {c : v ~> ⟨ α ⟩} -> c ∈ₑ e -> α ∈ₒ e 

-- If a node α is present in the target y, then in the edit script that targets y,
-- there is an edit where α is the target. 
noEraseₒ : ∀ {xs ys as a} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys} ->
             Diff x y e -> α ∈ y -> α ∈ₒ e
noEraseₒ p q with noTargetErase p q
noEraseₒ p q | .(⟨ α ⟩) , Upd α β x = target-∈ x
noEraseₒ p q | .⊥ , Ins α x = target-∈ x

-- If a node α is a target in e, then α belongs to the the target of e. 
noMadeUpₒ : ∀ {xs ys as a} {α : View as a} {x : DList xs} {y : DList ys} {e : ES xs ys}
            -> α ∈ₒ e -> Diff x y e -> α ∈ y 
noMadeUpₒ (target-∈ x) q rewrite mkDiff⟦ q ⟧ = ∈-⟦⟧ x
