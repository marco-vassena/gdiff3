-- This module proves some safety property about edit scripts
-- and their corresponding source and target objects.
-- Note that these properties follow from the definition of ES
-- and the source and target values and not from the diff algorithm 
-- used to generate the script.

module EditScript.Safety where

open import EditScript.Core public
open import EditScript.Mapping
open import Relation.Binary.PropositionalEquality
open import Data.List
  
-- Transforms ∈ₑ between an edit and a edit script in ∈ between its target node and target object
∈-⟦⟧ : ∀ {xs ys as a bs cs} {v : Val bs cs} {α : View as a} {e : ES xs ys} {c : v ~> ⟨ α ⟩} -> c ∈ₑ e -> α ∈ ⟦ e ⟧ 
∈-⟦⟧ (here c) = ∈-here-⟦⟧ c
∈-⟦⟧ (there d p) = ∈-there-⟦⟧ d (∈-⟦⟧ p)

--------------------------------------------------------------------------------

-- Transforms ∈ₑ between an edit and a edit script in ∈ between its source node and source object
∈-⟪⟫ : ∀ {xs ys as a bs cs} {v : Val bs cs} {α : View as a} {e : ES xs ys} {c : ⟨ α ⟩ ~> v} -> c ∈ₑ e -> α ∈ ⟪ e ⟫
∈-⟪⟫ (here c) = ∈-here-⟪⟫ c
∈-⟪⟫ (there d p) = ∈-there-⟪⟫ d (∈-⟪⟫ p)

--------------------------------------------------------------------------------
-- High-level description of Safety properties

-- If in an edit script some value is mapped to a node α, then is α part of the target object.
targetOrigin : ∀ {xs ys as a bs cs} {v : Val bs cs} {e : ES xs ys} {α : View as a} -> e ⊢ₑ v ~> ⟨ α ⟩ -> α ∈ ⟦ e ⟧
targetOrigin (Upd α β x) = ∈-⟦⟧ x
targetOrigin (Ins α x) = ∈-⟦⟧ x

-- If in an edit script some node α is mapped to value, then α is part of the source object.
sourceOrigin : ∀ {xs ys as a bs cs} {v : Val bs cs} {e : ES xs ys} {α : View as a} -> e ⊢ₑ ⟨ α ⟩ ~> v -> α ∈ ⟪ e ⟫
sourceOrigin (Upd α β x) = ∈-⟪⟫ x
sourceOrigin (Del α x) = ∈-⟪⟫ x

--------------------------------------------------------------------------------
