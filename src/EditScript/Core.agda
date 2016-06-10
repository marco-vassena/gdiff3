module EditScript.Core where

open import Data.List
open import Data.Product
open import Data.DTree public hiding ([_])
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

-- A value either contains a node ⟨ α ⟩ or not ⊥.
-- It is indexed by the input and output types accordingly. 
data Val : List Set -> List Set -> Set₁ where
  ⊥ : Val [] []
  ⟨_⟩ : ∀ {as a} (α : View as a) -> Val as [ a ] 

-- u ~> v represents an edit that maps the value u to v.
data _~>_ : ∀ {as bs cs ds} -> Val as bs -> Val cs ds -> Set where
  Nop : ⊥ ~> ⊥
  Del : ∀ {as a} (α : View as a) -> ⟨ α ⟩ ~> ⊥
  Ins : ∀ {as a} (α : View as a) -> ⊥ ~> ⟨ α ⟩
  Upd : ∀ {as bs a} (α : View as a) (β : View bs a) -> ⟨ α ⟩ ~> ⟨ β ⟩

-- ES xs ys is an edit script that represents a well-typed sequence of edits,
-- which transform the input list (DList xs) to the target list (DList ys).
data ES : List Set -> List Set -> Set₁ where
  [] : ES [] []
  _∷_ : ∀ {xs ys as bs cs ds} {v : Val as bs} {w : Val cs ds} -> 
          (x : v ~> w) -> (e : ES (as ++ xs) (cs ++ ys)) -> ES (bs ++ xs) (ds ++ ys)
  
--------------------------------------------------------------------------------

-- ⟦_⟧ is the target function, which returns the target object.
⟦_⟧ : ∀ {xs ys} -> ES xs ys -> DList ys
⟦ [] ⟧ = []
⟦ Nop ∷ e ⟧ = ⟦ e ⟧
⟦ Del α ∷ e ⟧ = ⟦ e ⟧
⟦ Upd α β ∷ e ⟧ with dsplit ⟦ e ⟧
... | ds₁ , ds₂ = Node β ds₁ ∷ ds₂
⟦ Ins α ∷ e ⟧ with dsplit ⟦ e ⟧
... | ds₁ , ds₂ = Node α ds₁ ∷ ds₂

-- ⟪_⟫ is the source function, which returns the source object.
⟪_⟫ : ∀ {xs ys} -> ES xs ys -> DList xs
⟪ [] ⟫ = []
⟪ Nop ∷ e ⟫ = ⟪ e ⟫
⟪ Del α ∷ e ⟫ with dsplit ⟪ e ⟫
... | ds₁ , ds₂ = Node α ds₁ ∷ ds₂
⟪ Ins α ∷ e ⟫ = ⟪ e ⟫
⟪ Upd α β ∷ e ⟫ with dsplit ⟪ e ⟫
... | ds₁ , ds₂ = Node α ds₁ ∷ ds₂

--------------------------------------------------------------------------------
-- Membership

-- f ∈ₑ e is the proof that the edit f belongs to e.
data _∈ₑ_ : ∀ {as bs cs ds xs ys} {v : Val as bs} {w : Val cs ds} -> v ~> w -> ES xs ys -> Set₁ where
  here : ∀ {as bs cs ds xs ys} {v : Val as bs} {w : Val cs ds} {e : ES (as ++ xs) (cs ++ ys)} -> (c : v ~> w) -> c ∈ₑ c ∷ e
  there : ∀ {as bs cs ds es fs gs hs xs ys} {u : Val as bs} {v : Val cs ds} {w : Val es fs} {z : Val gs hs} {c : u ~> v} 
            {e : ES (es ++ xs) (gs ++ ys)} (d : w ~> z) -> c ∈ₑ e -> c ∈ₑ d ∷ e

infixl 3 _∈ₑ_

--------------------------------------------------------------------------------

-- e ⊢ₑ f ⊏ g is the proof that in e the edit f preceeds g.
data _⊢ₑ_⊏_ : ∀ {xs ys as bs cs ds es fs gs hs} {u : Val as cs} {v : Val bs ds} {w : Val es gs} {z : Val fs hs} -> 
                ES xs ys -> u ~> v -> w ~> z -> Set₁ where
  here : ∀ {as bs cs ds es fs gs hs xs ys} {u : Val es fs} {v : Val gs hs} {d : u ~> v} 
           {w : Val as bs} {z : Val cs ds} {e : ES (as ++ xs) (cs ++ ys)} 
           (c : w ~> z) -> (o : d ∈ₑ e) -> c ∷ e ⊢ₑ c ⊏ d 
  there : ∀ {as bs cs ds es fs gs hs is ls ms ns xs ys} {u : Val es fs} {v : Val gs hs} {d : u ~> v} {w : Val as bs} 
          {z : Val cs ds} {c : w ~> z} {e : ES (is ++ xs) (ms ++ ys)} {s : Val is ls} {t : Val ms ns} -> (a : s ~> t)
          (o : e ⊢ₑ c ⊏ d) -> a ∷ e ⊢ₑ c ⊏ d 

infixl 3 _⊢ₑ_⊏_

-- If e ⊢ₑ f ⊏ g then f ∈ₑ e
⊏ₑ-∈₁ : ∀ {xs ys as bs cs ds es fs gs hs} {e : ES xs ys} 
          {u : Val as cs} {v : Val bs ds} {w : Val es gs} {z : Val fs hs}
          {d : w ~> z} {c : u ~> v} -> e ⊢ₑ c ⊏ d -> c ∈ₑ e
⊏ₑ-∈₁ (here c o) = here c
⊏ₑ-∈₁ (there e p) = there e (⊏ₑ-∈₁ p)

-- If e ⊢ₑ f ⊏ g then g ∈ₑ e
⊏ₑ-∈₂ : ∀ {xs ys as bs cs ds es fs gs hs} {e : ES xs ys} 
          {u : Val as cs} {v : Val bs ds} {w : Val es gs} {z : Val fs hs}
          {d : w ~> z} {c : u ~> v} -> e ⊢ₑ c ⊏ d -> d ∈ₑ e
⊏ₑ-∈₂ (here c o) = there c o
⊏ₑ-∈₂ (there e p) = there e (⊏ₑ-∈₂ p)

--------------------------------------------------------------------------------
-- Auxiliary lemmas that relate DList and membership with edit scripts

∈-here-⟪⟫ : ∀ {a as bs cs xs ys} {α : View as a} {v : Val bs cs} {e : ES (as ++ xs) (bs ++ ys)} (c : ⟨ α ⟩ ~> v) -> α ∈ ⟪ c ∷ e ⟫
∈-here-⟪⟫ (Del α) = ∈-here α
∈-here-⟪⟫ (Upd α β) = ∈-here α

∈-there-⟪⟫ :  ∀ {as bs cs ds ms m xs ys} {v : Val as bs} {w : Val cs ds} {e : ES (as ++ xs) (cs ++ ys)} {α : View ms m} -> 
               (d : v ~> w) -> α ∈ ⟪ e ⟫ -> α ∈ ⟪ d ∷ e ⟫
∈-there-⟪⟫ (Ins α) p = p
∈-there-⟪⟫ (Del α) p = ∈-there (∈-dsplit _ p)
∈-there-⟪⟫ (Upd α β) p = ∈-there (∈-dsplit _ p)
∈-there-⟪⟫ Nop p = p

∈-there-⟦⟧ :  ∀ {as bs cs ds ms m xs ys} {v : Val as bs} {w : Val cs ds} {e : ES (as ++ xs) (cs ++ ys)} {α : View ms m} -> 
               (d : v ~> w) -> α ∈ ⟦ e ⟧ -> α ∈ ⟦ d ∷ e ⟧
∈-there-⟦⟧ (Ins α) p = ∈-there (∈-dsplit _ p)
∈-there-⟦⟧ (Del α) p = p
∈-there-⟦⟧ (Upd α β) p = ∈-there (∈-dsplit _ p)
∈-there-⟦⟧ Nop p = p

∈-here-⟦⟧ : ∀ {a as bs cs xs ys} {α : View cs a} {v : Val as bs} {e : ES (as ++ xs) (cs ++ ys)} (c : v ~> ⟨ α ⟩) -> α ∈ ⟦ c ∷ e ⟧
∈-here-⟦⟧ (Ins α) = ∈-here α
∈-here-⟦⟧ (Upd α β) = ∈-here β

--------------------------------------------------------------------------------

-- The second edit script extends the first, adding a finite number of Nop.
data _⊴_ : ∀ {xs ys} -> ES xs ys -> ES xs ys -> Set where
  stop : [] ⊴ []
  cons : ∀ {xs ys as bs cs ds} {v : Val as bs} {w : Val cs ds} {e₁ e₂ : ES (as ++ xs) (cs ++ ys)} -> 
          (x : v ~> w) -> e₁ ⊴ e₂ -> x ∷ e₁ ⊴ x ∷ e₂
  nop : ∀ {xs ys} {e₁ e₂ : ES xs ys} -> e₁ ⊴ e₂ -> e₁ ⊴ Nop ∷ e₂

infixr 3 _⊴_

-- ≈ is the equivalence relation for edit scripts.
-- e₁ ≈ e₂ if the source and target tree of e₁ and e₂ are the same.
data _≈_ {xs ys} (e₁ e₂ : ES xs ys) : Set₁ where
  eq : ⟪ e₁ ⟫ ≡ ⟪ e₂ ⟫ -> ⟦ e₁ ⟧ ≡ ⟦ e₂ ⟧ -> e₁ ≈ e₂

-- Extending an edit script does not change its semantic with respect to ⟪_⟫
⊴-⟪_⟫ : ∀ {xs ys} {e₁ e₂ : ES xs ys} -> e₁ ⊴ e₂ -> ⟪ e₁ ⟫ ≡ ⟪ e₂ ⟫
⊴-⟪ stop ⟫ = refl
⊴-⟪ cons (Ins α) p ⟫ = ⊴-⟪ p ⟫
⊴-⟪ cons (Del α) p ⟫ rewrite ⊴-⟪ p ⟫ = refl
⊴-⟪ cons (Upd α β) p ⟫ rewrite ⊴-⟪ p ⟫ = refl
⊴-⟪ cons Nop p ⟫ = ⊴-⟪ p ⟫
⊴-⟪ nop p ⟫ = ⊴-⟪ p ⟫

-- Extending an edit script does not change its semantic with respect to ⟦_⟧
⊴-⟦_⟧ : ∀ {xs ys} {e₁ e₂ : ES xs ys} -> e₁ ⊴ e₂ -> ⟦ e₁ ⟧ ≡ ⟦ e₂ ⟧
⊴-⟦ stop ⟧ = refl
⊴-⟦ cons (Ins α) p ⟧ rewrite ⊴-⟦ p ⟧ = refl
⊴-⟦ cons (Del α) p ⟧ = ⊴-⟦ p ⟧
⊴-⟦ cons (Upd α β) p ⟧ rewrite ⊴-⟦ p ⟧ = refl
⊴-⟦ cons Nop p ⟧ = ⊴-⟦ p ⟧
⊴-⟦ nop p ⟧ = ⊴-⟦ p ⟧

-- Any e₁ and e₂ for which e₁ ⊴ e₂ is always a safe extension 
⊴-safe : ∀ {xs ys} {e₁ e₂ : ES xs ys} (p : e₁ ⊴ e₂) -> e₁ ≈ e₂
⊴-safe p = eq ⊴-⟪ p ⟫ ⊴-⟦ p ⟧

--------------------------------------------------------------------------------
-- Auxiliary functions about Val and ~> equality

-- Heterogeneous equality for Val
data _≃_ {as bs} (v : Val as bs) : ∀ {cs ds} (w : Val cs ds) -> Set where
  refl : v ≃ v

-- Heterogeneous equality tailored for transformations
data _≅_ {as bs cs ds} {u : Val as bs} {v : Val cs ds} (x : u ~> v) 
         : ∀ {es fs gs hs} {w : Val es fs} {z : Val gs hs} (y : w ~> z) → Set where
   refl : x ≅ x

≃-⋍ : ∀ {as bs} {a b : Set} {α : View as a} {β : View bs b} -> ¬ (⟨ α ⟩ ≃ ⟨ β ⟩) -> ¬ (α ⋍ β)
≃-⋍ ¬p refl = ¬p refl

-- Decidable equality for values.
_≟ⱽ_ : ∀ {as bs cs ds} (v : Val as bs) (w : Val cs ds) -> Dec (v ≃ w)
⊥ ≟ⱽ ⊥ = yes refl
⊥ ≟ⱽ ⟨ α ⟩ = no (λ ())
⟨ α ⟩ ≟ⱽ ⊥ = no (λ ())
⟨ α ⟩ ≟ⱽ ⟨ β ⟩ with α ≟ β
⟨ α ⟩ ≟ⱽ ⟨ .α ⟩ | yes refl = yes refl
⟨ α ⟩ ≟ⱽ ⟨ β ⟩ | no α≠β = no (aux α≠β) 
  where aux : ∀ {as bs a b} {α : View as a} {β : View bs b} -> ¬ (α ⋍ β) -> ¬ (⟨ α ⟩ ≃ ⟨ β ⟩)
        aux α≠β₁ refl = α≠β₁ refl

--------------------------------------------------------------------------------

-- Does the transformation perform a change?
data Change {as bs cs ds} {v : Val as bs} {w : Val cs ds} (f : v ~> w) : Set₁ where
  IsChange : (v≠w : ¬ (v ≃ w)) -> Change f

------------------------------------------------------------------------------------------
open import Level as L

-- Existential tailored for Values
data ∃ⱽ {a} : (∀ {as bs} -> Val as bs -> Set a) -> Set (a ⊔ (L.suc (L.zero))) where
  _,_ : ∀ {cs ds} {P : ∀ {as bs} -> Val as bs -> Set a} -> (v : Val cs ds) -> P v -> ∃ⱽ P

-- Existential tailored for Mapping (edits).
data ∃ᴹ {a} {as bs} {u : Val as bs} : (∀ {cs ds} {w : Val cs ds} -> u ~> w -> Set a) -> Set (a ⊔ (L.suc (L.zero))) where
  _,_ : ∀ {es fs} {w : Val es fs} {P : ∀ {cs ds} {v : Val cs ds} -> u ~> v -> Set a} 
          (f : u ~> w) -> P f -> ∃ᴹ P 

infixr 3 _,_

-- Identity on Val, and maps the function on the proof P v.
map∃ⱽ : ∀ {a b} {P : ∀ {as bs} -> Val as bs -> Set a} {Q : ∀ {as bs} -> Val as bs -> Set b} ->
         (∀ {as bs} {v : Val as bs} -> P v -> Q v) -> ∃ⱽ P -> ∃ⱽ Q
map∃ⱽ f (v , p) = v , f p

-- Type synonym: two nested value existential.
∃ⱽ₂ : ∀ {a} -> (∀ {as bs cs ds} -> Val as bs -> Val cs ds -> Set a) -> Set _
∃ⱽ₂ P = ∃ⱽ (λ v → ∃ⱽ (λ w → P v w))
