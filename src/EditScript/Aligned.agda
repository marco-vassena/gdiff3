module EditScript.Aligned where

open import EditScript.Core

open import Data.Empty
open import Data.Unit
open import Data.List
open import Relation.Binary.PropositionalEquality

-- e₁ ~ e₂ is the proof that e₁ and e₂ are aligned, i.e. all their edits share the same source
data _⋎_ : ∀ {xs ys zs ws} -> (e₁ : ES xs ys) (e₂ : ES zs ws) -> Set₁ where
  nil : [] ⋎ []
  cons : ∀ {as bs cs ds es fs xs ys zs} {v : Val as bs} {w : Val cs ds} {z : Val es fs}
           {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (es ++ zs)} 
           (x : v ~> w) (y : v ~> z) -> e₁ ⋎ e₂ -> x ∷ e₁ ⋎ y ∷ e₂ 
          
infixr 3 _⋎_

--------------------------------------------------------------------------------
-- Properties of the ⋎ relatin
--------------------------------------------------------------------------------

-- The ⋎ relation is reflexive
⋎-refl : ∀ {xs ys} -> (e : ES xs ys) -> e ⋎ e
⋎-refl (x ∷ e) = cons x x (⋎-refl e)
⋎-refl [] = nil

-- The ⋎ relation is symmetric
⋎-sym : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} -> e₁ ⋎ e₂ -> e₂ ⋎ e₁
⋎-sym nil = nil
⋎-sym (cons x y p) = cons y x (⋎-sym p)

-- The ⋎ relation is transitive 
⋎-trans : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} -> e₁ ⋎ e₂ -> e₂ ⋎ e₃ -> e₁ ⋎  e₃
⋎-trans nil nil = nil
⋎-trans (cons x y p) (cons .y z q) = cons x z (⋎-trans p q)

-- If e₁ is aligned with e₂, then they share the same source object. 
⋎-⟪⟫ : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} -> e₁ ⋎ e₂
       -> ⟪ e₁ ⟫ ≡ ⟪ e₂ ⟫
⋎-⟪⟫ nil = refl
⋎-⟪⟫ (cons (Ins α) (Ins β) p) = ⋎-⟪⟫ p
⋎-⟪⟫ (cons (Ins α) Nop p) = ⋎-⟪⟫ p
⋎-⟪⟫ (cons (Del α) (Del .α) p) rewrite ⋎-⟪⟫ p = refl
⋎-⟪⟫ (cons (Del α) (Upd .α β) p) rewrite ⋎-⟪⟫ p = refl
⋎-⟪⟫ (cons (Upd α β) (Del .α) p) rewrite ⋎-⟪⟫ p = refl
⋎-⟪⟫ (cons (Upd α β) (Upd .α γ) p) rewrite ⋎-⟪⟫ p = refl
⋎-⟪⟫ (cons Nop (Ins α) p) = ⋎-⟪⟫ p
⋎-⟪⟫ (cons Nop Nop p) = ⋎-⟪⟫ p

--------------------------------------------------------------------------------

-- e₁ ~ e₂, if there exists extension of e₁ and e₂ that are aligned. 
data _~_ {xs ys zs : List Set} (e₁ : ES xs ys) (e₂ : ES xs zs) : Set₁ where
  Align : ∀ {e₁' : ES xs ys} {e₂' : ES xs zs} -> (a : e₁ ⊴ e₁') (b : e₂ ⊴ e₂')(p : e₁' ⋎ e₂') -> e₁ ~ e₂

--------------------------------------------------------------------------------

-- p ⊢ u ~>[ v , w ] is the proof that in two aligned scripts e₁ and e₂, the same source value u
-- is mapped respectively to v in e₁ and to w in e₂.
data Map⋎ {as bs cs ds es fs} (u : Val as bs) (v : Val cs ds) (w : Val es fs) 
          : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} (p : e₁ ⋎ e₂) -> Set where
  here : ∀ {xs ys zs} {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (es ++ zs)} {p : e₁ ⋎ e₂} 
           (x : u ~> v) (y : u ~> w) -> Map⋎ u v w (cons x y p) 
  cons : ∀ {xs ys zs as' bs' cs' ds' es' fs'} {e₁ : ES (as' ++ xs) (cs' ++ ys)} {e₂ : ES (as' ++ xs) (es' ++ zs)} 
           {p : e₁ ⋎ e₂} {u' : Val as' bs'} {v' : Val cs' ds'} {w' : Val es' fs'} 
           (x : u' ~> v') (y : u' ~> w') -> Map⋎ u v w p -> Map⋎ u v w (cons x y p)

-- A type synonim to provide a more readable syntax 
-- Note that a syntax declaration would not work here, because it is not possible
-- to include instance arguments (e₁ ⋎ e₂) 
_,_⊢_~>[_,_] : ∀ {xs ys zs as bs cs ds es fs} (e₁ : ES xs ys) (e₂ : ES xs zs) {{p : e₁ ⋎ e₂}} -> 
                 (u : Val as bs) (v : Val cs ds) (w : Val es fs) -> Set
_,_⊢_~>[_,_] e₁ e₂ {{p}} u v w = Map⋎ u v w p

infixr 2 _,_⊢_~>[_,_]
