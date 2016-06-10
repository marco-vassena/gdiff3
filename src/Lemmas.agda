module Lemmas where

open import Relation.Nullary
open import Data.List
open import Data.Nat hiding (eq?)
open import Relation.Binary.PropositionalEquality

+-assoc : ∀ (a b c : ℕ) -> a + b + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

+-distr : ∀ (a b : ℕ) -> a + suc b ≡ suc (a + b)
+-distr zero b = refl
+-distr (suc a) b = cong suc (+-distr a b)

+-distr3 : ∀ (a b c : ℕ) -> a + b + suc c ≡ suc (a + b + c)
+-distr3 zero b c = +-distr b c
+-distr3 (suc a) b c = cong suc (+-distr3 a b c)

≤-step : ∀ {a b} -> a ≤ b -> a ≤ suc b
≤-step z≤n = z≤n
≤-step (s≤s p) = s≤s (≤-step p)

≤-refl : ∀ (a : ℕ) -> a ≤ a
≤-refl zero = z≤n
≤-refl (suc a) = s≤s (≤-refl a)

≤-lemma : ∀ {n} (a b : ℕ) -> a + (suc b) ≤ n -> a + b ≤ n
≤-lemma zero m (s≤s p) = ≤-step p
≤-lemma (suc a) b (s≤s p) = s≤s (≤-lemma a b p)

open import Data.List

++-assoc : ∀ (a b c : List Set) -> (a ++ b) ++ c ≡ a ++ b ++ c
++-assoc [] b c = refl
++-assoc (x ∷ a) b c = cong (_∷_ x) (++-assoc a b c)

open import Data.Maybe
open import Data.Product

isPrefixOf : ∀ {a} {A : Set a} {_≟_ : (x y : A) -> Dec (x ≡ y)} -> (as bs : List A) -> Maybe (∃ (λ cs → bs ≡ as ++ cs))
isPrefixOf [] bs = just (bs , refl)
isPrefixOf (a ∷ as) [] = nothing
isPrefixOf {_≟_ = _≟_} (b ∷ bs) (a ∷ as) with a ≟ b
isPrefixOf {_≟_ = _≟_} (a ∷ as)  (.a ∷ bs) | yes refl with isPrefixOf {_≟_ = _≟_} as bs
isPrefixOf (a ∷ as)  (.a ∷ .(as ++ cs)) | yes refl | just (cs , refl) = just (cs , refl)
isPrefixOf (a ∷ as) (.a ∷ bs) | yes refl | nothing = nothing
isPrefixOf (a ∷ as) (b ∷ bs) | no ¬p = nothing
