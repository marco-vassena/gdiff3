module Data.DTree where

open import Data.Product
open import Data.List hiding ([_])

import Relation.Binary.HeterogeneousEquality as H
open import Relation.Binary.HeterogeneousEquality hiding ([_] ; sym)
open import Relation.Binary.PropositionalEquality hiding ([_])
import Relation.Binary.PropositionalEquality as P
open import Relation.Nullary

open import Data.Nat hiding (eq? ; _≟_)
open import Lemmas

--------------------------------------------------------------------------------

postulate View : List Set -> Set -> Set

-- A View-specific instance of equality.
-- Using propositional equality is not an option because then it's not possible to
-- relate views with different indexes.
-- Using heterogeneous equality is not an option either because it refuse
-- recognize refl, failing to solve the underlying constraint about the indexes.
data _⋍_ : ∀ {xs ys a b} -> View xs a -> View ys b -> Set where
  refl : ∀ {xs a} {x : View xs a} -> x ⋍ x

⋍-sym : ∀ {as bs a b} {α : View as a} {β : View bs b} -> α ⋍ β -> β ⋍ α
⋍-sym refl = refl

¬⋍-sym : ∀ {as bs a b} {α : View as a} {β : View bs b} -> ¬ (α ⋍ β) -> ¬ (β ⋍ α)
¬⋍-sym ¬p refl = ¬p refl

ty=>⋍ : ∀ {a b as bs} {x : View as a} {y : View bs b} -> ¬ (a ≡ b) -> ¬ (x ⋍ y)
ty=>⋍ ¬p refl = ¬p refl
 
postulate eq? : (a b : Set) -> Dec (a ≡ b)
postulate _=?=_ : ∀ {a as bs} (α : View as a) (β : View bs a) -> Dec (α ⋍ β)
postulate _≟_ : ∀ {a b as bs} (α : View as a) (β : View bs b) -> Dec (α ⋍ β)

--------------------------------------------------------------------------------
-- Even though it would be more convenient to work using a single 
-- comparison function rather than eq? followed by =?=, it turns out
-- that this produces ill-typed with clause with, preventing any proof. 

-- data _≅_ : ∀ {xs ys a b} -> View xs a -> View ys b -> Set where
--   refl : ∀ {xs a} {x : View xs a} -> x ≅ x

-- postulate _≟_ : ∀ {a b xs ys} -> (x : View xs a) (y : View ys b) -> Dec (x ≅ y)

postulate distance : ∀ {xs ys a} -> View xs a -> View ys a -> ℕ
--------------------------------------------------------------------------------

mutual 
  data DTree : Set -> Set₁ where
    Node : ∀ {a xs} -> (x : View xs a) -> (ts : DList xs) -> DTree a

  data DList : List Set -> Set₁ where
    [] : DList []
    _∷_ : ∀ {xs x} -> (t : DTree x) -> (ts : DList xs) -> DList (x ∷ xs)

  infixr 7 _∷_

[_] : ∀ {x} -> DTree x -> DList (x ∷ [])
[ x ] = x ∷ []

_+++_ : ∀ {xs ys} -> DList xs -> DList ys -> DList (xs ++ ys)
[] +++ bs = bs
(t ∷ as) +++ bs = t ∷ (as +++ bs)

infixr 5 _+++_

-- Heterogeneous Equality because the index are different due to associativity of ++.
-- Is it possible to use rewrite in the signature ?
postulate assoc+++ : ∀ {xs ys zs} (a : DList xs) (b : DList ys) (c : DList zs) -> a +++ b +++ c ≅ (a +++ b) +++ c
-- assoc+++ [] b c = refl
-- assoc+++ {x ∷ xs} {ys} {zs} (t ∷ a) b c with (xs ++ ys) ++ zs | ++-assoc xs ys zs
-- ... | r | p = cong (_∷_ t) {!assoc+++ a b c!}

dsplit : ∀ {{xs}} {{ys}} -> DList (xs ++ ys) -> DList xs × DList ys
dsplit {{[]}} ds = [] , ds
dsplit {{x ∷ xs}} (t ∷ ds) with dsplit ds
dsplit {{x ∷ xs}} (t ∷ ds) | ds₁ , ds₂ = (t ∷ ds₁) , ds₂

dsplit-lemma : ∀ {{xs ys}} -> (ds : DList (xs ++ ys)) -> 
               let ds₁ , ds₂ = dsplit ds in ds₁ +++ ds₂ ≡ ds
dsplit-lemma {{[]}} ds = refl
dsplit-lemma {{x ∷ xs}} (t ∷ ds) = P.cong (_∷_ t) (dsplit-lemma ds)

-- TODO rename to just here and there?
data _∈_ : ∀ {ys xs a} -> View xs a -> DList ys -> Set₁ where
  ∈-here : ∀ {xs a ys} (x : View xs a) {ts₁ : DList xs} {ts₂ : DList ys} -> x ∈ Node x ts₁ ∷ ts₂
  ∈-there : ∀ {xs a b zs ys} {x : View xs a} {y : View ys b} {ts₁ : DList ys} {ts₂ : DList zs} 
            -> x ∈ ts₁ +++ ts₂ -> x ∈ Node y ts₁ ∷ ts₂

infixl 3 _∈_

-- Ancestor/Successor relation
-- mutual
--   data _⊢ᵗ_≺_ : ∀ {a b c xs ys} -> DTree a -> View xs b -> View ys c -> Set where
--     here : ∀ {xs ys a b} {y : View ys b} (x : View xs a) (ts : DList xs) -> y ∈ ts -> Node x ts ⊢ᵗ x ≺ y
--     there : ∀ {xs ys zs a b c} {z : View zs c} {y : View ys b} (x : View xs a) (ts : DList xs) -> ts ⊢ y ≺ z -> Node x ts ⊢ᵗ y ≺ z

data _⊢_≺_ : ∀ {xs as bs a b} -> DList xs -> View as a -> View bs b -> Set₁ where
  here : ∀ {xs ys zs a b} (x : View xs a) {y : View ys b} {ts₁ : DList xs} {ts₂ : DList zs} -> y ∈ ts₁ -> Node x ts₁ ∷ ts₂ ⊢ x ≺ y
  there : ∀ {xs ys zs a b c} {x : View xs a} {y : View ys b} {t : DTree c} {ts : DList zs} -> ts ⊢ x ≺ y -> t ∷ ts ⊢ x ≺ y

infixl 3 _⊢_≺_

there+++ : ∀ {xs ys a b as bs}{x : View as a} {y : View bs b} (ts₁ : DList xs) {ts₂ : DList ys} -> ts₂ ⊢ x ≺ y -> ts₁ +++ ts₂ ⊢ x ≺ y
there+++ [] r = r
there+++ (t ∷ ts) r = there (there+++ ts r)

-- -- Left-Right ordering
-- mutual
--   data _⊢ᵗ_⊲_ : ∀ {a b c xs ys} -> DTree a -> View xs b -> View ys c -> Set where
--     Node : ∀ {xs ys zs a b c} {y : View ys b} {z : View zs c} (x : View xs a) (ts : DList xs) -> ts ⊢ y ⊲ z -> Node x ts ⊢ᵗ y ⊲ z

--   data _⊢_⊲_ : ∀ {xs ys zs a b} -> DList xs -> View ys a -> View zs b -> Set where
--     here : ∀ {xs ys zs a b c} {y : View ys b} {z : View zs c} (t : DTree a) (ts : DList xs) -> y ∈ᵗ t -> z ∈ ts -> t ∷ ts ⊢ y ⊲ z
--     there₁ : ∀ {xs ys zs a b c} {y : View ys b} {z : View zs c} (t : DTree a) (ts : DList xs) -> ts ⊢ y ⊲ z -> t ∷ ts ⊢ y ⊲ z
--     there₂ : ∀ {xs ys zs a b c} {y : View ys b} {z : View zs c} (t : DTree a) (ts : DList xs) -> t ⊢ᵗ y ⊲ z -> t ∷ ts ⊢ y ⊲ z

--   infixl 3 _⊢_⊲_

-- Depth-first order
data _⊢_⊏_ : ∀ {xs as bs a b} -> DList xs -> View as a -> View bs b -> Set₁ where
  here : ∀ {as bs cs a b} (α : View as a) {β : View bs b} {ts₁ : DList as} {ts₂ : DList cs} -> β ∈ (ts₁ +++ ts₂) 
         -> Node α ts₁ ∷ ts₂ ⊢ α ⊏ β
  there : ∀ {as bs cs xs a b c} {α : View as a} {β : View bs b} {γ : View cs c} {ts₁ : DList cs} {ts₂ : DList xs} 
          -> ts₁ +++ ts₂ ⊢ α ⊏ β -> Node γ ts₁ ∷ ts₂ ⊢ α ⊏ β

⊏-∈₁ : ∀ {xs as bs a b} {ts : DList xs} {α : View as a} {β : View bs b} -> ts ⊢ α ⊏ β -> α ∈ ts
⊏-∈₁ (here α x) = ∈-here α
⊏-∈₁ (there p) = ∈-there (⊏-∈₁ p)

⊏-∈₂ : ∀ {xs as bs a b} {ts : DList xs} {α : View as a} {β : View bs b} -> ts ⊢ α ⊏ β -> β ∈ ts
⊏-∈₂ (here α x) = ∈-there x
⊏-∈₂ (there p) = ∈-there (⊏-∈₂ p)

infixl 3 _⊢_⊏_

postulate there⊏+++ : ∀ {xs ys a b as bs}{x : View as a} {y : View bs b} {{ts₂ : DList ys}} (ts₁ : DList xs) -> ts₂ ⊢ x ⊏ y -> ts₁ +++ ts₂ ⊢ x ⊏ y
-- I could not even use the first postulate to prove this ... same problem
-- there⊏+++ [] r = r
-- there⊏+++ {ys = cs} {{ts₂ = ts₂}} (_∷_ {xs = bs} (Node {xs = as} x xs) ts₁) r 
--   with as ++ bs ++ cs | ++-assoc as bs cs 
-- there⊏+++ {{ts₂ = ts₂}} (Node x xs ∷ ts₁) r | ._ | refl with xs +++ ts₁ +++ ts₂ | (xs +++ ts₁) +++ ts₂ | assoc+++ xs ts₁ ts₂
-- ... | a | b | c = {!!} -- there {!there⊏+++ (xs +++ ts₁) r!} 

-- there⊏+++ [] r = r
-- there⊏+++ (t ∷ ts) r = there (there⊏+++ ts r)

size : ∀ {xs} -> DList xs -> ℕ 
size [] = 0
size (Node x xs ∷ ts) = 1 + size xs + size ts

open import Relation.Binary.PropositionalEquality

size-+++ : ∀ {xs ys} (x : DList xs) (y : DList ys) -> size (x +++ y) ≡ size x + size y
size-+++ [] y = refl
size-+++ (Node x xs ∷ ts) y rewrite
    size-+++ ts y
  | +-assoc (size xs) (size ts) (size y) = refl

--------------------------------------------------------------------------------

∈-dsplit : ∀ {as a} {{ys zs}} {ds : DList (ys ++ zs)} (α : View as a) ->  
           let ds₁ , ds₂ = dsplit ds in α ∈ ds -> α ∈ ds₁ +++ ds₂
∈-dsplit {ds = ds} _ q
  rewrite dsplit-lemma ds = q
