module Diff3.Safety where

open import Diff3.Core public
open import Data.DTree
open import Lemmas

open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Data.Product
open import Data.Sum as S
open import Data.Empty using (⊥-elim)

-- Changing edits in the first edit are found in the merged edit script, if no conflict is raised.
noBackOutChanges₁ : ∀ {xs ys zs as bs cs ds} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES₃ xs} {p : e₁ ⋎ e₂}
                      {u : Val as bs} {v : Val cs ds} {f : u ~> v} -> 
                      Change f -> Diff₃ e₁ e₂ e₃ -> f ∈ₑ e₁ -> NoCnf e₃ -> f ∈₃ e₃
noBackOutChanges₁ (IsChange v≠w) (merge (Id₁ f g) d) (here .f) _ = ⊥-elim (v≠w refl)
noBackOutChanges₁ (IsChange v≠w) (merge (Id₂ f g) d) (here .f) _ = here f
noBackOutChanges₁ (IsChange v≠w) (merge (Idem g) d) (here .g) _ = here g
noBackOutChanges₁ c (conflict u d) (here f) ()
noBackOutChanges₁ c (merge m d) (there f₁ p) (h ∷ q) = there h (noBackOutChanges₁ c d p q)
noBackOutChanges₁ c (conflict u₁ d) (there f₁ p₁) ()

-- Changing edits in the second edit are found in the merged edit script, if no conflict is raised.
noBackOutChanges₂ : ∀ {xs ys zs as bs cs ds} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES₃ xs} {p : e₁ ⋎ e₂}
                      {u : Val as bs} {v : Val cs ds} {f : u ~> v} -> 
                      Change f -> Diff₃ e₁ e₂ e₃ -> f ∈ₑ e₂ -> NoCnf e₃ -> f ∈₃ e₃
noBackOutChanges₂ {e₃ = e₃} c d p q = noBackOutChanges₁ c (⇓-sym' d q) p q
 
--------------------------------------------------------------------------------
-- Similar lemmas for Merged

-- Just reuse noBackOutChanges₁ using a `downgraded' Merged₃ 
noBackOutChangesMerged₁ : ∀ {xs ys zs ws as bs cs ds} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws}
                            {u : Val as bs} {v : Val cs ds} {f : u ~> v} -> 
                            {{c : Change f}} -> Merged₃ e₁ e₂ e₃ -> f ∈ₑ e₁ -> f ∈ₑ e₃
noBackOutChangesMerged₁ {{c}} m p = ∈₃-∈ₑ (noBackOutChanges₁ c (Merged₃-Diff₃ m) p (ES-NoCnf _))

noBackOutChangesMerged₂ : ∀ {xs ys zs ws as bs cs ds} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws}
                            {u : Val as bs} {v : Val cs ds} {f : u ~> v} -> 
                            {{c : Change f}} -> Merged₃ e₁ e₂ e₃ -> f ∈ₑ e₂ -> f ∈ₑ e₃
noBackOutChangesMerged₂ {{c}} m p = ∈₃-∈ₑ (noBackOutChanges₂ c (Merged₃-Diff₃ m) p (ES-NoCnf _))

-- Each edit found in the merged edit script belongs to either of the two input scripts.
noEditMadeUp : ∀ {xs ys zs as bs cs ds} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES₃ xs} {p : e₁ ⋎ e₂}
                 {u : Val as bs} {v : Val cs ds} {f : u ~> v} -> 
                 f ∈₃ e₃ -> Diff₃ e₁ e₂ e₃ -> f ∈ₑ e₁ ⊎ f ∈ₑ e₂
noEditMadeUp (here f) (merge (Id₁ g .f) d) = inj₂ (here f)
noEditMadeUp (here f) (merge (Id₂ .f g) d) = inj₁ (here f)
noEditMadeUp (here f) (merge (Idem .f) d) = inj₁ (here f)
noEditMadeUp (there g p) (merge m d) = S.map (there _) (there _) (noEditMadeUp p d)
noEditMadeUp (thereᶜ c p) (conflict u d) = S.map (there _) (there _) (noEditMadeUp p d)

--------------------------------------------------------------------------------

-- xs ⊆ ys , zs is the proof that xs is a list composed from elements of ys and zs
data _⊆_,_ : List Set -> List Set -> List Set -> Set where
  stop : [] ⊆ [] , []
  cons₁ : ∀ {y xs ys zs} -> xs ⊆ ys , zs -> y ∷ xs ⊆ y ∷ ys , zs
  cons₂ : ∀ {z xs ys zs} -> xs ⊆ ys , zs -> z ∷ xs ⊆ ys , z ∷ zs
  cons₁₂ : ∀ {x xs ys zs} -> xs ⊆ ys , zs -> x ∷ xs ⊆ x ∷ ys , x ∷ zs
  drop₁ : ∀ {y xs ys zs} -> xs ⊆ ys , zs -> xs ⊆ y ∷ ys , zs
  drop₂ : ∀ {z xs ys zs} -> xs ⊆ ys , zs -> xs ⊆ ys , z ∷ zs

infixr 2 _⊆_,_ 

-- Unwraps all the types of the subtrees contained in a DList in a depth-first order
typesOf : ∀ {xs} -> DList xs -> List Set
typesOf [] = []
typesOf (Node {a = a} x xs ∷ d) = a ∷ typesOf xs ++ typesOf d

-- typesOf distributes over +++ by associativity of ++
typesOf++ : ∀ {as bs} (a : DList as) (b : DList bs) -> typesOf a ++ typesOf b ≡ typesOf (a +++ b)
typesOf++ [] b = refl
typesOf++ (Node {a = ty} x xs ∷ a) b rewrite 
   sym (typesOf++ a b)  
  | ++-assoc (typesOf xs) (typesOf a) (typesOf b) = cong (_∷_ ty) refl

-- Auxiliary lemma
typesOf⟦_⟧ : ∀ {{ys zs}} {xs} (e : ES xs (ys ++ zs)) ->
              let ds₁ , ds₂ = dsplit ⟦ e ⟧ in typesOf ds₁ ++ typesOf ds₂ ≡ typesOf ⟦ e ⟧
typesOf⟦ e ⟧ rewrite
  typesOf++ (proj₁ (dsplit ⟦ e ⟧)) (proj₂ (dsplit ⟦ e ⟧)) 
  | dsplit-lemma ⟦ e ⟧ = refl

-- If a diff₃ is successful the output type list of the merged script is 
-- a mixture of the output type list of the two input scripts. 
mixOf : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws}
           -> Merged₃ e₁ e₂ e₃ -> typesOf ⟦ e₃ ⟧ ⊆ typesOf ⟦ e₁ ⟧ , typesOf ⟦ e₂ ⟧
mixOf nil = stop
mixOf (cons (Id₁ Nop Nop) p) = mixOf p
mixOf (cons {e₂ = e₂} {e₃} (Id₁ Nop (Ins α)) p) rewrite
  typesOf⟦ e₂ ⟧ | typesOf⟦ e₃ ⟧ = cons₂ (mixOf p)
mixOf (cons {e₁ = e₁} (Id₁ (Upd α .α) (Del .α)) p) rewrite
  typesOf⟦ e₁ ⟧ = drop₁ (mixOf p)
mixOf (cons {e₁ = e₁} {e₂} {e₃} (Id₁ (Upd α .α) (Upd .α β)) p) rewrite
  typesOf⟦ e₁ ⟧ | typesOf⟦ e₂ ⟧ | typesOf⟦ e₃ ⟧ = cons₁₂ (mixOf p)
mixOf (cons (Id₂ Nop Nop) p) = mixOf p
mixOf (cons {e₂ = e₂} (Id₂ (Del α) (Upd .α .α)) p) rewrite
  typesOf⟦ e₂ ⟧ = drop₂ (mixOf p)
mixOf (cons {e₁ = e₁} {e₃ = e₃} (Id₂ (Ins α) Nop) p) rewrite
  typesOf⟦ e₁ ⟧ | typesOf⟦ e₃ ⟧ = cons₁ (mixOf p)
mixOf (cons {e₁ = e₁} {e₂} {e₃} (Id₂ (Upd α β) (Upd .α .α)) p) rewrite
  typesOf⟦ e₁ ⟧ | typesOf⟦ e₂ ⟧ | typesOf⟦ e₃ ⟧ = cons₁₂ (mixOf p)
mixOf (cons (Idem Nop) p) = mixOf p
mixOf (cons (Idem (Del α)) p) = mixOf p
mixOf (cons {e₁ = e₁} {e₂} {e₃} (Idem (Ins α)) p) rewrite 
  typesOf⟦ e₁ ⟧ | typesOf⟦ e₂ ⟧ | typesOf⟦ e₃ ⟧ = cons₁₂ (mixOf p)
mixOf (cons {e₁ = e₁} {e₂} {e₃} (Idem (Upd α β)) p) rewrite 
  typesOf⟦ e₁ ⟧ | typesOf⟦ e₂ ⟧ | typesOf⟦ e₃ ⟧ = cons₁₂ (mixOf p)
