module Diff3.Core where

open import Diff3.ES3 public 

open import Relation.Nullary
open import Data.Product hiding (swap)
open import Data.Sum
open import Data.List
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------
-- Merge datatypes.
-- These datatypes describe merging declaratively and succintly.
--------------------------------------------------------------------------------

-- It minimally represents how transformations can be merged.
-- Id₁ and Id₂ can be used when one of the two transformation is just id, 
-- in which case we choose the other transformation.
-- The third constructor Idem corresponds to the fact that ⊔ is idempotent, therefore any 
-- transformation can be successfully merged against itself producing itself. 
-- Note that this datatype is polymorphic in the source node v, which is the same
-- in all the three mappings.
data _⊔_↧_ {as bs} {v : Val as bs} : ∀ {cs ds es fs gs hs} {a : Val cs ds} {b : Val es fs} {c : Val gs hs} -> 
                                     v ~> a -> v ~> b -> v ~> c -> Set₁ where
  Id₁ : ∀ {cs ds} {w : Val cs ds} -> (f : v ~> v) (g : v ~> w) -> f ⊔ g ↧ g
  Id₂ : ∀ {cs ds} {w : Val cs ds} -> (f : v ~> w) (g : v ~> v) -> f ⊔ g ↧ f
  Idem : ∀ {cs ds} {w : Val cs ds} -> (f : v ~> w) -> f ⊔ f ↧ f

infixl 2 _⊔_↧_
 
-- ⊔ is symmetric in the input transformations.
↧-sym : ∀ {as bs cs ds es fs gs hs} {v : Val as bs} {a : Val cs ds} {b : Val es fs} {c : Val gs hs}
          {f : v ~> a} {g : v ~> b} {h : v ~> c} -> f ⊔ g ↧ h -> g ⊔ f ↧ h
↧-sym (Id₁ f g) = Id₂ g f
↧-sym (Id₂ f g) = Id₁ g f
↧-sym (Idem f) = Idem f
 
-- This datatype is the proof that two mapping cannot be merged, thus ⊔ fails producing a conflict.
-- There are 4 constructors, one for each possible conflict.
-- Furthermore necessary inequality proofs about nodes are included.  
data _⊔_↥_ : ∀ {as bs cs ds es fs} {v : Val as bs} {w : Val cs ds} {z : Val es fs}
               -> (v ~> w) -> (v ~> z) -> Conflict v w z -> Set where
  InsIns : ∀ {as a bs b} {α : View as a} {β : View bs b} 
             (f : ⊥ ~> ⟨ α ⟩) (g : ⊥ ~> ⟨ β ⟩) (α≠β : ¬ (α ⋍ β)) -> f ⊔ g ↥ InsIns α β
  UpdUpd : ∀ {as bs cs a} {α : View as a} {β : View bs a} {γ : View cs a}
             (f : ⟨ α ⟩ ~> ⟨ β ⟩) (g : ⟨ α ⟩ ~> ⟨ γ ⟩)
             (α≠β : ¬ (α ⋍ β)) (α≠γ : ¬ (α ⋍ γ)) (β≠γ : ¬ (β ⋍ γ)) -> f ⊔ g ↥ UpdUpd α β γ
  UpdDel : ∀ {as bs a} {α : View as a} {β : View bs a} 
             (f : ⟨ α ⟩ ~> ⟨ β ⟩) (g : ⟨ α ⟩ ~> ⊥) (α≠β : ¬ (α ⋍ β)) -> f ⊔ g ↥ UpdDel α β
  DelUpd : ∀ {as bs a} {α : View as a} {β : View bs a} 
             (f : ⟨ α ⟩ ~> ⊥) (g : ⟨ α ⟩ ~> ⟨ β ⟩) (α≠β : ¬ (α ⋍ β)) -> f ⊔ g ↥ DelUpd α β

infixl 2 _⊔_↥_

-- ↥ is symmetric modulo `swap', because conflicts are inherently ordered.
↥-sym : ∀ {as bs cs ds es fs} {v : Val as bs} {a : Val cs ds} {b : Val es fs} {c : Conflict v a b}
          {f : v ~> a} {g : v ~> b} -> f ⊔ g ↥ c -> g ⊔ f ↥ swap c
↥-sym (InsIns f g α≠β) = InsIns g f (¬⋍-sym α≠β)
↥-sym (UpdUpd f g α≠β α≠γ β≠γ) = UpdUpd g f α≠γ α≠β (¬⋍-sym β≠γ)
↥-sym (UpdDel f g α≠β) = DelUpd g f α≠β
↥-sym (DelUpd f g α≠β) = UpdDel g f α≠β

-- For any two mapping from the same source u, either there is a third mapping h from u that merges them
-- or the merge fails with some conflict c. 
_⊔_ : ∀ {as bs cs ds es fs} {u : Val as bs} {v : Val cs ds} {w : Val es fs} 
                    (f : u ~> v) (g : u ~> w) -> (∃ λ c -> f ⊔ g ↥ c) ⊎ (∃ᴹ λ h → f ⊔ g ↧ h)
(Ins {a = a} α) ⊔ (Ins {a = b} β) with α ≟ β
(Ins α) ⊔ (Ins .α) | yes refl = inj₂ (Ins α , Idem (Ins α))
(Ins α) ⊔ (Ins β) | no ¬p = inj₁ (InsIns α β , InsIns (Ins α) (Ins β) ¬p)
(Ins α) ⊔ Nop = inj₂ (Ins α , Id₂ (Ins α) Nop)
(Del α) ⊔ (Del .α) = inj₂ (Del α , Idem (Del α))
(Del α) ⊔ (Upd .α β) with α =?= β
(Del α) ⊔ (Upd .α .α) | yes refl = inj₂ (Del α , Id₂ (Del α) (Upd α α))
(Del α) ⊔ (Upd .α β) | no ¬p = inj₁ (DelUpd α β , DelUpd (Del α) (Upd α β) ¬p)
(Upd α β) ⊔ (Del .α) with α =?= β
(Upd α .α) ⊔ (Del .α) | yes refl = inj₂ (Del α , Id₁ (Upd α α) (Del α))
(Upd α β) ⊔ (Del .α) | no ¬p = inj₁ (UpdDel α β , UpdDel (Upd α β) (Del α) ¬p)
(Upd α β) ⊔ (Upd .α γ) with ⟨ β ⟩ ≟ⱽ ⟨ γ ⟩
(Upd α β) ⊔ (Upd .α .β) | yes refl = inj₂ (Upd α β , Idem (Upd α β))
(Upd α β) ⊔ (Upd .α γ) | no β≠γ with ⟨ α ⟩ ≟ⱽ ⟨ β ⟩
(Upd β .β) ⊔ (Upd .β γ) | no β≠γ | yes refl = inj₂ (Upd β γ , Id₁ (Upd β β) (Upd β γ))
(Upd α β) ⊔ (Upd .α γ) | no β≠γ | no α≠β with ⟨ α ⟩ ≟ⱽ ⟨ γ ⟩
(Upd α β) ⊔ (Upd .α .α) | no β≠γ | no α≠β | yes refl = inj₂ (Upd α β , Id₂ (Upd α β) (Upd α α))
(Upd α β) ⊔ (Upd .α γ) | no β≠γ | no α≠β | no α≠γ 
  = inj₁ (UpdUpd α β γ , UpdUpd (Upd α β) (Upd α γ) (≃-⋍ α≠β) (≃-⋍ α≠γ) (≃-⋍ β≠γ))
Nop ⊔ (Ins α) = inj₂ (Ins α , Id₁ Nop (Ins α))
Nop ⊔ Nop = inj₂ (Nop , Idem Nop)

--------------------------------------------------------------------------------

-- Merge and conficts are exclusive:
-- For any pair of transformations either they are merged or raise a conflict
mergeConflictExclusive : ∀ {as bs cs ds es fs gs hs} {s : Val as bs} {u : Val cs ds} {v : Val es fs} {w : Val gs hs} 
                           {c : Conflict s u v} {x : s ~> u} {y : s ~> v} {z : s ~> w} -> x ⊔ y ↧ z -> ¬ (x ⊔ y ↥ c)
mergeConflictExclusive (Id₁ f y) (UpdUpd .f .y α≠β α≠γ β≠γ) = α≠β refl
mergeConflictExclusive (Id₁ f y) (UpdDel .f .y α≠β) = α≠β refl
mergeConflictExclusive (Id₂ f y) (UpdUpd .f .y α≠β α≠γ β≠γ) = α≠γ refl
mergeConflictExclusive (Id₂ f y) (DelUpd .f .y α≠β) = α≠β refl
mergeConflictExclusive (Idem x) (InsIns .x .x α≠β) = α≠β refl
mergeConflictExclusive (Idem x) (UpdUpd .x .x α≠β α≠γ β≠γ) = β≠γ refl

-- Identity edits with the same type are equal.
edit-≅ : ∀ {as bs} {v : Val as bs} -> (f g : v ~> v) -> f ≅ g
edit-≅ Nop Nop = refl
edit-≅ (Upd α .α) (Upd .α .α) = refl

-- Merges are deterministic.
-- If f ⊔ g ↧ h₁ and f ⊔ g ↧ h₂ then h₁ ≅ h₂.
mergeDeterministic : ∀ {as bs cs ds es fs gs hs is ls} 
                       {a : Val as bs} {b : Val cs ds} {c : Val es fs} {d : Val gs hs} {e : Val is ls} 
                       {f : a ~> b} {g : a ~> c} {h₁ : a ~> d} {h₂ : a ~> e} ->
                       f ⊔ g ↧ h₁ -> f ⊔ g ↧ h₂ -> h₁ ≅ h₂
mergeDeterministic (Id₁ f g) (Id₁ .f .g) = refl
mergeDeterministic (Id₁ f g) (Id₂ .f .g) = edit-≅ g f
mergeDeterministic (Id₁ f .f) (Idem .f) = refl
mergeDeterministic (Id₂ f g) (Id₁ .f .g) = edit-≅ f g
mergeDeterministic (Id₂ f g) (Id₂ .f .g) = refl
mergeDeterministic (Id₂ f .f) (Idem .f) = refl
mergeDeterministic (Idem f) (Id₁ .f .f) = refl
mergeDeterministic (Idem f) (Id₂ .f .f) = refl
mergeDeterministic (Idem f) (Idem .f) = refl

-- Conflicts are deterministic.
-- If x ⊔ y ↥ c₁ and x ⊔ y ↥ c₂ then c₁ ≡ c₂.
conflictDeterministic : ∀ {as bs cs ds es fs} {u : Val as bs} {v : Val cs ds} {w : Val es fs} 
                          {c₁ c₂ : Conflict u v w} {f : u ~> v} {g : u ~> w} -> 
                          f ⊔ g ↥ c₁ -> f ⊔ g ↥ c₂ -> c₁ ≡ c₂
conflictDeterministic (InsIns f g α≠β) (InsIns .f .g α≠β₁) = refl
conflictDeterministic (UpdUpd f g α≠β α≠γ β≠γ) (UpdUpd .f .g α≠β₁ α≠γ₁ β≠γ₁) = refl
conflictDeterministic (UpdDel f g α≠β) (UpdDel .f .g α≠β₁) = refl
conflictDeterministic (DelUpd f g α≠β) (DelUpd .f .g α≠β₁) = refl

--------------------------------------------------------------------------------
-- Minors proofs about the merge data-types

-- If both transformations perform a change and they are merged then they are all the same transformation.
changeAll-≡ : ∀ {as bs cs ds es fs gs hs} {u : Val as bs} {v : Val cs ds} {w : Val es fs} {z : Val gs hs}
                {f : u ~> v} {g : u ~> w} {h : u ~> z} -> Change f -> Change g -> f ⊔ g ↧ h -> f ≅ g × f ≅ h
changeAll-≡ (IsChange v≠w) q (Id₁ f g) = ⊥-elim (v≠w refl)
changeAll-≡ p (IsChange v≠w) (Id₂ f g) = ⊥-elim (v≠w refl)
changeAll-≡ p q (Idem f) = refl , refl

-- An id transformation can never raise a conflict
⊥-IdConflict : ∀ {as bs cs ds} {v : Val as bs} {w : Val cs ds} 
                  {f : v ~> v} {g : v ~> w} {c : Conflict v v w} -> ¬ (f ⊔ g ↥ c)
⊥-IdConflict (UpdUpd f g α≠β α≠γ β≠γ) = α≠β refl
⊥-IdConflict (UpdDel f g α≠β) = α≠β refl

--------------------------------------------------------------------------------
-- Refifies result of Diff3
data _⇓_ : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} -> e₁ ⋎ e₂ -> ES₃ xs -> Set₁ where
  nil : nil ⇓ []
  merge : ∀ {xs ys zs as bs cs ds es fs gs hs} 
            {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (es ++ zs)} {e₃ : ES₃ (as ++ xs)} 
            {p : e₁ ⋎ e₂} {u : Val as bs} {v : Val cs ds} {w : Val es fs} {z : Val gs hs} 
            {f : u ~> v} {g : u ~> w} {h : u ~> z} -> 
            (m : f ⊔ g ↧ h) -> p ⇓ e₃ -> (cons f g p) ⇓ (h ∷ e₃)
  conflict : ∀ {xs ys zs as bs cs ds es fs} 
               {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (es ++ zs)} {e₃ : ES₃ (as ++ xs)}
               {v : Val as bs} {w : Val cs ds} {z : Val es fs} {c : Conflict v w z}
               {f : v ~> w} {g : v ~> z} {p : e₁ ⋎ e₂} -> 
               (u : f ⊔ g ↥ c) -> p ⇓ e₃ -> (cons f g p) ⇓ (c ∷ᶜ e₃)

-- ⇓ is a symmetric relation, module swap for conflicts
⇓-sym : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES₃ xs} {p : e₁ ⋎ e₂} 
            -> p ⇓ e₃ -> (⋎-sym p) ⇓ (sym₃ e₃)
⇓-sym nil = nil
⇓-sym (merge m d) = merge (↧-sym m) (⇓-sym d)
⇓-sym (conflict u d) = conflict (↥-sym u) (⇓-sym d)

-- The symmetric script is actually the same if no conflict is raised
⇓-sym' : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES₃ xs} {p : e₁ ⋎ e₂} -> 
           p ⇓ e₃ -> NoCnf e₃ -> (⋎-sym p) ⇓ e₃
⇓-sym' nil q = nil
⇓-sym' (merge m p) (h ∷ q) = merge (↧-sym m) (⇓-sym' p q)
⇓-sym' (conflict u p) ()

-- A simple type synonym more readable than ⇓:
-- Diff₃ e₁ e₂ e₃ is more intuitive than p ⇓ e₃
Diff₃ : ∀ {xs ys zs} (e₁ : ES xs ys) (e₂ : ES xs zs) {{p : e₁ ⋎ e₂}} -> ES₃ xs -> Set₁
Diff₃ _ _ {{p}} e₃ = p ⇓ e₃

-- Diff₃ e₁ e₂ e₃ implies that the three editscripts originated from the same source.
Diff₃⟪_⟫ : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES₃ xs} {p : e₁ ⋎ e₂} ->
            Diff₃ e₁ e₂ e₃ -> ⟪ e₁ ⟫ ≡ ⟪ e₃ ⟫₃
Diff₃⟪ nil ⟫ = refl
Diff₃⟪ merge {f = Ins α} {h = Ins α₁} m e ⟫ = Diff₃⟪ e ⟫
Diff₃⟪ merge {f = Ins α} {h = Nop} m e ⟫ = Diff₃⟪ e ⟫
Diff₃⟪ merge {f = Del α} {h = Del .α} m e ⟫ rewrite Diff₃⟪ e ⟫ = refl
Diff₃⟪ merge {f = Del α} {h = Upd .α β} m e ⟫ rewrite Diff₃⟪ e ⟫ = refl
Diff₃⟪ merge {f = Upd α β} {h = Del .α} m e ⟫ rewrite Diff₃⟪ e ⟫ = refl
Diff₃⟪ merge {f = Upd α β} {h = Upd .α γ} m e ⟫ rewrite Diff₃⟪ e ⟫ = refl
Diff₃⟪ merge {f = Nop} {h = Ins α} m e ⟫ = Diff₃⟪ e ⟫
Diff₃⟪ merge {f = Nop} {h = Nop} m e ⟫ = Diff₃⟪ e ⟫
Diff₃⟪ conflict (InsIns (Ins α) y α≠β) e ⟫ = Diff₃⟪ e ⟫
Diff₃⟪ conflict (UpdUpd (Upd α β) y α≠β α≠γ β≠γ) e ⟫ rewrite Diff₃⟪ e ⟫ = refl
Diff₃⟪ conflict (UpdDel (Upd α β) y α≠β) e ⟫ rewrite Diff₃⟪ e ⟫ = refl
Diff₃⟪ conflict (DelUpd (Del α) y α≠β) e ⟫ rewrite Diff₃⟪ e ⟫ = refl

--------------------------------------------------------------------------------

-- Merged₃ e₁ e₂ e₃ is the proof that e₃ is well-typed edit script
-- obtained succesfully merging e₁ and e₂.
-- The absence of conflicts and the fact that it is well-typed 
-- are implicit in the fact that e₃ is a ES, and not an ES₃
-- as it happens for Diff₃.
data Merged₃ : ∀ {xs ys zs ws} -> ES xs ys -> ES xs zs -> ES xs ws -> Set₁ where  
  nil : Merged₃ [] [] []
  cons : ∀ {xs ys zs ws as bs cs ds es fs gs hs} 
            {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (es ++ zs)} {e₃ : ES (as ++ xs) (gs ++ ws)} 
            {u : Val as bs} {v : Val cs ds} {w : Val es fs} {z : Val gs hs} 
            {f : u ~> v} {g : u ~> w} {h : u ~> z} -> 
            (m : f ⊔ g ↧ h) -> Merged₃ e₁ e₂ e₃ -> Merged₃ (f ∷ e₁) (g ∷ e₂) (h ∷ e₃)

-- Shows that successful merges are symmetric, i.e. the order of the two input script is not relevant.
Merged₃-sym : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} -> Merged₃ e₁ e₂ e₃ -> Merged₃ e₂ e₁ e₃
Merged₃-sym nil = nil
Merged₃-sym (cons m d) = cons (↧-sym m) (Merged₃-sym d)

-- Since e₁ and e₂ are merged they are aligned.
Merged₃⋎ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} ->
             Merged₃ e₁ e₂ e₃ -> e₁ ⋎ e₂
Merged₃⋎ nil = nil
Merged₃⋎ (cons m d) = cons _ _ (Merged₃⋎ d)

-- Merged₃ can be downgraded in Diff₃
Merged₃-Diff₃ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} ->
                  (m : Merged₃ e₁ e₂ e₃) -> Diff₃ e₁ e₂ {{Merged₃⋎ m}} ⌞ e₃ ⌟ 
Merged₃-Diff₃ nil = nil
Merged₃-Diff₃ (cons m d) = merge m (Merged₃-Diff₃ d)

-- The merged edit script has the same source object as the input edit scripts.
Merged₃⟪_⟫ : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {e₃ : ES xs ws} ->
               Merged₃ e₁ e₂ e₃ -> ⟪ e₁ ⟫ ≡ ⟪ e₃ ⟫
Merged₃⟪_⟫ {e₃ = e₃} d rewrite ⟪⟫-⟪⟫₃ e₃ = Diff₃⟪ Merged₃-Diff₃ d ⟫
