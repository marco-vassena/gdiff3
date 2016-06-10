module Diff.Core where

open import EditScript.Core public 
open import EditScript.Aligned public
open import Lemmas 

open import Data.Unit hiding (_≤?_ ; _≤_)
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- Diff x y e denotes that e is the edit script that transform x in y.
data Diff : ∀ {xs ys} ->  DList xs -> DList ys -> ES xs ys -> Set₁ where
  End : Diff [] [] []
  Del : ∀ {as a xs ys} {e : ES (as ++ xs) ys} {ts₁ : DList as} {ts₂ : DList xs} {ts : DList ys}
        ->  (α : View as a) -> Diff (ts₁ +++ ts₂) ts e -> Diff (Node α ts₁ ∷ ts₂ ) ts (Del α ∷ e)
  Upd : ∀ {bs xs ys as a} {e : ES (as ++ xs) (bs ++ ys)} {ts₁ : DList as} {ts₂ : DList xs} {ts₃ : DList bs} {ts₄ : DList ys}
      -> (α : View as a) (β : View bs a) -> Diff (ts₁ +++ ts₂) (ts₃ +++ ts₄) e 
      -> Diff (Node α ts₁ ∷ ts₂) (Node β ts₃ ∷ ts₄) (Upd α β ∷ e)
  Ins : ∀ {bs b xs ys} {e : ES xs (bs ++ ys)} {ts₁ : DList xs} {ts₂ : DList bs} {ts₃ : DList ys}   
        -> (β : View bs b) -> Diff ts₁ (ts₂ +++ ts₃) e -> Diff ts₁ (Node β ts₂ ∷ ts₃) (Ins β ∷ e)
  Nop : ∀ {xs ys} {ts₁ : DList xs} {ts₂ : DList ys} {e : ES xs ys} -> Diff ts₁ ts₂ e -> Diff ts₁ ts₂ (Nop ∷ e)

-- Once more we need to have an explicit separate function to deal with dsplit.
-- Simple rewriting fails because (probably), the underlying with clause becomes ill-typed.
Diff-⟦⟧ : ∀ {xs} {{ys zs}} {t₀ : DList xs} (e : ES xs (ys ++ zs)) ->
              let ds₁ , ds₂ = dsplit ⟦ e ⟧ in Diff t₀ ⟦ e ⟧ e -> Diff t₀ (ds₁ +++ ds₂) e
Diff-⟦⟧ e d 
  rewrite dsplit-lemma ⟦ e ⟧ = d

Diff-⟪⟫ : ∀ {{xs ys}} {zs} {t₁ : DList zs} (e : ES (xs ++ ys) zs) ->
              let ds₁ , ds₂ = dsplit ⟪ e ⟫ in Diff ⟪ e ⟫ t₁ e -> Diff (ds₁ +++ ds₂) t₁ e
Diff-⟪⟫ e d 
  rewrite dsplit-lemma ⟪ e ⟫ = d

-- From an edit script we can produce a Diff object where the input and output
-- object correspond to the source and target trees of the edit script.
mkDiff : ∀ {xs ys} (e : ES xs ys) -> Diff ⟪ e ⟫ ⟦ e ⟧ e
mkDiff (Ins α ∷ e) = Ins α (Diff-⟦⟧ e (mkDiff e))
mkDiff (Del α ∷ e) = Del α (Diff-⟪⟫ e (mkDiff e))
mkDiff (Upd α β ∷ e) = Upd α β (Diff-⟦⟧ e (Diff-⟪⟫ e (mkDiff e)))
mkDiff (Nop ∷ e) = Nop (mkDiff e)
mkDiff [] = End

open import Function

≡-split : ∀ {xs ys} (a : DList xs) (b : DList ys) (c : DList (xs ++ ys)) -> (a +++ b) ≡ c ->
        let ds₁ , ds₂ = dsplit c in a ≡ ds₁ × b ≡ ds₂
≡-split [] b .b refl = refl , refl
≡-split (t ∷ a) b (.t ∷ .(a +++ b)) refl with proj₁ (dsplit (a +++ b)) | proj₂ (dsplit (a +++ b)) | ≡-split a b (a +++ b) refl
≡-split (t ∷ a) b (.t ∷ .(a +++ b)) refl | .a | .b | refl , refl = refl , refl
 

-- Shows that the source x in Diff x y e corresponds to ⟪ e ⟫, the source object of the edit script.
mkDiff⟪_⟫ : ∀ {xs ys} {t₀ : DList xs} {t₁ : DList ys} {e : ES xs ys} -> Diff t₀ t₁ e -> t₀ ≡ ⟪ e ⟫
mkDiff⟪ End ⟫ = refl
mkDiff⟪ Del {e = e} {ts₁ = ts₁} {ts₂ = ts₂} α d ⟫ with ≡-split ts₁ ts₂ ⟪ e ⟫ mkDiff⟪ d ⟫
mkDiff⟪ Del α d ⟫ | refl , refl = refl
mkDiff⟪ Upd {e = e} {ts₁ = ts₁} {ts₂ = ts₂} α β d ⟫ with ≡-split ts₁ ts₂ ⟪ e ⟫ mkDiff⟪ d ⟫
mkDiff⟪ Upd α β d ⟫ | refl , refl = refl
mkDiff⟪ Ins β d ⟫ = mkDiff⟪ d ⟫
mkDiff⟪ Nop d ⟫ = mkDiff⟪ d ⟫

-- Shows that the target y in Diff x y e corresponds to ⟦ e ⟧, the target object of the edit script.
mkDiff⟦_⟧ : ∀ {xs ys} {t₀ : DList xs} {t₁ : DList ys} {e : ES xs ys} -> Diff t₀ t₁ e -> t₁ ≡ ⟦ e ⟧
mkDiff⟦ End ⟧ = refl
mkDiff⟦ Del α d ⟧ = mkDiff⟦ d ⟧
mkDiff⟦ Upd {e = e} {ts₃ = ts₃} {ts₄ = ts₄} α β d ⟧  with ≡-split ts₃ ts₄ ⟦ e ⟧ mkDiff⟦ d ⟧
mkDiff⟦ Upd α β d ⟧ | refl , refl = refl
mkDiff⟦ Ins {e = e} {ts₂ = ts₂} {ts₃ = ts₃} β d ⟧ with ≡-split ts₂ ts₃ ⟦ e ⟧ mkDiff⟦ d ⟧
mkDiff⟦ Ins β d ⟧ | refl , refl = refl
mkDiff⟦ Nop d ⟧ = mkDiff⟦ d ⟧

--------------------------------------------------------------------------------

-- If two edit scripts e₁ and e₂ are derived from the same source object, then e₁ ~ e₂.
Diff⋎ : ∀ {xs ys zs} {x : DList xs} {y : DList ys} {z : DList zs} {e₁ : ES xs ys} {e₂ : ES xs zs} 
        -> Diff x y e₁ -> Diff x z e₂ -> e₁ ~ e₂
Diff⋎ End End = Align stop stop nil
Diff⋎ End (Ins β d₂) with Diff⋎ End d₂
Diff⋎ End (Ins β d₂) | Align a b p = Align (nop a) (cons (Ins β) b) (cons Nop (Ins β) p)
Diff⋎ End (Nop d₂) with Diff⋎ End d₂
Diff⋎ End (Nop d₂) | Align a b p = Align (nop a) (cons Nop b) (cons Nop Nop p)
Diff⋎ (Del α d₁) (Del .α d₂) with Diff⋎ d₁ d₂
Diff⋎ (Del α d₁) (Del .α d₂) | Align a b p = Align (cons (Del α) a) (cons (Del α) b) (cons (Del α) (Del α) p)
Diff⋎ (Del α d₁) (Upd .α β d₂) with Diff⋎ d₁ d₂
Diff⋎ (Del α d₁) (Upd .α β d₂) | Align a b p = Align (cons (Del α) a) (cons (Upd α β) b) (cons (Del α) (Upd α β) p)
Diff⋎ (Del α d₁) (Ins β d₂) with Diff⋎ (Del α d₁) d₂
Diff⋎ (Del α d₁) (Ins β d₂) | Align a b p = Align (nop a) (cons (Ins β) b) (cons Nop (Ins β) p)
Diff⋎ (Del α d₁) (Nop d₂) with Diff⋎ (Del α d₁) d₂
Diff⋎ (Del α d₁) (Nop d₂) | Align a b p = Align (nop a) (cons Nop b) (cons Nop Nop p)
Diff⋎ (Upd α β d₁) (Del .α d₂) with Diff⋎ d₁ d₂
Diff⋎ (Upd α β d₁) (Del .α d₂) | Align a b p = Align (cons (Upd α β) a) (cons (Del α) b) (cons (Upd α β) (Del α) p)
Diff⋎ (Upd α β d₁) (Upd .α γ d₂) with Diff⋎ d₁ d₂
Diff⋎ (Upd α β d₁) (Upd .α γ d₂) | Align a b p = Align (cons (Upd α β) a) (cons (Upd α γ) b) (cons (Upd α β) (Upd α γ) p)
Diff⋎ (Upd {ts₃ = ts₃} {ts₄ = ts₄} α β d₁) (Ins γ d₂) with Diff⋎ (Upd {ts₃ = ts₃} {ts₄ = ts₄} α β d₁) d₂
Diff⋎ (Upd α β d₁) (Ins γ d₂) | Align a b p = Align (nop a) (cons (Ins γ) b) (cons Nop (Ins γ) p)
Diff⋎ (Upd {ts₃ = ts₃} {ts₄ = ts₄} α β d₁) (Nop d₂) with Diff⋎ (Upd {ts₃ = ts₃} {ts₄ = ts₄} α β d₁) d₂
Diff⋎ (Upd α β d₁) (Nop d₂) | Align a b p = Align (nop a) (cons Nop b) (cons Nop Nop p)
Diff⋎ (Ins β d₁) End with Diff⋎ d₁ End
Diff⋎ (Ins β d₁) End | Align a b p = Align (cons (Ins β) a) (nop b) (cons (Ins β) Nop p)
Diff⋎ (Ins β d₁) (Del α d₂) with Diff⋎ d₁ (Del α d₂) 
Diff⋎ (Ins β d₁) (Del α d₂) | Align a b p = Align (cons (Ins β) a) (nop b) (cons (Ins β) Nop p)
Diff⋎ (Ins β d₁) (Upd {ts₃ = ts₃} {ts₄ = ts₄} α γ d₂) with Diff⋎ d₁ (Upd {ts₃ = ts₃} {ts₄ = ts₄} α γ d₂)
Diff⋎ (Ins β d₁) (Upd α γ d₂) | Align a b p = Align (cons (Ins β) a) (nop b) (cons (Ins β) Nop p)
Diff⋎ (Ins β d₁) (Ins γ d₂) with Diff⋎ d₁ d₂
Diff⋎ (Ins β d₁) (Ins γ d₂) | Align a b p = Align (cons (Ins β) a) (cons (Ins γ) b) (cons (Ins β) (Ins γ) p)
Diff⋎ (Ins β d₁) (Nop d₂) with Diff⋎ d₁ d₂
Diff⋎ (Ins β d₁) (Nop d₂) | Align a b p = Align (cons (Ins β) a) (cons Nop b) (cons (Ins β) Nop p)
Diff⋎ (Nop d₁) End with Diff⋎ d₁ End
Diff⋎ (Nop d₁) End | Align a b p = Align (cons Nop a) (nop b) (cons Nop Nop p)
Diff⋎ (Nop d₁) (Del α d₂) with Diff⋎ d₁ (Del α d₂)
Diff⋎ (Nop d₁) (Del α d₂) | Align a b p = Align (cons Nop a) (nop b) (cons Nop Nop p)
Diff⋎ (Nop d₁) (Upd {ts₃ = ts₃} {ts₄ = ts₄} α β d₂) with Diff⋎ d₁ (Upd {ts₃ = ts₃} {ts₄ = ts₄} α β d₂)
Diff⋎ (Nop d₁) (Upd α β d₂) | Align a b p = Align (cons Nop a) (nop b) (cons Nop Nop p)
Diff⋎ (Nop d₁) (Ins β d₂) with Diff⋎ d₁ d₂
Diff⋎ (Nop d₁) (Ins β d₂) | Align a b p = Align (cons Nop a) (cons (Ins β) b) (cons Nop (Ins β) p)
Diff⋎ (Nop d₁) (Nop d₂) with Diff⋎ d₁ d₂
Diff⋎ (Nop d₁) (Nop d₂) | Align a b p = Align (cons Nop a) (cons Nop b) (cons Nop Nop p)

Diff⋎nec : ∀ {xs ys zs} {x₁ x₂ : DList xs} {y : DList ys} {z : DList zs} {e₁ : ES xs ys} {e₂ : ES xs zs} 
        -> Diff x₁ y e₁ -> Diff x₂ z e₂ -> e₁ ⋎ e₂ -> x₁ ≡ x₂
Diff⋎nec d₁ d₂ p rewrite
  mkDiff⟪ d₁ ⟫ | mkDiff⟪ d₂ ⟫ = ⋎-⟪⟫ p
