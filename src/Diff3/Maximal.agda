module Diff3.Maximal where

open import Diff3.Core
open import EditScript.Mapping

open import Data.List

--------------------------------------------------------------------------------

-- Maximal e₁ e₂ e₃ represents the fact that e₃ contains all the changes from e₁ and e₂.
-- We define maximality in terms of the transormations involved.
data Maximal : ∀ {xs ys zs} -> ES xs ys -> ES xs zs -> ES₃ xs -> Set₁ where
  Nil : Maximal [] [] []
  Id₁ : ∀ {as bs cs ds xs ys zs} {v : Val as bs} {w : Val cs ds}
          {e₁ : ES (as ++ xs) (as ++ ys)} {e₂ : ES (as ++ xs) (cs ++ zs)} {e₃ : ES₃ (as ++ xs) } 
          (f : v ~> v) (g : v ~> w) -> Maximal e₁ e₂ e₃ -> Maximal (f ∷ e₁) (g ∷ e₂) (g ∷ e₃)
  Id₂ : ∀ {as bs cs ds xs ys zs} {v : Val as bs} {w : Val cs ds}
          {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (as ++ zs)} {e₃ : ES₃ (as ++ xs) } 
          (f : v ~> w) (g : v ~> v) -> Maximal e₁ e₂ e₃ -> Maximal (f ∷ e₁) (g ∷ e₂) (f ∷ e₃)
  Idem : ∀ {as bs cs ds xs ys zs} {u : Val as bs} {v : Val cs ds} 
           {e₁ : ES (as ++ xs) (cs ++ ys)} {e₂ : ES (as ++ xs) (cs ++ zs)} {e₃ : ES₃ (as ++ xs) } 
           (f : u ~> v) -> Maximal e₁ e₂ e₃ -> Maximal (f ∷ e₁) (f ∷ e₂) (f ∷ e₃)
 
--------------------------------------------------------------------------------

-- A Diff₃ run that does not raise any conflict is Maximal.
Diff₃-maximal : ∀ {xs ys zs} {e₁ : ES xs ys} {e₂ : ES xs zs} {{p : e₁ ⋎ e₂}} {e₃ : ES₃ xs} -> 
                  Diff₃ e₁ e₂ e₃ -> NoCnf e₃ -> Maximal e₁ e₂ e₃
Diff₃-maximal nil [] = Nil
Diff₃-maximal (merge (Id₁ f g) d) (.g ∷ q) = Id₁ f g (Diff₃-maximal d q)
Diff₃-maximal (merge (Id₂ f g) d) (.f ∷ q) = Id₂ f g (Diff₃-maximal d q)
Diff₃-maximal (merge (Idem f) d) (.f ∷ q) = Idem f (Diff₃-maximal d q)

-- Similarly it holds for successful merges.
Merged₃-maximal : ∀ {xs ys zs ws} {e₁ : ES xs ys} {e₂ : ES xs zs} {{p : e₁ ⋎ e₂}} {e₃ : ES xs ws} -> 
                    Merged₃ e₁ e₂ e₃ -> Maximal e₁ e₂ ⌞ e₃ ⌟
Merged₃-maximal m = Diff₃-maximal (Merged₃-Diff₃ m) (ES-NoCnf _)
