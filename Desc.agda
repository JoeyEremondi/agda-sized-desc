{-# OPTIONS --safe  --no-sized --prop #-}

open import Data.Empty
open import Data.Unit.Polymorphic renaming (⊤ to 𝟙)
open import Data.Bool
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Level renaming ( zero to lzero ; suc to lsuc)


module Desc {ℓ}  where

----------------------------------------------------------------------

data Desc  : Set (lsuc ℓ) where
  End : Desc
  Rec : Desc → Desc
  HRec : (A : Set ℓ) → (B : Desc ) → Desc
  Arg : (A : Set ℓ) → (B : A → Desc ) → Desc

----------------------------------------------------------------------
import Ord
open import Ord {lsuc ℓ} (Set ℓ) (Lift _) -- using (Ord ; _≤ₒ_ ; _<ₒ_ ; ≤ₒ-trans ; ≤ₒ-refl; ↑ ; Z ; lim  )
open Ord.UpperBound (Set ℓ) (Lift _) (Lift _ Bool) (λ { (lift (lift l)) → l}) (lift (lift true)) (lift (lift false)) refl refl
Size = Ord


El : Desc -> Set ℓ → Set ℓ
El End X = 𝟙
El (Rec B) X = Σ[ x ∈ X ] El B X
El (HRec A B) X = Σ[ f ∈ (A → X) ] (El B X)
El (Arg A B) X = Σ[ a ∈ A ] El (B a) X

data μ (D : Desc ) : Set ℓ where
    init : El D (μ D) -> μ D

size : ∀ {D : Desc} -> μ D -> Size
size {D = D} (init x) = ↑ (sizeHelper D D x)
  where
    sizeHelper : ∀ D E → El D (μ E) → Size
    sizeHelper End E x = Z
    sizeHelper (Rec D) E (x , y) = size {D = E} x ⊔lim sizeHelper _ E y -- size x ⊔lim {!!}
    sizeHelper (HRec A D) E (f , x) = (lim A λ (lift a) → size {D = E} (f a)) ⊔lim (sizeHelper _ E x)
    sizeHelper (Arg A B) E (a , x) = sizeHelper _ E x
-- sizeHelper {D = .(End _)} ElEnd = Z
-- sizeHelper {D = .(Rec _)} (ElRec x x₁) = ((size x) ⊔lim  (sizeHelper x₁))
-- sizeHelper {D = (Ref A _)} (ElRef f x) = ((lim A (λ (lift a) -> size (f a))) ⊔lim (sizeHelper x))
-- sizeHelper {D = .(Arg _ _)} (ElArg a x) = sizeHelper x

-- _<D_ : ∀ {D} → μ D → μ D → Set (lsuc ℓ)
-- x <D y = size x <ₒ size y

-- open import Induction.WellFounded


-- genRec : ∀ {ℓ'} {D : Desc} → (P : μ D → Set ℓ') → (∀ x → (∀ y → y <D x → P y) → P x) → ∀ x → P x
-- genRec P rec x = helper (x , refl)
--   where
--     recHelper : _
--     recHelper sz rec' (x , refl) = rec x λ y lt → rec' (size y) lt (y , refl)
--     helper = All.wfRec ordWf _ (λ sz → ((x , _) : ∃[ x ](size x ≡ sz)) → P x) recHelper (size x)
