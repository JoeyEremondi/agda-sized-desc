{-# OPTIONS --safe --without-K --no-sized  #-}

open import Data.Empty
open import Data.Unit.Polymorphic renaming (⊤ to 𝟙)
open import Data.Bool
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Level renaming ( zero to lzero ; suc to lsuc)


module DescIR {ℓ}  where

--Based off of http://spire-lang.org/blog/2014/08/04/inductive-recursive-descriptions/

----------------------------------------------------------------------
-- Generic description of an inductive recursive type
-- 
data Desc  : Set (lsuc ℓ) where
  End : (o : Set ℓ) → Desc
  Rec : (B : Set ℓ → Desc ) → Desc
  Ref : (A : Set ℓ)  (B : (o : (a : A) → Set ℓ ) → Desc ) → Desc
  Arg : (A : Set ℓ) (B : A → Desc ) → Desc

----------------------------------------------------------------------
import Ord
open import Ord {lsuc ℓ} (Set ℓ) (Lift _) -- using (Ord ; _≤ₒ_ ; _<ₒ_ ; ≤ₒ-trans ; ≤ₒ-refl; ↑ ; Z ; lim  )
open Ord.UpperBound (Set ℓ) (Lift _) (Lift _ Bool) (λ { (lift (lift l)) → l}) (lift (lift true)) (lift (lift false)) refl refl

data El (X : Set (lsuc ℓ)) (Y : X -> Set ℓ) : Desc -> Set (lsuc ℓ) where
      ElEnd : ∀ {o } -> El X Y (End o)
      ElRec : ∀ {B } -> (x : X ) ->  El X Y (B (Y x))   -> El X Y (Rec B)
      ElRef : ∀ {A B }  ->  (f : (a : A) ->  X ) -> El X Y (B (λ a → Y (f a)))  -> El X Y (Ref A B )
      ElArg : ∀ {A B } -> (a : A) -> El X Y (B a)  -> El X Y (Arg A B)

data SimpleSig (X : Set ℓ) (Y :  Set ℓ) : Set ℓ where
  SigPair : (x : X) -> Y -> SimpleSig X Y


data μ (D : Desc ) : Set (lsuc ℓ)
foldO : (D : Desc ) → μ D  → Set ℓ
foldsO : ∀  (D E : Desc ) → El (μ E) (foldO E) D  → Set ℓ

data μ D where
    init : El (μ D) (foldO D) D -> μ D

foldO D (init xs ) = foldsO D D xs

foldsO (End o) E (ElEnd) = o
foldsO (Rec B) E (ElRec x  xs) = foldsO (B (foldO E x )) E xs
foldsO (Ref A B ) E (ElRef f xs) = foldsO (B ( λ a -> foldO E (f a))) E xs
foldsO (Arg A B) E (ElArg a  xs) = foldsO (B a) E xs



size : ∀ {D : Desc} -> μ D -> Ord
size (init x) = ↑ (sizeHelper x)
  where
    sizeHelper : ∀ {D E : Desc} ->  El (μ E) (foldO E) D -> Ord
    sizeHelper {D = .(End _)} ElEnd = Z
    sizeHelper {D = .(Rec _)} (ElRec x x₁) = ((size x) ⊔lim  (sizeHelper x₁))
    sizeHelper {D = (Ref A _)} (ElRef f x) = ((lim A (λ (lift a) -> size (f a))) ⊔lim (sizeHelper x))
    sizeHelper {D = .(Arg _ _)} (ElArg a x) = sizeHelper x

_<D_ : ∀ {D} → μ D → μ D → Set (lsuc ℓ)
x <D y = size x <ₒ size y

open import Induction.WellFounded


genRec : ∀ {ℓ'} {D : Desc} → (P : μ D → Set ℓ') → (∀ x → (∀ y → y <D x → P y) → P x) → ∀ x → P x
genRec P rec x = helper (x , refl)
  where
    recHelper : _
    recHelper sz rec' (x , refl) = rec x λ y lt → rec' (size y) lt (y , refl)
    helper = All.wfRec ordWf _ (λ sz → ((x , _) : ∃[ x ](size x ≡ sz)) → P x) recHelper (size x)
