{-# OPTIONS --safe --without-K  #-}

--Some inspiration from https://github.com/martijnvermaat/infinitary-rewriting-coq/blob/master/Ordinal.v

open import Agda.Primitive
open import Induction.WellFounded
open import Relation.Binary.PropositionalEquality
module Ord {ℓ} (ℂₒ : Set ℓ) (⟦_⟧ₒ : ℂₒ -> Set ℓ ) where

data Ord  : Set ℓ  where
  Z : Ord
  ↑ : Ord   -> Ord
  lim : (c : ℂₒ) -> (⟦ c ⟧ₒ -> Ord   ) -> Ord

data _≤ₒ_  : Ord -> Ord -> Set ( ℓ) where
  Z≤ : ∀ {o} -> Z ≤ₒ o
  ↑≤ : ∀ {o1 o2} -> o1 ≤ₒ o2 -> (↑ o1) ≤ₒ (↑ o2)
  ↑≤' : ∀ {o1 o2} -> o1 ≤ₒ o2 -> ( o1) ≤ₒ (↑ o2)
  lim≤ : ∀ (A : ℂₒ) (f1 f2 : ⟦ A ⟧ₒ -> Ord)  -> (∀ a -> f1 a ≤ₒ f2 a ) -> lim A f1 ≤ₒ lim A f2
  ≤lim : ∀ {o}{ A : ℂₒ} (f : ⟦ A ⟧ₒ -> Ord) -> ((a : _) -> f a ≤ₒ o) ->  lim A f ≤ₒ o
  inlim≤ : ∀ {o } { A : ℂₒ} (f : ⟦ A ⟧ₒ -> Ord)  -> (a : _) -> o ≤ₒ (f a) -> o ≤ₒ lim A f
  -- lim↑ : ∀ {o}{ A : ℂₒ} (f : ⟦ A ⟧ₒ -> Ord) -> o ≤ₒ ↑ (lim A f) -> o ≤ₒ lim A (λ x -> ↑ (f x))



_<ₒ_ :  Ord  -> Ord -> Set ( ℓ)
x <ₒ y = ↑ x ≤ₒ y

≤ₒ-refl : ∀  {o : Ord } -> o ≤ₒ o
≤ₒ-refl {o = Z} = Z≤
≤ₒ-refl {o = ↑ o} = ↑≤ ≤ₒ-refl
≤ₒ-refl {o = lim A x} = lim≤ A x x (λ a → ≤ₒ-refl)

↑> : ∀  {o : Ord } -> o ≤ₒ ↑ o
↑> {o = Z} = Z≤
↑> {o = ↑ o} = ↑≤ ↑>
↑> {o = lim A x} = ↑≤' ≤ₒ-refl



<ₒ-implies-≤ₒ : ∀  {o1 o2 : Ord } -> o1 <ₒ o2 -> o1 ≤ₒ o2
<ₒ-implies-≤ₒ {o1 = Z} (↑≤ lt) = Z≤
<ₒ-implies-≤ₒ {o1 = o1} (↑≤' lt) = ↑≤' (<ₒ-implies-≤ₒ lt)
<ₒ-implies-≤ₒ {o1 = ↑ o1} (↑≤ lt) = ↑≤ (<ₒ-implies-≤ₒ lt)
<ₒ-implies-≤ₒ {o1 = lim A x} (↑≤ lt) = ↑≤' lt
<ₒ-implies-≤ₒ (inlim≤ f a lt) = inlim≤ f a (<ₒ-implies-≤ₒ lt)

invert-↑≤ : ∀ {o1 o2} -> ↑ o1 ≤ₒ ↑ o2 -> o1 ≤ₒ o2
invert-↑≤ (↑≤ lt) = lt
invert-↑≤ (↑≤' lt) = <ₒ-implies-≤ₒ lt


≤ₒ-trans : ∀  {o1 o2 o3 : Ord } -> o1 ≤ₒ o2 -> o2 ≤ₒ o3 -> o1 ≤ₒ o3
≤ₒ-trans Z≤ lt2 = Z≤
≤ₒ-trans lt1 (↑≤' lt2) = ↑≤' (≤ₒ-trans lt1 lt2)
≤ₒ-trans (↑≤' lt1) (↑≤ lt2) = ↑≤' (≤ₒ-trans lt1 lt2)
≤ₒ-trans (↑≤' lt1) (inlim≤ f a lt2) = ≤ₒ-trans lt1 (inlim≤ _ _ (<ₒ-implies-≤ₒ lt2))
≤ₒ-trans (↑≤ lt1) (↑≤ lt2) = ↑≤ (≤ₒ-trans lt1 lt2)
≤ₒ-trans (↑≤ lt1) (inlim≤ _ a lt2) = inlim≤ _ _ (≤ₒ-trans (↑≤ lt1) lt2)
≤ₒ-trans (lim≤ A f1 f2 x) (lim≤ .A .f2 f3 x₁) = lim≤ A f1 f3 (λ a → ≤ₒ-trans (x a) (x₁ a))
≤ₒ-trans lt1 (inlim≤ f a lt2) = inlim≤ _ _ (≤ₒ-trans lt1 lt2)
≤ₒ-trans (inlim≤ f a lt1) (lim≤ _ .f f2 x) = inlim≤ f2 a (≤ₒ-trans lt1 (x a))
≤ₒ-trans (lim≤ A f1 f2 x) (≤lim .f2 x₁) = ≤lim f1 (λ a → ≤ₒ-trans (x a) (x₁ a))
≤ₒ-trans (≤lim f x) Z≤ = ≤lim f (λ a -> ≤ₒ-trans (x a) Z≤)
≤ₒ-trans (≤lim f x) (↑≤ lt2) = ≤lim f (λ a -> ≤ₒ-trans (x a) (↑≤ lt2))
≤ₒ-trans (≤lim f x) (lim≤ A f1 f2 x₁) = ≤lim f (λ a → ≤ₒ-trans (x a) (lim≤ A f1 f2 x₁))
≤ₒ-trans (≤lim f x) (≤lim f₁ x₁) = ≤lim f (λ a -> ≤ₒ-trans (x a) (≤lim f₁ x₁))
≤ₒ-trans (inlim≤ f a lt1) (≤lim .f x) = ≤ₒ-trans lt1 (x a)


ordWf : WellFounded (_<ₒ_ )
ordWf o = acc (go o)
  where
    go : (o1 o2 : Ord) -> o2 <ₒ o1 -> (Acc _<ₒ_) o2
    go (↑ o1) o2 (↑≤ lt) = acc λ o3 lt' -> go o1 o3 (≤ₒ-trans lt' lt)
    go .(lim _ _) o2 (inlim≤ f a lt)  = acc λ o4 lt' -> go _ _ (≤ₒ-trans lt' (<ₒ-implies-≤ₒ lt))
    go (↑ o1) o2 (↑≤' lt) = acc λ o3 lt' -> go o1 _ (≤ₒ-trans (↑≤ (<ₒ-implies-≤ₒ lt')) lt)
    -- acc (λ o4 lt' -> go (f a) _ (≤ₒ-trans lt' {!lt!}))




open import Data.Bool
open import Level

module UpperBound (𝔹 : ℂₒ) (toBool : ⟦ 𝔹 ⟧ₒ -> Bool) (𝔹T 𝔹F :  ⟦ 𝔹 ⟧ₒ) (eqT : toBool 𝔹T ≡ true) (eqF : toBool 𝔹F ≡ false) where

  -- substₚ : ∀ l {!!}
  -- substₚ = {!subst!}


  bif : ∀ {ℓ'} {A : Set ℓ'} -> A -> A -> ⟦ 𝔹 ⟧ₒ -> A
  bif x y arg with toBool arg
  ... | true = x
  ... | false = y


  b≤L : ∀  {x y : Ord} {arg} -> arg ≡ 𝔹T -> x ≤ₒ bif x y arg
  b≤L {arg = arg} pf with toBool arg | inspect toBool arg
  ... | true | _ =  ≤ₒ-refl
  b≤L {arg = arg} refl | false | [ eq ] with () <- trans (sym eqT) eq



  b≤R : ∀ {x y : Ord} {arg} -> arg ≡ 𝔹F -> y ≤ₒ bif x y arg
  b≤R {arg = arg} pf with toBool arg | inspect toBool arg
  ... | false | _ =  ≤ₒ-refl
  b≤R {arg = arg} refl | true | [ eq ] with () <- trans (sym eqF) eq

  _⊔lim_ :  (o1 o2 : Ord ) -> Ord
  o1 ⊔lim o2  = lim 𝔹 (bif o1 o2)

  ⊔lim-L : ∀ {o1 o2} -> o1 ≤ₒ (o1 ⊔lim o2)
  ⊔lim-L {o1} {o2}  = inlim≤ (bif o1 o2) 𝔹T (b≤L refl) -- inlim≤ (bif o1 o2) 𝔹T (subst (λ x → o1 ≤ₒ x) (sym (bifL refl)) ≤ₒ-refl)

  ⊔lim-R : ∀ {o1 o2} -> o2 ≤ₒ (o1 ⊔lim o2)
  ⊔lim-R {o1} {o2}  =  inlim≤ (bif o1 o2) 𝔹F (b≤R refl)

  ⊔lim-max : ∀  {o1 o2 o3 : Ord } -> (o1 ≤ₒ o3) -> (o2 ≤ₒ o3) -> ((o1 ⊔lim o2) ≤ₒ o3)
  ⊔lim-max lt1 lt2  = ≤lim _ ret
    where
      ret : (a : ⟦ 𝔹 ⟧ₒ) → bif _ _ a ≤ₒ _
      ret b with toBool b
      ... | true = lt1
      ... | false = lt2

  ⊔lim-commut : ∀ {o1 o2} -> (o1 ⊔lim o2) ≤ₒ (o2 ⊔lim o1)
  ⊔lim-commut = ⊔lim-max ⊔lim-R ⊔lim-L

module Sized (A : Set ℓ) (size : A -> Ord) where




  record Sized (bound : Ord) :   Set ℓ where
    constructor sized
    field
      erase : A
      eraseLt : (size erase ≤ₒ bound)
    -- sized : ∀ {sz} -> (x : A) -> (size x ≤ₚ sz) -> Sized sz

  open Sized public

  -- sized-inj : ∀ {x y : A} {sz} {lt1 : size x ≤ₒ sz} {lt2 : size y ≤ₒ sz} -> x ≡ y -> sized x lt1 ≡ sized y lt2
  -- sized-inj refl = ?

  toSized : ∀ (x : A) -> Sized (size x)
  toSized x = sized x ( ≤ₒ-refl)

  liftSized : ∀ {sz1 sz2} -> (sz1 ≤ₒ sz2) -> Sized sz1 -> Sized sz2
  liftSized lt1 (sized x lt2) = sized x  (≤ₒ-trans lt2 lt1)


  eraseEmbed : ∀ (x : A) -> erase (toSized x) ≡ x
  eraseEmbed x = refl

  eraseEmbed' : ∀ (x y : A) -> x ≡ y ->  erase (toSized x) ≡ y
  eraseEmbed' x y refl = refl

  liftSizedErase : ∀ {sz1 sz2} -> (lt : sz1 ≤ₒ sz2) -> (x : Sized sz1) -> erase (liftSized lt x) ≡ erase x
  liftSizedErase lt (sized x _) = refl

  -- liftSizedIrrel : ∀ {sz1 sz2} -> .(lt1 lt2 : sz1 ≤ₒ sz2) -> (x : Sized sz1) -> (liftSized lt1 x) ≡ (liftSized lt2 x)
  -- liftSizedIrrel lt1 lt2 (sized x _) = refl

  -- liftSizedCompose :  ∀ {sz1 sz2 sz3} -> .(lt12 : sz1 ≤ₒ sz2) -> .(lt23 : sz2 ≤ₒ sz3) -> .(lt13 : sz1 ≤ₒ sz3)
  --   -> (x : Sized sz1) -> liftSized lt23 (liftSized lt12 x) ≡ liftSized lt13 x
  -- liftSizedCompose _ _ _ (sized x _) = refl

  -- sizedErase : ∀ {x} lt -> sized (erase x) lt ≡ sized

--Over-approximation of +
-- _+ₒ_ :  Ord  -> Ord -> Ord
-- Z +ₒ o' = o'
-- o +ₒ Z = o
-- ↑ o +ₒ ↑ o' = ↑ (o +ₒ o')
-- o +ₒ o' = lim (Lift _ Bool) (λ {(lift true) -> o ; (lift false) -> o'})

-- +<ₒL : ∀  {o1 o2 : Ord } -> o1 ≤ₒ (o1 +ₒ o2)
-- +<ₒL {o1 = Z} {o2} = Z≤
-- +<ₒL {o1 = ↑ o1} {↑ o2} = ↑≤ +<ₒL
-- +<ₒL {o1 = o1} {o2} = {!!}

-- +<ₒR : ∀  {o1 o2 : Ord } -> o2 ≤ₒ (o1 +ₒ o2)
-- +<ₒR {o1 = Z} {o2} = ≤ₒ-refl
-- +<ₒR {o1 = ↑ o1} {↑ o2} = ↑≤' +<ₒR
-- +<ₒR {o1 = o1} {o2} = {!!}


-- +ₒ-max : ∀  {o1 o2 o3 : Ord } -> (o1 ≤ₒ o3) -> (o2 ≤ₒ o3) -> ((o1 +ₒ o2) ≤ₒ o3)
-- +ₒ-max {o1 = Z} {o2} {o3} lt1 lt2 = lt2
-- +ₒ-max {o1 = ↑ o1} {↑ o2} {o3} lt1 lt2 = {!!}
-- +ₒ-max {o1 = o1} {o2} {o3} lt1 lt2 = {!!} -- ≤lim _ λ { (lift false) → lt2 ; (lift true) → lt1}
