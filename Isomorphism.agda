{-# OPTIONS --safe --without-K #-}

module Isomorphism where

open import Relation.Binary.PropositionalEquality
open import Level

--Adapted from  https://plfa.github.io/Isomorphism/
-- by Wen Kokke and Philip Waddler

infix 0 _↔_
record _↔_ {l1} {l2} (A : Set l1) (B : Set l2) : Set (l1 ⊔ l2) where
  constructor isomorphism
  field
    ito   : A → B
    ifrom : B → A
    from∘to : ∀ (x : A) → ifrom (ito x) ≡ x
    to∘from : ∀ (y : B) → ito (ifrom y) ≡ y

open _↔_ public

irefl : ∀ {l} (A : Set l)  -> A ↔ A
ito (irefl A) x = x
ifrom (irefl A) x = x
from∘to (irefl A) x = refl
to∘from (irefl A) x = refl


isym : ∀ {l1} {l2} {A : Set l1} {B : Set l2} -> A ↔ B -> B ↔ A
ito (isym iso) = ifrom iso
ifrom (isym iso) = ito iso
from∘to (isym iso) = to∘from iso
to∘from (isym iso) = from∘to iso

itrans : ∀ {l1 l2 l3} {A : Set l1} {B : Set l2} {C : Set l3} -> A ↔ B -> B ↔ C -> A ↔ C
ito (itrans AB BC) x = ito BC (ito AB x)
ifrom (itrans AB BC) x = ifrom AB (ifrom BC x)
from∘to (itrans AB BC) x rewrite from∘to BC (ito AB x) = from∘to AB x
to∘from (itrans AB BC) x rewrite to∘from AB (ifrom BC x) = to∘from BC x

liftIso : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} -> A ↔ Lift ℓ₂ A
ito liftIso x = lift x
ifrom liftIso (lift x) = x
from∘to liftIso x = refl
to∘from liftIso (lift x) = refl

infix 0 _↪_
record _↪_ {l1} {l2} (A : Set l1) (B : Set l2) : Set (l1 ⊔ l2) where
  constructor embedding
  field
    eto   : A → B
    efrom : B → A
    efrom∘to : ∀ (x : A) → efrom (eto x) ≡ x
open _↪_ public

-- repr : ∀ {l1} {l2} {A : Set l1} {B : Set l2} -> A ↪ B -> B -> B
-- repr emb x = {!!}
