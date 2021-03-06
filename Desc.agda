{-# OPTIONS --safe  --no-sized --prop #-}

open import Data.Empty
open import Data.Unit.Polymorphic renaming (β€ to π)
open import Data.Bool
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Level renaming ( zero to lzero ; suc to lsuc)


module Desc {β}  where

----------------------------------------------------------------------

data Desc  : Set (lsuc β) where
  End : Desc
  Rec : Desc β Desc
  HRec : (A : Set β) β (B : Desc ) β Desc
  Arg : (A : Set β) β (B : A β Desc ) β Desc

----------------------------------------------------------------------
import Ord
open import Ord {lsuc β} (Set β) (Lift _) -- using (Ord ; _β€β_ ; _<β_ ; β€β-trans ; β€β-refl; β ; Z ; lim  )
open Ord.UpperBound (Set β) (Lift _) (Lift _ Bool) (Ξ» { (lift (lift l)) β l}) (lift (lift true)) (lift (lift false)) refl refl
Size = Ord


El : Desc -> Set β β Set β
El End X = π
El (Rec B) X = Ξ£[ x β X ] El B X
El (HRec A B) X = Ξ£[ f β (A β X) ] (El B X)
El (Arg A B) X = Ξ£[ a β A ] El (B a) X

data ΞΌ (D : Desc ) : Set β where
    init : El D (ΞΌ D) -> ΞΌ D

size : β {D : Desc} -> ΞΌ D -> Size
size {D = D} (init x) = β (sizeHelper D D x)
  where
    sizeHelper : β D E β El D (ΞΌ E) β Size
    sizeHelper End E x = Z
    sizeHelper (Rec D) E (x , y) = size {D = E} x βlim sizeHelper _ E y -- size x βlim {!!}
    sizeHelper (HRec A D) E (f , x) = (lim A Ξ» (lift a) β size {D = E} (f a)) βlim (sizeHelper _ E x)
    sizeHelper (Arg A B) E (a , x) = sizeHelper _ E x
-- sizeHelper {D = .(End _)} ElEnd = Z
-- sizeHelper {D = .(Rec _)} (ElRec x xβ) = ((size x) βlim  (sizeHelper xβ))
-- sizeHelper {D = (Ref A _)} (ElRef f x) = ((lim A (Ξ» (lift a) -> size (f a))) βlim (sizeHelper x))
-- sizeHelper {D = .(Arg _ _)} (ElArg a x) = sizeHelper x

-- _<D_ : β {D} β ΞΌ D β ΞΌ D β Set (lsuc β)
-- x <D y = size x <β size y

-- open import Induction.WellFounded


-- genRec : β {β'} {D : Desc} β (P : ΞΌ D β Set β') β (β x β (β y β y <D x β P y) β P x) β β x β P x
-- genRec P rec x = helper (x , refl)
--   where
--     recHelper : _
--     recHelper sz rec' (x , refl) = rec x Ξ» y lt β rec' (size y) lt (y , refl)
--     helper = All.wfRec ordWf _ (Ξ» sz β ((x , _) : β[ x ](size x β‘ sz)) β P x) recHelper (size x)
