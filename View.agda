module View where

open import Data.List
open import Data.Fin
open import Data.Bin
open import Relation.Binary.PropositionalEquality

bzero : Bin
bzero = 0#

bsuc⁺ : Bin⁺ → Bin⁺
bsuc⁺ [] = zero ∷ []
bsuc⁺ (zero ∷ xs) = Fin.suc zero ∷ xs
bsuc⁺ (Fin.suc i ∷ xs) = zero ∷ bsuc⁺ xs

bsuc : Bin → Bin
bsuc 0# = [] 1#
bsuc (bs 1#) = (bsuc⁺ bs) 1#

bsuc*2 : ∀ n → bsuc n *2 ≡ bsuc (bsuc (n *2))
bsuc*2 0# = refl
bsuc*2 (bs 1#) = refl 

data ℕView : Bin → Set where
  Zero : ℕView bzero
--  Suc : ∀ {n} → ℕView n → ℕView (bsuc n)
  Suc : ∀ {m n} → (m ≡ bsuc n) → ℕView n → ℕView m

--2× : ∀ {bs} → ℕView (bs 1#) → ℕView ((zero ∷ bs) 1#)
--2× (Suc eq n) = Suc {!!} {!!} -- Suc {!!} (Suc {!!} {!2× n!})
2× : ∀ {b} → ℕView b → ℕView (b *2)
2× Zero = Zero
2× (Suc {m = m} {n = n} eq v) = Suc (trans (cong _*2 eq) (bsuc*2 n)) (Suc {m = bsuc (n *2)} refl (2× v))

ℕview⁺ : (bs : Bin⁺) → ℕView (bs 1#)
ℕview⁺ [] = Suc refl Zero
ℕview⁺ (b ∷ bs) with ℕview⁺ bs
ℕview⁺ (zero ∷ bs) | Suc eq n = 2× (Suc eq n)
ℕview⁺ (Fin.suc zero ∷ bs) | Suc eq n = Suc refl (2× (Suc eq n))
ℕview⁺ (Fin.suc (Fin.suc ()) ∷ bs) | Suc y y'

ℕview : (n : Bin) → ℕView n
ℕview 0# = Zero
ℕview (bs 1#) = ℕview⁺ bs

plus : Bin → Bin → Bin
plus x y with ℕview x
plus .0# y | Zero = y
plus x y | Suc {n = n} eq v = bsuc (plus n y)