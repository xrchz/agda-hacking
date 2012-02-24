module View where

open import Data.List
open import Data.Fin hiding (_+_)
open import Data.Bin hiding (_+_)
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming (_*_ to _×_)
open import Data.Empty

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

sizeof : Bin → ℕ
sizeof 0# = 0
sizeof ([] 1#) = 1
sizeof ((zero ∷ xs) 1#) = 2 × (sizeof (xs 1#))
sizeof ((Fin.suc i ∷ xs) 1#) = ℕ.suc (2 × (sizeof (xs 1#)))

open ≡-Reasoning

-- in Data.Nat.Properties but private!
m+1+n≡1+m+n : ∀ m n → m + ℕ.suc n ≡ ℕ.suc (m + n)
m+1+n≡1+m+n zero    n = refl
m+1+n≡1+m+n (ℕ.suc m) n = cong ℕ.suc (m+1+n≡1+m+n m n)


sizeof-bsuc⁺ : ∀ n → sizeof (bsuc⁺ n 1#) ≡ ℕ.suc (sizeof (n 1#))
sizeof-bsuc⁺ [] = refl
sizeof-bsuc⁺ (zero ∷ xs) = refl
sizeof-bsuc⁺ (Fin.suc i ∷ xs) = begin
  sizeof (bsuc⁺ xs 1#) + (sizeof (bsuc⁺ xs 1#) + 0)
    ≡⟨ cong₂ _+_ (sizeof-bsuc⁺ xs) (cong₂ _+_ (sizeof-bsuc⁺ xs) refl) ⟩
  ℕ.suc (sizeof (xs 1#)) + (ℕ.suc (sizeof (xs 1#)) + 0) ≡⟨ m+1+n≡1+m+n (ℕ.suc (sizeof (xs 1#))) (sizeof (xs 1#) + zero) ⟩
  (ℕ.suc (ℕ.suc (sizeof (xs 1#)) + (sizeof (xs 1#) + 0)) ∎)

sizeof-bsuc : ∀ n → sizeof (bsuc n) ≡ ℕ.suc (sizeof n)
sizeof-bsuc 0# = refl
sizeof-bsuc (x 1#) = sizeof-bsuc⁺ x

sizeof-suc-inj : ∀ n z → sizeof (bsuc n) ≡ ℕ.suc z → sizeof n ≡ z
sizeof-suc-inj n z p with ℕview n
sizeof-suc-inj .0# z p | Zero = cong Data.Nat.pred p
sizeof-suc-inj n z p | Suc {n = a} y y' = cong Data.Nat.pred (trans (sym (sizeof-bsuc n)) p)

sizeof-suc-pos : ∀ n → sizeof (bsuc n) ≡ 0 → ⊥
sizeof-suc-pos 0# ()
sizeof-suc-pos (bs 1#) p with trans (sym p) (sizeof-bsuc⁺ bs)
sizeof-suc-pos (bs 1#) p | ()

plus : (x : Bin) → (n : ℕ) → (sizeof x ≡ n) → Bin → Bin
plus x _ _ _ with ℕview x
plus .0# _ _ y | Zero = y
plus x ℕ.zero p _ | Suc {n = n} eq v = ⊥-elim (sizeof-suc-pos n p')
  where
    p' = begin
           sizeof (bsuc n) ≡⟨ sym (cong sizeof eq) ⟩
           sizeof x        ≡⟨ p ⟩
           zero ∎
plus x (ℕ.suc z) p y | Suc {n = n} eq v = bsuc (plus n z p' y)
  where
    p' = sizeof-suc-inj n z (
      begin
        sizeof (bsuc n) ≡⟨ cong sizeof (sym eq) ⟩
        sizeof x        ≡⟨ p    ⟩
        ℕ.suc z
      ∎ )
