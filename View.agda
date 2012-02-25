module View where

open import Data.List
open import Data.Fin hiding (_+_;toℕ)
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

bsuc-pos : ∀ n → bsuc n ≡ 0# → ⊥
bsuc-pos 0# ()
bsuc-pos (bs 1#) ()

open ≡-Reasoning
open import Data.Digit
open import Data.Nat.Properties using (module SemiringSolver)
open SemiringSolver
open import Function using (flip)

fromDigits-bsuc⁺ : ∀ bs → fromDigits ((bsuc⁺ bs) ++ (Fin.suc zero ∷ [])) ≡ ℕ.suc (fromDigits (bs ++ (Fin.suc zero ∷ [])))
fromDigits-bsuc⁺ [] = refl
fromDigits-bsuc⁺ (zero ∷ xs) = refl
fromDigits-bsuc⁺ (Fin.suc zero ∷ xs) = begin
  let t = Fin.suc zero ∷ [] in
  let l = fromDigits (bsuc⁺ xs ++ t) in
  let r-1 = fromDigits (xs ++ t) in
  let r = 1 + r-1 in
  l × 2 ≡⟨ cong (flip _×_ 2) (fromDigits-bsuc⁺ xs) ⟩ 
  r × 2 ≡⟨ solve 1 (λ r-1 → (con 1 :+ r-1) :* con 2 := con 1 :+ (con 1 :+ r-1 :* con 2)) refl r-1 ⟩
  1 + (1 + (r-1 × 2))
  ∎
fromDigits-bsuc⁺ (Fin.suc (Fin.suc ()) ∷ _)

toℕ-suc-inj : ∀ n z → toℕ (bsuc n) ≡ ℕ.suc z → toℕ n ≡ z
toℕ-suc-inj 0# z p = cong Data.Nat.pred p
toℕ-suc-inj (bs 1#) z p = cong Data.Nat.pred (trans (sym (fromDigits-bsuc⁺ bs)) p)

toℕ-bsuc-pos : ∀ n → toℕ (bsuc n) ≡ 0 → ⊥
toℕ-bsuc-pos 0# ()
toℕ-bsuc-pos (bs 1#) p with trans (sym p) (fromDigits-bsuc⁺ bs)
toℕ-bsuc-pos (bs 1#) p | ()

plus : (x : Bin) → (n : ℕ) → (toℕ x ≡ n) → Bin → Bin
plus x _ _ _ with ℕview x
plus .0# _ _ y | Zero = y
plus .(bsuc n) zero p _ | Suc {.(bsuc n)} {n} refl v = ⊥-elim (toℕ-bsuc-pos n p)
plus x (ℕ.suc z) p y | Suc {n = n} eq v = bsuc (plus n z p' y)
  where
    p' = toℕ-suc-inj n z (
      begin
        toℕ (bsuc n) ≡⟨ cong toℕ (sym eq) ⟩
        toℕ x        ≡⟨ p    ⟩
        ℕ.suc z
      ∎ )

-- define a view from Bin to Bin indexed by their toℕ size?
