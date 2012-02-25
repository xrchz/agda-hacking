module View3 where

open import Data.Nat as Nat
open import Data.Product
open import Data.Bin as Bin hiding (_*_;_+_)
open import Data.Digit as Digit
open import Data.List
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality

{-
plus : Bin → Bin → Bin
plus m n with (toℕ m)
plus m n | zero = n
plus _ n | Nat.suc m = Bin.suc (plus {!!} n)
-}

IBin : ℕ → Set
IBin n = Σ[ b ∶ Bin ] toℕ b ≡ n

data IView : Bin → Set where
  IV : ∀ {n} → (b : IBin n) → IView (proj₁ b)

Iview : (b : Bin) → IView b
Iview 0# = IV {0} (0# , refl)
Iview (bs 1#) = IV {toℕ (bs 1#)} (bs 1# , refl)

bsuc⁺ : Bin⁺ → Bin⁺
bsuc⁺ [] = 0b ∷ []
bsuc⁺ (Fin.zero ∷ xs) = 1b ∷ xs
bsuc⁺ (Fin.suc i ∷ xs) = 0b ∷ bsuc⁺ xs

bsuc : Bin → Bin
bsuc 0# = [] 1#
bsuc (bs 1#) = (bsuc⁺ bs) 1#

open import Data.Nat.Properties using (module SemiringSolver)
open ≡-Reasoning
open SemiringSolver
open import Function using (flip)
bsuc-correct : ∀ b → toℕ (bsuc b) ≡ Nat.suc (toℕ b)
bsuc-correct 0# = refl
bsuc-correct ([] 1#) = refl
bsuc-correct ((Fin.zero ∷ xs) 1#) = refl
bsuc-correct ((Fin.suc Fin.zero ∷ xs) 1#) = begin
{- fromDigits (bsuc⁺ xs ++ Fin.suc Fin.zero ∷ []) * 2 ≡
   Nat.suc (Nat.suc (fromDigits (xs ++ Fin.suc Fin.zero ∷ []) * 2))
-}let t = Fin.suc Fin.zero ∷ [] in
  let l = fromDigits (bsuc⁺ xs ++ t) in
  let r-1 = fromDigits (xs ++ t) in
  let r = 1 + r-1 in
  l * 2 ≡⟨ cong (flip _*_ 2) (bsuc-correct (xs 1#)) ⟩
  r * 2 ≡⟨ solve 1 (λ r-1 → (con 1 :+ r-1) :* con 2 := con 1 :+ (con 1 :+ r-1 :* con 2)) refl r-1 ⟩
  1 + (1 + (r-1 * 2)) ∎
bsuc-correct ((Fin.suc (Fin.suc ()) ∷ xs) 1#)

isuc : ∀ {n} → IBin n → IBin (Nat.suc n)
isuc {n} (b , p) = bsuc b , (begin
  toℕ (bsuc b) ≡⟨ bsuc-correct b ⟩
  Nat.suc (toℕ b) ≡⟨ cong Nat.suc p ⟩
  Nat.suc n ∎)

{-
data ℕView : ∀ {n} → IBin n → Set where
  NV : ∀ b → ℕView {toℕ b} ( b , refl )

ℕview : ∀ {n} → (i : IBin n) → ℕView i
ℕview i = {!!}

plus : ∀ {m n} → IBin m → IBin n → IBin (m + n)
plus m n with ℕview m
plus .(b , refl) n' | NV {n} b = {!!}
-- plus .(0# , refl) n | Zero = n
-- plus ._ n | Suc {_} {m} refl refl _ = isuc (plus m n)
-}

{-
data ℕView : ∀ {n} → IBin n → Set where
  Zero : ℕView (0# , refl)
  Suc : ∀ {n i j b} → i ≡ ( b , refl ) → j ≡ isuc i → ℕView {n} i → ℕView j

ℕview⁺ : ∀ bs → ℕView (bs 1# , refl)
ℕview⁺ [] = Suc refl refl Zero
ℕview⁺ (b ∷ bs) with ℕview⁺ bs
... | q = {!q!}

ℕview : ∀ {n} → (i : IBin n) → ℕView i
ℕview (0# , refl) = Zero
ℕview (bs 1# , refl) = {!ℕview⁺ bs!}

{-
ℕview⁺ : ∀ (bs : Bin⁺) → ℕView (bs 1# , refl)
ℕview⁺ [] = Suc Zero
ℕview⁺ (b ∷ bs) with ℕview⁺ bs
... | q = {!q!}

ℕview : ∀ {n} → (i : IBin n) → ℕView i
ℕview (0# , refl) = Zero
ℕview (bs 1# , refl) = ℕview⁺ bs
-}

plus : ∀ {m n} → IBin m → IBin n → IBin (m + n)
plus m n with ℕview m
plus .(0# , refl) n | Zero = n
plus ._ n | Suc {_} {m} refl refl _ = isuc (plus m n)
-}
