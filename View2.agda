module View2 where

open import Data.Bin as Bin hiding (_+_;_*_)
open import Data.Nat as Nat
open import Data.Digit
open import Data.List
import Data.Fin as Fin
import Data.Product as Prod

data SnocView (A : Set) : List A → Set where
  Snil : SnocView A []
  Snoc : ∀ {ls} → (x : A) → (xs : SnocView A ls) → SnocView A (ls ++ [ x ])

Scons : ∀ {A xs} x → SnocView A xs → SnocView A (x ∷ xs) 
Scons x Snil = Snoc x Snil
Scons x (Snoc l xs) = Snoc l (Scons x xs)

Sview : ∀ {A} → (ls : List A) → SnocView A ls
Sview [] = Snil
Sview (x ∷ xs) = Scons x (Sview xs)

data IView⁺ : Bin⁺ → ℕ → Set where
  INil  : IView⁺ [] 0
  ICons : ∀ {bs n} b → IView⁺ bs n → IView⁺ (b ∷ bs) ((Fin.toℕ b) + n * 2)

Iview⁺ : (bs : Bin⁺) → IView⁺ bs (fromDigits bs)
Iview⁺ [] = INil
Iview⁺ (b ∷ bs) = ICons b (Iview⁺ bs)

data IView : Bin → ℕ → Set where
  I0# : IView 0# 0
  _I1# : ∀ (bs : Bin⁺) → IView (bs 1#) (fromDigits (bs ++ [ 1b ]))

Iview : (b : Bin) → IView b (toℕ b)
Iview 0# = I0#
Iview (bs 1#) = bs I1#

{-
isuc : ∀ {b n} → IView b n → IView (Bin.suc b) (Nat.suc n)
isuc I0# = [] I1#
isuc (bs I1#) with Sview bs
isuc (.[] I1#) | Snil = (0b ∷ []) I1#
isuc (.(ls ++ x ∷ []) I1#) | Snoc {ls} x xs = {! ? I1#!}
-}

-- isuc⁺ : ∀ {bs n} → IView⁺ bs n → IView⁺ _ (Nat.suc n)
-- isuc⁺ bs = {!!}
-- open import Relation.Binary.PropositionalEquality using (_≡_)
-- isuc⁺ : (bs : Bin⁺) → Prod.∃ (λ bs+1 → fromDigits {2} bs+1 ≡ Nat.suc (fromDigits bs))    
-- isuc⁺ x = {!!}

isuc⁺ : Bin⁺ → Bin⁺
isuc⁺ [] = [ 0b ]
isuc⁺ (Fin.zero ∷ xs) = 1b ∷ xs
isuc⁺ (Fin.suc i ∷ xs) = 0b ∷ (isuc⁺ xs)

open import Relation.Binary.PropositionalEquality using (_≡_;sym;refl)
lem0 : ∀ bs → fromBits (bs ++ [ 1b ]) ≡ bs 1#
lem0 [] = refl
lem0 (x ∷ xs) rewrite lem0 xs = refl

fromBitsToBits : ∀ b → fromBits (toBits b) ≡ b
fromBitsToBits 0# = refl
fromBitsToBits (bs 1#) rewrite lem0 bs = refl

toBitsFromBits : ∀ bs → toBits (fromBits bs) ≡ 0b ∷ bs
toBitsFromBits [] = refl
toBitsFromBits (x ∷ xs) with (sym (fromBitsToBits (fromBits xs)))
toBitsFromBits (Fin.zero ∷ xs) | q  = {!!}
toBitsFromBits (Fin.suc i ∷ xs) | q = {!!}

lem3 : ∀ bs → fromBits (addCarryToBitList 1b bs) ≡ Bin.suc (fromBits bs)
lem3 bs = {!!}

lem1 : ∀ bs → isuc⁺ bs 1# ≡ fromBits (addBitLists 0b [ 1b ] (bs ++ [ 1b ]))
lem1 [] = refl
lem1 (Fin.zero ∷ xs) rewrite lem0 xs = refl
lem1 (Fin.suc Fin.zero ∷ xs) rewrite lem0 xs = {!!}
lem1 (Fin.suc (Fin.suc ()) ∷ xs)
{-
lem1 bs with Sview bs
lem1 .[] | Snil = refl
lem1 .(Fin.zero ∷ []) | Snoc {[]} Fin.zero xs = refl
lem1 .(Fin.suc Fin.zero ∷ []) | Snoc {[]} (Fin.suc Fin.zero) xs = refl
lem1 ._ | Snoc {[]} (Fin.suc (Fin.suc ())) xs
lem1 .(Fin.zero ∷ xs ++ x' ∷ []) | Snoc {Fin.zero ∷ xs} x' xs' = {!!}
lem1 .(Fin.suc i ∷ xs ++ x' ∷ []) | Snoc {Fin.suc i ∷ xs} x' xs' = {!!}
-}

lem2 : ∀ bs → fromDigits (isuc⁺ bs ++ [ 1b ]) ≡ Nat.suc (fromDigits (bs ++ [ 1b ]))
lem2 bs = {!!}

isuc : ∀ {b n} → IView b n → IView (Bin.suc b) (Nat.suc n)
isuc I0# = [] I1#
isuc (bs I1#) = {!!}
-- isuc (bs I1#) rewrite (sym (lem1 bs)) | (sym (lem2 bs)) = (isuc⁺ bs) I1#
{-
isuc (bs I1#) with (isuc⁺ bs)
isuc (bs I1#) | Prod._,_ bs+1 p = {!bs+1 I1#!}
-}
{-
isuc ([] I1#) = (0b ∷ []) I1#
isuc ((Fin.zero ∷ []) I1#) = (1b ∷ []) I1#
isuc ((Fin.zero ∷ Fin.zero ∷ xs) I1#) = {!(1b ∷ 0b ∷ xs) I1#!}
isuc ((Fin.zero ∷ Fin.suc i ∷ xs) I1#) = {!!}
isuc ((Fin.suc i ∷ xs) I1#) = {!!}
-}

data ℕIView : ∀ {b n} → IView b n → Set where
  IZero : ℕIView I0#
  ISuc : ∀ {b n x} → ℕIView {b} {n} x → ℕIView {Bin.suc b} {Nat.suc n} (isuc x)

data ℕView : Bin → Set where
  Zero : ℕView 0#
  Suc : ∀ {b} → ℕView b → ℕView (Bin.suc b)

-- ℕview : (b : Bin) → ℕview b

{- 
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
-}
