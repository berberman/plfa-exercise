module plfa.part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)


data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
    → suc m ≤ suc n


_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

infix 4 _≤_


inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m :  ℕ}
  → m ≤ zero
  → m ≡ zero
inv-z≤n z≤n = refl


≤-refl : ∀ {n : ℕ}
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
  → m ≤ p
≤-trans z≤n _  = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
  → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)


data Total (m n : ℕ) : Set where
  forward :
    m ≤ n
    → Total m n

  flipped :
    n ≤ m
    → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
  → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)  → m ≤ n
  → p ≤ q
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
  → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
  → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q =  ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ}
    → zero < suc n
  s<s : ∀ {m n : ℕ}
    → m < n
    → suc m < suc n


infix 4 _<_

<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
  → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)



data Trichotomy (m n : ℕ) : Set where
  lt :
    m < n
    → Trichotomy m n
  eq :
    m ≡ n
    → Trichotomy m n
  gt :
    n < m
    → Trichotomy m n


<-total : ∀ (m n : ℕ) → Trichotomy m n
<-total zero zero = eq refl
<-total zero (suc n) = lt z<s
<-total (suc n) zero = gt z<s
<-total (suc m) (suc n) with <-total m n
...                      | lt m<n = lt  (s<s m<n)
...                      | eq m≡n = eq (cong suc m≡n)
...                      | gt n<m = gt (s<s n<m)

+-monoʳ-< : ∀ (n p q : ℕ)
  → p < q
  → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ)
  → m < n
  → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n


+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
  → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

≤-iff-< : ∀ {m n : ℕ}
  → suc m ≤ n
  → m < n
≤-iff-< {zero} {suc n} sm≤n = z<s
≤-iff-< {suc m} {suc n} (s≤s sm<n) = s<s (≤-iff-< sm<n)

<-iff-≤ : ∀ {m n : ℕ}
  → m < n
  → suc m ≤ n
<-iff-≤ {zero} {suc n} _ = s≤s z≤n
<-iff-≤ {suc m} {suc n} (s<s m<n) = s≤s (<-iff-≤ m<n)


data even : ℕ → Set
data odd : ℕ → Set

data even where
  zero :
    even zero
  suc : ∀ {n : ℕ}
    → odd n
    → even (suc n)
data odd where
  suc : ∀ {n : ℕ}
    → even n
    → odd (suc n)


e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
  → even (m + n)
o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
  → odd (m + n)

o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
  → even (m + n)

e+e≡e zero n = n
e+e≡e (suc m) n = suc (o+e≡o m n)
o+e≡o (suc m) n = suc (e+e≡e m n)
o+o≡e {suc m} {n} (suc e) o rewrite +-comm m n = suc (o+e≡o o e)
