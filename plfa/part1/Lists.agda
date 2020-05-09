module plfa.part1.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+; *-comm; +-suc; +-comm)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_; extensionality)


data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs rewrite cong (x ∷_) (++-assoc xs ys zs) = refl


++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) rewrite cong (x ∷_) (++-identityʳ xs) = refl

length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x ∷ xs)  =  suc (length xs)

length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys rewrite cong suc (length-++ xs ys) = refl

reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]

reverse-++-distrib : ∀ {A : Set} (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys rewrite ++-identityʳ (reverse ys) = refl
reverse-++-distrib (x ∷ xs) ys rewrite cong (_++ [ x ]) (reverse-++-distrib xs ys) | ++-assoc (reverse ys) (reverse xs) [ x ] = refl

reverse-involutive : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) rewrite reverse-++-distrib (reverse xs) [ x ] | cong (x ∷_) (reverse-involutive xs) = refl


shunt : ∀ {A : Set} → List A → List A → List A
shunt [] ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A) → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys = refl
shunt-reverse (x ∷ xs) ys rewrite shunt-reverse xs (x ∷ ys) | ++-assoc (reverse xs) [ x ] ys = refl

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} → (xs : List A) → reverse xs ≡ reverse′ xs
reverses (xs) rewrite shunt-reverse xs [] | ++-identityʳ (reverse xs) = refl


map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

map-compose : ∀ {A B C : Set} → (f : A → B) → (g : B → C) → map (g ∘ f) ≡ map g ∘ map f
map-compose f g = extensionality λ xs → e xs f g
  where
    e : ∀ {A B C : Set} (xs : List A) → (f : A → B) → (g : B → C) → map (g ∘ f) xs ≡ (map g ∘ map f) xs
    e [] f g = refl
    e (x ∷ xs) f g rewrite cong (g (f x) ∷_) (e xs f g) = refl

map-++-distribute : ∀ {A B : Set} (xs ys : List A) → (f : A → B) → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute [] ys f = refl
map-++-distribute (x ∷ xs) ys f rewrite cong ((f x) ∷_) (map-++-distribute xs ys f) = refl

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B


map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node l x r) = node (map-Tree f g l) (g x) (map-Tree f g r)


foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs

sum : List ℕ → ℕ
sum = foldr _+_ 0

product : List ℕ → ℕ
product = foldr _*_ 1


foldr-++ : ∀ {A B : Set} (xs ys : List A) → (_⊗_ : A → B → B) → (e : B)
  → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ [] ys _⊗_ e = refl
foldr-++ (x ∷ xs) ys _⊗_ e rewrite cong (x ⊗_) (foldr-++ xs ys _⊗_ e) = refl

foldr-∷ : ∀ {A : Set} (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-∷ [] = refl
foldr-∷ (x ∷ xs) rewrite cong (x ∷_) (foldr-∷ xs) = refl


foldr-++-∷ : ∀ {A : Set} (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
foldr-++-∷ [] ys = refl
foldr-++-∷ (x ∷ xs) ys rewrite cong (x ∷_) (foldr-++-∷ xs ys) = refl

    
map-is-foldr : ∀ {A B : Set} (f : A → B) → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr f = extensionality λ xs → e f xs
  where
    e : ∀ {A B : Set} (f : A → B) (xs : List A) → map f xs ≡ foldr (λ x xs → f x ∷ xs) [] xs
    e f [] = refl
    e f (x ∷ xs) rewrite cong ((f x) ∷_) (e f xs) = refl

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf x) = f x
fold-Tree f g (node l x r) = g (fold-Tree f g l) x (fold-Tree f g r)

downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n

sum-downFrom-ll : ∀ (n k : ℕ) → n + n + k ≡ n + k + n
sum-downFrom-ll n k rewrite +-assoc n n k | +-comm n (n + k) = refl

sum-downFrom-l : ∀ (n : ℕ) → n * 2 + n * (n ∸ 1) ≡ suc n * (suc n ∸ 1)
sum-downFrom-l zero = refl
sum-downFrom-l (suc n) rewrite *-comm n (suc n) | sym (+-suc n (suc (n + (n + n * n)))) | *-comm n 2 | +-identityʳ n | sym (+-suc n (suc (n + (n + n * n)))) | +-comm n (suc (suc (n + (n + n * n)))) = cong (suc ∘ suc) (sum-downFrom-ll n (n + n * n))

sum-downFrom : ∀ (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc n) =
  begin
    sum (downFrom (suc n)) * 2
  ≡⟨⟩
    (n + sum (downFrom n)) * 2
  ≡⟨ *-distribʳ-+ 2 n (sum (downFrom n)) ⟩
    n * 2 + sum (downFrom n) * 2
  ≡⟨ cong ((n * 2) +_) (sum-downFrom n) ⟩
    n * 2 + n * (n ∸ 1)
  ≡⟨ sum-downFrom-l n ⟩
    n + n * n
  ∎

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }


