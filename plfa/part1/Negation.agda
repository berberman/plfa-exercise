module plfa.part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality)
open import Function using (_∘_)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
  → ¬ ¬ A
¬¬-intro x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
  → ¬ A
¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality λ ()

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality λ x → ⊥-elim (¬x x)


⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× =
  record
    { to = λ f → f ∘ inj₁ , f ∘ inj₂ 
    ; from = λ{(¬x , ¬y) → λ{(inj₁ x) → ¬x x; (inj₂ y) → ¬y y}}
    ; from°to = λ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl}
    ; to°from = λ{(¬x , ¬y) → refl}
    }

×-qaq-⊎ : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
×-qaq-⊎ (inj₁ ¬x) = ¬x ∘ proj₁
×-qaq-⊎ (inj₂ ¬y) = ¬y ∘ proj₂


postulate
  em : {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = k (inj₂ λ{x → k (inj₁ x)})


→second : ∀ {A : Set} → A ⊎ (¬ A) → (¬ ¬ A → A)
→second (inj₁ x) _ = x
→second (inj₂ ¬x) ¬¬x = ⊥-elim (¬¬x ¬x)

→third : ∀ {A B : Set} → A ⊎ (¬ A) → (((A → B) → A) → A)
→third (inj₁ x) _ = x
→third (inj₂ ¬x) f = f λ x → ⊥-elim (¬x x)

→fourth : ∀ {A B : Set} → A ⊎ (¬ A) → ((A → B) → ¬ A ⊎ B)
→fourth (inj₁ x) f = inj₂ (f x)
→fourth (inj₂ ¬x) _ = inj₁ ¬x

→fifth : ∀ {A B : Set} → (∀ {A : Set} → A ⊎ (¬ A)) → (¬ (¬ A × ¬ B) → A ⊎ B)
→fifth {A} {B} em f with em{A} | em{B}
... | inj₁ x | _ = inj₁ x
... | inj₂ ¬x | inj₁ y = inj₂ y
... | inj₂ y₁ | inj₂ y = ⊥-elim (f (y₁ , y))

-- ......

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-stable : ∀ {A : Set} → Stable (¬ A)
¬-stable ¬¬¬x x = ¬¬¬x (¬¬-intro x)

×-stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
×-stable f g ¬¬x,y = f (λ ¬x → ¬¬x,y λ (x , y)→ ¬x x) , g λ ¬y → ¬¬x,y λ (x , y) → ¬y y
