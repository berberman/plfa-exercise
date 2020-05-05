module plfa.part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa.part1.Isomorphism.≃-Reasoning

data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
  → B
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , x₁ ⟩ = refl

infixr 2 _×_

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to = λ {⟨ x , y ⟩ → ⟨ y , x ⟩}
    ; from =  λ {⟨ y , x ⟩ → ⟨ x , y ⟩}
    ; from°to = λ {⟨ x , y ⟩ → refl }
    ; to°from = λ {⟨ y , x ⟩ → refl}
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from°to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to°from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× =
  record
    { to = λ {record {to = A→B; from = B→A} → ⟨ A→B , B→A ⟩}
    ; from = λ {⟨ A→B , B→A ⟩ → record {to = A→B; from = B→A}}
    ; from°to = λ x → refl
    ; to°from = λ { ⟨ A→B , B→A ⟩ → refl}
    }


data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from°to = λ{ ⟨ tt , x ⟩ → refl }
    ; to°from = λ{ x → refl }
    }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎


data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
    → A ⊎ B

  inj₂ :
      B
    → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
  → C
case-⊎ A→C B→C (inj₁ A) = A→C A
case-⊎ A→C B→C (inj₂ B) = B→C B

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) → case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infixr 1 _⊎_

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to = λ { (inj₁ x) → inj₂ x; (inj₂ x) → inj₁ x}
    ; from = λ { (inj₁ x) → inj₂ x; (inj₂ x) → inj₁ x}
    ; from°to = λ { (inj₁ x) → refl; (inj₂ x) → refl}
    ; to°from =  λ { (inj₁ x) → refl; (inj₂ x) → refl}
    }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to = λ{
       (inj₁ (inj₁ x)) → inj₁ x
      ;(inj₁ (inj₂ x)) → inj₂ (inj₁ x)
      ;(inj₂ x) → inj₂ (inj₂ x)
    }
    ; from = λ{
       (inj₁ x) → inj₁ (inj₁ x)
      ;(inj₂ (inj₁ x)) → inj₁ (inj₂ x)
      ;(inj₂ (inj₂ x)) → inj₂ x
    }
    ; from°to = λ {
       (inj₁ (inj₁ x)) → refl
      ;(inj₁ (inj₂ x)) → refl
      ;(inj₂ x) → refl
    }
    ; to°from = λ{
       (inj₁ x) → refl
      ;(inj₂ (inj₁ x)) → refl
      ;(inj₂ (inj₂ x)) → refl
    }
    }


data ⊥ : Set where

⊥-elim : ∀ {A : Set}
  → ⊥
  → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { to = λ { (inj₂ A) → A }
    ; from = λ A → inj₂ A
    ; from°to = λ { (inj₂ A) → refl }
    ; to°from = λ A → refl
    }


⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ {A} =
  ≃-begin
    (A ⊎ ⊥)
  ≃⟨ ⊎-comm ⟩
    (⊥ ⊎ A)
  ≃⟨ ⊥-identityˡ ⟩
    A
  ≃-∎

→-elim : ∀ {A B : Set}
  → (A → B)
  → A
  → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to = λ {f → λ {⟨ x , y ⟩ → f x y }}
    ; from = λ {f → λ {x → λ {y → f ⟨ x , y ⟩ } }}
    ; from°to = λ x → refl
    ; to°from = λ y → extensionality λ { ⟨ x , y ⟩ → refl }
    }



→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to = λ { f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
    ; from = λ {⟨ f , g ⟩ → λ { (inj₁ x) → f x ; (inj₂ x) → g x }}
    ; from°to = λ f → extensionality λ { (inj₁ x) → refl ; (inj₂ x) → refl }
    ; to°from = λ {⟨ f , g ⟩ → refl}
    }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to =  λ{f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from = λ{⟨ f , g ⟩ → λ{x → ⟨ f x , g x ⟩}}
    ; from°to = λ{f → extensionality λ{x → η-× (f x)}}
    ; to°from = λ{ ⟨ f , g ⟩ → refl}
    }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to = λ{⟨ inj₁ x , y ⟩ → (inj₁ ⟨ x , y ⟩) ; ⟨ inj₂ x , y ⟩ → inj₂ ⟨ x , y ⟩ }
    ; from = λ{(inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , y ⟩ ; (inj₂ ⟨ x , y ⟩) → ⟨ inj₂ x , y ⟩}
    ; from°to = λ{⟨ inj₁ x , y ⟩ → refl ; ⟨ inj₂ x , y ⟩ → refl}
    ; to°from = λ{(inj₁ ⟨ x , y ⟩) → refl ; (inj₂ ⟨ x , y ⟩) → refl}
    }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to = λ{(inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩ ; (inj₂ x) → ⟨ inj₂ x , inj₂ x ⟩}
    ; from = λ{⟨ inj₁ x , inj₁ y ⟩ → inj₁ ⟨ x , y ⟩ ; ⟨ inj₁ x , inj₂ y ⟩ →  inj₂ y ; ⟨ inj₂ c , _ ⟩ → inj₂ c}
    ; from°to = λ{(inj₁ ⟨ x , y ⟩) → refl ; (inj₂ x) → refl}
    }



⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× = λ{ ⟨ inj₁ x , _ ⟩ → inj₁ x ; ⟨ inj₂ x , y ⟩ → inj₂ ⟨ x , y ⟩}

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ = λ{(inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩ ; (inj₂ ⟨ x , y ⟩) → ⟨ inj₂ x , inj₂ y ⟩}
