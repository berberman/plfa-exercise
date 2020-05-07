module plfa.part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-comm; *-comm; ≤-refl; +-monoˡ-≤)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality)
open import Function using (_∘_)
open import Data.Empty using (⊥)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
  → B M
∀-elim L M = L M

∀-distrib-× : ∀ {A : Set} {B C : A → Set}
  → (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)

∀-distrib-× =
  record
    { to = λ f → (proj₁ ∘ f , proj₂ ∘ f)
    ; from = λ {(f , g) → λ x → (f x , g x)}
    ; from°to = λ f → refl
    ; to°from = λ f → refl
    }



⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set}
  → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
  → ∀ (x : A) → B x ⊎ C x

⊎∀-implies-∀⊎ (inj₁ f) = inj₁ ∘ f
⊎∀-implies-∀⊎ (inj₂ g) = inj₂ ∘ g

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri


postulate
  ext-dep : ∀ {A : Set} {B : A → Set} {f g : ∀ (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
    → f ≡ g

∀-x : ∀ {B : Tri → Set}
  → (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc)
∀-x =
  record
    { to = λ f → (f aa , f bb , f cc)
    ; from = λ { (baa , bbb , bcc) → λ { aa → baa ; bb → bbb ; cc → bcc }}
    ; from°to = λ f → ext-dep λ {aa → refl ; bb → refl ; cc → refl}
    ; to°from =  λ { (baa , bbb , bcc) → refl }
    }

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B


∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to = λ f → λ { ⟨ x , y ⟩ → f x y }
    ; from = λ f → λ x → λ y → f ⟨ x , y ⟩
    ; from°to = λ f → refl
    ; to°from = λ f → extensionality λ { ⟨ x , y ⟩ → refl }
    }

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set}
  → ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to = λ { ⟨ x , (inj₁ y) ⟩ → inj₁ ⟨ x , y ⟩ ; ⟨ x , (inj₂ y) ⟩ → inj₂ ⟨ x , y ⟩ }
    ; from = λ { (inj₁ ⟨ x , y ⟩) → ⟨ x , inj₁ y ⟩ ; (inj₂ ⟨ x , y ⟩) → ⟨ x , inj₂ y ⟩ }
    ; from°to = λ { ⟨ x , (inj₁ y) ⟩ → refl ; ⟨ x , (inj₂ y) ⟩ → refl }
    ; to°from = λ { (inj₁ ⟨ x , y ⟩) → refl ; (inj₂ ⟨ x , y ⟩) → refl }
    }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set}
  → ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , (y , z) ⟩ = ⟨ x , y ⟩ , ⟨ x , z ⟩


∃-⊎ : ∀ {B : Tri → Set}
  → (∃[ x ] B x) ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎ =
  record
    { to = λ { ⟨ aa , y ⟩ → inj₁ y ; ⟨ bb , y ⟩ → inj₂ (inj₁ y) ; ⟨ cc , y ⟩ → inj₂ (inj₂ y) }
    ; from = λ { (inj₁ baa) → ⟨ aa , baa ⟩ ; (inj₂ (inj₁ bbb)) → ⟨ bb , bbb ⟩ ; (inj₂ (inj₂ bcc)) → ⟨ cc , bcc ⟩ }
    ; from°to =   λ { ⟨ aa , y ⟩ → refl ; ⟨ bb , y ⟩ → refl ; ⟨ cc , y ⟩ → refl }
    ; to°from = λ { (inj₁ baa) → refl ; (inj₂ (inj₁ bbb)) → refl ; (inj₂ (inj₂ bcc)) → refl }
    }


data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
    → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero = ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩ = ⟨ suc m  , refl ⟩
odd-∃ (odd-suc e) with even-∃ e
...                    | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨ zero , refl ⟩ = even-zero
∃-even ⟨ suc m , refl ⟩ = even-suc (∃-odd ⟨ m , refl ⟩)
∃-odd ⟨ zero , refl ⟩ = odd-suc even-zero
∃-odd ⟨ suc m , refl ⟩ = odd-suc (∃-even ⟨ suc m , refl ⟩)

-- Termination checking failed for the following functions : ???
-- ∃-even′ : ∀ {n : ℕ} → ∃[ m ] (    2 * m ≡ n) → even n
-- ∃-odd′  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) →  odd n


-- ∃-even′ ⟨ zero , refl ⟩ = even-zero
-- ∃-even′ ⟨ suc m , refl ⟩ = even-suc (∃-odd′ ⟨ m , e ⟩)
--   where
--     e : m + (m + zero) + 1 ≡ m + suc (m + zero)
--     e rewrite cong (_+ 1) (cong (m +_) (+-identityʳ m)) | +-comm m (suc (m + 0)) | +-comm (m + m) 1 | cong suc (cong (_+ m) (+-identityʳ m)) = refl
-- ∃-odd′ ⟨ zero , refl ⟩ = odd-suc even-zero
-- ∃-odd′ ⟨ suc m , refl ⟩ = odd-suc (∃-even′ ⟨ suc m , e ⟩)
--   where
--     e : 2 * suc m ≡ m + 1 * suc m + 1
--     e rewrite *-comm 2 (suc m) | +-identityʳ m | +-suc m m | *-comm m 2 | +-identityʳ m | +-comm (m + m) 1 = refl

∃-+-≤ : ∀ {y z : ℕ} → ∃[ x ] (x + y ≡ z) → (y ≤ z)
∃-+-≤ ⟨ zero , refl ⟩ = ≤-refl
∃-+-≤ {y} ⟨ suc x , refl ⟩ = +-monoˡ-≤ y z≤n 

≤-+-∃ : ∀ {y z : ℕ} → (y ≤ z) → ∃[ x ] (x + y ≡ z)
≤-+-∃ {zero} {zero} z≤n = ⟨ zero , refl ⟩
≤-+-∃ {zero} {suc z} y≤z = ⟨ suc z , cong suc (+-identityʳ z) ⟩
≤-+-∃ {suc y} {suc z} (s≤s y≤z) = ∃-elim (λ x x+y≡z → ⟨ x , e x+y≡z ⟩) (≤-+-∃ y≤z)
  where
    e : ∀ {x y : ℕ} → x + y ≡ z → x + suc y ≡ suc z
    e {x} {y} ev rewrite (+-comm x (suc y)) | +-comm y x | cong suc ev = refl

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to = λ f x y → f ⟨ x , y ⟩
    ; from = λ f → λ { ⟨ x , y ⟩ → f x y }
    ; from°to = λ f → extensionality λ { ⟨ x , y ⟩ → refl }
    ; to°from = λ f → refl
    }

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , f ⟩ g = f (g x)
