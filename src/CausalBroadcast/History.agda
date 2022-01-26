------------------------------------------------------------------------
-- An `Event` can also represent a `History` of events perceived by it.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module CausalBroadcast.History (n : ℕ) (Msg : Set) where

open import CausalBroadcast.Event n Msg
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; proj₁; proj₂; ∃-syntax; -,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; fromInj₁)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

infix 4 _∈_ _∈⁻_ _∈ˢ_ _∈ˢ⁻_ _∈ʳ_ _∈ʳ⁻_

private
  variable
    p p′ p″ : Fin n
    m       : Msg

History = Event

private
  variable
    e  : Event p
    e′ : Event p′
    e″ : Event p″

data _∈_ : Event p → History p′ → Set where
  here   : e ∈ e
  there₁ : e ∈ e′ → e ∈ send m  e′
  there₂ : e ∈ e′ → e ∈ recv e″ e′
  there₃ : e ∈ e″ → e ∈ recv e″ e′

∈-trans : e ∈ e′ → e′ ∈ e″ → e ∈ e″
∈-trans here       y          = y
∈-trans (there₁ x) here       = there₁ x
∈-trans (there₁ x) (there₁ y) = there₁ (∈-trans x (∈-trans (there₁ here) y))
∈-trans (there₁ x) (there₂ y) = there₂ (∈-trans x (∈-trans (there₁ here) y))
∈-trans (there₁ x) (there₃ y) = there₃ (∈-trans x (∈-trans (there₁ here) y))
∈-trans (there₂ x) here       = there₂ x
∈-trans (there₂ x) (there₁ y) = there₁ (∈-trans x (∈-trans (there₂ here) y))
∈-trans (there₂ x) (there₂ y) = there₂ (∈-trans x (∈-trans (there₂ here) y))
∈-trans (there₂ x) (there₃ y) = there₃ (∈-trans x (∈-trans (there₂ here) y))
∈-trans (there₃ x) here       = there₃ x
∈-trans (there₃ x) (there₁ y) = there₁ (∈-trans x (∈-trans (there₃ here) y))
∈-trans (there₃ x) (there₂ y) = there₂ (∈-trans x (∈-trans (there₃ here) y))
∈-trans (there₃ x) (there₃ y) = there₃ (∈-trans x (∈-trans (there₃ here) y))

-- This is the Lemma 2.2 of the "holy grail" paper
∈↔⊏ : e ≢ᵉ e′ → (e ∈ e′ → e ⊏ e′) × (e ⊏ e′ → e ∈ e′)
proj₁ (∈↔⊏ e≢ᵉe′) = fromInj₁ (λ x → ⊥-elim (e≢ᵉe′ x)) ∘ ∈→⊏
  where
  ∈→⊏ : e ∈ e′ → e ⊏ e′ ⊎ e ≡ᵉ e′
  ∈→⊏ here        = inj₂ refl
  ∈→⊏ (there₁ x) with ∈→⊏ x
  ... | inj₁ y    = inj₁ (trans y processOrder₁)
  ... | inj₂ refl = inj₁ processOrder₁
  ∈→⊏ (there₂ x) with ∈→⊏ x
  ... | inj₁ y    = inj₁ (trans y processOrder₂)
  ... | inj₂ refl = inj₁ processOrder₂
  ∈→⊏ (there₃ x) with ∈→⊏ x
  ... | inj₁ y    = inj₁ (trans y send⊏recv)
  ... | inj₂ refl = inj₁ send⊏recv
proj₂ (∈↔⊏ _) = ⊏→∈
  where
  ⊏→∈ : e ⊏ e′ → e ∈ e′
  ⊏→∈ processOrder₁ = there₁ here
  ⊏→∈ processOrder₂ = there₂ here
  ⊏→∈ send⊏recv     = there₃ here
  ⊏→∈ (trans x y)   = ∈-trans (⊏→∈ x) (⊏→∈ y)

------------------------------------------------------------------------
-- Some handy subsets of `_∈_`.

-- `e ∈⁻ h` means `e` is a event that originates from history `h`
data _∈⁻_ : Event p → History p′ → Set where
  here   : e ∈⁻ e
  there₁ : e ∈⁻ e′ → e ∈⁻ send m  e′
  there₂ : e ∈⁻ e′ → e ∈⁻ recv e″ e′

∈⁻→∈ : e ∈⁻ e′ → e ∈ e′
∈⁻→∈ here       = here
∈⁻→∈ (there₁ x) = there₁ (∈⁻→∈ x)
∈⁻→∈ (there₂ x) = there₂ (∈⁻→∈ x)

-- `e ∈ˢ h` means `e` is a send event in history `h`
data _∈ˢ_ : Event p → History p′ → Set where
  here   : send m e ∈ˢ send m e
  there₁ : e ∈ˢ e′ → e ∈ˢ send m  e′
  there₂ : e ∈ˢ e′ → e ∈ˢ recv e″ e′
  there₃ : e ∈ˢ e″ → e ∈ˢ recv e″ e′

∈ˢ→∈ : e ∈ˢ e′ → e ∈ e′
∈ˢ→∈ here       = here
∈ˢ→∈ (there₁ x) = there₁ (∈ˢ→∈ x)
∈ˢ→∈ (there₂ x) = there₂ (∈ˢ→∈ x)
∈ˢ→∈ (there₃ x) = there₃ (∈ˢ→∈ x)

∈ˢ→send : e ∈ˢ e′ → ∃[ m ] ∃[ e″ ] e ≡ send m e″
∈ˢ→send here       = -, -, refl
∈ˢ→send (there₁ x) = ∈ˢ→send x
∈ˢ→send (there₂ x) = ∈ˢ→send x
∈ˢ→send (there₃ x) = ∈ˢ→send x

-- `e ∈ˢ⁻ h` means `e` is a send event that originates from history `h`
data _∈ˢ⁻_ : Event p → History p′ → Set where
  here   : send m e ∈ˢ⁻ send m e
  there₁ : e ∈ˢ⁻ e′ → e ∈ˢ⁻ send m  e′
  there₂ : e ∈ˢ⁻ e′ → e ∈ˢ⁻ recv e″ e′

∈ˢ⁻→∈ˢ : e ∈ˢ⁻ e′ → e ∈ˢ e′
∈ˢ⁻→∈ˢ here       = here
∈ˢ⁻→∈ˢ (there₁ x) = there₁ (∈ˢ⁻→∈ˢ x)
∈ˢ⁻→∈ˢ (there₂ x) = there₂ (∈ˢ⁻→∈ˢ x)

-- `e ∈ʳ h` means there is a receive event of `e` in history `h`
data _∈ʳ_ : Event p → History p′ → Set where
  here   : e ∈ʳ recv e e′
  there₁ : e ∈ʳ e′ → e ∈ʳ send m  e′
  there₂ : e ∈ʳ e′ → e ∈ʳ recv e″ e′
  there₃ : e ∈ʳ e″ → e ∈ʳ recv e″ e′

∈ʳ→∈ : e ∈ʳ e′ → e ∈ e′
∈ʳ→∈ here       = there₃ here
∈ʳ→∈ (there₁ x) = there₁ (∈ʳ→∈ x)
∈ʳ→∈ (there₂ x) = there₂ (∈ʳ→∈ x)
∈ʳ→∈ (there₃ x) = there₃ (∈ʳ→∈ x)

-- `e ∈ˢ⁻ h` means there is a receive event of `e` that originates from
-- history `h`
data _∈ʳ⁻_ : Event p → History p′ → Set where
  here   : e ∈ʳ⁻ recv e e′
  there₁ : e ∈ʳ⁻ e′ → e ∈ʳ⁻ send m  e′
  there₂ : e ∈ʳ⁻ e′ → e ∈ʳ⁻ recv e″ e′

∈ʳ⁻→∈ʳ : e ∈ʳ⁻ e′ → e ∈ʳ e′
∈ʳ⁻→∈ʳ here       = here
∈ʳ⁻→∈ʳ (there₁ x) = there₁ (∈ʳ⁻→∈ʳ x)
∈ʳ⁻→∈ʳ (there₂ x) = there₂ (∈ʳ⁻→∈ʳ x)
