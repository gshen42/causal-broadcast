------------------------------------------------------------------------
-- Defines the execution of a distributed system as a transition system.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module CausalBroadcast.Execution (n : ℕ) (Msg : Set) where

open import CausalBroadcast.Event n Msg
open import CausalBroadcast.History n Msg
import CausalBroadcast.Reachable as Reachable
open import Data.Fin using (Fin; _≟_)
open import Data.Product using (∃; _,_; ∃-syntax; -,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (yes; no)

State : Set
State = (p : Pid) → History p

s₀ : State
s₀ _ = init

update : State → Pid → (∀ {p} → History p → History p) → State
update s p f p′ with p ≟ p′
... | yes _ = f (s p′)
... | no  _ = s p′

data _—⟶_ : State → State → Set where
  send : ∀ {s} p m →
         s —⟶ update s p (send m)
  recv : ∀ {s} p p′ m {e} →
         p ≢ p′ →
         send m e ∈⁻ s p′ →
         s —⟶ update s p (recv (send m e))

open Reachable s₀ _—⟶_

-- Receives are well-formed, i.e., the last event of the sending process is a send event.
wf-recv : ∀ {s} → reachable s →
          ∀ p p′ (e : Event p) (e′ : Event p′) →
          recv e′ e ∈⁻ s p →
          ∃[ m ] ∃[ e″ ] e′ ≡ send m e″
wf-recv = induction P P₀ Pstep
  where
  P : State → Set
  P s = ∀ p p′ e e′ → recv e′ e ∈⁻ s p → ∃[ m ] ∃[ e″ ] e′ ≡ send m e″

  P₀ : P s₀
  P₀ p p′ e e′ ()

  Pstep : ∀ {s s′} → reachable s → P s → s —⟶ s′ → P s′
  Pstep _ Ps (send p _) p′ _ _ _ a          with p ≟ p′
  Pstep _ Ps (send p _) p′ _ _ _ (there₁ a) | yes _ = Ps _ _ _ _ a
  Pstep _ Ps (send p _) p′ _ _ _ a          | no  _ = Ps _ _ _ _ a
  Pstep _ Ps (recv p _ _ _ _) p′ _ _ _ a          with p ≟ p′
  Pstep _ Ps (recv p _ _ _ t) p′ _ _ _ here       | yes _ = -, (-, refl)
  Pstep _ Ps (recv p _ _ _ _) p′ _ _ _ (there₂ a) | yes _ = Ps _ _ _ _ a
  Pstep _ Ps (recv p _ _ _ _) p′ _ _ _ a          | no  _ = Ps _ _ _ _ a

e⊏head⊎e≡head : ∀ {s} → reachable s →
                ∀ p e → e ∈⁻ (s p) →
                e ⊏ s p ⊎ e ≡ s p
e⊏head⊎e≡head = induction P P₀ Pstep
  where
  P : State → Set
  P s = ∀ p e → e ∈⁻ (s p) →
        e ⊏ s p ⊎ e ≡ s p

  P₀ : P s₀
  P₀ _ _ here = inj₂ refl

  Pstep : ∀ {s s′} → reachable s → P s → s —⟶ s′ → P s′
  Pstep _ Ps (send p _) q _ _          with p ≟ q
  Pstep _ Ps (send p _) q _ here       | yes _ = inj₂ refl
  Pstep _ Ps (send p _) q _ (there₁ x) | yes _ with Ps _ _ x
  ...                                          | inj₁ a    = inj₁ (trans a processOrder₁)
  ...                                          | inj₂ refl = inj₁ processOrder₁
  Pstep _ Ps (send p _) q _ x          | no  _ = Ps _ _ x
  Pstep _ Ps (recv p _ _ _ _) q _ _          with p ≟ q
  Pstep _ Ps (recv p _ _ _ _) q _ here       | yes _ = inj₂ refl
  Pstep _ Ps (recv p _ _ _ _) q _ (there₂ x) | yes _ with Ps _ _ x
  ...                                                | inj₁ a    = inj₁ (trans a processOrder₂)
  ...                                                | inj₂ refl = inj₁ processOrder₂
  Pstep _ Ps (recv p _ _ _ _) q _ x          | no  _ = Ps _ _ x

⊏-total : ∀ {s} → reachable s →
                   ∀ p e e′ → e ∈⁻ (s p) → e′ ∈⁻ (s p) →
                   e ⊏ e′ ⊎ e′ ⊏ e ⊎ e ≡ e′
⊏-total = induction P P₀ Pstep
  where
  P : State → Set
  P s = ∀ p e e′ → e ∈⁻ (s p) → e′ ∈⁻ (s p) →
        e ⊏ e′ ⊎ e′ ⊏ e ⊎ e ≡ e′

  P₀ : P s₀
  P₀ _ _ _ here here = inj₂ (inj₂ refl)

  Pstep : ∀ {s s′} → reachable s → P s → s —⟶ s′ → P s′
  Pstep _ Ps (send p _) p′ _ _ _          _          with p ≟ p′
  Pstep _ Ps (send p _) p′ _ _ here       here       | yes _ = inj₂ (inj₂ refl)
  Pstep r Ps (send p _) p′ _ _ here       (there₁ y) | yes _ with e⊏head⊎e≡head r _ _ y
  ...                                                        | inj₁ a    = inj₂ (inj₁ (trans a processOrder₁))
  ...                                                        | inj₂ refl = inj₂ (inj₁ processOrder₁)
  Pstep r Ps (send p _) p′ _ _ (there₁ x) here       | yes _ with e⊏head⊎e≡head r _ _ x
  ...                                                        | inj₁ a    = inj₁ (trans a processOrder₁)
  ...                                                        | inj₂ refl = inj₁ processOrder₁
  Pstep _ Ps (send p _) p′ _ _ (there₁ x) (there₁ y) | yes _ = Ps _ _ _ x y
  Pstep _ Ps (send p _) p′ _ _ x          y          | no  _ = Ps _ _ _ x y
  Pstep _ Ps (recv p _ _ _ _) p′ _ _ _          _          with p ≟ p′
  Pstep _ Ps (recv p _ _ _ _) p′ _ _ here       here       | yes _ = inj₂ (inj₂ refl)
  Pstep r Ps (recv p _ _ _ _) p′ _ _ here       (there₂ y) | yes _ with e⊏head⊎e≡head r _ _ y
  ...                                                              | inj₁ a    = inj₂ (inj₁ (trans a processOrder₂))
  ...                                                              | inj₂ refl = inj₂ (inj₁ processOrder₂)
  Pstep r Ps (recv p _ _ _ _) p′ _ _ (there₂ x) here       | yes _ with e⊏head⊎e≡head r _ _ x
  ...                                                              | inj₁ a    = inj₁ (trans a processOrder₂)
  ...                                                              | inj₂ refl = inj₁ processOrder₂
  Pstep _ Ps (recv p _ _ _ _) p′ _ _ (there₂ x) (there₂ y) | yes _ = Ps _ _ _ x y
  Pstep _ Ps (recv p _ _ _ _) p′ _ _ x          y          | no  _ = Ps _ _ _ x y

fifo-delivery : State → Set
fifo-delivery s = ∀ p p′ (e e′ : Event p′) →
                  e  ∈ʳ⁻ (s p) →
                  e′ ∈ˢ⁻ e     →
                  e′ ∈ʳ⁻ (s p)

causal-delivery : State → Set
causal-delivery s = ∀ p p′ (e e′ : Event p′) →
                    e  ∈ʳ⁻ (s p) →
                    e′ ∈ˢ  e     →
                    e′ ∈ʳ⁻ (s p)
