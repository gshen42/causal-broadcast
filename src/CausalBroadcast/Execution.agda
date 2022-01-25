------------------------------------------------------------------------
-- Defines the execution of a distributed system as a transition system.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module CausalBroadcast.Execution (n : ℕ) (Msg : Set) where

open import CausalBroadcast.Event n Msg
open import CausalBroadcast.History n Msg
import CausalBroadcast.Reachable as Reachable
open import Data.Fin using (Fin; _≟_)
open import Data.Product using (∃-syntax; -,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
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
  broadcast : ∀ {s} pᵇ m →
              s —⟶ update s pᵇ (send m)
  deliver   : ∀ {s} pᵈ pᵇ {e : Event pᵇ} →
              pᵈ ≢ pᵇ →
              e ∈ˢ⁻ s pᵇ →
              s —⟶ update s pᵈ (recv e)

fifo-delivery : State → Set
fifo-delivery s = ∀ p₀ p p′ (e : Event p) (e′ : Event p′) →
                  e  ∈ʳ⁻ (s p₀) →
                  e′ ∈ˢ⁻ e      →
                  e′ ∈ʳ⁻ (s p₀)

causal-delivery : State → Set
causal-delivery s = ∀ p₀ p p′ (e : Event p) (e′ : Event p′) →
                    e  ∈ʳ⁻ (s p₀) →
                    e′ ∈ˢ  e      →
                    e′ ∈ʳ⁻ (s p₀)

------------------------------------------------------------------------
-- Properties about executions

open Reachable s₀ _—⟶_

-- Receives are well-formed, i.e., the last event of the sending process is a send event.
wf-recv : ∀ {s} → reachable s →
          ∀ p (e : Event p) →
          e ∈ʳ⁻ s p →
          ∃[ m ] ∃[ e′ ] e ≡ send m e′
wf-recv = induction P P₀ Pstep
  where
  P : State → Set
  P s = ∀ p (e : Event p) →
        e ∈ʳ⁻ s p →
        ∃[ m ] ∃[ e′ ] e ≡ send m e′

  P₀ : P s₀
  P₀ _ _ ()

  Pstep : ∀ {s s′} → reachable s → P s → s —⟶ s′ → P s′
  Pstep _ Ps (broadcast pᵇ _) p _ x          with pᵇ ≟ p
  Pstep _ Ps (broadcast pᵇ _) p _ (there₁ x) | yes _ = Ps _ _ x
  Pstep _ Ps (broadcast pᵇ _) p _ x          | no  _ = Ps _ _ x
  Pstep _ Ps (deliver pᵈ pᵇ _ _) p _ x          with pᵈ ≟ p
  Pstep _ Ps (deliver pᵈ pᵇ _ y) p _ here       | yes _ = ∈ˢ→send (∈ˢ⁻→∈ˢ y)
  Pstep _ Ps (deliver pᵈ pᵇ _ _) p _ (there₂ x) | yes _ = Ps _ _ x
  Pstep _ Ps (deliver pᵈ pᵇ _ _) p _ x          | no  _ = Ps _ _ x
