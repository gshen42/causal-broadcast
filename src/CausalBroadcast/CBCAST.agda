------------------------------------------------------------------------
-- Defines the execution of CBCAST as a transition system.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _+_; _≤_)

module CausalBroadcast.CBCAST (n : ℕ) (Msg : Set) where

open import CausalBroadcast.Event n Msg
open import CausalBroadcast.Execution n Msg
open import CausalBroadcast.History n Msg
import CausalBroadcast.Reachable as Reachable
open import CausalBroadcast.VectorClock n
open import Data.Bool using (true;false)
open import Data.Fin using (Fin; _≟_)
open import Data.Product using (_×_; ∃; _,_; ∃-syntax; -,_;Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_;sym)
open import Relation.Nullary using (yes; no;_because_)

vc : ∀{p} → Event p → VC
vc {p} (init) = vc₀
vc {p} (send _ e ) = tick p (vc e)
vc {p} (recv e e′) = combine (vc e) (vc e′)

deliverable : ∀ p → VC → VC → Set
deliverable p vc vc′ =
   ∀ k → ((k ≡ p) → vc [ k ] ≡ vc′ [ k ] + 1) ×
         ((k ≢ p) → vc [ k ] ≤ vc′ [ k ])

data _—⟶ᶜ_ : State → State → Set where
  send : ∀ {s} p m →
         s —⟶ᶜ update s p (send m)
  recv : ∀ {s} p p′ m {e} →
         p ≢ p′ →
         send m e ∈⁻ s p′ →
         deliverable p′ (vc (send m e)) (vc (s p)) →
         s —⟶ᶜ update s p (recv (send m e))

open Reachable s₀ _—⟶ᶜ_

causal-deliveryᶜ : ∀ s → reachable s →
                   causal-delivery s
