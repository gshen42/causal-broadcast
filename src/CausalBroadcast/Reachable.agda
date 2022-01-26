------------------------------------------------------------------------
-- Define reachable states for a given transition system and correspond-
-- ing induction principles.
------------------------------------------------------------------------

module CausalBroadcast.Reachable
  {State : Set}
  (s₀ : State)
  (_==>_ : State → State → Set)
  where

open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)

-- reflxive transitive closure of `_==>_`
data _==>*_ : State → State → Set where
  lift  : ∀ {s s′} → s ==> s′ → s ==>* s′
  refl  : ∀ {s} → s ==>* s
  trans : ∀ {s s′ s″} → s ==>* s′ → s′ ==>* s″ → s ==>* s″

reachable : State → Set
reachable = s₀ ==>*_

-- Induction principle for reachable states, it requires the induction
-- hypothesis `P` to be an inductive invariant.
induction : ∀ (P : State → Set) →
            P s₀ →
            (∀ {s s′} → P s → s ==> s′ → P s′) →
            ∀ {s} → reachable s → P s
induction P P₀ Pstep r = Pstep→Psteps Pstep P₀ r
  where
  Pstep→Psteps : (∀ {s s′} → P s → s ==> s′ → P s′) →
                 ∀ {s s′} → P s → s ==>* s′ → P s′
  Pstep→Psteps Pstep Ps (lift a)    = Pstep Ps a
  Pstep→Psteps Pstep Ps refl        = Ps
  Pstep→Psteps Pstep Ps (trans a b) = Pstep→Psteps Pstep (Pstep→Psteps Pstep Ps a) b

-- Same as `induction` except `P` doesn't have to be an inductive
-- invariant. It does this by adding `reachable s` to `Pstep`.
induction⁺ : ∀ (P : State → Set) →
             P s₀ →
             (∀ {s s′} → reachable s → P s → s ==> s′ → P s′) →
             ∀ {s} → reachable s → P s
induction⁺ P P₀ Pstep r =
  proj₂ (induction (λ s → reachable s × P s)
                   (refl , P₀)
                   (λ (x , y) z → trans x (lift z) , Pstep x y z)
                   r)
