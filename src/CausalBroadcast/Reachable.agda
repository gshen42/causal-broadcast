module CausalBroadcast.Reachable {State : Set} (s₀ : State) (_—⟶_ : State → State → Set) where

data _—⟶*_ : State → State → Set where
  lift  : ∀ {s s′} → s —⟶ s′ → s —⟶* s′
  refl  : ∀ {s} → s —⟶* s
  trans : ∀ {s s′ s″} → s —⟶* s′ → s′ —⟶* s″ → s —⟶* s″

reachable : State → Set
reachable = s₀ —⟶*_

-- Induction principle for reachable states.
induction : ∀ (P : State → Set) →
            P s₀ →
            (∀ {s s′} → reachable s → P s → s —⟶ s′ → P s′) →
            ∀ {s} → reachable s → P s
induction P P₀ Pstep r = Pstep→Psteps Pstep refl P₀ r
  where
  Pstep→Psteps : (∀ {s s′} → reachable s → P s → s —⟶  s′ → P s′) →
                 ∀ {s s′} → reachable s → P s → s —⟶* s′ → P s′
  Pstep→Psteps Pstep r Ps (lift a)    = Pstep r Ps a
  Pstep→Psteps Pstep r Ps refl        = Ps
  Pstep→Psteps Pstep r Ps (trans a b) = Pstep→Psteps Pstep (trans r a) (Pstep→Psteps Pstep r Ps a) b
