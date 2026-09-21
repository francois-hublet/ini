/-
  Insertions: reinserting a partner's labels into a trace.

  When one component of a parallel composition is held fixed, a trace of the
  other is turned into a trace of the composition by reinserting the partner's
  contribution.  An `Insertion` packages such a map together with the two
  properties that make it usable:

  * the inserted trace is compatible with `=_{valL α}` and `=_{presL α}`, so
    that the induced strategy is legal;
  * the insertion does not depend on the strategy, so that it preserves
    ℓ-equivalence of strategies, which is what lets INI be applied to a
    component inside a composed context.

  `prependStrat` (Det.lean) is the special case `σ_α(u) = u₀ ++ u`.
-/
import InteractiveNI.Det

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

namespace Sec

variable {Level Channel Value : Type} {S : Sec Level Channel}

/-- A *context insertion*: a family `σ_α` of trace transformations that is
    compatible with the two projections a strategy on `α` is allowed to see.
    This is the abstract interface satisfied by "reinsert the frozen partner's
    labels at the positions they occupy in the original run". -/
structure Insertion (S : Sec Level Channel) (Value : Type) where
  σ : Channel → List (Lbl Channel Value) → List (Lbl Channel Value)
  resp_val  : ∀ a t₁ t₂, S.teq (S.valL a) t₁ t₂ → S.teq (S.valL a) (σ a t₁) (σ a t₂)
  resp_pres : ∀ a t₁ t₂, S.teq (S.presL a) t₁ t₂ → S.teq (S.presL a) (σ a t₁) (σ a t₂)

end Sec

end InteractiveNI
