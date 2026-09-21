/-
  The freeze lemma (Theorem B of `chain-composition.md`).

  When one component of a parallel composition is held fixed, the global
  strategy induces a strategy on the other component:

      ν_α(u)  =  ω_α(σ_α(u))

  where `σ_α(u)` reinserts the frozen partner's contribution into `u`.  Two
  things have to be checked, and they are the whole content of the lemma:

  * `ν` is a *legal* strategy — this needs `σ_α` to be compatible with
    `=_{valL α}` and `=_{presL α}`.  For the ℓ-skeleton merge used in §3 of the
    notes this is exactly where comparability of `valL α` with `ℓ` is used: an
    incomparable level satisfies neither clause, which is why the construction
    breaks on the counterexample of §3 of the paper.
  * `ν` preserves ℓ-equivalence of strategies — this is immediate once `σ` does
    not depend on the strategy, and is what lets `INI` be applied to a component
    in a composed context.

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

/-- The strategy induced on a component by freezing its partner. -/
def Insertion.induced (ins : Insertion S Value) (w : S.Strategy Value) : S.Strategy Value where
  ω := fun a t => w.ω a (ins.σ a t)
  resp_val  := fun a t₁ t₂ h => w.resp_val  a _ _ (ins.resp_val  a t₁ t₂ h)
  resp_pres := fun a t₁ t₂ h => w.resp_pres a _ _ (ins.resp_pres a t₁ t₂ h)

@[simp] theorem Insertion.induced_apply (ins : Insertion S Value) (w : S.Strategy Value)
    (a : Channel) (t : List (Lbl Channel Value)) :
    (ins.induced w).ω a t = w.ω a (ins.σ a t) := rfl

/-- **Freeze lemma.**  Freezing a partner preserves ℓ-equivalence of strategies,
    so `INI` of a component may be applied inside a composed context. -/
theorem seq_induced {ℓ : Level} (ins : Insertion S Value) {w₁ w₂ : S.Strategy Value}
    (hw : S.seq ℓ w₁ w₂) : S.seq ℓ (ins.induced w₁) (ins.induced w₂) :=
  fun a t => ⟨fun hl => (hw a (ins.σ a t)).1 hl, fun hl => (hw a (ins.σ a t)).2 hl⟩

/-- More generally, two *different* frozen partners that are ℓ-equivalent at every
    channel still induce ℓ-equivalent strategies. -/
theorem seq_induced' {ℓ : Level} (ins ins' : Insertion S Value) {w₁ w₂ : S.Strategy Value}
    (hw : S.seq ℓ w₁ w₂)
    (hσ : ∀ a t, S.le (S.valL a) ℓ → ins.σ a t = ins'.σ a t)
    (hσ' : ∀ a t, S.le (S.presL a) ℓ → ins.σ a t = ins'.σ a t) :
    S.seq ℓ (ins.induced w₁) (ins'.induced w₂) := by
  intro a t
  refine ⟨fun hl => ?_, fun hl => ?_⟩
  · rw [Insertion.induced_apply, Insertion.induced_apply, hσ a t hl]
    exact (hw a (ins'.σ a t)).1 hl
  · rw [Insertion.induced_apply, Insertion.induced_apply, hσ' a t hl]
    exact (hw a (ins'.σ a t)).2 hl

/-- Prepending a fixed context is an insertion; this recovers `prependStrat`. -/
def prependIns (u : List (Lbl Channel Value)) : Insertion S Value where
  σ := fun _ t => u ++ t
  resp_val  := fun _ _ _ h => teq_append (rfl : S.teq _ u u) h
  resp_pres := fun _ _ _ h => teq_append (rfl : S.teq _ u u) h

theorem prependIns_induced (u : List (Lbl Channel Value)) (w : S.Strategy Value) :
    (prependIns u).induced w = prependStrat u w := rfl

end Sec

end InteractiveNI
