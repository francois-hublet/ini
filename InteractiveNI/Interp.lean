/-
  The interpolation reduction (Theorem A of `chain-composition.md`).

  Over a totally ordered lattice, compositionality of INI need not be proved by
  moving from `ω₁` to `ω₂` in one jump.  One may instead move one *layer of
  channels* at a time, from the top down, because a single-layer move can be
  matched while preserving a much finer projection than `π_ℓ`.

  This file proves that reduction: `MatchesAt` at a level `m` follows from
  `MatchesAt` at the next level up together with the single-layer statement
  (SLP).  Nothing here is specific to parallel composition -- it is a statement
  about an arbitrary transition system -- which is why it applies to `parStep`.
-/
import InteractiveNI.Freeze

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

namespace Sec

variable {Level Channel Value : Type} {S : Sec Level Channel}

/-! ### Hybrid strategies -/

/-- `mixStrat P w₁ w₂` follows `w₂` on the channels satisfying `P` and `w₁`
    elsewhere.  Legality is inherited channelwise. -/
noncomputable def mixStrat (P : Channel → Prop) (w₁ w₂ : S.Strategy Value) :
    S.Strategy Value where
  ω := fun a t => if P a then w₂.ω a t else w₁.ω a t
  resp_val := by
    intro a t₁ t₂ h
    by_cases hp : P a
    · rw [if_pos hp, if_pos hp]; exact w₂.resp_val a t₁ t₂ h
    · rw [if_neg hp, if_neg hp]; exact w₁.resp_val a t₁ t₂ h
  resp_pres := by
    intro a t₁ t₂ h
    by_cases hp : P a
    · rw [if_pos hp, if_pos hp]; exact w₂.resp_pres a t₁ t₂ h
    · rw [if_neg hp, if_neg hp]; exact w₁.resp_pres a t₁ t₂ h

@[simp] theorem mixStrat_pos {P : Channel → Prop} {w₁ w₂ : S.Strategy Value}
    {a : Channel} (hp : P a) (t : List (Lbl Channel Value)) :
    (mixStrat P w₁ w₂).ω a t = w₂.ω a t := by
  show (if P a then w₂.ω a t else w₁.ω a t) = _
  rw [if_pos hp]

@[simp] theorem mixStrat_neg {P : Channel → Prop} {w₁ w₂ : S.Strategy Value}
    {a : Channel} (hp : ¬ P a) (t : List (Lbl Channel Value)) :
    (mixStrat P w₁ w₂).ω a t = w₁.ω a t := by
  show (if P a then w₂.ω a t else w₁.ω a t) = _
  rw [if_neg hp]

/-- The channels whose value level lies in the layer `(m, mu]`.  These are the
    channels on which the hybrid differs from `w₂`. -/
def Layer (S : Sec Level Channel) (m mu : Level) (a : Channel) : Prop :=
  S.le (S.valL a) mu ∧ ¬ S.le (S.valL a) m

/-- Channels strictly above `mu`, on which the hybrid already follows `w₂`. -/
def AboveL (S : Sec Level Channel) (mu : Level) (a : Channel) : Prop :=
  ¬ S.le (S.valL a) mu

/-! ### The three properties of the hybrid -/

section
variable {m mu : Level} {w₁ w₂ : S.Strategy Value}

/-- The hybrid is `mu`-equivalent to `w₁`: it only moved channels that are
    invisible at `mu`.  The presence side needs that a channel whose value level
    is above `mu` has its presence level at or below `m` -- automatic when
    presence levels are public, as in every example of the paper. -/
theorem seq_mix_up
    (hpres : ∀ a, AboveL S mu a → S.le (S.presL a) m)
    (hw : S.seq m w₁ w₂) :
    S.seq mu w₁ (mixStrat (AboveL S mu) w₁ w₂) := by
  intro a t
  by_cases hp : AboveL S mu a
  · refine ⟨fun hl => absurd hl hp, fun hl => ?_⟩
    rw [mixStrat_pos hp]
    exact (hw a t).2 (hpres a hp)
  · rw [mixStrat_neg hp]
    exact ⟨fun _ => rfl, fun _ => dotEq.refl _⟩

/-- The hybrid is still `m`-equivalent to `w₂`, so the single-layer statement
    may be applied to the pair `(hybrid, w₂)`. -/
theorem seq_mix_down (_hle : S.le m mu) (hw : S.seq m w₁ w₂) :
    S.seq m (mixStrat (AboveL S mu) w₁ w₂) w₂ := by
  intro a t
  by_cases hp : AboveL S mu a
  · rw [mixStrat_pos hp]; exact ⟨fun _ => rfl, fun _ => dotEq.refl _⟩
  · rw [mixStrat_neg hp]
    exact ⟨fun hl => (hw a t).1 hl, fun hl => (hw a t).2 hl⟩

/-- **The hybrid differs from `w₂` only on the layer `(m, mu]`.**  This is the
    payload of the interpolation: one layer of channels at a time. -/
theorem mix_differs_only_on_layer (_hle : S.le m mu) (hw : S.seq m w₁ w₂) :
    ∀ a, ¬ Layer S m mu a → ∀ t, (mixStrat (AboveL S mu) w₁ w₂).ω a t = w₂.ω a t := by
  intro a hnl t
  by_cases hp : AboveL S mu a
  · rw [mixStrat_pos hp]
  · rw [mixStrat_neg hp]
    have hlow : S.le (S.valL a) m := by
      unfold AboveL at hp
      rcases Classical.em (S.le (S.valL a) m) with h | h
      · exact h
      · exact absurd ⟨Classical.byContradiction hp, h⟩ hnl
    exact (hw a t).1 hlow

end

/-! ### The reduction -/

/-- `MatchesAt … ℓ` is the level-`ℓ` instance of INI. -/
def MatchesAt {St : Type} (step : St → Act Channel Value → St → Prop)
    (W : S.Strategy Value → Prop) (s : St) (ℓ : Level) : Prop :=
  ∀ w₁ w₂, W w₁ → W w₂ → S.seq ℓ w₁ w₂ →
    ∀ t₁, S.produces step w₁ s t₁ → ∃ t₂, S.produces step w₂ s t₂ ∧ S.teq ℓ t₁ t₂

theorem INI_iff_matchesAt {St : Type} {step : St → Act Channel Value → St → Prop}
    {W : S.Strategy Value → Prop} {s : St} :
    S.INI step W s ↔ ∀ ℓ, MatchesAt step W s ℓ :=
  ⟨fun h ℓ => fun w₁ w₂ h₁ h₂ hs t₁ hp => h ℓ w₁ w₂ h₁ h₂ hs t₁ hp,
   fun h ℓ w₁ w₂ h₁ h₂ hs t₁ hp => h ℓ w₁ w₂ h₁ h₂ hs t₁ hp⟩

/-- The single-layer statement (SLP): matching at level `m` when the two
    strategies differ only on the channels of the layer `(m, mu]`. -/
def SingleLayer {St : Type} (step : St → Act Channel Value → St → Prop)
    (W : S.Strategy Value → Prop) (s : St) (m mu : Level) : Prop :=
  ∀ w w', W w → W w' → S.seq m w w' →
    (∀ a, ¬ Layer S m mu a → ∀ t, w.ω a t = w'.ω a t) →
    ∀ t₁, S.produces step w s t₁ → ∃ t₂, S.produces step w' s t₂ ∧ S.teq m t₁ t₂

/-- **Theorem A (interpolation step).**  Matching at level `m` follows from
    matching at the next level up together with the single-layer statement.
    Iterating from the top level downwards reduces compositionality of INI over
    a chain to the single-layer case. -/
theorem interpolate_step {St : Type} {step : St → Act Channel Value → St → Prop}
    {W : S.Strategy Value → Prop} {s : St} {m mu : Level}
    (hle : S.le m mu)
    (hpres : ∀ a, AboveL S mu a → S.le (S.presL a) m)
    (hWmix : ∀ w₁ w₂, W w₁ → W w₂ → W (mixStrat (AboveL S mu) w₁ w₂))
    (hUp : MatchesAt step W s mu)
    (hSLP : SingleLayer step W s m mu) :
    MatchesAt step W s m := by
  intro w₁ w₂ hW₁ hW₂ hw t₁ hp
  have hWm : W (mixStrat (AboveL S mu) w₁ w₂) := hWmix w₁ w₂ hW₁ hW₂
  -- step 1: move the channels strictly above `mu`, preserving `π_mu`
  obtain ⟨tm, hpm, htm⟩ := hUp w₁ _ hW₁ hWm (seq_mix_up hpres hw) t₁ hp
  -- step 2: move the single layer `(m, mu]`, preserving `π_m`
  obtain ⟨t₂, hp₂, ht₂⟩ :=
    hSLP _ w₂ hWm hW₂ (seq_mix_down hle hw) (mix_differs_only_on_layer hle hw) tm hpm
  exact ⟨t₂, hp₂, (teq_mono hle htm).trans ht₂⟩

end Sec

end InteractiveNI
