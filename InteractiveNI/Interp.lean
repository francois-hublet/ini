/-
  Mixing two strategies channel by channel.

  The hybrid of the composition proof never replaces `ω₁` by `ω₂` in one jump:
  it moves one class of channels at a time.  `mixStrat P ω₁ ω₂` follows `ω₁` on
  the channels satisfying `P` and `ω₂` on the others, and is legal because the
  conditions on a strategy constrain each channel separately.  Nothing here is
  specific to parallel composition -- it is a statement
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

/-! ### The three properties of the hybrid -/

section
variable {m mu : Level} {w₁ w₂ : S.Strategy Value}

end

end Sec

end InteractiveNI
