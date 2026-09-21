/-
  **Secret presence: the generalised theorem applies where the old one does not.**

  A two-point chain `Lo ⊑ Hi` with two channels: `p`, public in every respect, and
  `s`, whose *presence* -- not merely its value -- is secret.  Presence is
  therefore not public, so `coalition_compositional_total` does not apply; but the
  peeling can be chosen presence-monotone, so `coalition_compositional_totalW`
  does.  The two hypotheses are thus not equivalent: the generalisation is
  strict.

  The instantiation uses an output-only component, which is coalition
  noninterfering for a trivial reason -- the point here is the security context,
  not the program.
-/
import InteractiveNI.LayerStepW

namespace InteractiveNI

namespace SecretPresence

open Classical
attribute [local instance] Classical.propDecidable

/-! ### The context -/

inductive L2 where | Lo | Hi
deriving DecidableEq

/-- The two-point chain. -/
def L2.le : L2 → L2 → Prop
  | .Lo, _ => True
  | .Hi, .Hi => True
  | .Hi, .Lo => False

theorem L2.le_refl : ∀ x : L2, L2.le x x := by intro x; cases x <;> trivial

theorem L2.le_trans : ∀ {x y z : L2}, L2.le x y → L2.le y z → L2.le x z := by
  intro x y z h1 h2; cases x <;> cases y <;> cases z <;> simp_all [L2.le]

inductive Ch2 where | p | s
deriving DecidableEq

/-- `s` has a secret presence: `ℓ₂(s) = Hi`. -/
def Sc2 : Sec L2 Ch2 where
  le := L2.le
  le_refl := L2.le_refl
  le_trans := L2.le_trans
  presL := fun c => match c with | .p => L2.Lo | .s => L2.Hi
  valL := fun c => match c with | .p => L2.Lo | .s => L2.Hi
  pres_le_val := fun c => by cases c <;> exact L2.le_refl _

/-- **Presence is not public**: the occurrence of `s` is invisible at `Lo`. -/
theorem not_pub : ¬ Sec.PublicPresence Sc2 := by
  intro h
  exact absurd (h Ch2.s L2.Lo) (by intro hc; exact hc)

/-! ### The peeling is presence-monotone -/

theorem vis_of {C : Sec.Coalition L2} {a : Ch2} {d : L2} (hd : C d)
    (hle : L2.le (Sc2.valL a) d) : Sc2.coalition.le (Sec.sing (Sc2.valL a)) C :=
  fun c hc => ⟨d, hd, by rw [show c = Sc2.valL a from hc]; exact hle⟩

theorem not_vis {C : Sec.Coalition L2} {x : L2}
    (h : ∀ d, C d → ¬ L2.le x d) : ¬ Sc2.coalition.le (Sec.sing x) C := by
  intro hh
  obtain ⟨d, hd, hle⟩ := hh _ rfl
  exact h d hd hle

theorem cplus_Hi : Sec.Cplus Sc2 L2.Hi L2.Lo := by intro h; exact h

theorem cplus_Lo_empty : ∀ d, ¬ Sec.Cplus Sc2 L2.Lo d := by
  intro d h; exact h trivial

/-- Every level admits a presence-monotone peeling. -/
theorem peelableM_Sc2 : ∀ m : L2, Sec.PeelableM Sc2 m [L2.Lo, L2.Hi] := by
  intro m
  cases m
  · -- `Lo`: nothing is visible at `C⁺`; peel `Lo`, then `Hi`
    refine ⟨[L2.Hi, L2.Lo], ?_, ⟨?_, ?_, trivial⟩, ⟨?_, ?_, trivial⟩⟩
    · intro a _; cases a
      · exact vis_of (Or.inl (Or.inr rfl)) (show L2.le L2.Lo L2.Lo from trivial)
      · exact vis_of (Or.inr rfl) (show L2.le L2.Hi L2.Hi from trivial)
    · -- flat at the layer adding `Hi`
      intro a _ ha; cases a
      · exact absurd (vis_of (a := Ch2.p) (Or.inr rfl)
          (show L2.le L2.Lo L2.Lo from trivial)) ha.2
      · exact show L2.le L2.Hi L2.Hi from trivial
    · -- flat at the layer adding `Lo`
      intro a _ _; cases a
      · exact show L2.le L2.Lo L2.Lo from trivial
      · exact show L2.le L2.Lo L2.Hi from trivial
    · -- presence-monotone at the layer adding `Hi`
      intro a _ _; cases a
      · exact show L2.le L2.Lo L2.Hi from trivial
      · exact show L2.le L2.Hi L2.Hi from trivial
    · -- presence-monotone at the layer adding `Lo`: `C⁺(Lo)` is empty
      intro a _ ha
      exact absurd ha (not_vis (fun d hd _ => cplus_Lo_empty d hd))
  · -- `Hi`: only `s` is hidden at `C⁺`
    refine ⟨[L2.Hi], ?_, ⟨?_, trivial⟩, ⟨?_, trivial⟩⟩
    · intro a _; cases a
      · exact vis_of (Or.inl cplus_Hi) (show L2.le L2.Lo L2.Lo from trivial)
      · exact vis_of (Or.inr rfl) (show L2.le L2.Hi L2.Hi from trivial)
    · intro a _ ha; cases a
      · exact absurd (vis_of (a := Ch2.p) cplus_Hi
          (show L2.le L2.Lo L2.Lo from trivial)) ha.2
      · exact show L2.le L2.Hi L2.Hi from trivial
    · intro a _ _; cases a
      · exact show L2.le L2.Lo L2.Hi from trivial
      · exact show L2.le L2.Hi L2.Hi from trivial

/-! ### An instantiation -/

inductive E where | e0 | e1
deriving DecidableEq

/-- An output-only component: it announces one bit on the secret channel. -/
inductive stepE : E → Act Ch2 Bool → E → Prop where
  | out (x : Bool) : stepE .e0 (.out Ch2.s x) .e1

theorem reach_no_inp : ∀ {q t q'}, Reach stepE q t q' →
    ∀ x ∈ t, ∀ (a : Ch2) (v : Bool), x ≠ Lbl.inp a v := by
  intro q t q' h
  induction h with
  | nil => intro x hx; exact absurd hx (by simp)
  | tau hs _ ih => exact ih
  | @inp q q' q'' a v t hs _ _ => cases hs
  | @out q q' q'' a v t hs _ ih =>
      intro x hx b u
      rcases List.mem_cons.mp hx with rfl | hx
      · exact fun hc => absurd hc (by simp)
      · exact ih x hx b u

/-- Output-only components are coalition noninterfering for a trivial reason:
    every run is a run of every strategy. -/
theorem E_coalitionNI : Sc2.coalition.StratTNI stepE E.e0 := by
  intro C w₁ w₂ _ _ _ t₁ h₁
  refine ⟨t₁, ⟨h₁.1, ?_⟩, rfl⟩
  intro u a v r hdec
  obtain ⟨q', hq⟩ := h₁.1
  exact absurd rfl (reach_no_inp hq (Lbl.inp a v) (by rw [hdec]; simp) a v)

theorem all_channels : ∀ a : Ch2, a ∈ [Ch2.p, Ch2.s] := by
  intro a; cases a <;> simp

theorem uses_E : Sec.UsesLevels Sc2 stepE E.e0 [L2.Lo, L2.Hi] := by
  intro t q h x hx
  cases hc : Sc2.valL x.chan <;> simp [hc]

/-- **The generalised theorem, instantiated with secret presence.**  The old
    theorem does not apply here (`not_pub`). -/
theorem E_par_E_total :
    Sc2.coalition.StratTNI (parStep stepE stepE) (E.e0, E.e0) :=
  Sec.coalition_compositional_totalW false uses_E uses_E
    peelableM_Sc2 E_coalitionNI E_coalitionNI

end SecretPresence

end InteractiveNI
