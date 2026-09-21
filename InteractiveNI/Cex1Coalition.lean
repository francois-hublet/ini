/-
  The counterexample program of Theorem 10 is **not** coalition-noninterfering.

  This machine-checks the remark of §3: the construction of Theorem 10 works only
  because `𝓛` contains no level standing for the coalition `{H₁, H₃}` -- that is,
  for an observer who sees both the channel on which `P_A` discloses its mask and
  the channel on which it delivers its output.  Under the coalition reading of
  noninterference (`InteractiveNI/Coalition.lean`), `P_A` is rejected outright.

  Together with `A_NI` of `Cex1.lean`, this shows that coalition noninterference
  is *strictly* stronger than `Strat-NI`.
-/
import InteractiveNI.Cex1
import InteractiveNI.Coalition

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

namespace Cex1

/-- The coalition of the user of the mask channel `H₁` and of the observer `H₃`. -/
def coalC : Sec.Coalition L5 := fun c => c = L5.H1 ∨ c = L5.H3

/-- The channels whose *values* the coalition is cleared to read. -/
def visC (c : L5) : Bool := (c == L5.Lo) || (c == L5.H1) || (c == L5.H3)

theorem coalC_le_iff (c : L5) :
    Sc.coalition.le (Sec.sing c) coalC ↔ visC c = true := by
  constructor
  · intro h
    obtain ⟨d, hd, hcd⟩ := h c rfl
    rcases hd with rfl | rfl <;>
      rcases hcd with h1 | h1 | h1 <;>
      first
        | (subst h1; rfl)
        | exact absurd h1 (by simp)
  · intro h x hx
    have key : ∃ d, coalC d ∧ Sc.le c d := by
      revert h
      cases c <;> intro h
      · exact ⟨L5.H1, Or.inl rfl, Or.inl rfl⟩
      · exact absurd h (by simp [visC])
      · exact ⟨L5.H1, Or.inl rfl, Or.inr (Or.inl rfl)⟩
      · exact absurd h (by simp [visC])
      · exact ⟨L5.H3, Or.inr rfl, Or.inr (Or.inl rfl)⟩
      · exact absurd h (by simp [visC])
    obtain ⟨d, hd, hcd⟩ := key
    exact ⟨d, hd, by rw [hx]; exact hcd⟩

/-! ### Computing `π_C` -/

def hideC (c : L5) (v : Bool) : Option Bool := if visC c then some v else none

def pjC : Lbl L5 Bool → PLbl L5 Bool
  | .inp c v => .inp c (hideC c v)
  | .out c v => .out c (hideC c v)

theorem projLblC_eq (l : Lbl L5 Bool) : Sc.coalition.projLbl coalC l = some (pjC l) := by
  have hpres : ∀ c : L5, Sc.coalition.le (Sc.coalition.presL c) coalC := by
    intro c
    exact (coalC_le_iff L5.Lo).mpr rfl
  cases l with
  | inp c v =>
      by_cases h : Sc.coalition.le (Sc.coalition.valL c) coalC
      · rw [Sec.projLbl_inp_full (hpres c) h]
        have : visC c = true := (coalC_le_iff c).mp h
        simp [pjC, hideC, this]
      · rw [Sec.projLbl_inp_pres (hpres c) h]
        have : ¬ (visC c = true) := fun hc => h ((coalC_le_iff c).mpr hc)
        simp [pjC, hideC, this]
  | out c v =>
      by_cases h : Sc.coalition.le (Sc.coalition.valL c) coalC
      · rw [Sec.projLbl_out_full (hpres c) h]
        have : visC c = true := (coalC_le_iff c).mp h
        simp [pjC, hideC, this]
      · rw [Sec.projLbl_out_pres (hpres c) h]
        have : ¬ (visC c = true) := fun hc => h ((coalC_le_iff c).mpr hc)
        simp [pjC, hideC, this]

theorem projC_eq_map (t : List (Lbl L5 Bool)) :
    Sc.coalition.proj coalC t = t.map pjC := by
  induction t with
  | nil => rfl
  | cons l t ih => rw [Sec.proj_cons_some (projLblC_eq l), ih, List.map_cons]

theorem teqC_iff (t t' : List (Lbl L5 Bool)) :
    Sc.coalition.teq coalC t t' ↔ t.map pjC = t'.map pjC := by
  unfold Sec.teq; rw [projC_eq_map, projC_eq_map]

/-! ### Two coalition-equivalent strategies -/

/-- `ω_b` offers `b` on `H` and `false` on `H₂`, and nothing anywhere else. -/
noncomputable def coOmega (b : Bool) : Sc.Strategy Bool where
  ω := fun c _ v => if c = L5.H then v = b else if c = L5.H2 then v = false else False
  resp_val := fun _ _ _ _ => rfl
  resp_pres := fun _ _ _ _ => Iff.rfl

theorem coOmega_seq :
    Sc.coalition.seq coalC (Sec.Strategy.toCoalition (coOmega false))
      (Sec.Strategy.toCoalition (coOmega true)) := by
  intro a t
  refine ⟨fun hl => ?_, fun _ => ?_⟩
  · have hv : visC a = true := (coalC_le_iff a).mp hl
    show (coOmega false).ω a t = (coOmega true).ω a t
    revert hv
    cases a <;> intro hv <;> simp [coOmega, visC] at hv ⊢
  · show dotEq ((coOmega false).ω a t) ((coOmega true).ω a t)
    cases a <;>
      simp [coOmega, dotEq, VSet.isEmpty] <;>
      exact ⟨fun h => absurd rfl (h true), fun h => absurd rfl (h false)⟩

/-! ### `P_A` fails coalition noninterference -/

/-- The run of `P_A` under `ω_false` with the mask `x = false`. -/
def tA : List (Lbl L5 Bool) :=
  [Lbl.inp L5.H false, Lbl.out L5.H1 true, Lbl.inp L5.H2 false, Lbl.out L5.H3 false]

theorem tA_reach : Reach stepA AState.a0 tA AState.a5 := by
  refine Reach.inp (stepA.inH false) ?_
  refine Reach.tau (stepA.x0 false) ?_
  refine Reach.out (stepA.outH1 false false) ?_
  refine Reach.inp (stepA.inH2 false false false) ?_
  exact Reach.out (stepA.outH3 false false false) Reach.nil

theorem tA_produces :
    Sc.coalition.produces stepA (Sec.Strategy.toCoalition (coOmega false)) AState.a0 tA := by
  refine ⟨⟨AState.a5, tA_reach⟩, ?_⟩
  intro t₁ a v t₂ heq
  show (coOmega false).ω a t₁ v
  rcases t₁ with _ | ⟨l0, t₁⟩
  · simp [tA] at heq; obtain ⟨⟨rfl, rfl⟩, -⟩ := heq; simp [coOmega]
  rcases t₁ with _ | ⟨l1, t₁⟩
  · simp [tA] at heq
  rcases t₁ with _ | ⟨l2, t₁⟩
  · simp [tA] at heq
    obtain ⟨-, -, ⟨rfl, rfl⟩, -⟩ := heq
    simp [coOmega]
  rcases t₁ with _ | ⟨l3, t₁⟩ <;> simp [tA] at heq

theorem no_matchC (t' : List (Lbl L5 Bool))
    (hprod : Sc.coalition.produces stepA (Sec.Strategy.toCoalition (coOmega true)) AState.a0 t')
    (hteq : Sc.coalition.teq coalC tA t') : False := by
  obtain ⟨⟨s', hreach⟩, hcons⟩ := hprod
  have hmap : tA.map pjC = t'.map pjC := (teqC_iff _ _).mp hteq
  have hlen : t'.length = 4 := by
    have := congrArg List.length hmap
    simpa [tA] using this.symm
  obtain ⟨r, x, y, rfl⟩ := specA0_full (reachA_spec hreach) hlen
  -- the strategy forces the value read on `H`
  have hr : r = true := by
    have := hcons [] L5.H r _ rfl
    simpa [coOmega] using this
  subst hr
  -- and the value read on `H₂`
  have hy : y = false := by
    have := hcons [Lbl.inp L5.H true, Lbl.out L5.H1 (!x)] L5.H2 y
      [Lbl.out L5.H3 (Bool.xor true (Bool.xor x y))] rfl
    simpa [coOmega] using this
  subst hy
  -- the coalition sees both the mask on `H₁` and the output on `H₃`
  cases x <;> simp [tA, pjC, hideC, visC] at hmap

/-- **The counterexample program is not coalition-noninterfering.** -/
theorem A_not_coalitionNI : ¬ Sc.coalition.StratNI stepA AState.a0 := by
  intro hNI
  obtain ⟨t₂, hprod, hteq⟩ :=
    hNI coalC (Sec.Strategy.toCoalition (coOmega false)) (Sec.Strategy.toCoalition (coOmega true))
      trivial trivial coOmega_seq tA tA_produces
  exact no_matchC t₂ hprod hteq

/-- **Coalition noninterference is strictly stronger than `Strat-NI`.** -/
theorem coalitionNI_strictly_stronger :
    Sc.StratNI stepA AState.a0 ∧ ¬ Sc.coalition.StratNI stepA AState.a0 :=
  ⟨A_NI, A_not_coalitionNI⟩

end Cex1

end InteractiveNI
