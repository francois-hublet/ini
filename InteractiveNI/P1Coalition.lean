/-
  The program `P₁` of the conclusion is coalition-noninterfering.

      P₁ = (x := 0 | x := 1); in_H(y); out_L(x ⊕ y)

  `P₁` is the program the conclusion asks a *stricter* notion of noninterference to
  keep accepting: non-determinism is used here precisely in order to achieve
  security, by masking the high input `y` with a fresh bit `x`.  Together with
  `Cex1Coalition.A_not_coalitionNI`, this shows that coalition noninterference
  rejects the counterexample of §3 while still accepting `P₁`, i.e. that it meets
  requirement (b) of the conclusion.
-/
import InteractiveNI.Coalition

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

namespace P1

/-! ### A two-point lattice -/

inductive L2 where
  | Lo | Hi
deriving DecidableEq, Repr

def L2.le (a b : L2) : Prop := a = L2.Lo ∨ a = b

theorem L2.le_refl (a : L2) : L2.le a a := Or.inr rfl

theorem L2.le_trans {a b c : L2} (h₁ : L2.le a b) (h₂ : L2.le b c) : L2.le a c := by
  rcases h₁ with rfl | rfl
  · exact Or.inl rfl
  · exact h₂

/-- Channels are level names: `Lo` is the public channel `L`, `Hi` the secret one `H`. -/
def Sc2 : Sec L2 L2 where
  le := L2.le
  le_refl := L2.le_refl
  le_trans := L2.le_trans
  presL := fun _ => L2.Lo
  valL := fun c => c
  pres_le_val := fun _ => Or.inl rfl

/-! ### The program -/

inductive P1State where
  | p0                    -- before `x := 0 | x := 1`
  | p1 (x : Bool)         -- before `in_H(y)`
  | p2 (x y : Bool)       -- before `out_L(x ⊕ y)`
  | p3                    -- done
deriving DecidableEq

inductive stepP1 : P1State → Act L2 Bool → P1State → Prop where
  | ch   (x)   : stepP1 .p0 .tau (.p1 x)
  | inH  (x y) : stepP1 (.p1 x) (.inp L2.Hi y) (.p2 x y)
  | outL (x y) : stepP1 (.p2 x y) (.out L2.Lo (Bool.xor x y)) .p3

/-! ### The traces of `P₁` -/

def specP3 (u : List (Lbl L2 Bool)) (s' : P1State) : Prop := u = [] ∧ s' = .p3

def specP2 (x y : Bool) (u : List (Lbl L2 Bool)) (s' : P1State) : Prop :=
  (u = [] ∧ s' = .p2 x y) ∨ (u = [Lbl.out L2.Lo (Bool.xor x y)] ∧ s' = .p3)

def specP1' (x : Bool) (u : List (Lbl L2 Bool)) (s' : P1State) : Prop :=
  (u = [] ∧ s' = .p1 x) ∨ (∃ y u', u = Lbl.inp L2.Hi y :: u' ∧ specP2 x y u' s')

def specP0 (u : List (Lbl L2 Bool)) (s' : P1State) : Prop :=
  (u = [] ∧ s' = .p0) ∨ (∃ x, specP1' x u s')

def specP : P1State → List (Lbl L2 Bool) → P1State → Prop
  | .p0 => specP0
  | .p1 x => specP1' x
  | .p2 x y => specP2 x y
  | .p3 => specP3

theorem reachP_spec {s : P1State} {u : List (Lbl L2 Bool)} {s' : P1State}
    (h : Reach stepP1 s u s') : specP s u s' := by
  induction h with
  | @nil s =>
      cases s <;>
        first
          | exact Or.inl ⟨rfl, rfl⟩
          | exact ⟨rfl, rfl⟩
  | tau hs _ ih => cases hs with | ch x => exact Or.inr ⟨x, ih⟩
  | @inp s s' s'' a v t hs _ ih => cases hs; exact Or.inr ⟨v, _, rfl, ih⟩
  | @out s s' s'' a v t hs _ ih => cases hs; exact Or.inr ⟨by rw [ih.1], ih.2⟩

/-! ### `P₁` is coalition-noninterfering -/

/-- If the coalition `C` can see the secret channel, the two strategies coincide
    on every channel. -/
theorem eq_of_sees_Hi {C : Sec.Coalition L2} {w₁ w₂ : Sc2.coalition.Strategy Bool}
    (hseq : Sc2.coalition.seq C w₁ w₂) (hHi : ∃ d, C d ∧ L2.le L2.Hi d)
    (a : L2) (t : List (Lbl L2 Bool)) : w₁.ω a t = w₂.ω a t := by
  refine (hseq a t).1 ?_
  obtain ⟨d, hd, hled⟩ := hHi
  intro c hc
  refine ⟨d, hd, ?_⟩
  rw [show c = Sc2.valL a from hc]
  cases a
  · exact Or.inl rfl
  · exact hled

/-- If the coalition is empty it observes nothing. -/
theorem proj_empty {C : Sec.Coalition L2} (hC : ¬ ∃ d, C d)
    (t : List (Lbl L2 Bool)) : Sc2.coalition.proj C t = [] := by
  induction t with
  | nil => rfl
  | cons l t ih =>
      refine Eq.trans (Sec.proj_cons_none ?_ t) ih
      rw [Sec.projLbl_eq_none_iff]
      intro h
      exact hC (by obtain ⟨d, hd, -⟩ := h (Sc2.presL (l.chan)) rfl; exact ⟨d, hd⟩)

/-- **`P₁` satisfies coalition noninterference.** -/
theorem P1_coalitionNI : Sc2.coalition.StratNI stepP1 P1State.p0 := by
  intro C w₁ w₂ _ _ hseq t₁ hprod
  obtain ⟨⟨s', hreach⟩, hcons⟩ := hprod
  by_cases hHi : ∃ d, C d ∧ L2.le L2.Hi d
  · -- the coalition sees the secret channel: the strategies are equal, replay `t₁`
    refine ⟨t₁, ⟨⟨s', hreach⟩, ?_⟩, rfl⟩
    intro u a v r heq
    rw [← eq_of_sees_Hi hseq hHi a u]
    exact hcons u a v r heq
  by_cases hC : ∃ d, C d
  · -- the coalition is non-empty but blind to `H`: the mask `x` absorbs the change
    have hdot : ∀ (a : L2) (t : List (Lbl L2 Bool)), dotEq (w₁.ω a t) (w₂.ω a t) := by
      intro a t
      refine (hseq a t).2 ?_
      obtain ⟨d, hd⟩ := hC
      exact fun c hc => ⟨d, hd, Or.inl hc⟩
    rcases reachP_spec hreach with ⟨rfl, -⟩ | ⟨x, hx⟩
    · exact ⟨[], ⟨⟨P1State.p0, Reach.nil⟩, by intro u a v r heq; simp at heq⟩, rfl⟩
    rcases hx with ⟨rfl, -⟩ | ⟨y, u', rfl, h2⟩
    · exact ⟨[], ⟨⟨P1State.p0, Reach.nil⟩, by intro u a v r heq; simp at heq⟩, rfl⟩
    -- `ω₂` offers *some* value on `H`
    have hy : w₁.ω L2.Hi [] y := hcons [] L2.Hi y u' rfl
    have hy₂ : ∃ y₂, w₂.ω L2.Hi [] y₂ := by
      rcases Classical.em (∃ y₂, w₂.ω L2.Hi [] y₂) with h | h
      · exact h
      · exact absurd hy ((hdot L2.Hi []).mpr (fun v hv => h ⟨v, hv⟩) y)
    obtain ⟨y₂, hy₂⟩ := hy₂
    rcases h2 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · -- `t₁ = H?y`
      refine ⟨[Lbl.inp L2.Hi y₂], ⟨⟨P1State.p2 x y₂, ?_⟩, ?_⟩, ?_⟩
      · exact Reach.tau (stepP1.ch x) (Reach.inp (stepP1.inH x y₂) Reach.nil)
      · intro u a v r heq
        rcases u with _ | ⟨l0, u⟩
        · simp at heq; obtain ⟨⟨rfl, rfl⟩, -⟩ := heq; exact hy₂
        · simp at heq
      · unfold Sec.teq
        rw [Sec.proj_cons_some (Sec.projLbl_inp_pres ?_ ?_),
            Sec.proj_cons_some (Sec.projLbl_inp_pres ?_ ?_)]
        · obtain ⟨d, hd⟩ := hC
          exact fun c hc => ⟨d, hd, Or.inl hc⟩
        · exact fun h => hHi (by obtain ⟨d, hd, hle⟩ := h L2.Hi rfl; exact ⟨d, hd, hle⟩)
        · obtain ⟨d, hd⟩ := hC
          exact fun c hc => ⟨d, hd, Or.inl hc⟩
        · exact fun h => hHi (by obtain ⟨d, hd, hle⟩ := h L2.Hi rfl; exact ⟨d, hd, hle⟩)
    · -- `t₁ = H?y . L!(x ⊕ y)`; choose the mask so that the output is unchanged
      refine ⟨[Lbl.inp L2.Hi y₂, Lbl.out L2.Lo (Bool.xor x y)], ⟨⟨P1State.p3, ?_⟩, ?_⟩, ?_⟩
      · obtain ⟨x₂, hx₂⟩ : ∃ x₂ : Bool, Bool.xor x₂ y₂ = Bool.xor x y :=
          ⟨Bool.xor (Bool.xor x y) y₂, by cases x <;> cases y <;> cases y₂ <;> rfl⟩
        refine Reach.tau (stepP1.ch x₂) ?_
        refine Reach.inp (stepP1.inH x₂ y₂) ?_
        rw [← hx₂]
        exact Reach.out (stepP1.outL x₂ y₂) Reach.nil
      · intro u a v r heq
        rcases u with _ | ⟨l0, u⟩
        · simp at heq; obtain ⟨⟨rfl, rfl⟩, -⟩ := heq; exact hy₂
        · rcases u with _ | ⟨l1, u⟩ <;> simp at heq
      · unfold Sec.teq
        have hpres : Sc2.coalition.le (Sc2.coalition.presL L2.Hi) C := by
          obtain ⟨d, hd⟩ := hC
          exact fun c hc => ⟨d, hd, Or.inl hc⟩
        have hpresL : Sc2.coalition.le (Sc2.coalition.presL L2.Lo) C := by
          obtain ⟨d, hd⟩ := hC
          exact fun c hc => ⟨d, hd, Or.inl hc⟩
        have hnv : ¬ Sc2.coalition.le (Sc2.coalition.valL L2.Hi) C :=
          fun h => hHi (by obtain ⟨d, hd, hle⟩ := h L2.Hi rfl; exact ⟨d, hd, hle⟩)
        rw [Sec.proj_cons_some (Sec.projLbl_inp_pres hpres hnv),
            Sec.proj_cons_some (Sec.projLbl_inp_pres hpres hnv)]
  · -- the coalition is empty: it observes nothing at all
    exact ⟨[], ⟨⟨P1State.p0, Reach.nil⟩, by intro u a v r heq; simp at heq⟩,
      by unfold Sec.teq; rw [proj_empty hC, proj_empty hC]⟩

end P1

end InteractiveNI
