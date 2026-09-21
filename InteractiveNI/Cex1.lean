/-
  §3.1 — Non-compositionality of `Strat-NI` (Theorem 10).

  The security context, the two secret-sharing programs `P_A` and `P_B`,
  and their basic metatheory.
-/
import InteractiveNI.Compose

namespace InteractiveNI
namespace Cex1

open Classical
attribute [local instance] Classical.propDecidable

/-! ### The lattice `{L, H, H₁, H₂, H₃}` -/

inductive L5 where
  | Lo | H | H1 | H2 | H3 | Top
deriving DecidableEq, Repr

/-- `a ⊑ b` iff `a = L` (bottom), `a = b`, or `b = ⊤`; all `Hᵢ` are incomparable.
    (The paper's counterexample lattice, completed with a top element so that
    `(𝓛, ⊑)` really is a bounded lattice, as required in §2.  The extra level is
    also a channel, which no program uses.) -/
def L5.le (a b : L5) : Prop := a = L5.Lo ∨ a = b ∨ b = L5.Top

theorem L5.le_refl (a : L5) : L5.le a a := Or.inr (Or.inl rfl)

theorem L5.le_trans {a b c : L5} (h₁ : L5.le a b) (h₂ : L5.le b c) : L5.le a c := by
  rcases h₁ with h₁ | h₁ | h₁
  · exact Or.inl h₁
  · subst h₁; exact h₂
  · subst h₁
    rcases h₂ with h₂ | h₂ | h₂
    · exact absurd h₂ (by simp)
    · exact Or.inr (Or.inr h₂.symm)
    · exact Or.inr (Or.inr h₂)

/-- Decidable version of `⊑`. -/
def L5.leB (a b : L5) : Bool := (a == L5.Lo) || (a == b) || (b == L5.Top)

theorem L5.le_iff_leB {a b : L5} : L5.le a b ↔ L5.leB a b = true := by
  simp [L5.le, L5.leB, or_assoc]

/-- Joins: `(𝓛, ⊑)` really is a join-semilattice (indeed a bounded lattice). -/
def L5.join (a b : L5) : L5 := if L5.leB a b then b else if L5.leB b a then a else L5.Top

theorem L5.join_le_left (a b : L5) : L5.le a (L5.join a b) := by
  rw [L5.le_iff_leB]; cases a <;> cases b <;> rfl

theorem L5.join_le_right (a b : L5) : L5.le b (L5.join a b) := by
  rw [L5.le_iff_leB]; cases a <;> cases b <;> rfl

theorem L5.join_least (a b d : L5) (h1 : L5.le a d) (h2 : L5.le b d) :
    L5.le (L5.join a b) d := by
  rw [L5.le_iff_leB] at *
  revert h1 h2
  cases a <;> cases b <;> cases d <;> decide

/-- The security context: channels are level names, `γ(ℓ) = ℓ^L`. -/
def Sc : Sec L5 L5 where
  le := L5.le
  le_refl := L5.le_refl
  le_trans := L5.le_trans
  presL := fun _ => L5.Lo
  valL := fun c => c
  pres_le_val := fun _ => Or.inl rfl

@[simp] theorem Sc_valL (c : L5) : Sc.valL c = c := rfl
@[simp] theorem Sc_le (a b : L5) : Sc.le a b = L5.le a b := rfl

theorem Sc_pres_le (c ℓ : L5) : Sc.le (Sc.presL c) ℓ := Or.inl rfl

/-! ### Computing `π_ℓ` in this context -/

/-- The value shown by `π_ℓ` for a label on channel `c`. -/
def hide (c ℓ : L5) (v : Bool) : Option Bool := if L5.leB c ℓ then some v else none

/-- `π_ℓ` acts label-wise (no label is ever erased, since all presence levels are `L`). -/
def pj (ℓ : L5) : Lbl L5 Bool → PLbl L5 Bool
  | .inp c v => .inp c (hide c ℓ v)
  | .out c v => .out c (hide c ℓ v)

theorem projLbl_eq (ℓ : L5) (l : Lbl L5 Bool) : Sc.projLbl ℓ l = some (pj ℓ l) := by
  cases l with
  | inp c v =>
      by_cases h : L5.le c ℓ
      · rw [Sec.projLbl_inp_full (Sc_pres_le c ℓ) h]
        simp [pj, hide, ← L5.le_iff_leB, h]
      · rw [Sec.projLbl_inp_pres (Sc_pres_le c ℓ) h]
        simp [pj, hide, ← L5.le_iff_leB, h]
  | out c v =>
      by_cases h : L5.le c ℓ
      · rw [Sec.projLbl_out_full (Sc_pres_le c ℓ) h]
        simp [pj, hide, ← L5.le_iff_leB, h]
      · rw [Sec.projLbl_out_pres (Sc_pres_le c ℓ) h]
        simp [pj, hide, ← L5.le_iff_leB, h]

theorem proj_eq_map (ℓ : L5) (t : List (Lbl L5 Bool)) :
    Sc.proj ℓ t = t.map (pj ℓ) := by
  induction t with
  | nil => rfl
  | cons l t ih => rw [Sec.proj_cons_some (projLbl_eq ℓ l), ih, List.map_cons]

theorem teq_iff (ℓ : L5) (t t' : List (Lbl L5 Bool)) :
    Sc.teq ℓ t t' ↔ t.map (pj ℓ) = t'.map (pj ℓ) := by
  unfold Sec.teq; rw [proj_eq_map, proj_eq_map]

/-! ### The program `P_A` -/

inductive AState where
  | a0                          -- before `in_H(r)`
  | a1 (r : Bool)               -- before `x := 0 | x := 1`
  | a2 (r x : Bool)             -- before `out_{H₁}(¬x)`
  | a3 (r x : Bool)             -- before `in_{H₂}(y)`
  | a4 (r x y : Bool)           -- before `out_{H₃}(r⊕x⊕y)`
  | a5                          -- done
deriving DecidableEq

inductive stepA : AState → Act L5 Bool → AState → Prop where
  | inH   (r)     : stepA .a0 (.inp L5.H r) (.a1 r)
  | x0    (r)     : stepA (.a1 r) .tau (.a2 r false)
  | x1    (r)     : stepA (.a1 r) .tau (.a2 r true)
  | outH1 (r x)   : stepA (.a2 r x) (.out L5.H1 (!x)) (.a3 r x)
  | inH2  (r x y) : stepA (.a3 r x) (.inp L5.H2 y) (.a4 r x y)
  | outH3 (r x y) : stepA (.a4 r x y) (.out L5.H3 (Bool.xor r (Bool.xor x y))) .a5

theorem stepA.choose (r x : Bool) : stepA (.a1 r) .tau (.a2 r x) := by
  cases x
  · exact stepA.x0 r
  · exact stepA.x1 r

/-! ### The program `P_B` -/

inductive BState where
  | b0                          -- before `x' := 0 | x' := 1`
  | b1 (x' : Bool)              -- before `out_{H₂}(¬x')`
  | b2 (x' : Bool)              -- before `in_{H₁}(y')`
  | b3 (x' y' : Bool)           -- before `out_{H₃}(x'⊕y')`
  | b4                          -- done
deriving DecidableEq

inductive stepB : BState → Act L5 Bool → BState → Prop where
  | x0            : stepB .b0 .tau (.b1 false)
  | x1            : stepB .b0 .tau (.b1 true)
  | outH2 (x')    : stepB (.b1 x') (.out L5.H2 (!x')) (.b2 x')
  | inH1  (x' y') : stepB (.b2 x') (.inp L5.H1 y') (.b3 x' y')
  | outH3 (x' y') : stepB (.b3 x' y') (.out L5.H3 (Bool.xor x' y')) .b4

theorem stepB.choose (x : Bool) : stepB .b0 .tau (.b1 x) := by
  cases x
  · exact stepB.x0
  · exact stepB.x1

theorem stepA_neutral : InputNeutral stepA := by
  rintro s s' a v h v'
  cases h
  · exact ⟨_, stepA.inH v'⟩
  · exact ⟨_, stepA.inH2 _ _ v'⟩

theorem stepB_neutral : InputNeutral stepB := by
  rintro s s' a v h v'
  cases h
  · exact ⟨_, stepB.inH1 _ v'⟩


/-! ### Characterisation of the traces of `P_A` -/

def specA5 (u : List (Lbl L5 Bool)) (s' : AState) : Prop := u = [] ∧ s' = .a5

def specA4 (r x y : Bool) (u : List (Lbl L5 Bool)) (s' : AState) : Prop :=
  (u = [] ∧ s' = .a4 r x y) ∨
  (u = [.out L5.H3 (Bool.xor r (Bool.xor x y))] ∧ s' = .a5)

def specA3 (r x : Bool) (u : List (Lbl L5 Bool)) (s' : AState) : Prop :=
  (u = [] ∧ s' = .a3 r x) ∨ (∃ y u', u = .inp L5.H2 y :: u' ∧ specA4 r x y u' s')

def specA2 (r x : Bool) (u : List (Lbl L5 Bool)) (s' : AState) : Prop :=
  (u = [] ∧ s' = .a2 r x) ∨ (∃ u', u = .out L5.H1 (!x) :: u' ∧ specA3 r x u' s')

def specA1 (r : Bool) (u : List (Lbl L5 Bool)) (s' : AState) : Prop :=
  (u = [] ∧ s' = .a1 r) ∨ (∃ x, specA2 r x u s')

def specA0 (u : List (Lbl L5 Bool)) (s' : AState) : Prop :=
  (u = [] ∧ s' = .a0) ∨ (∃ r u', u = .inp L5.H r :: u' ∧ specA1 r u' s')

def specA : AState → List (Lbl L5 Bool) → AState → Prop
  | .a0 => specA0
  | .a1 r => specA1 r
  | .a2 r x => specA2 r x
  | .a3 r x => specA3 r x
  | .a4 r x y => specA4 r x y
  | .a5 => specA5

theorem reachA_spec {s : AState} {u : List (Lbl L5 Bool)} {s' : AState}
    (h : Reach stepA s u s') : specA s u s' := by
  induction h with
  | @nil s =>
      cases s <;>
        first
          | exact Or.inl ⟨rfl, rfl⟩
          | exact ⟨rfl, rfl⟩
  | tau hs _ ih =>
      cases hs with
      | x0 r => exact Or.inr ⟨false, ih⟩
      | x1 r => exact Or.inr ⟨true, ih⟩
  | @inp s s' s'' a v t hs _ ih =>
      cases hs
      · exact Or.inr ⟨v, _, rfl, ih⟩
      · exact Or.inr ⟨v, _, rfl, ih⟩
  | @out s s' s'' a v t hs _ ih =>
      cases hs
      · exact Or.inr ⟨_, rfl, ih⟩
      · exact Or.inr ⟨by rw [ih.1], ih.2⟩

/-! ### Characterisation of the traces of `P_B` -/

def specB4 (u : List (Lbl L5 Bool)) (s' : BState) : Prop := u = [] ∧ s' = .b4

def specB3 (x' y' : Bool) (u : List (Lbl L5 Bool)) (s' : BState) : Prop :=
  (u = [] ∧ s' = .b3 x' y') ∨ (u = [.out L5.H3 (Bool.xor x' y')] ∧ s' = .b4)

def specB2 (x' : Bool) (u : List (Lbl L5 Bool)) (s' : BState) : Prop :=
  (u = [] ∧ s' = .b2 x') ∨ (∃ y' u', u = .inp L5.H1 y' :: u' ∧ specB3 x' y' u' s')

def specB1 (x' : Bool) (u : List (Lbl L5 Bool)) (s' : BState) : Prop :=
  (u = [] ∧ s' = .b1 x') ∨ (∃ u', u = .out L5.H2 (!x') :: u' ∧ specB2 x' u' s')

def specB0 (u : List (Lbl L5 Bool)) (s' : BState) : Prop :=
  (u = [] ∧ s' = .b0) ∨ (∃ x', specB1 x' u s')

def specB : BState → List (Lbl L5 Bool) → BState → Prop
  | .b0 => specB0
  | .b1 x => specB1 x
  | .b2 x => specB2 x
  | .b3 x y => specB3 x y
  | .b4 => specB4

theorem reachB_spec {s : BState} {u : List (Lbl L5 Bool)} {s' : BState}
    (h : Reach stepB s u s') : specB s u s' := by
  induction h with
  | @nil s =>
      cases s <;>
        first
          | exact Or.inl ⟨rfl, rfl⟩
          | exact ⟨rfl, rfl⟩
  | tau hs _ ih =>
      cases hs with
      | x0 => exact Or.inr ⟨false, ih⟩
      | x1 => exact Or.inr ⟨true, ih⟩
  | @inp s s' s'' a v t hs _ ih =>
      cases hs
      · exact Or.inr ⟨v, _, rfl, ih⟩
  | @out s s' s'' a v t hs _ ih =>
      cases hs
      · exact Or.inr ⟨_, rfl, ih⟩
      · exact Or.inr ⟨by rw [ih.1], ih.2⟩


/-! ### `π_ℓ` congruences -/

theorem pj_eq_inp {c ℓ : L5} {v v' : Bool} (h : L5.le c ℓ → v = v') :
    pj ℓ (Lbl.inp c v) = pj ℓ (Lbl.inp c v') := by
  by_cases hc : L5.leB c ℓ = true
  · rw [h (L5.le_iff_leB.mpr hc)]
  · simp [pj, hide, hc]

theorem pj_eq_out {c ℓ : L5} {v v' : Bool} (h : L5.le c ℓ → v = v') :
    pj ℓ (Lbl.out c v) = pj ℓ (Lbl.out c v') := by
  by_cases hc : L5.leB c ℓ = true
  · rw [h (L5.le_iff_leB.mpr hc)]
  · simp [pj, hide, hc]

theorem xor_cancel (A e : Bool) : A = Bool.xor (Bool.xor A e) e := by
  cases A <;> cases e <;> rfl

theorem xor_fix (A d e : Bool) :
    A = Bool.xor d (Bool.xor (Bool.xor A (Bool.xor d e)) e) := by
  cases A <;> cases d <;> cases e <;> rfl

theorem le_cases {c ℓ : L5} (hc : c ≠ L5.Lo) (h : L5.le c ℓ) : ℓ = c ∨ ℓ = L5.Top := by
  rcases h with h | h | h
  · exact absurd h hc
  · exact Or.inl h.symm
  · exact Or.inr h

theorem le_top (c : L5) : L5.le c L5.Top := Or.inr (Or.inr rfl)

/-- At level `H₂`, the prefixes of `P_A` differing on `H` and `H₁` are equivalent. -/
theorem teq_H2_pre (r r' x x' : Bool) :
    Sc.teq L5.H2 [Lbl.inp L5.H r, Lbl.out L5.H1 (!x)]
                 [Lbl.inp L5.H r', Lbl.out L5.H1 (!x')] := by
  rw [teq_iff]
  simp [pj, hide, L5.leB]

/-- At level `H₁`, the prefixes of `P_B` differing on `H₂` are equivalent. -/
theorem teq_H1_pre (x x' : Bool) :
    Sc.teq L5.H1 [Lbl.out L5.H2 (!x)] [Lbl.out L5.H2 (!x')] := by
  rw [teq_iff]
  simp [pj, hide, L5.leB]

/-! ### `P_A` is noninterfering -/

theorem A_NI : Sc.StratNI stepA AState.a0 := by
  intro ℓ w₁ w₂ _ _ hww t₁ hprod
  obtain ⟨⟨s', hreach⟩, hcons⟩ := hprod
  have hspec : specA0 t₁ s' := reachA_spec hreach
  rcases hspec with ⟨rfl, -⟩ | ⟨r, u₁, rfl, hs1⟩
  · exact ⟨[], ⟨⟨.a0, Reach.nil⟩, Sec.consistent_nil _⟩, rfl⟩
  have hr : w₁.ω L5.H [] r := hcons [] L5.H r u₁ rfl
  obtain ⟨r₂, hr₂, hr₂eq⟩ :=
    Sec.match_input hww (Sc_pres_le _ _) (rfl : Sc.teq (Sc.valL L5.H) [] []) hr
  have hrpj : L5.le L5.H ℓ → r = r₂ := fun h => (hr₂eq (by simpa using h)).symm
  rcases hs1 with ⟨rfl, -⟩ | ⟨x, hs2⟩
  · -- `t₁ = H?r`
    refine ⟨[Lbl.inp L5.H r₂], ⟨⟨_, Reach.inp (stepA.inH r₂) Reach.nil⟩,
      Sec.consistent_cons_inp hr₂ (Sec.consistent_nil _)⟩, ?_⟩
    rw [teq_iff]
    simp only [List.map_cons, List.map_nil]
    rw [pj_eq_inp hrpj]
  rcases hs2 with ⟨rfl, -⟩ | ⟨u₂, rfl, hs3⟩
  · -- `t₁ = H?r` (after the internal choice)
    refine ⟨[Lbl.inp L5.H r₂], ⟨⟨_, Reach.inp (stepA.inH r₂) Reach.nil⟩,
      Sec.consistent_cons_inp hr₂ (Sec.consistent_nil _)⟩, ?_⟩
    rw [teq_iff]
    simp only [List.map_cons, List.map_nil]
    rw [pj_eq_inp hrpj]
  rcases hs3 with ⟨rfl, -⟩ | ⟨y, u₃, rfl, hs4⟩
  · -- `t₁ = H?r.H₁!(¬x)`
    refine ⟨[Lbl.inp L5.H r₂, Lbl.out L5.H1 (!x)],
      ⟨⟨_, Reach.inp (stepA.inH r₂) (Reach.tau (stepA.choose r₂ x)
        (Reach.out (stepA.outH1 r₂ x) Reach.nil))⟩,
      Sec.consistent_cons_inp hr₂ (Sec.consistent_cons_out (Sec.consistent_nil _))⟩, ?_⟩
    rw [teq_iff]
    simp only [List.map_cons, List.map_nil]
    rw [pj_eq_inp hrpj]
  -- the input on `H₂` is available in both runs
  have hy : w₁.ω L5.H2 [Lbl.inp L5.H r, Lbl.out L5.H1 (!x)] y :=
    hcons [Lbl.inp L5.H r, Lbl.out L5.H1 (!x)] L5.H2 y u₃ rfl
  obtain ⟨y₂, hy₂, hy₂eq⟩ :=
    Sec.match_input (u₂ := [Lbl.inp L5.H r₂, Lbl.out L5.H1 (!false)]) hww
      (Sc_pres_le _ _) (teq_H2_pre r r₂ x false) hy
  have hypj : L5.le L5.H2 ℓ → y = y₂ := fun h => (hy₂eq (by simpa using h)).symm
  -- the same input is available after any choice of `x₂`
  have hy₂' : ∀ x₂ : Bool, w₂.ω L5.H2 [Lbl.inp L5.H r₂, Lbl.out L5.H1 (!x₂)] y₂ := by
    intro x₂
    have := w₂.resp_val L5.H2 [Lbl.inp L5.H r₂, Lbl.out L5.H1 (!false)]
      [Lbl.inp L5.H r₂, Lbl.out L5.H1 (!x₂)] (teq_H2_pre r₂ r₂ false x₂)
    rw [← this]; exact hy₂
  rcases hs4 with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · -- `t₁ = H?r.H₁!(¬x).H₂?y`
    refine ⟨[Lbl.inp L5.H r₂, Lbl.out L5.H1 (!x), Lbl.inp L5.H2 y₂],
      ⟨⟨_, Reach.inp (stepA.inH r₂) (Reach.tau (stepA.choose r₂ x)
        (Reach.out (stepA.outH1 r₂ x) (Reach.inp (stepA.inH2 r₂ x y₂) Reach.nil)))⟩,
      Sec.consistent_cons_inp hr₂ (Sec.consistent_cons_out
        (Sec.consistent_cons_inp (hy₂' x) (Sec.consistent_nil _)))⟩, ?_⟩
    rw [teq_iff]
    simp only [List.map_cons, List.map_nil]
    rw [pj_eq_inp hrpj, pj_eq_inp (c := L5.H2) hypj]
  · -- the full trace `H?r.H₁!(¬x).H₂?y.H₃!(r⊕x⊕y)`
    obtain ⟨x₂, hx₂⟩ : ∃ z : Bool,
        z = (if ℓ = L5.H3 then Bool.xor (Bool.xor r (Bool.xor x y)) (Bool.xor r₂ y₂) else x) :=
      ⟨_, rfl⟩
    have hxpj : L5.le L5.H1 ℓ → (!x) = (!x₂) := by
      intro h
      rcases le_cases (by decide) h with hℓ | hℓ <;> subst hℓ <;> rw [hx₂] <;> simp
    have hopj : L5.le L5.H3 ℓ →
        Bool.xor r (Bool.xor x y) = Bool.xor r₂ (Bool.xor x₂ y₂) := by
      intro h
      rcases le_cases (by decide) h with hℓ | hℓ
      · subst hℓ
        rw [hx₂, if_pos rfl]
        exact xor_fix _ _ _
      · subst hℓ
        rw [hx₂, if_neg (by simp), ← hrpj (le_top _), ← hypj (le_top _)]
    refine ⟨[Lbl.inp L5.H r₂, Lbl.out L5.H1 (!x₂), Lbl.inp L5.H2 y₂,
             Lbl.out L5.H3 (Bool.xor r₂ (Bool.xor x₂ y₂))],
      ⟨⟨_, Reach.inp (stepA.inH r₂) (Reach.tau (stepA.choose r₂ x₂)
        (Reach.out (stepA.outH1 r₂ x₂) (Reach.inp (stepA.inH2 r₂ x₂ y₂)
          (Reach.out (stepA.outH3 r₂ x₂ y₂) Reach.nil))))⟩,
      Sec.consistent_cons_inp hr₂ (Sec.consistent_cons_out
        (Sec.consistent_cons_inp (hy₂' x₂) (Sec.consistent_cons_out
          (Sec.consistent_nil _))))⟩, ?_⟩
    rw [teq_iff]
    simp only [List.map_cons, List.map_nil]
    rw [pj_eq_inp hrpj, pj_eq_inp (c := L5.H2) hypj, pj_eq_out (c := L5.H1) hxpj,
      pj_eq_out (c := L5.H3) hopj]

/-! ### `P_B` is noninterfering -/

theorem B_NI : Sc.StratNI stepB BState.b0 := by
  intro ℓ w₁ w₂ _ _ hww t₁ hprod
  obtain ⟨⟨s', hreach⟩, hcons⟩ := hprod
  have hspec : specB0 t₁ s' := reachB_spec hreach
  rcases hspec with ⟨rfl, -⟩ | ⟨x, hs1⟩
  · exact ⟨[], ⟨⟨.b0, Reach.nil⟩, Sec.consistent_nil _⟩, rfl⟩
  rcases hs1 with ⟨rfl, -⟩ | ⟨u₁, rfl, hs2⟩
  · exact ⟨[], ⟨⟨.b0, Reach.nil⟩, Sec.consistent_nil _⟩, rfl⟩
  rcases hs2 with ⟨rfl, -⟩ | ⟨y, u₂, rfl, hs3⟩
  · -- `t₁ = H₂!(¬x')`
    refine ⟨[Lbl.out L5.H2 (!x)],
      ⟨⟨_, Reach.tau (stepB.choose x) (Reach.out (stepB.outH2 x) Reach.nil)⟩,
        Sec.consistent_cons_out (Sec.consistent_nil _)⟩, rfl⟩
  have hy : w₁.ω L5.H1 [Lbl.out L5.H2 (!x)] y :=
    hcons [Lbl.out L5.H2 (!x)] L5.H1 y u₂ rfl
  obtain ⟨y₂, hy₂, hy₂eq⟩ :=
    Sec.match_input (u₂ := [Lbl.out L5.H2 (!false)]) hww (Sc_pres_le _ _)
      (teq_H1_pre x false) hy
  have hypj : L5.le L5.H1 ℓ → y = y₂ := fun h => (hy₂eq (by simpa using h)).symm
  have hy₂' : ∀ x₂ : Bool, w₂.ω L5.H1 [Lbl.out L5.H2 (!x₂)] y₂ := by
    intro x₂
    have := w₂.resp_val L5.H1 [Lbl.out L5.H2 (!false)] [Lbl.out L5.H2 (!x₂)]
      (teq_H1_pre false x₂)
    rw [← this]; exact hy₂
  rcases hs3 with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · -- `t₁ = H₂!(¬x').H₁?y'`
    refine ⟨[Lbl.out L5.H2 (!x), Lbl.inp L5.H1 y₂],
      ⟨⟨_, Reach.tau (stepB.choose x) (Reach.out (stepB.outH2 x)
        (Reach.inp (stepB.inH1 x y₂) Reach.nil))⟩,
        Sec.consistent_cons_out (Sec.consistent_cons_inp (hy₂' x)
          (Sec.consistent_nil _))⟩, ?_⟩
    rw [teq_iff]
    simp only [List.map_cons, List.map_nil]
    rw [pj_eq_inp (c := L5.H1) hypj]
  · -- the full trace `H₂!(¬x').H₁?y'.H₃!(x'⊕y')`
    obtain ⟨x₂, hx₂⟩ : ∃ z : Bool, z = (if ℓ = L5.H3 then Bool.xor (Bool.xor x y) y₂ else x) :=
      ⟨_, rfl⟩
    have hxpj : L5.le L5.H2 ℓ → (!x) = (!x₂) := by
      intro h
      rcases le_cases (by decide) h with hℓ | hℓ <;> subst hℓ <;> rw [hx₂] <;> simp
    have hopj : L5.le L5.H3 ℓ → Bool.xor x y = Bool.xor x₂ y₂ := by
      intro h
      rcases le_cases (by decide) h with hℓ | hℓ
      · subst hℓ
        rw [hx₂, if_pos rfl]
        exact xor_cancel _ _
      · subst hℓ
        rw [hx₂, if_neg (by simp), ← hypj (le_top _)]
    refine ⟨[Lbl.out L5.H2 (!x₂), Lbl.inp L5.H1 y₂, Lbl.out L5.H3 (Bool.xor x₂ y₂)],
      ⟨⟨_, Reach.tau (stepB.choose x₂) (Reach.out (stepB.outH2 x₂)
        (Reach.inp (stepB.inH1 x₂ y₂) (Reach.out (stepB.outH3 x₂ y₂) Reach.nil)))⟩,
        Sec.consistent_cons_out (Sec.consistent_cons_inp (hy₂' x₂)
          (Sec.consistent_cons_out (Sec.consistent_nil _)))⟩, ?_⟩
    rw [teq_iff]
    simp only [List.map_cons, List.map_nil]
    rw [pj_eq_inp (c := L5.H1) hypj, pj_eq_out (c := L5.H2) hxpj,
      pj_eq_out (c := L5.H3) hopj]


/-! ### The attacking strategies -/

/-- The strategies `ω₁` (`b = false`) and `ω₂` (`b = true`) of the proof: on `H`
    they constantly return the secret bit `b`; on `H₁, H₂` they return the values
    already output on that channel; on `L, H₃` they are empty. -/
def omegaFun (b : Bool) (c : L5) (t : List (Lbl L5 Bool)) : VSet Bool :=
  match c with
  | L5.H => fun v => v = b
  | L5.H1 => fun v => Lbl.out L5.H1 v ∈ t
  | L5.H2 => fun v => Lbl.out L5.H2 v ∈ t
  | L5.H3 => fun _ => False
  | L5.Lo => fun _ => False
  | L5.Top => fun _ => False

theorem mem_iff_of_teq {c : L5} {t₁ t₂ : List (Lbl L5 Bool)}
    (ht : Sc.teq c t₁ t₂) (v : Bool) :
    (Lbl.out c v ∈ t₁) ↔ (Lbl.out c v ∈ t₂) := by
  have hp : Sc.le (Sc.presL c) c := Sc_pres_le c c
  have hv : Sc.le (Sc.valL c) c := L5.le_refl c
  rw [← Sec.mem_proj_out_full hp hv t₁, ← Sec.mem_proj_out_full hp hv t₂]
  unfold Sec.teq at ht
  rw [ht]

theorem exists_mem_iff_of_teq {c : L5} (hc : c ≠ L5.Lo) {t₁ t₂ : List (Lbl L5 Bool)}
    (ht : Sc.teq L5.Lo t₁ t₂) :
    (∃ v, Lbl.out c v ∈ t₁) ↔ (∃ v, Lbl.out c v ∈ t₂) := by
  have hp : Sc.le (Sc.presL c) L5.Lo := Sc_pres_le c L5.Lo
  have hv : ¬ Sc.le (Sc.valL c) L5.Lo := by
    simp only [Sc_valL, Sc_le, L5.le]
    rintro (h | h | h)
    · exact hc h
    · exact hc h
    · exact absurd h (by simp)
  rw [← Sec.mem_proj_out_pres hp hv t₁, ← Sec.mem_proj_out_pres hp hv t₂]
  unfold Sec.teq at ht
  rw [ht]

noncomputable def cexOmega (b : Bool) : Sc.Strategy Bool where
  ω := omegaFun b
  resp_val := by
    intro c t₁ t₂ ht
    cases c
    · rfl
    · rfl
    · funext v
      exact propext (mem_iff_of_teq ht v)
    · funext v
      exact propext (mem_iff_of_teq ht v)
    · rfl
    · rfl
  resp_pres := by
    intro c t₁ t₂ ht
    cases c
    · exact dotEq.refl _
    · exact dotEq.refl _
    · constructor
      · intro h v hv
        exact (exists_mem_iff_of_teq (c := L5.H1) (by decide) ht).mpr ⟨v, hv⟩
          |>.elim (fun w hw => h w hw)
      · intro h v hv
        exact (exists_mem_iff_of_teq (c := L5.H1) (by decide) ht).mp ⟨v, hv⟩
          |>.elim (fun w hw => h w hw)
    · constructor
      · intro h v hv
        exact (exists_mem_iff_of_teq (c := L5.H2) (by decide) ht).mpr ⟨v, hv⟩
          |>.elim (fun w hw => h w hw)
      · intro h v hv
        exact (exists_mem_iff_of_teq (c := L5.H2) (by decide) ht).mp ⟨v, hv⟩
          |>.elim (fun w hw => h w hw)
    · exact dotEq.refl _
    · exact dotEq.refl _

theorem cexOmega_seq : Sc.seq L5.H3 (cexOmega false) (cexOmega true) := by
  intro c t
  constructor
  · intro hle
    cases c
    · rfl
    · exact absurd hle (by rintro (hh | hh | hh) <;> exact L5.noConfusion hh)
    · exact absurd hle (by rintro (hh | hh | hh) <;> exact L5.noConfusion hh)
    · exact absurd hle (by rintro (hh | hh | hh) <;> exact L5.noConfusion hh)
    · rfl
    · exact absurd hle (by rintro (hh | hh | hh) <;> exact L5.noConfusion hh)
  · intro _
    cases c
    · exact dotEq.refl _
    · constructor
      · intro h; exact absurd (h false rfl) (fun x => x)
      · intro h; exact absurd (h true rfl) (fun x => x)
    · exact dotEq.refl _
    · exact dotEq.refl _
    · exact dotEq.refl _
    · exact dotEq.refl _


/-! ### Shapes of maximal traces -/

theorem specA0_len {u : List (Lbl L5 Bool)} {s' : AState} (h : specA0 u s') :
    u.length ≤ 4 := by
  rcases h with ⟨rfl, -⟩ | ⟨r, u₁, rfl, h1⟩
  · simp
  rcases h1 with ⟨rfl, -⟩ | ⟨x, h2⟩
  · simp
  rcases h2 with ⟨rfl, -⟩ | ⟨u₂, rfl, h3⟩
  · simp
  rcases h3 with ⟨rfl, -⟩ | ⟨y, u₃, rfl, h4⟩
  · simp
  rcases h4 with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem specA0_full {u : List (Lbl L5 Bool)} {s' : AState} (h : specA0 u s')
    (hl : u.length = 4) :
    ∃ r x y, u = [Lbl.inp L5.H r, Lbl.out L5.H1 (!x), Lbl.inp L5.H2 y,
                  Lbl.out L5.H3 (Bool.xor r (Bool.xor x y))] := by
  rcases h with ⟨rfl, -⟩ | ⟨r, u₁, rfl, h1⟩
  · simp at hl
  rcases h1 with ⟨rfl, -⟩ | ⟨x, h2⟩
  · simp at hl
  rcases h2 with ⟨rfl, -⟩ | ⟨u₂, rfl, h3⟩
  · simp at hl
  rcases h3 with ⟨rfl, -⟩ | ⟨y, u₃, rfl, h4⟩
  · simp at hl
  rcases h4 with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · simp at hl
  · exact ⟨r, x, y, rfl⟩

theorem specB0_len {u : List (Lbl L5 Bool)} {s' : BState} (h : specB0 u s') :
    u.length ≤ 3 := by
  rcases h with ⟨rfl, -⟩ | ⟨x, h1⟩
  · simp
  rcases h1 with ⟨rfl, -⟩ | ⟨u₁, rfl, h2⟩
  · simp
  rcases h2 with ⟨rfl, -⟩ | ⟨y, u₂, rfl, h3⟩
  · simp
  rcases h3 with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem specB0_full {u : List (Lbl L5 Bool)} {s' : BState} (h : specB0 u s')
    (hl : u.length = 3) :
    ∃ x y, u = [Lbl.out L5.H2 (!x), Lbl.inp L5.H1 y, Lbl.out L5.H3 (Bool.xor x y)] := by
  rcases h with ⟨rfl, -⟩ | ⟨x, h1⟩
  · simp at hl
  rcases h1 with ⟨rfl, -⟩ | ⟨u₁, rfl, h2⟩
  · simp at hl
  rcases h2 with ⟨rfl, -⟩ | ⟨y, u₂, rfl, h3⟩
  · simp at hl
  rcases h3 with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · simp at hl
  · exact ⟨x, y, rfl⟩

/-! ### The attacking trace -/

/-- `t = H?0.H₁!0.H₂!0.H₂?0.H₁?0.H₃!1.H₃!1` -/
def tcex : List (Lbl L5 Bool) :=
  [Lbl.inp L5.H false, Lbl.out L5.H1 false, Lbl.out L5.H2 false, Lbl.inp L5.H2 false,
   Lbl.inp L5.H1 false, Lbl.out L5.H3 true, Lbl.out L5.H3 true]

theorem tcex_reach :
    Reach (parStep stepA stepB) (AState.a0, BState.b0) tcex (AState.a5, BState.b4) := by
  refine Reach.inp (s' := (AState.a1 false, BState.b0))
    (Or.inl ⟨stepA.inH false, rfl⟩) ?_
  refine Reach.tau (s' := (AState.a2 false true, BState.b0))
    (Or.inl ⟨stepA.choose false true, rfl⟩) ?_
  refine Reach.out (s' := (AState.a3 false true, BState.b0))
    (Or.inl ⟨stepA.outH1 false true, rfl⟩) ?_
  refine Reach.tau (s' := (AState.a3 false true, BState.b1 true))
    (Or.inr ⟨stepB.choose true, rfl⟩) ?_
  refine Reach.out (s' := (AState.a3 false true, BState.b2 true))
    (Or.inr ⟨stepB.outH2 true, rfl⟩) ?_
  refine Reach.inp (s' := (AState.a4 false true false, BState.b2 true))
    (Or.inl ⟨stepA.inH2 false true false, rfl⟩) ?_
  refine Reach.inp (s' := (AState.a4 false true false, BState.b3 true false))
    (Or.inr ⟨stepB.inH1 true false, rfl⟩) ?_
  refine Reach.out (s' := (AState.a5, BState.b3 true false))
    (Or.inl ⟨stepA.outH3 false true false, rfl⟩) ?_
  exact Reach.out (s' := (AState.a5, BState.b4)) (Or.inr ⟨stepB.outH3 true false, rfl⟩)
    Reach.nil

theorem tcex_consistent : Sc.consistent (cexOmega false) tcex := by
  refine Sec.consistent_cons_inp ?_ (Sec.consistent_cons_out (Sec.consistent_cons_out
    (Sec.consistent_cons_inp ?_ (Sec.consistent_cons_inp ?_ (Sec.consistent_cons_out
      (Sec.consistent_cons_out (Sec.consistent_nil _)))))))
  · show (false : Bool) = false
    rfl
  · show Lbl.out L5.H2 false ∈
      [Lbl.inp L5.H false, Lbl.out L5.H1 false, Lbl.out L5.H2 false]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · show Lbl.out L5.H1 false ∈
      [Lbl.inp L5.H false, Lbl.out L5.H1 false, Lbl.out L5.H2 false, Lbl.inp L5.H2 false]
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem tcex_produces :
    Sc.produces (parStep stepA stepB) (cexOmega false) (AState.a0, BState.b0) tcex :=
  ⟨⟨_, tcex_reach⟩, tcex_consistent⟩

/-! ### No `H₃`-equivalent trace can be produced under `ω₂` -/

theorem pj_inp_eq {ℓ c : L5} {l : Lbl L5 Bool} {o : Option Bool}
    (h : pj ℓ l = PLbl.inp c o) : ∃ v, l = Lbl.inp c v ∧ hide c ℓ v = o := by
  cases l with
  | inp c' v =>
      simp only [pj] at h
      injection h with h1 h2
      subst h1
      exact ⟨v, rfl, h2⟩
  | out c' v => simp only [pj] at h; exact absurd h (by simp)

theorem pj_out_eq {ℓ c : L5} {l : Lbl L5 Bool} {o : Option Bool}
    (h : pj ℓ l = PLbl.out c o) : ∃ v, l = Lbl.out c v ∧ hide c ℓ v = o := by
  cases l with
  | out c' v =>
      simp only [pj] at h
      injection h with h1 h2
      subst h1
      exact ⟨v, rfl, h2⟩
  | inp c' v => simp only [pj] at h; exact absurd h (by simp)

theorem tcex_proj : List.map (pj L5.H3) tcex =
    [PLbl.inp L5.H none, PLbl.out L5.H1 none, PLbl.out L5.H2 none, PLbl.inp L5.H2 none,
     PLbl.inp L5.H1 none, PLbl.out L5.H3 (some true), PLbl.out L5.H3 (some true)] := rfl

theorem no_match (t' : List (Lbl L5 Bool))
    (hprod : Sc.produces (parStep stepA stepB) (cexOmega true) (AState.a0, BState.b0) t')
    (ht : Sc.teq L5.H3 tcex t') : False := by
  obtain ⟨⟨q, hr⟩, hc⟩ := hprod
  rw [teq_iff, tcex_proj] at ht
  have hlen : t'.length = 7 := by
    have h := congrArg List.length ht
    simpa using h.symm
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, rfl⟩ :
      ∃ a b c d e f g, t' = [a, b, c, d, e, f, g] := by
    rcases t' with _|⟨a,_|⟨b,_|⟨c,_|⟨d,_|⟨e,_|⟨f,_|⟨g,_|⟨h,rest⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp only [List.length_cons, List.length_nil] at hlen <;>
      first
        | exact ⟨_,_,_,_,_,_,_,rfl⟩
        | omega
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at ht
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := ht
  obtain ⟨r, rfl, -⟩ := pj_inp_eq e1.symm
  obtain ⟨a, rfl, -⟩ := pj_out_eq e2.symm
  obtain ⟨b, rfl, -⟩ := pj_out_eq e3.symm
  obtain ⟨c, rfl, -⟩ := pj_inp_eq e4.symm
  obtain ⟨d, rfl, -⟩ := pj_inp_eq e5.symm
  obtain ⟨o1, rfl, ho1⟩ := pj_out_eq e6.symm
  obtain ⟨o2, rfl, ho2⟩ := pj_out_eq e7.symm
  have ho1' : o1 = true := by
    have : some o1 = some true := ho1
    injection this
  have ho2' : o2 = true := by
    have : some o2 = some true := ho2
    injection this
  subst ho1'; subst ho2'
  -- constraints coming from consistency with `ω₂`
  have hr1 : r = true := hc [] L5.H r _ rfl
  have hcb : c = b := by
    have := hc [Lbl.inp L5.H r, Lbl.out L5.H1 a, Lbl.out L5.H2 b] L5.H2 c
      [Lbl.inp L5.H1 d, Lbl.out L5.H3 true, Lbl.out L5.H3 true] rfl
    have hmem : Lbl.out L5.H2 c ∈
        [Lbl.inp L5.H r, Lbl.out L5.H1 a, Lbl.out L5.H2 b] := this
    simpa using hmem
  have hda : d = a := by
    have := hc [Lbl.inp L5.H r, Lbl.out L5.H1 a, Lbl.out L5.H2 b, Lbl.inp L5.H2 c] L5.H1 d
      [Lbl.out L5.H3 true, Lbl.out L5.H3 true] rfl
    have hmem : Lbl.out L5.H1 d ∈
        [Lbl.inp L5.H r, Lbl.out L5.H1 a, Lbl.out L5.H2 b, Lbl.inp L5.H2 c] := this
    simpa using hmem
  -- decompose the run into the two components
  obtain ⟨tA, tB, hRA, hRB, hI⟩ := par_decompose hr
  have hlenI := hI.length
  have hlA : tA.length ≤ 4 := specA0_len (reachA_spec hRA)
  have hlB : tB.length ≤ 3 := specB0_len (reachB_spec hRB)
  have hlA4 : tA.length = 4 := by simp at hlenI; omega
  have hlB3 : tB.length = 3 := by simp at hlenI; omega
  obtain ⟨rA, xA, yA, rfl⟩ := specA0_full (reachA_spec hRA) hlA4
  obtain ⟨xB, yB, rfl⟩ := specB0_full (reachB_spec hRB) hlB3
  -- every label of a component occurs in the global trace
  have m1 := hI.mem_left (List.mem_cons_self ..)
  have m2 := hI.mem_left (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have m3 := hI.mem_left (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..)))
  have m4 := hI.mem_left (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  have n1 := hI.mem_right (List.mem_cons_self ..)
  have n2 := hI.mem_right (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have n3 := hI.mem_right (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..)))
  simp only [List.mem_cons, List.not_mem_nil, or_false, Lbl.inp.injEq, Lbl.out.injEq,
    reduceCtorEq, false_or, or_false, false_and] at m1 m2 m3 m4 n1 n2 n3
  -- put everything together
  subst hr1
  have hA3 : Bool.xor rA (Bool.xor xA yA) = true := by
    rcases m4 with ⟨-, h⟩ | ⟨-, h⟩ <;> exact h
  have hB3 : Bool.xor xB yB = true := by
    rcases n3 with ⟨-, h⟩ | ⟨-, h⟩ <;> exact h
  have hxA : (!xA) = a := m2.2
  have hyA : yA = c := m3.2
  have hxB : (!xB) = b := n1.2
  have hyB : yB = d := n2.2
  subst hcb; subst hda
  rw [← hxA] at hyB
  rw [← hxB] at hyA
  subst hyA; subst hyB
  have hrA : rA = true := m1.2
  subst hrA
  cases xA <;> cases xB <;> simp at hA3 hB3


/-- The composition of `sA` and `sB` is **not** `Strat-NI`. -/
theorem par_not_NI : ¬ Sc.StratNI (parStep stepA stepB) (AState.a0, BState.b0) := by
  intro hNI
  obtain ⟨t₂, hprod, hteq⟩ :=
    hNI L5.H3 (cexOmega false) (cexOmega true) trivial trivial cexOmega_seq tcex tcex_produces
  exact no_match t₂ hprod hteq

end Cex1

/-- **Theorem 10** (Non-compositionality).  There are `sA, sB ∈ Strat-NI` whose
    composition is not in `Strat-NI`. -/
theorem noncompositional :
    ∃ (Level Channel Value : Type) (S : Sec Level Channel) (St₁ St₂ : Type)
      (step₁ : St₁ → Act Channel Value → St₁ → Prop)
      (step₂ : St₂ → Act Channel Value → St₂ → Prop) (sA : St₁) (sB : St₂),
      S.IsJoinSemilattice ∧ InputNeutral step₁ ∧ InputNeutral step₂ ∧
      S.StratNI step₁ sA ∧ S.StratNI step₂ sB ∧
      ¬ S.StratNI (parStep step₁ step₂) (sA, sB) :=
  ⟨Cex1.L5, Cex1.L5, Bool, Cex1.Sc, Cex1.AState, Cex1.BState, Cex1.stepA, Cex1.stepB,
   .a0, .b0,
   ⟨Cex1.L5.join, fun a b =>
     ⟨Cex1.L5.join_le_left a b, Cex1.L5.join_le_right a b, Cex1.L5.join_least a b⟩⟩,
   Cex1.stepA_neutral, Cex1.stepB_neutral,
   Cex1.A_NI, Cex1.B_NI, Cex1.par_not_NI⟩

namespace Cex1

end Cex1
end InteractiveNI
