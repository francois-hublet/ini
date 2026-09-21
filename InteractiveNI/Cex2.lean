/-
  §3.3 — Non-compositionality of `Strat_T-NI` (Theorem 13), i.e. in the *total*
  (non-blocking) setup originally considered by O'Neill et al.
-/
import InteractiveNI.Cex1

namespace InteractiveNI
namespace Cex2

open Classical
attribute [local instance] Classical.propDecidable

/-! ### The lattice `{L₁, L₂, H, H₁, H₂, H₃}` -/

inductive L6 where
  | L1 | L2 | H | H1 | H2 | H3 | Top
deriving DecidableEq, Repr

/-- `⊑ = {(Lᵢ, ℓ)} ∪ {(ℓ,ℓ)} ∪ {(ℓ,⊤)}`.  (The paper's lattice for Theorem 13,
    completed with a top element so that joins exist, as §2 requires.) -/
def L6.le (a b : L6) : Prop := a = L6.L1 ∨ a = L6.L2 ∨ a = b ∨ b = L6.Top

theorem L6.le_refl (a : L6) : L6.le a a := Or.inr (Or.inr (Or.inl rfl))

theorem L6.le_trans {a b c : L6} (h₁ : L6.le a b) (h₂ : L6.le b c) : L6.le a c := by
  rcases h₁ with h₁ | h₁ | h₁ | h₁
  · exact Or.inl h₁
  · exact Or.inr (Or.inl h₁)
  · subst h₁; exact h₂
  · subst h₁
    rcases h₂ with h₂ | h₂ | h₂ | h₂
    · exact absurd h₂ (by simp)
    · exact absurd h₂ (by simp)
    · exact Or.inr (Or.inr (Or.inr h₂.symm))
    · exact Or.inr (Or.inr (Or.inr h₂))

def L6.leB (a b : L6) : Bool := (a == L6.L1) || (a == L6.L2) || (a == b) || (b == L6.Top)

theorem L6.le_iff_leB {a b : L6} : L6.le a b ↔ L6.leB a b = true := by
  simp [L6.le, L6.leB, or_assoc]

/-- Joins: `(𝓛, ⊑)` really is a join-semilattice. -/
def L6.join (a b : L6) : L6 := if L6.leB a b then b else if L6.leB b a then a else L6.Top

theorem L6.join_le_left (a b : L6) : L6.le a (L6.join a b) := by
  rw [L6.le_iff_leB]; cases a <;> cases b <;> rfl

theorem L6.join_le_right (a b : L6) : L6.le b (L6.join a b) := by
  rw [L6.le_iff_leB]; cases a <;> cases b <;> rfl

theorem L6.join_least (a b d : L6) (h1 : L6.le a d) (h2 : L6.le b d) :
    L6.le (L6.join a b) d := by
  rw [L6.le_iff_leB] at *
  revert h1 h2
  cases a <;> cases b <;> cases d <;> decide

/-- The security context: `γ(ℓ) = ℓ^{L₁}` (all presences public). -/
def Sc : Sec L6 L6 where
  le := L6.le
  le_refl := L6.le_refl
  le_trans := L6.le_trans
  presL := fun _ => L6.L1
  valL := fun c => c
  pres_le_val := fun _ => Or.inl rfl

@[simp] theorem Sc_valL (c : L6) : Sc.valL c = c := rfl
@[simp] theorem Sc_le (a b : L6) : Sc.le a b = L6.le a b := rfl

theorem Sc_pres_le (c ℓ : L6) : Sc.le (Sc.presL c) ℓ := Or.inl rfl

/-- `L₁` and `L₂` are below everything. -/
theorem le_L1 (ℓ : L6) : Sc.le L6.L1 ℓ := Or.inl rfl
theorem le_L2 (ℓ : L6) : Sc.le L6.L2 ℓ := Or.inr (Or.inl rfl)
theorem le_top (c : L6) : Sc.le c L6.Top := Or.inr (Or.inr (Or.inr rfl))

/-! ### Computing `π_ℓ` -/

def hide (c ℓ : L6) (v : Bool) : Option Bool := if L6.leB c ℓ then some v else none

def pj (ℓ : L6) : Lbl L6 Bool → PLbl L6 Bool
  | .inp c v => .inp c (hide c ℓ v)
  | .out c v => .out c (hide c ℓ v)

theorem projLbl_eq (ℓ : L6) (l : Lbl L6 Bool) : Sc.projLbl ℓ l = some (pj ℓ l) := by
  cases l with
  | inp c v =>
      by_cases h : L6.le c ℓ
      · rw [Sec.projLbl_inp_full (Sc_pres_le c ℓ) h]
        simp [pj, hide, ← L6.le_iff_leB, h]
      · rw [Sec.projLbl_inp_pres (Sc_pres_le c ℓ) h]
        simp [pj, hide, ← L6.le_iff_leB, h]
  | out c v =>
      by_cases h : L6.le c ℓ
      · rw [Sec.projLbl_out_full (Sc_pres_le c ℓ) h]
        simp [pj, hide, ← L6.le_iff_leB, h]
      · rw [Sec.projLbl_out_pres (Sc_pres_le c ℓ) h]
        simp [pj, hide, ← L6.le_iff_leB, h]

theorem proj_eq_map (ℓ : L6) (t : List (Lbl L6 Bool)) : Sc.proj ℓ t = t.map (pj ℓ) := by
  induction t with
  | nil => rfl
  | cons l t ih => rw [Sec.proj_cons_some (projLbl_eq ℓ l), ih, List.map_cons]

theorem teq_iff (ℓ : L6) (t t' : List (Lbl L6 Bool)) :
    Sc.teq ℓ t t' ↔ t.map (pj ℓ) = t'.map (pj ℓ) := by
  unfold Sec.teq; rw [proj_eq_map, proj_eq_map]

theorem pj_eq_inp {c ℓ : L6} {v v' : Bool} (h : L6.le c ℓ → v = v') :
    pj ℓ (Lbl.inp c v) = pj ℓ (Lbl.inp c v') := by
  by_cases hc : L6.leB c ℓ = true
  · rw [h (L6.le_iff_leB.mpr hc)]
  · simp [pj, hide, hc]

theorem pj_eq_out {c ℓ : L6} {v v' : Bool} (h : L6.le c ℓ → v = v') :
    pj ℓ (Lbl.out c v) = pj ℓ (Lbl.out c v') := by
  by_cases hc : L6.leB c ℓ = true
  · rw [h (L6.le_iff_leB.mpr hc)]
  · simp [pj, hide, hc]

theorem pj_inp_eq {ℓ c : L6} {l : Lbl L6 Bool} {o : Option Bool}
    (h : pj ℓ l = PLbl.inp c o) : ∃ v, l = Lbl.inp c v ∧ hide c ℓ v = o := by
  cases l with
  | inp c' v =>
      simp only [pj] at h
      injection h with h1 h2
      subst h1
      exact ⟨v, rfl, h2⟩
  | out c' v => simp only [pj] at h; exact absurd h (by simp)

theorem pj_out_eq {ℓ c : L6} {l : Lbl L6 Bool} {o : Option Bool}
    (h : pj ℓ l = PLbl.out c o) : ∃ v, l = Lbl.out c v ∧ hide c ℓ v = o := by
  cases l with
  | out c' v =>
      simp only [pj] at h
      injection h with h1 h2
      subst h1
      exact ⟨v, rfl, h2⟩
  | inp c' v => simp only [pj] at h; exact absurd h (by simp)

theorem le_cases {c ℓ : L6} (h1 : c ≠ L6.L1) (h2 : c ≠ L6.L2) (h : L6.le c ℓ) :
    ℓ = c ∨ ℓ = L6.Top := by
  rcases h with h | h | h | h
  · exact absurd h h1
  · exact absurd h h2
  · exact Or.inl h.symm
  · exact Or.inr h

/-! ### The programs -/

inductive AState where
  | a0                      -- before `in_H(r)`
  | a1 (r : Bool)           -- before the choice
  | a2 (r x : Bool)         -- before `out_{H₁}(¬x)`
  | a3 (r x : Bool)         -- before `out_{L₁}(1)`
  | a4 (r x : Bool)         -- before `in_{L₂}(z)`
  | a5 (r x z : Bool)       -- before `in_{H₂}(y)`
  | a6 (r x z y : Bool)     -- before `out_{H₃}(z)`
  | a7 (r x y : Bool)       -- before `out_{H₃}(r⊕x⊕y)`
  | a8
deriving DecidableEq

inductive stepA : AState → Act L6 Bool → AState → Prop where
  | inH   (r)         : stepA .a0 (.inp L6.H r) (.a1 r)
  | x0    (r)         : stepA (.a1 r) .tau (.a2 r false)
  | x1    (r)         : stepA (.a1 r) .tau (.a2 r true)
  | outH1 (r x)       : stepA (.a2 r x) (.out L6.H1 (!x)) (.a3 r x)
  | outL1 (r x)       : stepA (.a3 r x) (.out L6.L1 true) (.a4 r x)
  | inL2  (r x z)     : stepA (.a4 r x) (.inp L6.L2 z) (.a5 r x z)
  | inH2  (r x z y)   : stepA (.a5 r x z) (.inp L6.H2 y) (.a6 r x z y)
  | outZ  (r x z y)   : stepA (.a6 r x z y) (.out L6.H3 z) (.a7 r x y)
  | outH3 (r x y)     : stepA (.a7 r x y) (.out L6.H3 (Bool.xor r (Bool.xor x y))) .a8

theorem stepA.choose (r x : Bool) : stepA (.a1 r) .tau (.a2 r x) := by
  cases x
  · exact stepA.x0 r
  · exact stepA.x1 r

theorem stepA_neutral : InputNeutral stepA := by
  rintro s s' a v h v'
  cases h
  · exact ⟨_, stepA.inH v'⟩
  · exact ⟨_, stepA.inL2 _ _ v'⟩
  · exact ⟨_, stepA.inH2 _ _ _ v'⟩

inductive BState where
  | b0                      -- before the choice
  | b1 (x : Bool)           -- before `out_{H₂}(¬x')`
  | b2 (x : Bool)           -- before `out_{L₂}(1)`
  | b3 (x : Bool)           -- before `in_{L₁}(z')`
  | b4 (x z : Bool)         -- before `in_{H₁}(y')`
  | b5 (x z y : Bool)       -- before `out_{H₃}(z')`
  | b6 (x y : Bool)         -- before `out_{H₃}(x'⊕y')`
  | b7
deriving DecidableEq

inductive stepB : BState → Act L6 Bool → BState → Prop where
  | x0                : stepB .b0 .tau (.b1 false)
  | x1                : stepB .b0 .tau (.b1 true)
  | outH2 (x)         : stepB (.b1 x) (.out L6.H2 (!x)) (.b2 x)
  | outL2 (x)         : stepB (.b2 x) (.out L6.L2 true) (.b3 x)
  | inL1  (x z)       : stepB (.b3 x) (.inp L6.L1 z) (.b4 x z)
  | inH1  (x z y)     : stepB (.b4 x z) (.inp L6.H1 y) (.b5 x z y)
  | outZ  (x z y)     : stepB (.b5 x z y) (.out L6.H3 z) (.b6 x y)
  | outH3 (x y)       : stepB (.b6 x y) (.out L6.H3 (Bool.xor x y)) .b7

theorem stepB.choose (x : Bool) : stepB .b0 .tau (.b1 x) := by
  cases x
  · exact stepB.x0
  · exact stepB.x1

theorem stepB_neutral : InputNeutral stepB := by
  rintro s s' a v h v'
  cases h
  · exact ⟨_, stepB.inL1 _ v'⟩
  · exact ⟨_, stepB.inH1 _ _ v'⟩



/-! ### Characterisation of the traces -/

def specA8 (u : List (Lbl L6 Bool)) (s' : AState) : Prop := u = [] ∧ s' = .a8

def specA7 (r x y : Bool) (u : List (Lbl L6 Bool)) (s' : AState) : Prop :=
  (u = [] ∧ s' = .a7 r x y) ∨
  (u = [.out L6.H3 (Bool.xor r (Bool.xor x y))] ∧ s' = .a8)

def specA6 (r x z y : Bool) (u : List (Lbl L6 Bool)) (s' : AState) : Prop :=
  (u = [] ∧ s' = .a6 r x z y) ∨ (∃ u', u = .out L6.H3 z :: u' ∧ specA7 r x y u' s')

def specA5 (r x z : Bool) (u : List (Lbl L6 Bool)) (s' : AState) : Prop :=
  (u = [] ∧ s' = .a5 r x z) ∨ (∃ y u', u = .inp L6.H2 y :: u' ∧ specA6 r x z y u' s')

def specA4 (r x : Bool) (u : List (Lbl L6 Bool)) (s' : AState) : Prop :=
  (u = [] ∧ s' = .a4 r x) ∨ (∃ z u', u = .inp L6.L2 z :: u' ∧ specA5 r x z u' s')

def specA3 (r x : Bool) (u : List (Lbl L6 Bool)) (s' : AState) : Prop :=
  (u = [] ∧ s' = .a3 r x) ∨ (∃ u', u = .out L6.L1 true :: u' ∧ specA4 r x u' s')

def specA2 (r x : Bool) (u : List (Lbl L6 Bool)) (s' : AState) : Prop :=
  (u = [] ∧ s' = .a2 r x) ∨ (∃ u', u = .out L6.H1 (!x) :: u' ∧ specA3 r x u' s')

def specA1 (r : Bool) (u : List (Lbl L6 Bool)) (s' : AState) : Prop :=
  (u = [] ∧ s' = .a1 r) ∨ (∃ x, specA2 r x u s')

def specA0 (u : List (Lbl L6 Bool)) (s' : AState) : Prop :=
  (u = [] ∧ s' = .a0) ∨ (∃ r u', u = .inp L6.H r :: u' ∧ specA1 r u' s')

def specA : AState → List (Lbl L6 Bool) → AState → Prop
  | .a0 => specA0
  | .a1 r => specA1 r
  | .a2 r x => specA2 r x
  | .a3 r x => specA3 r x
  | .a4 r x => specA4 r x
  | .a5 r x z => specA5 r x z
  | .a6 r x z y => specA6 r x z y
  | .a7 r x y => specA7 r x y
  | .a8 => specA8

theorem reachA_spec {s : AState} {u : List (Lbl L6 Bool)} {s' : AState}
    (h : Reach stepA s u s') : specA s u s' := by
  induction h with
  | @nil s => cases s <;> first | exact Or.inl ⟨rfl, rfl⟩ | exact ⟨rfl, rfl⟩
  | tau hs _ ih =>
      cases hs
      · exact Or.inr ⟨false, ih⟩
      · exact Or.inr ⟨true, ih⟩
  | @inp s s' s'' a v t hs _ ih =>
      cases hs
      · exact Or.inr ⟨v, _, rfl, ih⟩
      · exact Or.inr ⟨v, _, rfl, ih⟩
      · exact Or.inr ⟨v, _, rfl, ih⟩
  | @out s s' s'' a v t hs _ ih =>
      cases hs
      · exact Or.inr ⟨_, rfl, ih⟩
      · exact Or.inr ⟨_, rfl, ih⟩
      · exact Or.inr ⟨_, rfl, ih⟩
      · exact Or.inr ⟨by rw [ih.1], ih.2⟩

def specB7 (u : List (Lbl L6 Bool)) (s' : BState) : Prop := u = [] ∧ s' = .b7

def specB6 (x y : Bool) (u : List (Lbl L6 Bool)) (s' : BState) : Prop :=
  (u = [] ∧ s' = .b6 x y) ∨ (u = [.out L6.H3 (Bool.xor x y)] ∧ s' = .b7)

def specB5 (x z y : Bool) (u : List (Lbl L6 Bool)) (s' : BState) : Prop :=
  (u = [] ∧ s' = .b5 x z y) ∨ (∃ u', u = .out L6.H3 z :: u' ∧ specB6 x y u' s')

def specB4 (x z : Bool) (u : List (Lbl L6 Bool)) (s' : BState) : Prop :=
  (u = [] ∧ s' = .b4 x z) ∨ (∃ y u', u = .inp L6.H1 y :: u' ∧ specB5 x z y u' s')

def specB3 (x : Bool) (u : List (Lbl L6 Bool)) (s' : BState) : Prop :=
  (u = [] ∧ s' = .b3 x) ∨ (∃ z u', u = .inp L6.L1 z :: u' ∧ specB4 x z u' s')

def specB2 (x : Bool) (u : List (Lbl L6 Bool)) (s' : BState) : Prop :=
  (u = [] ∧ s' = .b2 x) ∨ (∃ u', u = .out L6.L2 true :: u' ∧ specB3 x u' s')

def specB1 (x : Bool) (u : List (Lbl L6 Bool)) (s' : BState) : Prop :=
  (u = [] ∧ s' = .b1 x) ∨ (∃ u', u = .out L6.H2 (!x) :: u' ∧ specB2 x u' s')

def specB0 (u : List (Lbl L6 Bool)) (s' : BState) : Prop :=
  (u = [] ∧ s' = .b0) ∨ (∃ x, specB1 x u s')

def specB : BState → List (Lbl L6 Bool) → BState → Prop
  | .b0 => specB0
  | .b1 x => specB1 x
  | .b2 x => specB2 x
  | .b3 x => specB3 x
  | .b4 x z => specB4 x z
  | .b5 x z y => specB5 x z y
  | .b6 x y => specB6 x y
  | .b7 => specB7

theorem reachB_spec {s : BState} {u : List (Lbl L6 Bool)} {s' : BState}
    (h : Reach stepB s u s') : specB s u s' := by
  induction h with
  | @nil s => cases s <;> first | exact Or.inl ⟨rfl, rfl⟩ | exact ⟨rfl, rfl⟩
  | tau hs _ ih =>
      cases hs
      · exact Or.inr ⟨false, ih⟩
      · exact Or.inr ⟨true, ih⟩
  | @inp s s' s'' a v t hs _ ih =>
      cases hs
      · exact Or.inr ⟨v, _, rfl, ih⟩
      · exact Or.inr ⟨v, _, rfl, ih⟩
  | @out s s' s'' a v t hs _ ih =>
      cases hs
      · exact Or.inr ⟨_, rfl, ih⟩
      · exact Or.inr ⟨_, rfl, ih⟩
      · exact Or.inr ⟨_, rfl, ih⟩
      · exact Or.inr ⟨by rw [ih.1], ih.2⟩

theorem specA0_len {u : List (Lbl L6 Bool)} {s' : AState} (h : specA0 u s') :
    u.length ≤ 7 := by
  rcases h with ⟨rfl, -⟩ | ⟨r, u₁, rfl, h⟩
  · simp
  rcases h with ⟨rfl, -⟩ | ⟨x, h⟩
  · simp
  rcases h with ⟨rfl, -⟩ | ⟨u₂, rfl, h⟩
  · simp
  rcases h with ⟨rfl, -⟩ | ⟨u₃, rfl, h⟩
  · simp
  rcases h with ⟨rfl, -⟩ | ⟨z, u₄, rfl, h⟩
  · simp
  rcases h with ⟨rfl, -⟩ | ⟨y, u₅, rfl, h⟩
  · simp
  rcases h with ⟨rfl, -⟩ | ⟨u₆, rfl, h⟩
  · simp
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem specA0_full {u : List (Lbl L6 Bool)} {s' : AState} (h : specA0 u s')
    (hl : u.length = 7) :
    ∃ r x z y, u = [Lbl.inp L6.H r, Lbl.out L6.H1 (!x), Lbl.out L6.L1 true,
                    Lbl.inp L6.L2 z, Lbl.inp L6.H2 y, Lbl.out L6.H3 z,
                    Lbl.out L6.H3 (Bool.xor r (Bool.xor x y))] := by
  rcases h with ⟨rfl, -⟩ | ⟨r, u₁, rfl, h⟩
  · simp at hl
  rcases h with ⟨rfl, -⟩ | ⟨x, h⟩
  · simp at hl
  rcases h with ⟨rfl, -⟩ | ⟨u₂, rfl, h⟩
  · simp at hl
  rcases h with ⟨rfl, -⟩ | ⟨u₃, rfl, h⟩
  · simp at hl
  rcases h with ⟨rfl, -⟩ | ⟨z, u₄, rfl, h⟩
  · simp at hl
  rcases h with ⟨rfl, -⟩ | ⟨y, u₅, rfl, h⟩
  · simp at hl
  rcases h with ⟨rfl, -⟩ | ⟨u₆, rfl, h⟩
  · simp at hl
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · simp at hl
  · exact ⟨r, x, z, y, rfl⟩

theorem specB0_len {u : List (Lbl L6 Bool)} {s' : BState} (h : specB0 u s') :
    u.length ≤ 6 := by
  rcases h with ⟨rfl, -⟩ | ⟨x, h⟩
  · simp
  rcases h with ⟨rfl, -⟩ | ⟨u₁, rfl, h⟩
  · simp
  rcases h with ⟨rfl, -⟩ | ⟨u₂, rfl, h⟩
  · simp
  rcases h with ⟨rfl, -⟩ | ⟨z, u₃, rfl, h⟩
  · simp
  rcases h with ⟨rfl, -⟩ | ⟨y, u₄, rfl, h⟩
  · simp
  rcases h with ⟨rfl, -⟩ | ⟨u₅, rfl, h⟩
  · simp
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem specB0_full {u : List (Lbl L6 Bool)} {s' : BState} (h : specB0 u s')
    (hl : u.length = 6) :
    ∃ x z y, u = [Lbl.out L6.H2 (!x), Lbl.out L6.L2 true, Lbl.inp L6.L1 z,
                  Lbl.inp L6.H1 y, Lbl.out L6.H3 z, Lbl.out L6.H3 (Bool.xor x y)] := by
  rcases h with ⟨rfl, -⟩ | ⟨x, h⟩
  · simp at hl
  rcases h with ⟨rfl, -⟩ | ⟨u₁, rfl, h⟩
  · simp at hl
  rcases h with ⟨rfl, -⟩ | ⟨u₂, rfl, h⟩
  · simp at hl
  rcases h with ⟨rfl, -⟩ | ⟨z, u₃, rfl, h⟩
  · simp at hl
  rcases h with ⟨rfl, -⟩ | ⟨y, u₄, rfl, h⟩
  · simp at hl
  rcases h with ⟨rfl, -⟩ | ⟨u₅, rfl, h⟩
  · simp at hl
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · simp at hl
  · exact ⟨x, z, y, rfl⟩


/-! ### Prefix equivalences -/

theorem teqL2_pre (r r' x x' : Bool) :
    Sc.teq L6.L2 [Lbl.inp L6.H r, Lbl.out L6.H1 (!x), Lbl.out L6.L1 true]
                 [Lbl.inp L6.H r', Lbl.out L6.H1 (!x'), Lbl.out L6.L1 true] := by
  rw [teq_iff]; simp [pj, hide, L6.leB]

theorem teqH2_pre (r r' x x' z : Bool) :
    Sc.teq L6.H2 [Lbl.inp L6.H r, Lbl.out L6.H1 (!x), Lbl.out L6.L1 true, Lbl.inp L6.L2 z]
                 [Lbl.inp L6.H r', Lbl.out L6.H1 (!x'), Lbl.out L6.L1 true,
                  Lbl.inp L6.L2 z] := by
  rw [teq_iff]; simp [pj, hide, L6.leB]

theorem teqL1_pre (x x' : Bool) :
    Sc.teq L6.L1 [Lbl.out L6.H2 (!x), Lbl.out L6.L2 true]
                 [Lbl.out L6.H2 (!x'), Lbl.out L6.L2 true] := by
  rw [teq_iff]; simp [pj, hide, L6.leB]

theorem teqH1_pre (x x' z : Bool) :
    Sc.teq L6.H1 [Lbl.out L6.H2 (!x), Lbl.out L6.L2 true, Lbl.inp L6.L1 z]
                 [Lbl.out L6.H2 (!x'), Lbl.out L6.L2 true, Lbl.inp L6.L1 z] := by
  rw [teq_iff]; simp [pj, hide, L6.leB]

theorem xor_cancel (A e : Bool) : A = Bool.xor (Bool.xor A e) e := by
  cases A <;> cases e <;> rfl

theorem xor_fix (A d e : Bool) :
    A = Bool.xor d (Bool.xor (Bool.xor A (Bool.xor d e)) e) := by
  cases A <;> cases d <;> cases e <;> rfl

/-! ### `P_A` is noninterfering -/

theorem A_NI : Sc.StratNI stepA AState.a0 := by
  intro ℓ w₁ w₂ _ _ hww t₁ hprod
  obtain ⟨⟨s', hreach⟩, hcons⟩ := hprod
  have hspec : specA0 t₁ s' := reachA_spec hreach
  rcases hspec with ⟨rfl, -⟩ | ⟨r, u₁, rfl, h1⟩
  · exact ⟨[], ⟨⟨.a0, Reach.nil⟩, Sec.consistent_nil _⟩, rfl⟩
  have hr : w₁.ω L6.H [] r := hcons [] L6.H r u₁ rfl
  obtain ⟨r₂, hr₂, hr₂eq⟩ :=
    Sec.match_input hww (Sc_pres_le _ _) (rfl : Sc.teq (Sc.valL L6.H) [] []) hr
  have hrpj : L6.le L6.H ℓ → r = r₂ := fun h => (hr₂eq (by simpa using h)).symm
  have hstep1 : Reach stepA AState.a0 [Lbl.inp L6.H r₂] (AState.a1 r₂) :=
    Reach.inp (stepA.inH r₂) Reach.nil
  rcases h1 with ⟨rfl, -⟩ | ⟨x, h2⟩
  · refine ⟨[Lbl.inp L6.H r₂], ⟨⟨_, hstep1⟩,
      Sec.consistent_cons_inp hr₂ (Sec.consistent_nil _)⟩, ?_⟩
    rw [teq_iff]; simp only [List.map_cons, List.map_nil]; rw [pj_eq_inp hrpj]
  rcases h2 with ⟨rfl, -⟩ | ⟨u₂, rfl, h3⟩
  · refine ⟨[Lbl.inp L6.H r₂], ⟨⟨_, hstep1⟩,
      Sec.consistent_cons_inp hr₂ (Sec.consistent_nil _)⟩, ?_⟩
    rw [teq_iff]; simp only [List.map_cons, List.map_nil]; rw [pj_eq_inp hrpj]
  rcases h3 with ⟨rfl, -⟩ | ⟨u₃, rfl, h4⟩
  · -- `H?r.H₁!(¬x)`
    refine ⟨[Lbl.inp L6.H r₂, Lbl.out L6.H1 (!x)],
      ⟨⟨_, Reach.inp (stepA.inH r₂) (Reach.tau (stepA.choose r₂ x)
        (Reach.out (stepA.outH1 r₂ x) Reach.nil))⟩,
      Sec.consistent_cons_inp hr₂ (Sec.consistent_cons_out (Sec.consistent_nil _))⟩, ?_⟩
    rw [teq_iff]; simp only [List.map_cons, List.map_nil]; rw [pj_eq_inp hrpj]
  rcases h4 with ⟨rfl, -⟩ | ⟨z, u₄, rfl, h5⟩
  · -- `H?r.H₁!(¬x).L₁!1`
    refine ⟨[Lbl.inp L6.H r₂, Lbl.out L6.H1 (!x), Lbl.out L6.L1 true],
      ⟨⟨_, Reach.inp (stepA.inH r₂) (Reach.tau (stepA.choose r₂ x)
        (Reach.out (stepA.outH1 r₂ x) (Reach.out (stepA.outL1 r₂ x) Reach.nil)))⟩,
      Sec.consistent_cons_inp hr₂ (Sec.consistent_cons_out
        (Sec.consistent_cons_out (Sec.consistent_nil _)))⟩, ?_⟩
    rw [teq_iff]; simp only [List.map_cons, List.map_nil]; rw [pj_eq_inp hrpj]
  -- the input on `L₂` is forced to the same value (its level is below every level)
  have hz : w₁.ω L6.L2 [Lbl.inp L6.H r, Lbl.out L6.H1 (!x), Lbl.out L6.L1 true] z :=
    hcons [Lbl.inp L6.H r, Lbl.out L6.H1 (!x), Lbl.out L6.L1 true] L6.L2 z u₄ rfl
  obtain ⟨z₂, hz₂, hz₂eq⟩ :=
    Sec.match_input (u₂ := [Lbl.inp L6.H r₂, Lbl.out L6.H1 (!false), Lbl.out L6.L1 true])
      hww (Sc_pres_le _ _) (teqL2_pre r r₂ x false) hz
  have hz₂z : z₂ = z := hz₂eq (le_L2 ℓ)
  subst hz₂z
  have hz₂' : ∀ x₂ : Bool,
      w₂.ω L6.L2 [Lbl.inp L6.H r₂, Lbl.out L6.H1 (!x₂), Lbl.out L6.L1 true] z₂ := by
    intro x₂
    have := w₂.resp_val L6.L2
      [Lbl.inp L6.H r₂, Lbl.out L6.H1 (!false), Lbl.out L6.L1 true]
      [Lbl.inp L6.H r₂, Lbl.out L6.H1 (!x₂), Lbl.out L6.L1 true] (teqL2_pre r₂ r₂ false x₂)
    rw [← this]; exact hz₂
  rcases h5 with ⟨rfl, -⟩ | ⟨y, u₅, rfl, h6⟩
  · -- `H?r.H₁!(¬x).L₁!1.L₂?z`
    refine ⟨[Lbl.inp L6.H r₂, Lbl.out L6.H1 (!x), Lbl.out L6.L1 true, Lbl.inp L6.L2 z₂],
      ⟨⟨_, Reach.inp (stepA.inH r₂) (Reach.tau (stepA.choose r₂ x)
        (Reach.out (stepA.outH1 r₂ x) (Reach.out (stepA.outL1 r₂ x)
          (Reach.inp (stepA.inL2 r₂ x z₂) Reach.nil))))⟩,
      Sec.consistent_cons_inp hr₂ (Sec.consistent_cons_out (Sec.consistent_cons_out
        (Sec.consistent_cons_inp (hz₂' x) (Sec.consistent_nil _))))⟩, ?_⟩
    rw [teq_iff]; simp only [List.map_cons, List.map_nil]; rw [pj_eq_inp hrpj]
  -- the input on `H₂`
  have hy : w₁.ω L6.H2 [Lbl.inp L6.H r, Lbl.out L6.H1 (!x), Lbl.out L6.L1 true,
      Lbl.inp L6.L2 z₂] y :=
    hcons [Lbl.inp L6.H r, Lbl.out L6.H1 (!x), Lbl.out L6.L1 true, Lbl.inp L6.L2 z₂]
      L6.H2 y u₅ rfl
  obtain ⟨y₂, hy₂, hy₂eq⟩ :=
    Sec.match_input (u₂ := [Lbl.inp L6.H r₂, Lbl.out L6.H1 (!false), Lbl.out L6.L1 true,
      Lbl.inp L6.L2 z₂]) hww (Sc_pres_le _ _) (teqH2_pre r r₂ x false z₂) hy
  have hypj : L6.le L6.H2 ℓ → y = y₂ := fun h => (hy₂eq (by simpa using h)).symm
  have hy₂' : ∀ x₂ : Bool, w₂.ω L6.H2 [Lbl.inp L6.H r₂, Lbl.out L6.H1 (!x₂),
      Lbl.out L6.L1 true, Lbl.inp L6.L2 z₂] y₂ := by
    intro x₂
    have := w₂.resp_val L6.H2
      [Lbl.inp L6.H r₂, Lbl.out L6.H1 (!false), Lbl.out L6.L1 true, Lbl.inp L6.L2 z₂]
      [Lbl.inp L6.H r₂, Lbl.out L6.H1 (!x₂), Lbl.out L6.L1 true, Lbl.inp L6.L2 z₂]
      (teqH2_pre r₂ r₂ false x₂ z₂)
    rw [← this]; exact hy₂
  rcases h6 with ⟨rfl, -⟩ | ⟨u₆, rfl, h7⟩
  · -- `… .H₂?y`
    refine ⟨[Lbl.inp L6.H r₂, Lbl.out L6.H1 (!x), Lbl.out L6.L1 true, Lbl.inp L6.L2 z₂,
             Lbl.inp L6.H2 y₂],
      ⟨⟨_, Reach.inp (stepA.inH r₂) (Reach.tau (stepA.choose r₂ x)
        (Reach.out (stepA.outH1 r₂ x) (Reach.out (stepA.outL1 r₂ x)
          (Reach.inp (stepA.inL2 r₂ x z₂) (Reach.inp (stepA.inH2 r₂ x z₂ y₂)
            Reach.nil)))))⟩,
      Sec.consistent_cons_inp hr₂ (Sec.consistent_cons_out (Sec.consistent_cons_out
        (Sec.consistent_cons_inp (hz₂' x) (Sec.consistent_cons_inp (hy₂' x)
          (Sec.consistent_nil _)))))⟩, ?_⟩
    rw [teq_iff]; simp only [List.map_cons, List.map_nil]
    rw [pj_eq_inp hrpj, pj_eq_inp (c := L6.H2) hypj]
  rcases h7 with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · -- `… .H₃!z`
    refine ⟨[Lbl.inp L6.H r₂, Lbl.out L6.H1 (!x), Lbl.out L6.L1 true, Lbl.inp L6.L2 z₂,
             Lbl.inp L6.H2 y₂, Lbl.out L6.H3 z₂],
      ⟨⟨_, Reach.inp (stepA.inH r₂) (Reach.tau (stepA.choose r₂ x)
        (Reach.out (stepA.outH1 r₂ x) (Reach.out (stepA.outL1 r₂ x)
          (Reach.inp (stepA.inL2 r₂ x z₂) (Reach.inp (stepA.inH2 r₂ x z₂ y₂)
            (Reach.out (stepA.outZ r₂ x z₂ y₂) Reach.nil))))))⟩,
      Sec.consistent_cons_inp hr₂ (Sec.consistent_cons_out (Sec.consistent_cons_out
        (Sec.consistent_cons_inp (hz₂' x) (Sec.consistent_cons_inp (hy₂' x)
          (Sec.consistent_cons_out (Sec.consistent_nil _))))))⟩, ?_⟩
    rw [teq_iff]; simp only [List.map_cons, List.map_nil]
    rw [pj_eq_inp hrpj, pj_eq_inp (c := L6.H2) hypj]
  · -- the full trace
    obtain ⟨x₂, hx₂⟩ : ∃ w : Bool,
        w = (if ℓ = L6.H3 then Bool.xor (Bool.xor r (Bool.xor x y)) (Bool.xor r₂ y₂)
             else x) := ⟨_, rfl⟩
    have hxpj : L6.le L6.H1 ℓ → (!x) = (!x₂) := by
      intro h
      rcases le_cases (by decide) (by decide) h with hℓ | hℓ <;> subst hℓ <;>
        rw [hx₂] <;> simp
    have hopj : L6.le L6.H3 ℓ →
        Bool.xor r (Bool.xor x y) = Bool.xor r₂ (Bool.xor x₂ y₂) := by
      intro h
      rcases le_cases (by decide) (by decide) h with hℓ | hℓ
      · subst hℓ
        rw [hx₂, if_pos rfl]
        exact xor_fix _ _ _
      · subst hℓ
        rw [hx₂, if_neg (by simp), ← hrpj (le_top _), ← hypj (le_top _)]
    refine ⟨[Lbl.inp L6.H r₂, Lbl.out L6.H1 (!x₂), Lbl.out L6.L1 true, Lbl.inp L6.L2 z₂,
             Lbl.inp L6.H2 y₂, Lbl.out L6.H3 z₂,
             Lbl.out L6.H3 (Bool.xor r₂ (Bool.xor x₂ y₂))],
      ⟨⟨_, Reach.inp (stepA.inH r₂) (Reach.tau (stepA.choose r₂ x₂)
        (Reach.out (stepA.outH1 r₂ x₂) (Reach.out (stepA.outL1 r₂ x₂)
          (Reach.inp (stepA.inL2 r₂ x₂ z₂) (Reach.inp (stepA.inH2 r₂ x₂ z₂ y₂)
            (Reach.out (stepA.outZ r₂ x₂ z₂ y₂)
              (Reach.out (stepA.outH3 r₂ x₂ y₂) Reach.nil)))))))⟩,
      Sec.consistent_cons_inp hr₂ (Sec.consistent_cons_out (Sec.consistent_cons_out
        (Sec.consistent_cons_inp (hz₂' x₂) (Sec.consistent_cons_inp (hy₂' x₂)
          (Sec.consistent_cons_out (Sec.consistent_cons_out
            (Sec.consistent_nil _)))))))⟩, ?_⟩
    rw [teq_iff]; simp only [List.map_cons, List.map_nil]
    rw [pj_eq_inp hrpj, pj_eq_inp (c := L6.H2) hypj, pj_eq_out (c := L6.H1) hxpj,
      pj_eq_out (c := L6.H3) hopj]

theorem A_TNI : Sc.StratTNI stepA AState.a0 :=
  Sec.INI_mono (fun _ _ => trivial) A_NI

/-! ### `P_B` is noninterfering -/

theorem B_NI : Sc.StratNI stepB BState.b0 := by
  intro ℓ w₁ w₂ _ _ hww t₁ hprod
  obtain ⟨⟨s', hreach⟩, hcons⟩ := hprod
  have hspec : specB0 t₁ s' := reachB_spec hreach
  rcases hspec with ⟨rfl, -⟩ | ⟨x, h1⟩
  · exact ⟨[], ⟨⟨.b0, Reach.nil⟩, Sec.consistent_nil _⟩, rfl⟩
  rcases h1 with ⟨rfl, -⟩ | ⟨u₁, rfl, h2⟩
  · exact ⟨[], ⟨⟨.b0, Reach.nil⟩, Sec.consistent_nil _⟩, rfl⟩
  rcases h2 with ⟨rfl, -⟩ | ⟨u₂, rfl, h3⟩
  · -- `H₂!(¬x')`
    exact ⟨[Lbl.out L6.H2 (!x)],
      ⟨⟨_, Reach.tau (stepB.choose x) (Reach.out (stepB.outH2 x) Reach.nil)⟩,
        Sec.consistent_cons_out (Sec.consistent_nil _)⟩, rfl⟩
  rcases h3 with ⟨rfl, -⟩ | ⟨z, u₃, rfl, h4⟩
  · -- `H₂!(¬x').L₂!1`
    exact ⟨[Lbl.out L6.H2 (!x), Lbl.out L6.L2 true],
      ⟨⟨_, Reach.tau (stepB.choose x) (Reach.out (stepB.outH2 x)
        (Reach.out (stepB.outL2 x) Reach.nil))⟩,
        Sec.consistent_cons_out (Sec.consistent_cons_out (Sec.consistent_nil _))⟩, rfl⟩
  have hz : w₁.ω L6.L1 [Lbl.out L6.H2 (!x), Lbl.out L6.L2 true] z :=
    hcons [Lbl.out L6.H2 (!x), Lbl.out L6.L2 true] L6.L1 z u₃ rfl
  obtain ⟨z₂, hz₂, hz₂eq⟩ :=
    Sec.match_input (u₂ := [Lbl.out L6.H2 (!false), Lbl.out L6.L2 true])
      hww (Sc_pres_le _ _) (teqL1_pre x false) hz
  have hz₂z : z₂ = z := hz₂eq (le_L1 ℓ)
  subst hz₂z
  have hz₂' : ∀ x₂ : Bool, w₂.ω L6.L1 [Lbl.out L6.H2 (!x₂), Lbl.out L6.L2 true] z₂ := by
    intro x₂
    have := w₂.resp_val L6.L1 [Lbl.out L6.H2 (!false), Lbl.out L6.L2 true]
      [Lbl.out L6.H2 (!x₂), Lbl.out L6.L2 true] (teqL1_pre false x₂)
    rw [← this]; exact hz₂
  rcases h4 with ⟨rfl, -⟩ | ⟨y, u₄, rfl, h5⟩
  · -- `H₂!(¬x').L₂!1.L₁?z'`
    refine ⟨[Lbl.out L6.H2 (!x), Lbl.out L6.L2 true, Lbl.inp L6.L1 z₂],
      ⟨⟨_, Reach.tau (stepB.choose x) (Reach.out (stepB.outH2 x)
        (Reach.out (stepB.outL2 x) (Reach.inp (stepB.inL1 x z₂) Reach.nil)))⟩,
        Sec.consistent_cons_out (Sec.consistent_cons_out
          (Sec.consistent_cons_inp (hz₂' x) (Sec.consistent_nil _)))⟩, rfl⟩
  have hy : w₁.ω L6.H1 [Lbl.out L6.H2 (!x), Lbl.out L6.L2 true, Lbl.inp L6.L1 z₂] y :=
    hcons [Lbl.out L6.H2 (!x), Lbl.out L6.L2 true, Lbl.inp L6.L1 z₂] L6.H1 y u₄ rfl
  obtain ⟨y₂, hy₂, hy₂eq⟩ :=
    Sec.match_input (u₂ := [Lbl.out L6.H2 (!false), Lbl.out L6.L2 true, Lbl.inp L6.L1 z₂])
      hww (Sc_pres_le _ _) (teqH1_pre x false z₂) hy
  have hypj : L6.le L6.H1 ℓ → y = y₂ := fun h => (hy₂eq (by simpa using h)).symm
  have hy₂' : ∀ x₂ : Bool, w₂.ω L6.H1 [Lbl.out L6.H2 (!x₂), Lbl.out L6.L2 true,
      Lbl.inp L6.L1 z₂] y₂ := by
    intro x₂
    have := w₂.resp_val L6.H1
      [Lbl.out L6.H2 (!false), Lbl.out L6.L2 true, Lbl.inp L6.L1 z₂]
      [Lbl.out L6.H2 (!x₂), Lbl.out L6.L2 true, Lbl.inp L6.L1 z₂] (teqH1_pre false x₂ z₂)
    rw [← this]; exact hy₂
  rcases h5 with ⟨rfl, -⟩ | ⟨u₅, rfl, h6⟩
  · -- `… .H₁?y'`
    refine ⟨[Lbl.out L6.H2 (!x), Lbl.out L6.L2 true, Lbl.inp L6.L1 z₂, Lbl.inp L6.H1 y₂],
      ⟨⟨_, Reach.tau (stepB.choose x) (Reach.out (stepB.outH2 x)
        (Reach.out (stepB.outL2 x) (Reach.inp (stepB.inL1 x z₂)
          (Reach.inp (stepB.inH1 x z₂ y₂) Reach.nil))))⟩,
        Sec.consistent_cons_out (Sec.consistent_cons_out
          (Sec.consistent_cons_inp (hz₂' x) (Sec.consistent_cons_inp (hy₂' x)
            (Sec.consistent_nil _))))⟩, ?_⟩
    rw [teq_iff]; simp only [List.map_cons, List.map_nil]
    rw [pj_eq_inp (c := L6.H1) hypj]
  rcases h6 with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · -- `… .H₃!z'`
    refine ⟨[Lbl.out L6.H2 (!x), Lbl.out L6.L2 true, Lbl.inp L6.L1 z₂, Lbl.inp L6.H1 y₂,
             Lbl.out L6.H3 z₂],
      ⟨⟨_, Reach.tau (stepB.choose x) (Reach.out (stepB.outH2 x)
        (Reach.out (stepB.outL2 x) (Reach.inp (stepB.inL1 x z₂)
          (Reach.inp (stepB.inH1 x z₂ y₂) (Reach.out (stepB.outZ x z₂ y₂) Reach.nil)))))⟩,
        Sec.consistent_cons_out (Sec.consistent_cons_out
          (Sec.consistent_cons_inp (hz₂' x) (Sec.consistent_cons_inp (hy₂' x)
            (Sec.consistent_cons_out (Sec.consistent_nil _)))))⟩, ?_⟩
    rw [teq_iff]; simp only [List.map_cons, List.map_nil]
    rw [pj_eq_inp (c := L6.H1) hypj]
  · -- the full trace
    obtain ⟨x₂, hx₂⟩ : ∃ w : Bool,
        w = (if ℓ = L6.H3 then Bool.xor (Bool.xor x y) y₂ else x) := ⟨_, rfl⟩
    have hxpj : L6.le L6.H2 ℓ → (!x) = (!x₂) := by
      intro h
      rcases le_cases (by decide) (by decide) h with hℓ | hℓ <;> subst hℓ <;>
        rw [hx₂] <;> simp
    have hopj : L6.le L6.H3 ℓ → Bool.xor x y = Bool.xor x₂ y₂ := by
      intro h
      rcases le_cases (by decide) (by decide) h with hℓ | hℓ
      · subst hℓ
        rw [hx₂, if_pos rfl]
        exact xor_cancel _ _
      · subst hℓ
        rw [hx₂, if_neg (by simp), ← hypj (le_top _)]
    refine ⟨[Lbl.out L6.H2 (!x₂), Lbl.out L6.L2 true, Lbl.inp L6.L1 z₂, Lbl.inp L6.H1 y₂,
             Lbl.out L6.H3 z₂, Lbl.out L6.H3 (Bool.xor x₂ y₂)],
      ⟨⟨_, Reach.tau (stepB.choose x₂) (Reach.out (stepB.outH2 x₂)
        (Reach.out (stepB.outL2 x₂) (Reach.inp (stepB.inL1 x₂ z₂)
          (Reach.inp (stepB.inH1 x₂ z₂ y₂) (Reach.out (stepB.outZ x₂ z₂ y₂)
            (Reach.out (stepB.outH3 x₂ y₂) Reach.nil))))))⟩,
        Sec.consistent_cons_out (Sec.consistent_cons_out
          (Sec.consistent_cons_inp (hz₂' x₂) (Sec.consistent_cons_inp (hy₂' x₂)
            (Sec.consistent_cons_out (Sec.consistent_cons_out
              (Sec.consistent_nil _))))))⟩, ?_⟩
    rw [teq_iff]; simp only [List.map_cons, List.map_nil]
    rw [pj_eq_inp (c := L6.H1) hypj, pj_eq_out (c := L6.H2) hxpj,
      pj_eq_out (c := L6.H3) hopj]

theorem B_TNI : Sc.StratTNI stepB BState.b0 :=
  Sec.INI_mono (fun _ _ => trivial) B_NI


/-! ### The attacking (total) strategies -/

def omegaSet (c : L6) (t : List (Lbl L6 Bool)) : VSet Bool :=
  fun v => (Lbl.out c v ∈ t) ∨ ((∀ w, ¬ (Lbl.out c w ∈ t)) ∧ v = false)

def omegaFun (b : Bool) (c : L6) (t : List (Lbl L6 Bool)) : VSet Bool :=
  match c with
  | L6.H => fun v => v = b
  | L6.H3 => fun v => v = false
  | L6.L1 => omegaSet L6.L1 t
  | L6.L2 => omegaSet L6.L2 t
  | L6.H1 => omegaSet L6.H1 t
  | L6.H2 => omegaSet L6.H2 t
  | L6.Top => fun v => v = false

theorem omegaSet_nonempty (c : L6) (t : List (Lbl L6 Bool)) : ∃ v, omegaSet c t v := by
  by_cases h : ∃ w, Lbl.out c w ∈ t
  · obtain ⟨w, hw⟩ := h
    exact ⟨w, Or.inl hw⟩
  · exact ⟨false, Or.inr ⟨fun w hw => h ⟨w, hw⟩, rfl⟩⟩

theorem omega_nonempty (b : Bool) (c : L6) (t : List (Lbl L6 Bool)) :
    ∃ v, omegaFun b c t v := by
  cases c
  · exact omegaSet_nonempty _ _
  · exact omegaSet_nonempty _ _
  · exact ⟨b, rfl⟩
  · exact omegaSet_nonempty _ _
  · exact omegaSet_nonempty _ _
  · exact ⟨false, rfl⟩
  · exact ⟨false, rfl⟩

theorem dotEq_of_nonempty {a b : VSet Bool} (ha : ∃ v, a v) (hb : ∃ v, b v) :
    dotEq a b := by
  obtain ⟨v, hv⟩ := ha
  obtain ⟨w, hw⟩ := hb
  exact ⟨fun h => absurd hv (h v), fun h => absurd hw (h w)⟩

theorem mem_iff_of_teq {c : L6} {t₁ t₂ : List (Lbl L6 Bool)}
    (ht : Sc.teq c t₁ t₂) (v : Bool) : (Lbl.out c v ∈ t₁) ↔ (Lbl.out c v ∈ t₂) := by
  have hp : Sc.le (Sc.presL c) c := Sc_pres_le c c
  have hv : Sc.le (Sc.valL c) c := L6.le_refl c
  rw [← Sec.mem_proj_out_full hp hv t₁, ← Sec.mem_proj_out_full hp hv t₂]
  unfold Sec.teq at ht
  rw [ht]

theorem omegaSet_congr {c : L6} {t₁ t₂ : List (Lbl L6 Bool)} (ht : Sc.teq c t₁ t₂) :
    omegaSet c t₁ = omegaSet c t₂ := by
  funext v
  apply propext
  constructor
  · rintro (h | ⟨h, rfl⟩)
    · exact Or.inl ((mem_iff_of_teq ht v).mp h)
    · exact Or.inr ⟨fun w hw => h w ((mem_iff_of_teq ht w).mpr hw), rfl⟩
  · rintro (h | ⟨h, rfl⟩)
    · exact Or.inl ((mem_iff_of_teq ht v).mpr h)
    · exact Or.inr ⟨fun w hw => h w ((mem_iff_of_teq ht w).mp hw), rfl⟩

noncomputable def cexOmega (b : Bool) : Sc.Strategy Bool where
  ω := omegaFun b
  resp_val := by
    intro c t₁ t₂ ht
    cases c
    · exact omegaSet_congr ht
    · exact omegaSet_congr ht
    · rfl
    · exact omegaSet_congr ht
    · exact omegaSet_congr ht
    · rfl
    · rfl
  resp_pres := by
    intro c t₁ t₂ _
    exact dotEq_of_nonempty (omega_nonempty b c t₁) (omega_nonempty b c t₂)

theorem cexOmega_total (b : Bool) : (cexOmega b).total :=
  fun c t => omega_nonempty b c t

theorem cexOmega_seq : Sc.seq L6.H3 (cexOmega false) (cexOmega true) := by
  intro c t
  refine ⟨?_, fun _ => dotEq_of_nonempty (omega_nonempty _ c t) (omega_nonempty _ c t)⟩
  intro hle
  cases c
  · rfl
  · rfl
  · exact absurd hle (by rintro (hh | hh | hh | hh) <;> exact L6.noConfusion hh)
  · exact absurd hle (by rintro (hh | hh | hh | hh) <;> exact L6.noConfusion hh)
  · exact absurd hle (by rintro (hh | hh | hh | hh) <;> exact L6.noConfusion hh)
  · rfl
  · exact absurd hle (by rintro (hh | hh | hh | hh) <;> exact L6.noConfusion hh)

/-! ### The attacking trace -/

def tcex : List (Lbl L6 Bool) :=
  [Lbl.inp L6.H false, Lbl.out L6.H1 false, Lbl.out L6.L1 true, Lbl.out L6.H2 false,
   Lbl.out L6.L2 true, Lbl.inp L6.L2 true, Lbl.inp L6.H2 false, Lbl.inp L6.L1 true,
   Lbl.inp L6.H1 false, Lbl.out L6.H3 true, Lbl.out L6.H3 true, Lbl.out L6.H3 true,
   Lbl.out L6.H3 true]

theorem tcex_reach :
    Reach (parStep stepA stepB) (AState.a0, BState.b0) tcex (AState.a8, BState.b7) := by
  refine Reach.inp (s' := (AState.a1 false, BState.b0))
    (Or.inl ⟨stepA.inH false, rfl⟩) ?_
  refine Reach.tau (s' := (AState.a2 false true, BState.b0))
    (Or.inl ⟨stepA.choose false true, rfl⟩) ?_
  refine Reach.out (s' := (AState.a3 false true, BState.b0))
    (Or.inl ⟨stepA.outH1 false true, rfl⟩) ?_
  refine Reach.out (s' := (AState.a4 false true, BState.b0))
    (Or.inl ⟨stepA.outL1 false true, rfl⟩) ?_
  refine Reach.tau (s' := (AState.a4 false true, BState.b1 true))
    (Or.inr ⟨stepB.choose true, rfl⟩) ?_
  refine Reach.out (s' := (AState.a4 false true, BState.b2 true))
    (Or.inr ⟨stepB.outH2 true, rfl⟩) ?_
  refine Reach.out (s' := (AState.a4 false true, BState.b3 true))
    (Or.inr ⟨stepB.outL2 true, rfl⟩) ?_
  refine Reach.inp (s' := (AState.a5 false true true, BState.b3 true))
    (Or.inl ⟨stepA.inL2 false true true, rfl⟩) ?_
  refine Reach.inp (s' := (AState.a6 false true true false, BState.b3 true))
    (Or.inl ⟨stepA.inH2 false true true false, rfl⟩) ?_
  refine Reach.inp (s' := (AState.a6 false true true false, BState.b4 true true))
    (Or.inr ⟨stepB.inL1 true true, rfl⟩) ?_
  refine Reach.inp (s' := (AState.a6 false true true false, BState.b5 true true false))
    (Or.inr ⟨stepB.inH1 true true false, rfl⟩) ?_
  refine Reach.out (s' := (AState.a7 false true false, BState.b5 true true false))
    (Or.inl ⟨stepA.outZ false true true false, rfl⟩) ?_
  refine Reach.out (s' := (AState.a8, BState.b5 true true false))
    (Or.inl ⟨stepA.outH3 false true false, rfl⟩) ?_
  refine Reach.out (s' := (AState.a8, BState.b6 true false))
    (Or.inr ⟨stepB.outZ true true false, rfl⟩) ?_
  exact Reach.out (s' := (AState.a8, BState.b7))
    (Or.inr ⟨stepB.outH3 true false, rfl⟩) Reach.nil

theorem tcex_consistent : Sc.consistent (cexOmega false) tcex := by
  refine Sec.consistent_cons_inp ?_ (Sec.consistent_cons_out (Sec.consistent_cons_out
    (Sec.consistent_cons_out (Sec.consistent_cons_out (Sec.consistent_cons_inp ?_
      (Sec.consistent_cons_inp ?_ (Sec.consistent_cons_inp ?_ (Sec.consistent_cons_inp ?_
        (Sec.consistent_cons_out (Sec.consistent_cons_out (Sec.consistent_cons_out
          (Sec.consistent_cons_out (Sec.consistent_nil _)))))))))))))
  · show (false : Bool) = false
    rfl
  · exact Or.inl (by simp)
  · exact Or.inl (by simp)
  · exact Or.inl (by simp)
  · exact Or.inl (by simp)

theorem tcex_produces :
    Sc.produces (parStep stepA stepB) (cexOmega false) (AState.a0, BState.b0) tcex :=
  ⟨⟨_, tcex_reach⟩, tcex_consistent⟩

/-! ### No `H₃`-equivalent trace can be produced under `ω₂` -/

theorem tcex_proj : List.map (pj L6.H3) tcex =
    [PLbl.inp L6.H none, PLbl.out L6.H1 none, PLbl.out L6.L1 (some true),
     PLbl.out L6.H2 none, PLbl.out L6.L2 (some true), PLbl.inp L6.L2 (some true),
     PLbl.inp L6.H2 none, PLbl.inp L6.L1 (some true), PLbl.inp L6.H1 none,
     PLbl.out L6.H3 (some true), PLbl.out L6.H3 (some true), PLbl.out L6.H3 (some true),
     PLbl.out L6.H3 (some true)] := rfl

theorem no_match (t' : List (Lbl L6 Bool))
    (hprod : Sc.produces (parStep stepA stepB) (cexOmega true) (AState.a0, BState.b0) t')
    (ht : Sc.teq L6.H3 tcex t') : False := by
  obtain ⟨⟨q, hr⟩, hc⟩ := hprod
  rw [teq_iff, tcex_proj] at ht
  have hlen : t'.length = 13 := by
    have h := congrArg List.length ht
    simpa using h.symm
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, rfl⟩ :
      ∃ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13,
        t' = [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13] := by
    rcases t' with _|⟨l1,_|⟨l2,_|⟨l3,_|⟨l4,_|⟨l5,_|⟨l6,_|⟨l7,_|⟨l8,_|⟨l9,_|⟨l10,_|⟨l11,_|⟨l12,_|⟨l13,_|⟨l14,rest⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp only [List.length_cons, List.length_nil] at hlen <;>
      first
        | exact ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,rfl⟩
        | omega
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at ht
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩ := ht
  obtain ⟨r, rfl, -⟩ := pj_inp_eq e1.symm
  obtain ⟨a, rfl, -⟩ := pj_out_eq e2.symm
  obtain ⟨v3, rfl, h3⟩ := pj_out_eq e3.symm
  obtain ⟨b, rfl, -⟩ := pj_out_eq e4.symm
  obtain ⟨v5, rfl, h5⟩ := pj_out_eq e5.symm
  obtain ⟨v6, rfl, h6⟩ := pj_inp_eq e6.symm
  obtain ⟨c, rfl, -⟩ := pj_inp_eq e7.symm
  obtain ⟨v8, rfl, h8⟩ := pj_inp_eq e8.symm
  obtain ⟨d, rfl, -⟩ := pj_inp_eq e9.symm
  obtain ⟨o1, rfl, k1⟩ := pj_out_eq e10.symm
  obtain ⟨o2, rfl, k2⟩ := pj_out_eq e11.symm
  obtain ⟨o3, rfl, k3⟩ := pj_out_eq e12.symm
  obtain ⟨o4, rfl, k4⟩ := pj_out_eq e13.symm
  have hval : ∀ {cc : L6} {v : Bool}, hide cc L6.H3 v = some true → v = true := by
    intro cc v h
    by_cases hb : L6.leB cc L6.H3 = true
    · rw [hide, if_pos hb] at h; injection h
    · rw [hide, if_neg hb] at h; exact absurd h (by simp)
  have := hval h3; subst this
  have := hval h5; subst this
  have := hval h6; subst this
  have := hval h8; subst this
  have := hval k1; subst this
  have := hval k2; subst this
  have := hval k3; subst this
  have := hval k4; subst this
  -- consistency with `ω₂`
  have hr1 : r = true := hc [] L6.H r _ rfl
  have hcb : c = b := by
    have hh := hc [Lbl.inp L6.H r, Lbl.out L6.H1 a, Lbl.out L6.L1 true,
      Lbl.out L6.H2 b, Lbl.out L6.L2 true, Lbl.inp L6.L2 true] L6.H2 c
      [Lbl.inp L6.L1 true, Lbl.inp L6.H1 d, Lbl.out L6.H3 true, Lbl.out L6.H3 true,
       Lbl.out L6.H3 true, Lbl.out L6.H3 true] rfl
    have hh2 : omegaSet L6.H2 [Lbl.inp L6.H r, Lbl.out L6.H1 a, Lbl.out L6.L1 true,
      Lbl.out L6.H2 b, Lbl.out L6.L2 true, Lbl.inp L6.L2 true] c := hh
    rcases hh2 with hm | ⟨hn, -⟩
    · simpa using hm
    · exact absurd (by simp : Lbl.out L6.H2 b ∈ [Lbl.inp L6.H r, Lbl.out L6.H1 a,
        Lbl.out L6.L1 true, Lbl.out L6.H2 b, Lbl.out L6.L2 true, Lbl.inp L6.L2 true])
        (hn b)
  have hda : d = a := by
    have hh := hc [Lbl.inp L6.H r, Lbl.out L6.H1 a, Lbl.out L6.L1 true,
      Lbl.out L6.H2 b, Lbl.out L6.L2 true, Lbl.inp L6.L2 true, Lbl.inp L6.H2 c,
      Lbl.inp L6.L1 true] L6.H1 d
      [Lbl.out L6.H3 true, Lbl.out L6.H3 true, Lbl.out L6.H3 true, Lbl.out L6.H3 true] rfl
    have hh2 : omegaSet L6.H1 [Lbl.inp L6.H r, Lbl.out L6.H1 a, Lbl.out L6.L1 true,
      Lbl.out L6.H2 b, Lbl.out L6.L2 true, Lbl.inp L6.L2 true, Lbl.inp L6.H2 c,
      Lbl.inp L6.L1 true] d := hh
    rcases hh2 with hm | ⟨hn, -⟩
    · simpa using hm
    · exact absurd (by simp : Lbl.out L6.H1 a ∈ [Lbl.inp L6.H r, Lbl.out L6.H1 a,
        Lbl.out L6.L1 true, Lbl.out L6.H2 b, Lbl.out L6.L2 true, Lbl.inp L6.L2 true,
        Lbl.inp L6.H2 c, Lbl.inp L6.L1 true]) (hn a)
  -- decompose
  obtain ⟨tA, tB, hRA, hRB, hI⟩ := par_decompose hr
  have hlenI := hI.length
  have hlA : tA.length ≤ 7 := specA0_len (reachA_spec hRA)
  have hlB : tB.length ≤ 6 := specB0_len (reachB_spec hRB)
  have hlA7 : tA.length = 7 := by simp at hlenI; omega
  have hlB6 : tB.length = 6 := by simp at hlenI; omega
  obtain ⟨rA, xA, zA, yA, rfl⟩ := specA0_full (reachA_spec hRA) hlA7
  obtain ⟨xB, zB, yB, rfl⟩ := specB0_full (reachB_spec hRB) hlB6
  have m1 := hI.mem_left (List.mem_cons_self ..)
  have m2 := hI.mem_left (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have m5 := hI.mem_left (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  have m7 := hI.mem_left (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))
  have n1 := hI.mem_right (List.mem_cons_self ..)
  have n4 := hI.mem_right (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  have n6 := hI.mem_right (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))))
  simp only [List.mem_cons, List.not_mem_nil, or_false, Lbl.inp.injEq, Lbl.out.injEq,
    reduceCtorEq, false_or, or_false, false_and, or_self] at m1 m2 m5 m7 n1 n4 n6
  subst hr1
  have hA3 : Bool.xor rA (Bool.xor xA yA) = true := m7.2
  have hB3 : Bool.xor xB yB = true := n6.2
  have hxA : (!xA) = a := m2.2
  have hyA : yA = c := m5.2
  have hxB : (!xB) = b := n1.2
  have hyB : yB = d := n4.2
  have hrA : rA = true := m1.2
  subst hcb; subst hda
  rw [← hxA] at hyB
  rw [← hxB] at hyA
  subst hyA; subst hyB; subst hrA
  cases xA <;> cases xB <;> simp at hA3 hB3

theorem par_not_TNI : ¬ Sc.StratTNI (parStep stepA stepB) (AState.a0, BState.b0) := by
  intro hNI
  obtain ⟨t₂, hprod, hteq⟩ :=
    hNI L6.H3 (cexOmega false) (cexOmega true) (cexOmega_total false) (cexOmega_total true)
      cexOmega_seq tcex tcex_produces
  exact no_match t₂ hprod hteq


end Cex2

/-- **Theorem 13** (Non-compositionality for total strategies).  There are
    `sA, sB ∈ Strat_T-NI` whose composition is not in `Strat_T-NI`. -/
theorem noncompositional_total :
    ∃ (Level Channel Value : Type) (S : Sec Level Channel) (St₁ St₂ : Type)
      (step₁ : St₁ → Act Channel Value → St₁ → Prop)
      (step₂ : St₂ → Act Channel Value → St₂ → Prop) (sA : St₁) (sB : St₂),
      S.IsJoinSemilattice ∧ InputNeutral step₁ ∧ InputNeutral step₂ ∧
      S.StratTNI step₁ sA ∧ S.StratTNI step₂ sB ∧
      ¬ S.StratTNI (parStep step₁ step₂) (sA, sB) :=
  ⟨Cex2.L6, Cex2.L6, Bool, Cex2.Sc, Cex2.AState, Cex2.BState, Cex2.stepA, Cex2.stepB,
   .a0, .b0,
   ⟨Cex2.L6.join, fun a b =>
     ⟨Cex2.L6.join_le_left a b, Cex2.L6.join_le_right a b, Cex2.L6.join_least a b⟩⟩,
   Cex2.stepA_neutral, Cex2.stepB_neutral,
   Cex2.A_TNI, Cex2.B_TNI, Cex2.par_not_TNI⟩

namespace Cex2

end Cex2
end InteractiveNI
