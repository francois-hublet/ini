/-
  Interleaving patterns, and the `Insertion` they induce.

  A composed run is an interleaving of the two components' runs.  To apply INI to
  one component inside a composed context we must turn the global strategy into a
  strategy for that component, by reinserting the partner's labels.  `weave`
  records the interleaving pattern explicitly, and `weaveIns` packages the
  reinsertion as an `Insertion` (`Freeze.lean`).

  Everything here assumes *public presence*: `presL a ⊑ c` for every channel and
  every level, i.e. the mere occurrence of a communication is never secret (only
  its value is).  Both counterexamples of the paper satisfy this.  Under it every
  projection keeps every label, so `π_ℓ` is a `map` and commutes with `weave`.
-/
import InteractiveNI.Interp
import InteractiveNI.Compose

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

/-! ### Weaving two lists along a pattern -/

/-- `weave p u v` interleaves `u` and `v` following the pattern `p`
    (`true` = take from `u`, `false` = take from `v`), stopping as soon as the
    pattern calls for a label that is not there.  Truncation is what makes
    `weave p u' v` the *actual* global prefix corresponding to a prefix `u'` of
    the component trace `u`: it stops exactly where the next component label
    would go, after any partner labels interleaved before it. -/
def weave {α : Type} : List Bool → List α → List α → List α
  | [], _, _ => []
  | true :: p,  x :: u, v => x :: weave p u v
  | false :: p, u, y :: v => y :: weave p u v
  | true :: _,  [], _ => []
  | false :: _, _, [] => []

theorem map_weave {α β : Type} (f : α → β) (p : List Bool) :
    ∀ (u v : List α), (weave p u v).map f = weave p (u.map f) (v.map f) := by
  induction p with
  | nil => intro u v; rfl
  | cons b p ih =>
      intro u v
      cases b with
      | true =>
          cases u with
          | nil => simp only [weave, List.map_nil]
          | cons x u => simp only [weave, List.map_cons]; exact congrArg _ (ih u v)
      | false =>
          cases v with
          | nil => simp only [weave, List.map_nil]
          | cons y v => simp only [weave, List.map_cons]; exact congrArg _ (ih u v)

/-- The pattern consumes both lists exactly, never hitting a truncation clause. -/
def Exact {α : Type} : List Bool → List α → List α → Prop
  | [], u, v => u = [] ∧ v = []
  | true :: p,  _ :: u, v => Exact p u v
  | true :: _,  [], _ => False
  | false :: p, u, _ :: v => Exact p u v
  | false :: _, _, [] => False

namespace Sec

variable {Level Channel Value : Type} {S : Sec Level Channel}

/-! ### Public presence -/

/-- Presence is never secret: every label survives every projection. -/
def PublicPresence (S : Sec Level Channel) : Prop := ∀ a ℓ, S.le (S.presL a) ℓ

/-- The total version of `projLbl`, available under public presence. -/
noncomputable def projL (S : Sec Level Channel) (ℓ : Level) :
    Lbl Channel Value → PLbl Channel Value
  | .inp a v => if S.le (S.valL a) ℓ then .inp a (some v) else .inp a none
  | .out a v => if S.le (S.valL a) ℓ then .out a (some v) else .out a none

end Sec

/-! ### Composing component runs along an interleaving

    `Compose.par_decompose` splits a run of a composition into runs of the two
    components.  The converse direction -- assembling a composed run from two
    component runs and an interleaving -- is what a compositionality proof needs,
    and is supplied here. -/

namespace Reach

/-- A run producing a nonempty trace splits as: silent steps, the first visible
    step, then the rest. -/
theorem cons_inv {C V St : Type} {step : St → Act C V → St → Prop} {x y : St}
    {l : Lbl C V} {t : List (Lbl C V)} (h : Reach step x (l :: t) y) :
    ∃ x₁ x₂, Reach step x [] x₁ ∧ step x₁ l.act x₂ ∧ Reach step x₂ t y := by
  generalize hlt : l :: t = lt at h
  induction h generalizing l t with
  | nil => exact absurd hlt (by simp)
  | @tau s s' s'' u hs _ ih =>
      obtain ⟨x₁, x₂, h1, h2, h3⟩ := ih hlt
      exact ⟨x₁, x₂, Reach.tau hs h1, h2, h3⟩
  | @inp s s' s'' a v u hs hr _ =>
      cases hlt
      exact ⟨s, s', Reach.nil, hs, hr⟩
  | @out s s' s'' a v u hs hr _ =>
      cases hlt
      exact ⟨s, s', Reach.nil, hs, hr⟩

end Reach

/-- **Assembling a composed run.**  Two component runs and an interleaving of
    their traces yield a run of the parallel composition. -/
theorem par_reach_interleave {C V St₁ St₂ : Type}
    {step₁ : St₁ → Act C V → St₁ → Prop} {step₂ : St₂ → Act C V → St₂ → Prop}
    {x y : St₁} {z w : St₂} {a b t : List (Lbl C V)}
    (hI : Interleave a b t) (h₁ : Reach step₁ x a y) (h₂ : Reach step₂ z b w) :
    Reach (parStep step₁ step₂) (x, z) t (y, w) := by
  induction hI generalizing x z with
  | nil =>
      exact Reach.trans (par_reach_left h₁) (par_reach_right h₂)
  | @left l a b t _ ih =>
      obtain ⟨x₁, x₂, hs, hstep, hrest⟩ := Reach.cons_inv h₁
      refine Reach.trans (par_reach_left (step₂ := step₂) (z := z) hs) ?_
      have hpar : parStep step₁ step₂ (x₁, z) l.act (x₂, z) := Or.inl ⟨hstep, rfl⟩
      cases l with
      | inp c v => exact Reach.inp hpar (ih hrest h₂)
      | out c v => exact Reach.out hpar (ih hrest h₂)
  | @right l a b t _ ih =>
      obtain ⟨z₁, z₂, hs, hstep, hrest⟩ := Reach.cons_inv h₂
      refine Reach.trans (par_reach_right (step₁ := step₁) (x := x) hs) ?_
      have hpar : parStep step₁ step₂ (x, z₁) l.act (x, z₂) := Or.inr ⟨hstep, rfl⟩
      cases l with
      | inp c v => exact Reach.inp hpar (ih h₁ hrest)
      | out c v => exact Reach.out hpar (ih h₁ hrest)


namespace Sec

variable {Level Channel Value : Type} {S : Sec Level Channel}

end Sec

/-- An exact pattern really does describe an interleaving. -/
theorem Exact.interleave {α : Type} :
    ∀ (p : List Bool) (u v : List α), Exact p u v → Interleave u v (weave p u v)
  | [], u, v, hE => by rw [hE.1, hE.2]; exact Interleave.nil
  | true :: p, [], _, hE => absurd hE (by simp [Exact])
  | true :: p, x :: u, v, hE => by
      simp only [weave]; exact Interleave.left (Exact.interleave p u v hE)
  | false :: p, _, [], hE => absurd hE (by simp [Exact])
  | false :: p, u, y :: v, hE => by
      simp only [weave]; exact Interleave.right (Exact.interleave p u v hE)

end InteractiveNI
