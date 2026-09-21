/-
  **One program that does not compose with itself.**

  Section 5.2 uses two components on two channels.  Neither is essential: let the
  program pick, internally, the value it will emit, and one channel suffices.  A
  single program `R` is then coalition noninterfering while `R ∥ R` is not --- the
  observer at `Ob` sees the values, so the alternating observation forces the two
  copies to have chosen differently, and the timing argument applies unchanged.
-/
import InteractiveNI.CexPresence

namespace InteractiveNI

namespace CexSelf

open Classical
open CexPresence

/-! ### The program -/

inductive RSt where
  | s0
  | c0 (v : Bool)
  | f1 (v : Bool) | f2 (v : Bool) | f3 (v : Bool)
  | t1 (v : Bool) | t2 (v : Bool) | t3 (v : Bool)
  | fin
deriving DecidableEq

/-- `R`: choose a value, then emit it three times on `p`, reading once on `a` --
    at the start if given `true`, after two messages if given `false`. -/
inductive rprog : RSt → Act Chan Bool → RSt → Prop where
  | pick (v)   : rprog .s0 .tau (.c0 v)
  | o1 (v)     : rprog (.c0 v) (.out Chan.p v) (.f1 v)
  | o2 (v)     : rprog (.f1 v) (.out Chan.p v) (.f2 v)
  | rf (v)     : rprog (.f2 v) (.inp Chan.a false) (.f3 v)
  | o3 (v)     : rprog (.f3 v) (.out Chan.p v) .fin
  | rt (v)     : rprog (.c0 v) (.inp Chan.a true) (.t1 v)
  | u1 (v)     : rprog (.t1 v) (.out Chan.p v) (.t2 v)
  | u2 (v)     : rprog (.t2 v) (.out Chan.p v) (.t3 v)
  | u3 (v)     : rprog (.t3 v) (.out Chan.p v) .fin

/-- The label emitted, as a function of the chosen value. -/
def E (v : Bool) : Lbl Chan Bool := Lbl.out Chan.p v

def tracesFrom : RSt → List (Lbl Chan Bool) → Prop
  | .s0 => fun t => ∃ v, t = [] ∨ t = [E v] ∨ t = [E v, E v] ∨ t = [E v, E v, RF] ∨
      t = [E v, E v, RF, E v] ∨ t = [RT] ∨ t = [RT, E v] ∨ t = [RT, E v, E v] ∨
      t = [RT, E v, E v, E v]
  | .c0 v => fun t => t = [] ∨ t = [E v] ∨ t = [E v, E v] ∨ t = [E v, E v, RF] ∨
      t = [E v, E v, RF, E v] ∨ t = [RT] ∨ t = [RT, E v] ∨ t = [RT, E v, E v] ∨
      t = [RT, E v, E v, E v]
  | .f1 v => fun t => t = [] ∨ t = [E v] ∨ t = [E v, RF] ∨ t = [E v, RF, E v]
  | .f2 v => fun t => t = [] ∨ t = [RF] ∨ t = [RF, E v]
  | .f3 v => fun t => t = [] ∨ t = [E v]
  | .t1 v => fun t => t = [] ∨ t = [E v] ∨ t = [E v, E v] ∨ t = [E v, E v, E v]
  | .t2 v => fun t => t = [] ∨ t = [E v] ∨ t = [E v, E v]
  | .t3 v => fun t => t = [] ∨ t = [E v]
  | .fin => fun t => t = []

theorem reach_traces {s s' : RSt} {t : List (Lbl Chan Bool)}
    (h : Reach rprog s t s') : tracesFrom s t := by
  induction h with
  | @nil s => cases s <;> simp [tracesFrom]
  | @tau s s' s'' u hs _ ih =>
      cases hs with
      | pick v => exact ⟨v, ih⟩
  | @inp s s' s'' ch v u hs _ ih =>
      cases hs <;> simp only [tracesFrom] at ih ⊢ <;>
        first
          | (rcases ih with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
          | (rcases ih with rfl|rfl|rfl|rfl)
          | (rcases ih with rfl|rfl|rfl)
          | (rcases ih with rfl|rfl)
          | (rcases ih with rfl)
      all_goals simp [E, RF, RT]
  | @out s s' s'' ch v u hs _ ih =>
      cases hs <;> simp only [tracesFrom] at ih ⊢ <;>
        first
          | (rcases ih with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
          | (rcases ih with rfl|rfl|rfl|rfl)
          | (rcases ih with rfl|rfl|rfl)
          | (rcases ih with rfl|rfl)
          | (rcases ih with rfl)
      all_goals simp [E, RF, RT]

/-! ### Projections -/

theorem projLbl_E {C : Sec.Coalition Lv} (hOb : Sc.coalition.le (Sec.sing Lv.Ob) C) (v : Bool) :
    Sc.coalition.projLbl C (E v) = some (PLbl.out Chan.p (some v)) :=
  Sec.projLbl_out_full hOb hOb

theorem projLbl_E_hidden {C : Sec.Coalition Lv}
    (hOb : ¬ Sc.coalition.le (Sec.sing Lv.Ob) C) (v : Bool) :
    Sc.coalition.projLbl C (E v) = none := Sec.projLbl_out_hidden hOb

theorem projLbl_E_Hi (v : Bool) :
    Sc.coalition.projLbl (Sec.sing (Sc.valL Chan.a)) (E v) = none :=
  Sec.projLbl_out_hidden ob_not_hi

/-! ### Runs -/

theorem reach_o1 (v : Bool) : Reach rprog RSt.s0 [E v] (RSt.f1 v) :=
  Reach.tau (rprog.pick v) (Reach.out (rprog.o1 v) Reach.nil)

theorem reach_o2 (v : Bool) : Reach rprog RSt.s0 [E v, E v] (RSt.f2 v) :=
  Reach.tau (rprog.pick v) (Reach.out (rprog.o1 v) (Reach.out (rprog.o2 v) Reach.nil))

theorem reach_f (v : Bool) : Reach rprog RSt.s0 [E v, E v, RF, E v] RSt.fin :=
  Reach.tau (rprog.pick v) (Reach.out (rprog.o1 v) (Reach.out (rprog.o2 v)
    (Reach.inp (rprog.rf v) (Reach.out (rprog.o3 v) Reach.nil))))

theorem reach_t (v : Bool) : Reach rprog RSt.s0 [RT, E v, E v, E v] RSt.fin :=
  Reach.tau (rprog.pick v) (Reach.inp (rprog.rt v) (Reach.out (rprog.u1 v)
    (Reach.out (rprog.u2 v) (Reach.out (rprog.u3 v) Reach.nil))))

theorem mem_inp {s' : RSt} {t : List (Lbl Chan Bool)} (h : Reach rprog RSt.s0 t s')
    {ch : Chan} {v : Bool} (hm : Lbl.inp ch v ∈ t) : ch = Chan.a := by
  have ht := reach_traces h
  simp only [tracesFrom] at ht
  obtain ⟨u, ht⟩ := ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all [E, RF, RT]

theorem cons_f {v : Bool} {w : Sc.coalition.Strategy Bool}
    (h : w.ω Chan.a [E v, E v] false) : Sc.coalition.consistent w [E v, E v, RF, E v] := by
  intro u ch x r hsplit
  match u with
  | [] => simp [RF, E] at hsplit
  | [y] => simp [RF, E] at hsplit
  | [y, z] =>
      simp only [E, RF, List.cons_append, List.nil_append, List.cons.injEq] at hsplit
      obtain ⟨rfl, rfl, ⟨rfl, rfl⟩, rfl⟩ := hsplit
      exact h
  | [y, z, q] => simp [RF, E] at hsplit
  | y :: z :: q :: m :: u => simp [RF, E] at hsplit

theorem cons_t {v : Bool} {w : Sc.coalition.Strategy Bool}
    (h : w.ω Chan.a [] true) : Sc.coalition.consistent w [RT, E v, E v, E v] := by
  intro u ch x r hsplit
  match u with
  | [] =>
      simp only [E, RT, List.nil_append, List.cons.injEq] at hsplit
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hsplit
      exact h
  | [y] => simp [RT, E] at hsplit
  | [y, z] => simp [RT, E] at hsplit
  | [y, z, q] => simp [RT, E] at hsplit
  | y :: z :: q :: m :: u => simp [RT, E] at hsplit

theorem cons_out {w : Sc.coalition.Strategy Bool} :
    ∀ t : List (Lbl Chan Bool), (∀ x ∈ t, ∃ (d : Chan) (u : Bool), x = Lbl.out d u) →
      Sc.coalition.consistent w t := by
  intro t ht u ch x r hsplit
  have : Lbl.inp ch x ∈ t := by rw [hsplit]; simp
  obtain ⟨d, u, hd⟩ := ht _ this
  exact absurd hd (by simp)

/-- Whatever it is offered, the program can emit its three messages. -/
theorem produces_three (v : Bool) {w : Sc.coalition.Strategy Bool} (htot : w.total) :
    ∃ t, Sc.coalition.produces rprog w RSt.s0 t ∧
      Sc.coalition.proj (Sec.sing Lv.Ob) t
        = [PLbl.out Chan.p (some v), PLbl.out Chan.p (some v), PLbl.out Chan.p (some v)] := by
  have hE := projLbl_E (C := Sec.sing Lv.Ob) ob_vis_ob
  have hRF : Sc.coalition.projLbl (Sec.sing Lv.Ob) RF = none := projLbl_R hi_not_ob
  have hRT : Sc.coalition.projLbl (Sec.sing Lv.Ob) RT = none := projLbl_R hi_not_ob
  obtain ⟨x, hx⟩ := htot Chan.a []
  cases x with
  | true =>
      exact ⟨[RT, E v, E v, E v], ⟨⟨RSt.fin, reach_t v⟩, cons_t hx⟩, by
        simp [Sec.proj, hE, hRT]⟩
  | false =>
      have hteq : Sc.coalition.teq (Sc.coalition.valL Chan.a) ([] : List (Lbl Chan Bool))
          [E v, E v] := by
        show Sc.coalition.proj _ _ = Sc.coalition.proj _ _
        simp [Sec.proj, projLbl_E_Hi]
      have hval : w.ω Chan.a [E v, E v] false := by
        rw [← w.resp_val Chan.a [] [E v, E v] hteq]; exact hx
      exact ⟨[E v, E v, RF, E v], ⟨⟨RSt.fin, reach_f v⟩, cons_f hval⟩, by
        simp [Sec.proj, hE, hRF]⟩

/-! ### The program is coalition noninterfering -/

theorem rprog_NI : Sc.coalition.StratTNI rprog RSt.s0 := by
  intro C w₁ w₂ _ htot₂ hseq t₁ h₁
  obtain ⟨⟨s', hreach⟩, hcons⟩ := h₁
  by_cases hHi : Sc.coalition.le (Sec.sing Lv.Hi) C
  · refine ⟨t₁, ⟨⟨s', hreach⟩, ?_⟩, rfl⟩
    intro u ch x r hsplit
    have hch : ch = Chan.a := mem_inp (v := x) hreach (by rw [hsplit]; simp)
    subst hch
    rw [← (hseq Chan.a u).1 hHi]
    exact hcons u Chan.a x r hsplit
  · have hRF : Sc.coalition.projLbl C RF = none := projLbl_R hHi
    have hRT : Sc.coalition.projLbl C RT = none := projLbl_R hHi
    have ht := reach_traces hreach
    simp only [tracesFrom] at ht
    obtain ⟨v, ht⟩ := ht
    have p0 : Sc.coalition.produces rprog w₂ RSt.s0 [] :=
      ⟨⟨RSt.s0, Reach.nil⟩, by intro u ch x r h; cases u <;> simp at h⟩
    have p1 : Sc.coalition.produces rprog w₂ RSt.s0 [E v] :=
      ⟨⟨RSt.f1 v, reach_o1 v⟩, cons_out _ (by intro x hx; simp at hx; exact ⟨Chan.p, v, hx⟩)⟩
    have p2 : Sc.coalition.produces rprog w₂ RSt.s0 [E v, E v] :=
      ⟨⟨RSt.f2 v, reach_o2 v⟩, cons_out _ (by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> exact ⟨Chan.p, v, rfl⟩)⟩
    by_cases hOb : Sc.coalition.le (Sec.sing Lv.Ob) C
    · have hE := projLbl_E (C := C) hOb
      obtain ⟨t₃, hp3, hq3⟩ := produces_three v htot₂
      have hvis : Sc.coalition.proj C t₃
          = [PLbl.out Chan.p (some v), PLbl.out Chan.p (some v),
             PLbl.out Chan.p (some v)] := by
        obtain ⟨⟨s₃, hr₃⟩, -⟩ := hp3
        have h3 := reach_traces hr₃
        simp only [tracesFrom] at h3
        obtain ⟨u, h3⟩ := h3
        have hE0 := projLbl_E (C := Sec.sing Lv.Ob) ob_vis_ob
        have hRF0 : Sc.coalition.projLbl (Sec.sing Lv.Ob) RF = none := projLbl_R hi_not_ob
        have hRT0 : Sc.coalition.projLbl (Sec.sing Lv.Ob) RT = none := projLbl_R hi_not_ob
        rcases h3 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          simp [Sec.proj, hE0, hRF0, hRT0] at hq3 <;>
          simp [Sec.proj, hE, hRF, hRT, hq3]
      simp only [Sec.proj] at hvis
      rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨[], p0, rfl⟩
      · exact ⟨[E v], p1, rfl⟩
      · exact ⟨[E v, E v], p2, rfl⟩
      · exact ⟨[E v, E v], p2, by simp [Sec.teq, Sec.proj, hE, hRF]⟩
      · exact ⟨t₃, hp3, by simp [Sec.teq, Sec.proj, hE, hRF, hvis]⟩
      · exact ⟨[], p0, by simp [Sec.teq, Sec.proj, hRT]⟩
      · exact ⟨[E v], p1, by simp [Sec.teq, Sec.proj, hE, hRT]⟩
      · exact ⟨[E v, E v], p2, by simp [Sec.teq, Sec.proj, hE, hRT]⟩
      · exact ⟨t₃, hp3, by simp [Sec.teq, Sec.proj, hE, hRT, hvis]⟩
    · have hE : Sc.coalition.projLbl C (E v) = none := projLbl_E_hidden hOb v
      refine ⟨[], p0, ?_⟩
      show Sc.coalition.proj C t₁ = Sc.coalition.proj C []
      rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [Sec.proj, hE, hRF, hRT]

/-! ### The composition with itself -/

def Obs2 : List (PLbl Chan Bool) :=
  [PLbl.out Chan.p (some true), PLbl.out Chan.p (some false),
   PLbl.out Chan.p (some true), PLbl.out Chan.p (some false),
   PLbl.out Chan.p (some true), PLbl.out Chan.p (some false)]

def wit2 : List (Lbl Chan Bool) :=
  [E true, E false, E true, E false, RF, E true, RF, E false]

theorem wit2_interleave :
    Interleave [E true, E true, RF, E true] [E false, E false, RF, E false] wit2 :=
  Interleave.left (Interleave.right (Interleave.left (Interleave.right
    (Interleave.left (Interleave.left (Interleave.right (Interleave.right
      Interleave.nil)))))))

theorem wit2_produces : Sc.coalition.produces (parStep rprog rprog) W1
    (RSt.s0, RSt.s0) wit2 := by
  refine ⟨⟨(RSt.fin, RSt.fin),
    par_reach_interleave wit2_interleave (reach_f true) (reach_f false)⟩, ?_⟩
  intro u ch x r hsplit
  have hx : ch = Chan.a ∧ x = false := by
    match u with
    | [] => simp [wit2, E, RF] at hsplit
    | [y] => simp [wit2, E, RF] at hsplit
    | [y, z] => simp [wit2, E, RF] at hsplit
    | [y, z, q] => simp [wit2, E, RF] at hsplit
    | [y, z, q, m] =>
        simp only [wit2, E, RF, List.cons_append, List.nil_append, List.cons.injEq] at hsplit
        obtain ⟨-, -, -, -, ⟨rfl, rfl⟩, -⟩ := hsplit
        exact ⟨rfl, rfl⟩
    | [y, z, q, m, k] => simp [wit2, E, RF] at hsplit
    | [y, z, q, m, k, i] =>
        simp only [wit2, E, RF, List.cons_append, List.nil_append, List.cons.injEq] at hsplit
        obtain ⟨-, -, -, -, -, -, ⟨rfl, rfl⟩, -⟩ := hsplit
        exact ⟨rfl, rfl⟩
    | [y, z, q, m, k, i, j] => simp [wit2, E, RF] at hsplit
    | y :: z :: q :: m :: k :: i :: j :: n :: u => simp [wit2, E, RF] at hsplit
  obtain ⟨rfl, rfl⟩ := hx
  rfl

theorem wit2_obs : Sc.coalition.proj (Sec.sing Lv.Ob) wit2 = Obs2 := by
  have hE := projLbl_E (C := Sec.sing Lv.Ob) ob_vis_ob
  have hRF : Sc.coalition.projLbl (Sec.sing Lv.Ob) RF = none := projLbl_R hi_not_ob
  simp [Sec.proj, wit2, Obs2, hE, hRF]

theorem le_three {s' : RSt} {t : List (Lbl Chan Bool)} (h : Reach rprog RSt.s0 t s') :
    (Sc.coalition.proj (Sec.sing Lv.Ob) t).length ≤ 3 := by
  have hE := projLbl_E (C := Sec.sing Lv.Ob) ob_vis_ob
  have hRF : Sc.coalition.projLbl (Sec.sing Lv.Ob) RF = none := projLbl_R hi_not_ob
  have hRT : Sc.coalition.projLbl (Sec.sing Lv.Ob) RT = none := projLbl_R hi_not_ob
  have ht := reach_traces h
  simp only [tracesFrom] at ht
  obtain ⟨v, ht⟩ := ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [Sec.proj, hE, hRF, hRT]

theorem three_out {s' : RSt} {t : List (Lbl Chan Bool)} (h : Reach rprog RSt.s0 t s')
    (hlen : (Sc.coalition.proj (Sec.sing Lv.Ob) t).length = 3) :
    ∃ v : Bool, t = [E v, E v, RF, E v] ∨ t = [RT, E v, E v, E v] := by
  have hE := projLbl_E (C := Sec.sing Lv.Ob) ob_vis_ob
  have hRF : Sc.coalition.projLbl (Sec.sing Lv.Ob) RF = none := projLbl_R hi_not_ob
  have hRT : Sc.coalition.projLbl (Sec.sing Lv.Ob) RT = none := projLbl_R hi_not_ob
  have ht := reach_traces h
  simp only [tracesFrom] at ht
  obtain ⟨v, ht⟩ := ht
  refine ⟨v, ?_⟩
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [Sec.proj, hE, hRF, hRT] at hlen ⊢

theorem proj_two (v : Bool) (t : List (Lbl Chan Bool)) :
    Sc.coalition.proj (Sec.sing Lv.Ob) (E v :: E v :: t)
      = PLbl.out Chan.p (some v) :: PLbl.out Chan.p (some v)
        :: Sc.coalition.proj (Sec.sing Lv.Ob) t := by
  simp [Sec.proj, projLbl_E (C := Sec.sing Lv.Ob) ob_vis_ob]

theorem projLbl_E_Hi' (v : Bool) :
    Sc.coalition.projLbl (Sec.sing Lv.Hi) (E v) = none :=
  Sec.projLbl_out_hidden ob_not_hi

theorem projLbl_RF_Hi' :
    Sc.coalition.projLbl (Sec.sing Lv.Hi) RF = some (PLbl.inp Chan.a (some false)) :=
  Sec.projLbl_inp_full (Sc.coalition.le_refl _) (Sc.coalition.le_refl _)

theorem no_match2 : ¬ ∃ t₂, Sc.coalition.produces (parStep rprog rprog) W2
    (RSt.s0, RSt.s0) t₂ ∧ Sc.coalition.proj (Sec.sing Lv.Ob) t₂ = Obs2 := by
  rintro ⟨t₂, ⟨⟨⟨sA, sB⟩, hreach⟩, hcons⟩, hobs⟩
  obtain ⟨tA, tB, hA, hB, hI⟩ := par_decompose hreach
  have hE := projLbl_E (C := Sec.sing Lv.Ob) ob_vis_ob
  have hRF0 : Sc.coalition.projLbl (Sec.sing Lv.Ob) RF = none := projLbl_R hi_not_ob
  have hRT0 : Sc.coalition.projLbl (Sec.sing Lv.Ob) RT = none := projLbl_R hi_not_ob
  have hIp : Interleave (Sc.coalition.proj (Sec.sing Lv.Ob) tA)
      (Sc.coalition.proj (Sec.sing Lv.Ob) tB)
      (Sc.coalition.proj (Sec.sing Lv.Ob) t₂) := Interleave.filterMap _ hI
  have hlen := hIp.length
  rw [hobs] at hlen
  have hA3 : (Sc.coalition.proj (Sec.sing Lv.Ob) tA).length ≤ 3 := le_three hA
  have hB3 : (Sc.coalition.proj (Sec.sing Lv.Ob) tB).length ≤ 3 := le_three hB
  have hObs6 : Obs2.length = 6 := by simp [Obs2]
  rw [hObs6] at hlen
  obtain ⟨vA, hA'⟩ := three_out hA (by omega)
  obtain ⟨vB, hB'⟩ := three_out hB (by omega)
  rcases hA' with rfl | rfl <;> rcases hB' with rfl | rfl
  · -- both read late
    obtain ⟨pre, post, hsplit, hmem⟩ :=
      interleave_both (x := RF) hI (by simp) (by simp)
    have hc2 := hcons pre Chan.a false post hsplit
    have hne : Sc.coalition.proj (Sec.sing Lv.Hi) pre ≠ [] :=
      proj_ne_nil hmem projLbl_RF_Hi'
    simp [W2, hasA, hne] at hc2
  · -- `A` late, `B` early: `A` emits twice before anything of `B`
    obtain ⟨u₁, u₂, w₂, hsplitA, hsplit2, -⟩ := interleave_split_right hI
    have hc2 := hcons u₁ Chan.a true w₂ hsplit2
    have hne : Sc.coalition.proj (Sec.sing Lv.Hi) u₁ ≠ [] := by
      intro hnil; simp [W2, hasA, hnil] at hc2
    rcases u₁ with _|⟨x,_|⟨y,_|⟨z,rest⟩⟩⟩
    · exact hne rfl
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsplitA
      obtain ⟨rfl, -⟩ := hsplitA
      exact hne (by simp [Sec.proj, projLbl_E_Hi'])
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsplitA
      obtain ⟨rfl, rfl, -⟩ := hsplitA
      exact hne (by simp [Sec.proj, projLbl_E_Hi'])
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsplitA
      obtain ⟨rfl, rfl, -⟩ := hsplitA
      rw [hsplit2] at hobs
      simp only [List.cons_append] at hobs
      rw [proj_two] at hobs
      simp only [Obs2, List.cons.injEq, PLbl.out.injEq, Option.some.injEq] at hobs
      obtain ⟨⟨-, h1⟩, ⟨-, h2⟩, -⟩ := hobs
      rw [h1] at h2
      exact Bool.noConfusion h2
  · -- `A` early, `B` late
    obtain ⟨v₁, v₂, w₂, hsplitB, hsplit2, -⟩ := interleave_split_left hI
    have hc2 := hcons v₁ Chan.a true w₂ hsplit2
    have hne : Sc.coalition.proj (Sec.sing Lv.Hi) v₁ ≠ [] := by
      intro hnil; simp [W2, hasA, hnil] at hc2
    rcases v₁ with _|⟨x,_|⟨y,_|⟨z,rest⟩⟩⟩
    · exact hne rfl
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsplitB
      obtain ⟨rfl, -⟩ := hsplitB
      exact hne (by simp [Sec.proj, projLbl_E_Hi'])
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsplitB
      obtain ⟨rfl, rfl, -⟩ := hsplitB
      exact hne (by simp [Sec.proj, projLbl_E_Hi'])
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsplitB
      obtain ⟨rfl, rfl, -⟩ := hsplitB
      rw [hsplit2] at hobs
      simp only [List.cons_append] at hobs
      rw [proj_two] at hobs
      simp only [Obs2, List.cons.injEq, PLbl.out.injEq, Option.some.injEq] at hobs
      obtain ⟨⟨-, h1⟩, ⟨-, h2⟩, -⟩ := hobs
      rw [h1] at h2
      exact Bool.noConfusion h2
  · -- both read early
    have hhead : ∃ rest, t₂ = RT :: rest := by
      cases hI with
      | left h => exact ⟨_, rfl⟩
      | right h => exact ⟨_, rfl⟩
    obtain ⟨rest, rfl⟩ := hhead
    have hc2 := hcons [] Chan.a true rest rfl
    simp [W2, hasA, Sec.proj] at hc2

/-- **One program that does not compose with itself.** -/
theorem rprog_par_not_NI :
    ¬ Sc.coalition.StratTNI (parStep rprog rprog) (RSt.s0, RSt.s0) := by
  intro h
  obtain ⟨t₂, hp, hteq⟩ :=
    h (Sec.sing Lv.Ob) W1 W2 W1_total W2_total W1_seq_W2 wit2 wit2_produces
  exact no_match2 ⟨t₂, hp, by rw [← hteq]; exact wit2_obs⟩

theorem self_composition_fails :
    Sc.coalition.StratTNI rprog RSt.s0 ∧
      ¬ Sc.coalition.StratTNI (parStep rprog rprog) (RSt.s0, RSt.s0) :=
  ⟨rprog_NI, rprog_par_not_NI⟩

end CexSelf

end InteractiveNI
