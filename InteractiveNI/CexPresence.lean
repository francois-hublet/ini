/-
  **Coalition noninterference does not compose when presence is secret.**

  Two incomparable levels, `Ob` and `Hi`.  Channels `p` and `q` at `Ob`, and a
  channel `a` at `Hi` -- *presence included*, so the observer at `Ob` cannot even
  tell that `a` is used, and, crucially, the user of `a` cannot tell how many
  messages have been sent on `p` or `q`.

  The component `prog c` emits three messages on `c` and reads once on `a`; where
  it reads depends on the value it gets: `true` at the very start, or `false`
  after the first two messages.  It is coalition noninterfering because the user
  of `a` cannot distinguish the two points at which it may be asked -- both have
  the empty `Hi`-view -- so whatever that user offers, one of the two branches
  fits.

  Two copies of it, on `p` and on `q`, do not compose.  Against the strategy that
  answers `false` first and `true` afterwards, the component that reads first is
  forced into the late-read branch and the other into the early-read branch, and
  either way one side has to emit two messages before the other emits any.  The
  perfectly alternating observation is therefore out of reach -- while the
  strategy that always answers `false` produces it.
-/
import InteractiveNI.JointW

namespace InteractiveNI

namespace CexPresence

open Classical
attribute [local instance] Classical.propDecidable

/-! ### The security context -/

inductive Lv where | Ob | Hi | Top
deriving DecidableEq

inductive Chan where | p | q | a
deriving DecidableEq

/-- A join-semilattice: `Ob` and `Hi` are incomparable, both below `Top`.  The
    presence of `a` is secret at `Ob`. -/
def Sc : Sec Lv Chan where
  le := fun x y => x = y ∨ y = Lv.Top
  le_refl := fun _ => Or.inl rfl
  le_trans := by
    rintro x y z (rfl | rfl) (h | rfl)
    · exact Or.inl h
    · exact Or.inr rfl
    · exact Or.inr (by rcases h with h | h <;> simp_all)
    · exact Or.inr rfl
  presL := fun c => match c with | .p => Lv.Ob | .q => Lv.Ob | .a => Lv.Hi
  valL := fun c => match c with | .p => Lv.Ob | .q => Lv.Ob | .a => Lv.Hi
  pres_le_val := fun c => by cases c <;> exact Or.inl rfl

theorem not_pub : ¬ Sec.PublicPresence Sc := by
  intro h
  rcases h Chan.a Lv.Ob with h | h <;> exact Lv.noConfusion h

/-! ### The component -/

inductive St where
  | s0 | f1 | f2 | f3 | t1 | t2 | t3 | fin | dead
deriving DecidableEq

/-- `prog c`: three messages on `c` and one read on `a`, read early if the value
    is `true` and late if it is `false`. -/
inductive prog (c : Chan) : St → Act Chan Bool → St → Prop where
  | o1 : prog c .s0 (.out c true) .f1
  | o2 : prog c .f1 (.out c true) .f2
  | rf : prog c .f2 (.inp Chan.a false) .f3
  | o3 : prog c .f3 (.out c true) .fin
  | rt : prog c .s0 (.inp Chan.a true) .t1
  | u1 : prog c .t1 (.out c true) .t2
  | u2 : prog c .t2 (.out c true) .t3
  | u3 : prog c .t3 (.out c true) .fin
  | d0 : prog c .s0 (.inp Chan.a false) .dead
  | d2 : prog c .f2 (.inp Chan.a true) .dead

/-- The component is an IOLTS: every input is available for every value.  Reading
    the value the branch does not expect leads to `dead`, from which nothing is
    possible -- input-neutrality demands a transition, not a continuation. -/
theorem prog_neutral (c : Chan) : InputNeutral (prog c) := by
  rintro s s' a v h v'
  cases h <;> cases v' <;>
    first
      | exact ⟨_, prog.rt⟩
      | exact ⟨_, prog.rf⟩
      | exact ⟨_, prog.d0⟩
      | exact ⟨_, prog.d2⟩

/-! ### The traces of the component -/

def O (c : Chan) : Lbl Chan Bool := Lbl.out c true
def RF : Lbl Chan Bool := Lbl.inp Chan.a false
def RT : Lbl Chan Bool := Lbl.inp Chan.a true

/-- The traces available from each state. -/
def tracesFrom (c : Chan) : St → List (Lbl Chan Bool) → Prop
  | .s0 => fun t => t = [] ∨ t = [O c] ∨ t = [O c, O c] ∨ t = [O c, O c, RF] ∨
      t = [O c, O c, RF, O c] ∨ t = [RT] ∨ t = [RT, O c] ∨ t = [RT, O c, O c] ∨
      t = [RT, O c, O c, O c] ∨ t = [RF] ∨ t = [O c, O c, RT]
  | .f1 => fun t => t = [] ∨ t = [O c] ∨ t = [O c, RF] ∨ t = [O c, RF, O c] ∨ t = [O c, RT]
  | .f2 => fun t => t = [] ∨ t = [RF] ∨ t = [RF, O c] ∨ t = [RT]
  | .f3 => fun t => t = [] ∨ t = [O c]
  | .t1 => fun t => t = [] ∨ t = [O c] ∨ t = [O c, O c] ∨ t = [O c, O c, O c]
  | .t2 => fun t => t = [] ∨ t = [O c] ∨ t = [O c, O c]
  | .t3 => fun t => t = [] ∨ t = [O c]
  | .fin => fun t => t = []
  | .dead => fun t => t = []

theorem reach_traces {c : Chan} {s s' : St} {t : List (Lbl Chan Bool)}
    (h : Reach (prog c) s t s') : tracesFrom c s t := by
  induction h with
  | @nil s => cases s <;> simp [tracesFrom]
  | tau hs _ _ => cases hs
  | @inp s s' s'' ch v u hs _ ih =>
      cases hs <;> simp only [tracesFrom] at ih ⊢ <;>
        first
          | (rcases ih with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
          | (rcases ih with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
          | (rcases ih with rfl|rfl|rfl|rfl|rfl)
          | (rcases ih with rfl|rfl|rfl|rfl)
          | (rcases ih with rfl|rfl|rfl)
          | (rcases ih with rfl|rfl)
          | (rcases ih with rfl)
      all_goals simp [O, RF, RT]
  | @out s s' s'' ch v u hs _ ih =>
      cases hs <;> simp only [tracesFrom] at ih ⊢ <;>
        first
          | (rcases ih with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
          | (rcases ih with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
          | (rcases ih with rfl|rfl|rfl|rfl|rfl)
          | (rcases ih with rfl|rfl|rfl|rfl)
          | (rcases ih with rfl|rfl|rfl)
          | (rcases ih with rfl|rfl)
          | (rcases ih with rfl)
      all_goals simp [O, RF, RT]

/-! ### Visibility -/

/-- Membership gives visibility. -/
theorem vis_self {C : Sec.Coalition Lv} {x : Lv} (h : C x) :
    Sc.coalition.le (Sec.sing x) C :=
  fun c hc => ⟨x, h, Or.inl (by rw [show c = x from hc])⟩

theorem ob_vis_ob : Sc.coalition.le (Sec.sing Lv.Ob) (Sec.sing Lv.Ob) :=
  Sc.coalition.le_refl _

theorem hi_not_ob : ¬ Sc.coalition.le (Sec.sing Lv.Hi) (Sec.sing Lv.Ob) := by
  intro h
  obtain ⟨d, hd, hle⟩ := h Lv.Hi rfl
  rw [show d = Lv.Ob from hd] at hle
  rcases hle with h | h <;> exact Lv.noConfusion h

theorem ob_not_hi : ¬ Sc.coalition.le (Sec.sing Lv.Ob) (Sec.sing Lv.Hi) := by
  intro h
  obtain ⟨d, hd, hle⟩ := h Lv.Ob rfl
  rw [show d = Lv.Hi from hd] at hle
  rcases hle with h | h <;> exact Lv.noConfusion h

theorem projLbl_O {C : Sec.Coalition Lv} {c : Chan} (hc : c ≠ Chan.a)
    (hOb : Sc.coalition.le (Sec.sing Lv.Ob) C) :
    Sc.coalition.projLbl C (O c) = some (PLbl.out c (some true)) := by
  have hp : Sc.coalition.le (Sc.coalition.presL c) C := by
    cases c <;> first | exact absurd rfl hc | exact hOb
  have hv : Sc.coalition.le (Sc.coalition.valL c) C := by
    cases c <;> first | exact absurd rfl hc | exact hOb
  exact Sec.projLbl_out_full hp hv

theorem projLbl_R {C : Sec.Coalition Lv} {v : Bool}
    (hHi : ¬ Sc.coalition.le (Sec.sing Lv.Hi) C) :
    Sc.coalition.projLbl (Value := Bool) C (Lbl.inp Chan.a v) = none :=
  Sec.projLbl_inp_hidden hHi

theorem projLbl_O_hidden {C : Sec.Coalition Lv} {c : Chan} (hc : c ≠ Chan.a)
    (hOb : ¬ Sc.coalition.le (Sec.sing Lv.Ob) C) :
    Sc.coalition.projLbl C (O c) = none := by
  refine Sec.projLbl_out_hidden (fun h => hOb ?_)
  cases c
  · exact h
  · exact h
  · exact absurd rfl hc

/-! ### The component is coalition noninterfering -/

theorem reach_o1 {c : Chan} : Reach (prog c) St.s0 [O c] St.f1 :=
  Reach.out prog.o1 Reach.nil

theorem reach_o2 {c : Chan} : Reach (prog c) St.s0 [O c, O c] St.f2 :=
  Reach.out prog.o1 (Reach.out prog.o2 Reach.nil)

theorem reach_f {c : Chan} : Reach (prog c) St.s0 [O c, O c, RF, O c] St.fin :=
  Reach.out prog.o1 (Reach.out prog.o2 (Reach.inp prog.rf (Reach.out prog.o3 Reach.nil)))

theorem reach_t {c : Chan} : Reach (prog c) St.s0 [RT, O c, O c, O c] St.fin :=
  Reach.inp prog.rt (Reach.out prog.u1 (Reach.out prog.u2 (Reach.out prog.u3 Reach.nil)))

theorem cons_out {w : Sc.coalition.Strategy Bool} :
    ∀ t : List (Lbl Chan Bool), (∀ x ∈ t, ∃ d : Chan, x = Lbl.out d true) →
      Sc.coalition.consistent w t := by
  intro t ht u ch v r hsplit
  have : Lbl.inp ch v ∈ t := by rw [hsplit]; simp
  obtain ⟨d, hd⟩ := ht _ this
  exact absurd hd (by simp)

theorem mem_inp {c : Chan} {s' : St} {t : List (Lbl Chan Bool)}
    (h : Reach (prog c) St.s0 t s') {ch : Chan} {v : Bool}
    (hm : Lbl.inp ch v ∈ t) : ch = Chan.a := by
  have ht := reach_traces h
  simp only [tracesFrom] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all [O, RF, RT]

theorem cons_f {c : Chan} {w : Sc.coalition.Strategy Bool}
    (h : w.ω Chan.a [O c, O c] false) : Sc.coalition.consistent w [O c, O c, RF, O c] := by
  intro u ch v r hsplit
  match u with
  | [] => simp [RF, O] at hsplit
  | [x] => simp [RF, O] at hsplit
  | [x, y] =>
      simp only [O, RF, List.cons_append, List.nil_append, List.cons.injEq] at hsplit
      obtain ⟨rfl, rfl, ⟨rfl, rfl⟩, rfl⟩ := hsplit
      exact h
  | [x, y, z] => simp [RF, O] at hsplit
  | x :: y :: z :: q :: u => simp [RF, O] at hsplit

theorem cons_t {c : Chan} {w : Sc.coalition.Strategy Bool}
    (h : w.ω Chan.a [] true) : Sc.coalition.consistent w [RT, O c, O c, O c] := by
  intro u ch v r hsplit
  match u with
  | [] =>
      simp only [O, RT, List.nil_append, List.cons.injEq] at hsplit
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hsplit
      exact h
  | [x] => simp [RT, O] at hsplit
  | [x, y] => simp [RT, O] at hsplit
  | [x, y, z] => simp [RT, O] at hsplit
  | x :: y :: z :: q :: u => simp [RT, O] at hsplit

/-- The component can always reach its full observation, whatever it is
    offered: the two points at which it may read have the same `Hi`-view. -/
theorem produces_three {c : Chan} (hc : c ≠ Chan.a) {w : Sc.coalition.Strategy Bool}
    (htot : w.total) :
    ∃ t, Sc.coalition.produces (prog c) w St.s0 t ∧
      Sc.coalition.proj (Sec.sing Lv.Ob) t
        = [PLbl.out c (some true), PLbl.out c (some true), PLbl.out c (some true)] := by
  have hOb := ob_vis_ob
  have hHi := hi_not_ob
  have hO := projLbl_O (C := Sec.sing Lv.Ob) hc hOb
  have hRF := projLbl_R (C := Sec.sing Lv.Ob) (v := false) hHi
  have hRT := projLbl_R (C := Sec.sing Lv.Ob) (v := true) hHi
  obtain ⟨v, hv⟩ := htot Chan.a []
  cases v with
  | true =>
      exact ⟨[RT, O c, O c, O c], ⟨⟨St.fin, reach_t⟩, cons_t hv⟩, by
        simp [Sec.proj, O, RF, RT] at hO hRT ⊢
        simp [hO, hRT]⟩
  | false =>
      have hteq : Sc.coalition.teq (Sc.coalition.valL Chan.a) ([] : List (Lbl Chan Bool))
          [O c, O c] := by
        have hn : Sc.coalition.projLbl (Sec.sing (Sc.valL Chan.a)) (O c) = none := by
          refine Sec.projLbl_out_hidden (fun h => ?_)
          cases c
          · exact ob_not_hi h
          · exact ob_not_hi h
          · exact hc rfl
        show Sc.coalition.proj _ _ = Sc.coalition.proj _ _
        simp [Sec.proj, hn]
      have hval : w.ω Chan.a [O c, O c] false := by
        rw [← w.resp_val Chan.a [] [O c, O c] hteq]; exact hv
      exact ⟨[O c, O c, RF, O c], ⟨⟨St.fin, reach_f⟩, cons_f hval⟩, by
        simp [Sec.proj, O, RF, RT] at hO hRF ⊢
        simp [hO, hRF]⟩

/-- **The component is coalition noninterfering.**  The user of `a` cannot tell
    the two points at which it may be asked apart -- both have the empty
    `Hi`-view, since the presence of `p` and `q` is invisible there -- so whatever
    it offers, one of the two branches fits. -/
theorem prog_NI {c : Chan} (hc : c ≠ Chan.a) : Sc.coalition.StratTNI (prog c) St.s0 := by
  intro C w₁ w₂ _ htot₂ hseq t₁ h₁
  obtain ⟨⟨s', hreach⟩, hcons⟩ := h₁
  by_cases hHi : Sc.coalition.le (Sec.sing Lv.Hi) C
  · -- the coalition sees `a`: the two strategies agree there, so the run stands
    refine ⟨t₁, ⟨⟨s', hreach⟩, ?_⟩, rfl⟩
    intro u ch v r hsplit
    have hch : ch = Chan.a := mem_inp (v := v) hreach (by rw [hsplit]; simp)
    subst hch
    rw [← (hseq Chan.a u).1 hHi]
    exact hcons u Chan.a v r hsplit
  · have hRF : Sc.coalition.projLbl C RF = none := projLbl_R hHi
    have hRT : Sc.coalition.projLbl C RT = none := projLbl_R hHi
    have ht := reach_traces hreach
    simp only [tracesFrom] at ht
    have p0 : Sc.coalition.produces (prog c) w₂ St.s0 [] :=
      ⟨⟨St.s0, Reach.nil⟩, by intro u ch v r h; cases u <;> simp at h⟩
    have p1 : Sc.coalition.produces (prog c) w₂ St.s0 [O c] :=
      ⟨⟨St.f1, reach_o1⟩, cons_out _ (by intro x hx; simp at hx; exact ⟨c, hx⟩)⟩
    have p2 : Sc.coalition.produces (prog c) w₂ St.s0 [O c, O c] :=
      ⟨⟨St.f2, reach_o2⟩, cons_out _ (by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> exact ⟨c, rfl⟩)⟩
    by_cases hOb : Sc.coalition.le (Sec.sing Lv.Ob) C
    · have hO : Sc.coalition.projLbl C (O c) = some (PLbl.out c (some true)) :=
        projLbl_O hc hOb
      -- the observation is one of four, and each is reachable under `w₂`
      obtain ⟨t₃, hp3, hq3⟩ := produces_three hc htot₂
      have hvis : Sc.coalition.proj C t₃
          = [PLbl.out c (some true), PLbl.out c (some true), PLbl.out c (some true)] := by
        -- `t₃`'s observation at `C` is the same as at `{Ob}`
        obtain ⟨⟨s₃, hr₃⟩, -⟩ := hp3
        have h3 := reach_traces hr₃
        simp only [tracesFrom] at h3
        have hO0 : Sc.coalition.projLbl (Sec.sing Lv.Ob) (O c)
            = some (PLbl.out c (some true)) := projLbl_O hc ob_vis_ob
        have hRF0 : Sc.coalition.projLbl (Sec.sing Lv.Ob) RF = none :=
          projLbl_R hi_not_ob
        have hRT0 : Sc.coalition.projLbl (Sec.sing Lv.Ob) RT = none :=
          projLbl_R hi_not_ob
        rcases h3 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          simp [Sec.proj, hO0, hRF0, hRT0] at hq3 <;>
          simp [Sec.proj, hO, hRF, hRT]
      simp only [Sec.proj] at hvis
      rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨[], p0, rfl⟩
      · exact ⟨[O c], p1, rfl⟩
      · exact ⟨[O c, O c], p2, rfl⟩
      · exact ⟨[O c, O c], p2, by simp [Sec.teq, Sec.proj, hO, hRF]⟩
      · exact ⟨t₃, hp3, by simp [Sec.teq, Sec.proj, hO, hRF, hvis]⟩
      · exact ⟨[], p0, by simp [Sec.teq, Sec.proj, hRT]⟩
      · exact ⟨[O c], p1, by simp [Sec.teq, Sec.proj, hO, hRT]⟩
      · exact ⟨[O c, O c], p2, by simp [Sec.teq, Sec.proj, hO, hRT]⟩
      · exact ⟨t₃, hp3, by simp [Sec.teq, Sec.proj, hO, hRT, hvis]⟩
      · exact ⟨[], p0, by simp [Sec.teq, Sec.proj, hRF]⟩
      · exact ⟨[O c, O c], p2, by simp [Sec.teq, Sec.proj, hO, hRT]⟩
    · -- the coalition sees nothing at all
      have hO : Sc.coalition.projLbl C (O c) = none := projLbl_O_hidden hc hOb
      refine ⟨[], p0, ?_⟩
      show Sc.coalition.proj C t₁ = Sc.coalition.proj C []
      rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [Sec.proj, hO, hRF, hRT]

/-! ### The two strategies -/

/-- Always `false`. -/
def W1 : Sc.coalition.Strategy Bool where
  ω := fun ch _ => match ch with | Chan.a => (fun v => v = false) | _ => (fun _ => True)
  resp_val := by intro ch _ _ _; cases ch <;> rfl
  resp_pres := by intro ch _ _ _; cases ch <;> exact dotEq.refl _

/-- `true` once `a` has been used. -/
noncomputable def hasA (t : List (Lbl Chan Bool)) : Bool :=
  decide (Sc.coalition.proj (Sec.sing Lv.Hi) t ≠ [])

def W2 : Sc.coalition.Strategy Bool where
  ω := fun ch t => match ch with | Chan.a => (fun v => v = hasA t) | _ => (fun _ => True)
  resp_val := by
    intro ch t₁ t₂ h
    cases ch
    · rfl
    · rfl
    · have hp : Sc.coalition.proj (Sec.sing Lv.Hi) t₁
          = Sc.coalition.proj (Sec.sing Lv.Hi) t₂ := h
      simp only [hasA, hp]
  resp_pres := by
    intro ch _ _ _
    cases ch
    · exact dotEq.refl _
    · exact dotEq.refl _
    · exact ⟨fun h => absurd rfl (h _), fun h => absurd rfl (h _)⟩

theorem W1_total : W1.total := by
  intro ch _; cases ch <;> exact ⟨false, by simp [W1]⟩

theorem W2_total : W2.total := by
  intro ch t; cases ch <;> first | exact ⟨false, trivial⟩ | exact ⟨hasA t, rfl⟩

/-- The two strategies agree on everything the coalition `{Ob}` can see. -/
theorem W1_seq_W2 : Sc.coalition.seq (Sec.sing Lv.Ob) W1 W2 := by
  intro ch t
  refine ⟨fun hvis => ?_, ?_⟩
  · cases ch
    · rfl
    · rfl
    · exact absurd hvis hi_not_ob
  · intro _
    cases ch
    · exact dotEq.refl _
    · exact dotEq.refl _
    · exact ⟨fun h => absurd rfl (h false), fun h => absurd rfl (h (hasA t))⟩

/-! ### The observation, and a run producing it under `W1` -/

/-- The alternating observation. -/
def Obs : List (PLbl Chan Bool) :=
  [PLbl.out Chan.p (some true), PLbl.out Chan.q (some true),
   PLbl.out Chan.p (some true), PLbl.out Chan.q (some true),
   PLbl.out Chan.p (some true), PLbl.out Chan.q (some true)]

def wit : List (Lbl Chan Bool) :=
  [O Chan.p, O Chan.q, O Chan.p, O Chan.q, RF, O Chan.p, RF, O Chan.q]

theorem wit_interleave :
    Interleave [O Chan.p, O Chan.p, RF, O Chan.p] [O Chan.q, O Chan.q, RF, O Chan.q] wit :=
  Interleave.left (Interleave.right (Interleave.left (Interleave.right
    (Interleave.left (Interleave.left (Interleave.right (Interleave.right
      Interleave.nil)))))))

theorem wit_reach :
    Reach (parStep (prog Chan.p) (prog Chan.q)) (St.s0, St.s0) wit (St.fin, St.fin) :=
  par_reach_interleave wit_interleave reach_f reach_f

theorem wit_inp {u r : List (Lbl Chan Bool)} {ch : Chan} {v : Bool}
    (h : wit = u ++ Lbl.inp ch v :: r) : ch = Chan.a ∧ v = false := by
  match u with
  | [] => simp [wit, O, RF] at h
  | [x] => simp [wit, O, RF] at h
  | [x, y] => simp [wit, O, RF] at h
  | [x, y, z] => simp [wit, O, RF] at h
  | [x, y, z, q] =>
      simp only [wit, O, RF, List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨-, -, -, -, ⟨rfl, rfl⟩, -⟩ := h
      exact ⟨rfl, rfl⟩
  | [x, y, z, q, m] => simp [wit, O, RF] at h
  | [x, y, z, q, m, k] =>
      simp only [wit, O, RF, List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨-, -, -, -, -, -, ⟨rfl, rfl⟩, -⟩ := h
      exact ⟨rfl, rfl⟩
  | [x, y, z, q, m, k, i] => simp [wit, O, RF] at h
  | x :: y :: z :: q :: m :: k :: i :: j :: u => simp [wit, O, RF] at h

theorem wit_produces : Sc.coalition.produces (parStep (prog Chan.p) (prog Chan.q)) W1
    (St.s0, St.s0) wit := by
  refine ⟨⟨(St.fin, St.fin), wit_reach⟩, ?_⟩
  intro u ch v r hsplit
  obtain ⟨rfl, rfl⟩ := wit_inp hsplit
  rfl

theorem wit_obs : Sc.coalition.proj (Sec.sing Lv.Ob) wit = Obs := by
  have hOp : Sc.coalition.projLbl (Sec.sing Lv.Ob) (O Chan.p)
      = some (PLbl.out Chan.p (some true)) := projLbl_O (by simp) ob_vis_ob
  have hOq : Sc.coalition.projLbl (Sec.sing Lv.Ob) (O Chan.q)
      = some (PLbl.out Chan.q (some true)) := projLbl_O (by simp) ob_vis_ob
  have hRF0 : Sc.coalition.projLbl (Sec.sing Lv.Ob) RF = none :=
    projLbl_R hi_not_ob
  simp [Sec.proj, wit, Obs, hOp, hOq, hRF0]

/-! ### Splitting an interleaving -/

theorem interleave_split_right {α : Type} {u v w : List α} {x : α}
    (h : Interleave u (x :: v) w) :
    ∃ u₁ u₂ w₂, u = u₁ ++ u₂ ∧ w = u₁ ++ x :: w₂ ∧ Interleave u₂ v w₂ := by
  generalize hv : x :: v = xv at h
  induction h with
  | nil => exact absurd hv.symm (by simp)
  | @left b u' v' w' _ ih =>
      obtain ⟨u₁, u₂, w₂, h1, h2, h3⟩ := ih hv
      exact ⟨b :: u₁, u₂, w₂, by rw [h1]; rfl, by rw [h2]; rfl, h3⟩
  | @right b u' v' w' hI _ =>
      injection hv with hb hv'
      subst hb; subst hv'
      exact ⟨[], u', w', rfl, rfl, hI⟩

theorem interleave_split_left {α : Type} {u v w : List α} {x : α}
    (h : Interleave (x :: u) v w) :
    ∃ v₁ v₂ w₂, v = v₁ ++ v₂ ∧ w = v₁ ++ x :: w₂ ∧ Interleave u v₂ w₂ := by
  generalize hu : x :: u = xu at h
  induction h with
  | nil => exact absurd hu.symm (by simp)
  | @right b u' v' w' _ ih =>
      obtain ⟨v₁, v₂, w₂, h1, h2, h3⟩ := ih hu
      exact ⟨b :: v₁, v₂, w₂, by rw [h1]; rfl, by rw [h2]; rfl, h3⟩
  | @left b u' v' w' hI _ =>
      injection hu with hb hu'
      subst hb; subst hu'
      exact ⟨[], v', w', rfl, rfl, hI⟩

theorem interleave_both {α : Type} {x : α} : ∀ {u v w : List α},
    Interleave u v w → x ∈ u → x ∈ v →
      ∃ pre post, w = pre ++ x :: post ∧ x ∈ pre := by
  intro u v w h
  induction h with
  | nil => intro hu _; exact absurd hu (by simp)
  | @left b u' v' w' hI ih =>
      intro hu hv
      by_cases hb : b = x
      · subst hb
        obtain ⟨s, t, hst⟩ := List.append_of_mem (hI.mem_right hv)
        exact ⟨b :: s, t, by rw [hst]; rfl, by simp⟩
      · obtain ⟨pre, post, h1, h2⟩ := ih (by
          rcases List.mem_cons.mp hu with rfl | h
          · exact absurd rfl hb
          · exact h) hv
        exact ⟨b :: pre, post, by rw [h1]; rfl, List.mem_cons.mpr (Or.inr h2)⟩
  | @right b u' v' w' hI ih =>
      intro hu hv
      by_cases hb : b = x
      · subst hb
        obtain ⟨s, t, hst⟩ := List.append_of_mem (hI.mem_left hu)
        exact ⟨b :: s, t, by rw [hst]; rfl, by simp⟩
      · obtain ⟨pre, post, h1, h2⟩ := ih hu (by
          rcases List.mem_cons.mp hv with rfl | h
          · exact absurd rfl hb
          · exact h)
        exact ⟨b :: pre, post, by rw [h1]; rfl, List.mem_cons.mpr (Or.inr h2)⟩

/-! ### Counting the messages -/

theorem le_three {c : Chan} (hc : c ≠ Chan.a) {s' : St} {t : List (Lbl Chan Bool)}
    (h : Reach (prog c) St.s0 t s') :
    (Sc.coalition.proj (Sec.sing Lv.Ob) t).length ≤ 3 := by
  have hO := projLbl_O (C := Sec.sing Lv.Ob) hc ob_vis_ob
  have hRF : Sc.coalition.projLbl (Sec.sing Lv.Ob) RF = none :=
    projLbl_R hi_not_ob
  have hRT : Sc.coalition.projLbl (Sec.sing Lv.Ob) RT = none :=
    projLbl_R hi_not_ob
  have ht := reach_traces h
  simp only [tracesFrom] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [Sec.proj, hO, hRF, hRT]

theorem three_out {c : Chan} (hc : c ≠ Chan.a) {s' : St} {t : List (Lbl Chan Bool)}
    (h : Reach (prog c) St.s0 t s')
    (hlen : (Sc.coalition.proj (Sec.sing Lv.Ob) t).length = 3) :
    t = [O c, O c, RF, O c] ∨ t = [RT, O c, O c, O c] := by
  have hO := projLbl_O (C := Sec.sing Lv.Ob) hc ob_vis_ob
  have hRF : Sc.coalition.projLbl (Sec.sing Lv.Ob) RF = none :=
    projLbl_R hi_not_ob
  have hRT : Sc.coalition.projLbl (Sec.sing Lv.Ob) RT = none :=
    projLbl_R hi_not_ob
  have ht := reach_traces h
  simp only [tracesFrom] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [Sec.proj, hO, hRF, hRT] at hlen ⊢

theorem proj_ne_nil {ℓ : Sec.Coalition Lv} {l : List (Lbl Chan Bool)}
    {x : Lbl Chan Bool} (hx : x ∈ l) {y : PLbl Chan Bool}
    (h : Sc.coalition.projLbl ℓ x = some y) : Sc.coalition.proj ℓ l ≠ [] := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hx
  rw [Sec.proj_append, Sec.proj_cons_some h]
  simp

theorem projLbl_RF_Hi :
    Sc.coalition.projLbl (Sec.sing Lv.Hi) RF = some (PLbl.inp Chan.a (some false)) :=
  Sec.projLbl_inp_full (Sc.coalition.le_refl _) (Sc.coalition.le_refl _)

theorem projLbl_RT_Hi :
    Sc.coalition.projLbl (Sec.sing Lv.Hi) RT = some (PLbl.inp Chan.a (some true)) :=
  Sec.projLbl_inp_full (Sc.coalition.le_refl _) (Sc.coalition.le_refl _)

/-! ### No run under `W2` produces the observation -/

theorem projLbl_O_Hi {c : Chan} (hc : c ≠ Chan.a) :
    Sc.coalition.projLbl (Sec.sing Lv.Hi) (O c) = none := by
  refine Sec.projLbl_out_hidden (fun h => ?_)
  cases c
  · exact ob_not_hi h
  · exact ob_not_hi h
  · exact hc rfl

theorem no_match : ¬ ∃ t₂, Sc.coalition.produces (parStep (prog Chan.p) (prog Chan.q)) W2
    (St.s0, St.s0) t₂ ∧ Sc.coalition.proj (Sec.sing Lv.Ob) t₂ = Obs := by
  rintro ⟨t₂, ⟨⟨⟨sA, sB⟩, hreach⟩, hcons⟩, hobs⟩
  obtain ⟨tA, tB, hA, hB, hI⟩ := par_decompose hreach
  have hOp := projLbl_O (C := Sec.sing Lv.Ob) (c := Chan.p) (by simp) ob_vis_ob
  have hOq := projLbl_O (C := Sec.sing Lv.Ob) (c := Chan.q) (by simp) ob_vis_ob
  have hRF0 : Sc.coalition.projLbl (Sec.sing Lv.Ob) RF = none :=
    projLbl_R hi_not_ob
  have hRT0 : Sc.coalition.projLbl (Sec.sing Lv.Ob) RT = none :=
    projLbl_R hi_not_ob
  -- both components emit three messages
  have hIp : Interleave (Sc.coalition.proj (Sec.sing Lv.Ob) tA)
      (Sc.coalition.proj (Sec.sing Lv.Ob) tB)
      (Sc.coalition.proj (Sec.sing Lv.Ob) t₂) := Interleave.filterMap _ hI
  have hlen := hIp.length
  rw [hobs] at hlen
  have hA3 : (Sc.coalition.proj (Sec.sing Lv.Ob) tA).length ≤ 3 := le_three (by simp) hA
  have hB3 : (Sc.coalition.proj (Sec.sing Lv.Ob) tB).length ≤ 3 := le_three (by simp) hB
  have hObs6 : Obs.length = 6 := by simp [Obs]
  rw [hObs6] at hlen
  have hA' : (Sc.coalition.proj (Sec.sing Lv.Ob) tA).length = 3 := by omega
  have hB' : (Sc.coalition.proj (Sec.sing Lv.Ob) tB).length = 3 := by omega
  rcases three_out (by simp) hA hA' with rfl | rfl <;>
    rcases three_out (by simp) hB hB' with rfl | rfl
  · -- both read late: the second read would have to be answered `false` twice
    obtain ⟨pre, post, hsplit, hmem⟩ :=
      interleave_both (x := RF) hI (by simp) (by simp)
    have hc2 := hcons pre Chan.a false post hsplit
    have hne : Sc.coalition.proj (Sec.sing Lv.Hi) pre ≠ [] :=
      proj_ne_nil hmem projLbl_RF_Hi
    simp [W2, hasA, hne] at hc2
  · -- `A` reads late, `B` early: `A` must emit two messages before `B` emits any
    obtain ⟨u₁, u₂, w₂, hsplitA, hsplit2, -⟩ := interleave_split_right hI
    have hc2 := hcons u₁ Chan.a true w₂ hsplit2
    have hne : Sc.coalition.proj (Sec.sing Lv.Hi) u₁ ≠ [] := by
      intro hnil; simp [W2, hasA, hnil] at hc2
    rcases u₁ with _|⟨x,_|⟨y,_|⟨z,rest⟩⟩⟩
    · exact hne rfl
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsplitA
      obtain ⟨rfl, -⟩ := hsplitA
      exact hne (by simp [Sec.proj, projLbl_O_Hi (c := Chan.p) (by simp)])
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsplitA
      obtain ⟨rfl, rfl, -⟩ := hsplitA
      exact hne (by simp [Sec.proj, projLbl_O_Hi (c := Chan.p) (by simp)])
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsplitA
      obtain ⟨rfl, rfl, -⟩ := hsplitA
      rw [hsplit2] at hobs
      simp [Sec.proj, hOp, hOq, Obs] at hobs
  · -- `B` reads late, `A` early
    obtain ⟨v₁, v₂, w₂, hsplitB, hsplit2, -⟩ := interleave_split_left hI
    have hc2 := hcons v₁ Chan.a true w₂ hsplit2
    have hne : Sc.coalition.proj (Sec.sing Lv.Hi) v₁ ≠ [] := by
      intro hnil; simp [W2, hasA, hnil] at hc2
    rcases v₁ with _|⟨x,_|⟨y,_|⟨z,rest⟩⟩⟩
    · exact hne rfl
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsplitB
      obtain ⟨rfl, -⟩ := hsplitB
      exact hne (by simp [Sec.proj, projLbl_O_Hi (c := Chan.q) (by simp)])
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsplitB
      obtain ⟨rfl, rfl, -⟩ := hsplitB
      exact hne (by simp [Sec.proj, projLbl_O_Hi (c := Chan.q) (by simp)])
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsplitB
      obtain ⟨rfl, rfl, -⟩ := hsplitB
      rw [hsplit2] at hobs
      simp [Sec.proj, hOp, hOq, Obs] at hobs
  · -- both read early: the first read would have to be answered `true`
    have hhead : ∃ rest, t₂ = RT :: rest := by
      cases hI with
      | left h => exact ⟨_, rfl⟩
      | right h => exact ⟨_, rfl⟩
    obtain ⟨rest, rfl⟩ := hhead
    have hc2 := hcons [] Chan.a true rest rfl
    simp [W2, hasA, Sec.proj] at hc2

/-! ### The counterexample -/

/-- **The composition is not coalition noninterfering.** -/
theorem par_not_NI :
    ¬ Sc.coalition.StratTNI (parStep (prog Chan.p) (prog Chan.q)) (St.s0, St.s0) := by
  intro h
  obtain ⟨t₂, hp, hteq⟩ :=
    h (Sec.sing Lv.Ob) W1 W2 W1_total W2_total W1_seq_W2 wit wit_produces
  exact no_match ⟨t₂, hp, by rw [← hteq]; exact wit_obs⟩

theorem progs_NI :
    Sc.coalition.StratTNI (prog Chan.p) St.s0 ∧ Sc.coalition.StratTNI (prog Chan.q) St.s0 :=
  ⟨prog_NI (by simp), prog_NI (by simp)⟩

/-- **Coalition noninterference does not compose when presence may be secret.**
    The hypothesis that presence is public cannot be dropped from
    `coalition_compositional_total_fin`, even with finitely many channels. -/
theorem no_general_composition :
    ¬ ∀ (Lvl Ch Val : Type) (S : Sec Lvl Ch) (cs : List Ch), (∀ a : Ch, a ∈ cs) →
        ∀ (StA StB : Type) (stepA : StA → Act Ch Val → StA → Prop)
          (stepB : StB → Act Ch Val → StB → Prop) (sA : StA) (sB : StB),
          S.coalition.StratTNI stepA sA → S.coalition.StratTNI stepB sB →
          S.coalition.StratTNI (parStep stepA stepB) (sA, sB) := by
  intro h
  exact par_not_NI (h Lv Chan Bool Sc [Chan.p, Chan.q, Chan.a] (fun a => by cases a <;> simp)
    St St (prog Chan.p) (prog Chan.q) St.s0 St.s0 progs_NI.1 progs_NI.2)

/-! ### The same example refutes the original claim about INI

    Coalition noninterference implies INI, and the failure above is at a
    *singleton* coalition, which is a level.  So this is also a counterexample to
    the compositionality of INI -- a second one, structurally unlike the masking
    counterexamples: it uses a lattice of width two, three channels, and
    components that satisfy the much stronger coalition noninterference. -/

theorem progs_INI :
    Sc.StratTNI (prog Chan.p) St.s0 ∧ Sc.StratTNI (prog Chan.q) St.s0 :=
  ⟨Sec.StratTNI_of_coalition progs_NI.1, Sec.StratTNI_of_coalition progs_NI.2⟩

theorem par_not_INI :
    ¬ Sc.StratTNI (parStep (prog Chan.p) (prog Chan.q)) (St.s0, St.s0) := by
  intro h
  obtain ⟨t₂, hp, ht⟩ := h Lv.Ob (Sec.Strategy.ofCoalition W1) (Sec.Strategy.ofCoalition W2)
    W1_total W2_total (Sec.seq_ofCoalition W1_seq_W2) wit wit_produces
  refine no_match ⟨t₂, hp, ?_⟩
  rw [← (Sec.coalition_teq_sing (S := Sc) (Value := Bool) Lv.Ob wit t₂).mpr ht]
  exact wit_obs

/-- **INI does not compose**, over a lattice of width two, with total strategies,
    and with components that are even coalition noninterfering. -/
theorem INI_not_compositional :
    ¬ ∀ (Lvl Ch Val : Type) (S : Sec Lvl Ch) (cs : List Ch), (∀ a : Ch, a ∈ cs) →
        ∀ (StA StB : Type) (stepA : StA → Act Ch Val → StA → Prop)
          (stepB : StB → Act Ch Val → StB → Prop) (sA : StA) (sB : StB),
          S.StratTNI stepA sA → S.StratTNI stepB sB →
          S.StratTNI (parStep stepA stepB) (sA, sB) := by
  intro h
  exact par_not_INI (h Lv Chan Bool Sc [Chan.p, Chan.q, Chan.a] (fun a => by cases a <;> simp)
    St St (prog Chan.p) (prog Chan.q) St.s0 St.s0 progs_INI.1 progs_INI.2)

end CexPresence

end InteractiveNI
