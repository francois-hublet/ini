/-
  **The causal-policy lemma fails over a general lattice.**

  Theorem 20 obtains compositionality of coalition noninterference by producing,
  for each component, a *causal policy*: a way of resolving the component's
  non-determinism that realises a prescribed target against *every* legal
  strategy.  That step is where the hypothesis on `γ` is used, and this file
  shows the step is not merely hard without it but false.

  The witness is as small as it can be.  Levels `⊥ ⊑ Ob`, `⊥ ⊑ Md ⊑ Hi`, with
  `Ob` incomparable to `Md` and to `Hi`; presence is public (`presL ≡ ⊥`), so we
  are inside the hypotheses of Theorem 20 except for spreadness, which fails
  because two channels sit at `Md ⊑ Hi`.  The program is

      Q  =  (out_β(0) | out_β(1)) ; in_α(y) ; out_pub(x ⊕ y)

  with `γ(pub) = Ob`, `γ(α) = Md`, `γ(β) = Hi`.  Perturb at `m = Md`: then
  `C⁺ = {⊥, Ob}`, `Vis C⁺ = {pub}`, and the adversarial channels are `α` and `β`.

  * `Q_coalitionNI` : `Q` is coalition-noninterfering.
  * `win_exists`    : against each adversary `W b` the target `out_pub(false)` is
                      reachable -- by opening with `out_β(b)`.
  * `no_policy`     : whichever value `x` the program commits to first, the
                      adversary `W (!x)` makes the target unreachable.

  The two together say exactly that no causal policy exists: the winning opening
  move depends on an answer the program has not yet received, and cannot receive,
  since `α`'s user does not see `β` (`Hi ⋢ Md`).  The obstruction is *not* removed
  by enlarging the coalition to see `β`: `C⁺ ∪ {Hi}` sees `α` as well -- because
  `Md ⊑ Hi` -- so coalition noninterference at it constrains nothing.  A proof of
  the general case must therefore use both components' hypotheses jointly; the
  per-component policy route is closed.
-/
import InteractiveNI.Coalition

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

namespace NoPolicy

/-! ### The lattice `⊥ ⊑ Ob`, `⊥ ⊑ Md ⊑ Hi` -/

inductive L3 where
  | Bot | Ob | Md | Hi
deriving DecidableEq, Repr

def L3.le (a b : L3) : Prop :=
  a = L3.Bot ∨ a = b ∨ (a = L3.Md ∧ b = L3.Hi)

theorem L3.le_refl (a : L3) : L3.le a a := Or.inr (Or.inl rfl)

theorem L3.le_trans {a b c : L3} (h₁ : L3.le a b) (h₂ : L3.le b c) : L3.le a c := by
  rcases h₁ with rfl | rfl | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact h₂
  · rcases h₂ with h | rfl | ⟨h, -⟩
    · exact absurd h (by simp)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact absurd h (by simp)

/-! ### Three channels -/

inductive Ch3 where
  | pub | alp | bet
deriving DecidableEq, Repr

def Sc3 : Sec L3 Ch3 where
  le := L3.le
  le_refl := L3.le_refl
  le_trans := L3.le_trans
  presL := fun _ => L3.Bot
  valL := fun c => match c with | .pub => L3.Ob | .alp => L3.Md | .bet => L3.Hi
  pres_le_val := fun _ => Or.inl rfl

/-! ### The program -/

inductive QState where
  | q0
  | q1 (x : Bool)
  | q2 (x y : Bool)
  | q3
deriving DecidableEq

inductive stepQ : QState → Act Ch3 Bool → QState → Prop where
  | outB (x)   : stepQ .q0 (.out Ch3.bet x) (.q1 x)
  | inA  (x y) : stepQ (.q1 x) (.inp Ch3.alp y) (.q2 x y)
  | outP (x y) : stepQ (.q2 x y) (.out Ch3.pub (Bool.xor x y)) .q3

/-! ### The traces of `Q` -/

def specQ3 (u : List (Lbl Ch3 Bool)) (s' : QState) : Prop := u = [] ∧ s' = .q3

def specQ2 (x y : Bool) (u : List (Lbl Ch3 Bool)) (s' : QState) : Prop :=
  (u = [] ∧ s' = .q2 x y) ∨ (u = [Lbl.out Ch3.pub (Bool.xor x y)] ∧ s' = .q3)

def specQ1 (x : Bool) (u : List (Lbl Ch3 Bool)) (s' : QState) : Prop :=
  (u = [] ∧ s' = .q1 x) ∨ (∃ y u', u = Lbl.inp Ch3.alp y :: u' ∧ specQ2 x y u' s')

def specQ0 (u : List (Lbl Ch3 Bool)) (s' : QState) : Prop :=
  (u = [] ∧ s' = .q0) ∨ (∃ x u', u = Lbl.out Ch3.bet x :: u' ∧ specQ1 x u' s')

def specQ : QState → List (Lbl Ch3 Bool) → QState → Prop
  | .q0 => specQ0
  | .q1 x => specQ1 x
  | .q2 x y => specQ2 x y
  | .q3 => specQ3

theorem reachQ_spec {s : QState} {u : List (Lbl Ch3 Bool)} {s' : QState}
    (h : Reach stepQ s u s') : specQ s u s' := by
  induction h with
  | @nil s =>
      cases s <;>
        first
          | exact Or.inl ⟨rfl, rfl⟩
          | exact ⟨rfl, rfl⟩
  | tau hs _ _ => cases hs
  | @inp s s' s'' a v t hs _ ih => cases hs; exact Or.inr ⟨v, _, rfl, ih⟩
  | @out s s' s'' a v t hs _ ih =>
      cases hs with
      | outB => exact Or.inr ⟨v, _, rfl, ih⟩
      | outP x y => exact Or.inr ⟨by rw [ih.1], ih.2⟩

/-! ### The adversaries and the observing coalition -/

/-- `W b` answers `b` on `α` and anything elsewhere.  Its answers do not depend on
    the trace at all, so it is legal at every level. -/
def W (b : Bool) : Sc3.coalition.Strategy Bool where
  ω := fun a _ => match a with
    | Ch3.alp => (fun v => v = b)
    | _ => (fun _ => True)
  resp_val := fun a _ _ _ => by cases a <;> rfl
  resp_pres := fun a _ _ _ => by cases a <;> exact dotEq.refl _

/-- The observing coalition of the perturbation at `Md`: every level that does
    not dominate `Md`, i.e. `{⊥, Ob}`.  It sees `pub` and nothing else. -/
def Cp : Sec.Coalition L3 := Sec.Cplus Sc3 L3.Md

theorem Cp_Ob : Cp L3.Ob := by intro h; rcases h with h | h | ⟨-, h⟩ <;> simp at h

/-- `α` is invisible to the coalition. -/
theorem alp_hidden : ¬ Sc3.coalition.le (Sc3.coalition.valL Ch3.alp) Cp := by
  intro h
  obtain ⟨d, hd, hle⟩ := h L3.Md rfl
  exact hd hle

/-- `β` is invisible to the coalition. -/
theorem bet_hidden : ¬ Sc3.coalition.le (Sc3.coalition.valL Ch3.bet) Cp := by
  intro h
  obtain ⟨d, hd, hle⟩ := h L3.Hi rfl
  refine hd ?_
  rcases hle with h' | rfl | ⟨h', -⟩
  · simp at h'
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · simp at h'

/-- Presence is public, so the coalition sees the shape of every trace. -/
theorem pres_public (a : Ch3) : Sc3.coalition.le (Sc3.coalition.presL a) Cp :=
  fun c hc => ⟨L3.Ob, Cp_Ob, by rw [show c = L3.Bot from hc]; exact Or.inl rfl⟩

/-- **All the `W b` are indistinguishable to the coalition.**  They differ only on
    `α`, which the coalition cannot see. -/
theorem W_seq (b b' : Bool) : Sc3.coalition.seq Cp (W b) (W b') := by
  intro a t
  refine ⟨fun hvis => ?_, fun _ => ?_⟩
  · cases a
    · rfl
    · exact absurd hvis alp_hidden
    · rfl
  · cases a
    · exact dotEq.refl _
    · exact ⟨fun h => absurd rfl (h b), fun h => absurd rfl (h b')⟩
    · exact dotEq.refl _

/-! ### `Q` has no causal policy -/

/-- **Whatever `Q` plays first, one adversary defeats it.**  Under `W (!x)` the
    user of `α` answers `!x`, so a run opening with `out_β(x)` can only output
    `x ⊕ !x = true` on `pub`: the target `out_pub(false)` becomes unreachable. -/
theorem no_policy (x : Bool) {t : List (Lbl Ch3 Bool)} {s' : QState}
    (hr : Reach stepQ QState.q0 t s')
    (hc : Sc3.coalition.consistent (W (!x)) t)
    (hfst : t.head? = some (Lbl.out Ch3.bet x)) :
    Lbl.out Ch3.pub false ∉ t := by
  rcases reachQ_spec hr with ⟨rfl, -⟩ | ⟨x', u', rfl, h1⟩
  · simp at hfst
  have hxx : x' = x := by simpa using hfst
  subst hxx
  rcases h1 with ⟨rfl, -⟩ | ⟨y, u'', rfl, h2⟩
  · simp
  have hy : y = !x' := hc [Lbl.out Ch3.bet x'] Ch3.alp y u'' rfl
  subst hy
  rcases h2 with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · simp
  · intro hmem
    rcases List.mem_cons.mp hmem with h | hmem
    · exact absurd h (by simp)
    rcases List.mem_cons.mp hmem with h | hmem
    · exact absurd h (by simp)
    rcases List.mem_cons.mp hmem with h | hmem
    · injection h with _ hv
      cases x' <;> simp at hv
    · simp at hmem

/-- **Yet every adversary admits a winning run**: against `W b`, open with
    `out_β(b)`.  So the failure is not a failure of noninterference; it is the
    *uniformity* over adversaries that is impossible. -/
theorem win_exists (b : Bool) :
    Sc3.coalition.produces stepQ (W b) QState.q0
      [Lbl.out Ch3.bet b, Lbl.inp Ch3.alp b, Lbl.out Ch3.pub false] := by
  refine ⟨⟨QState.q3, ?_⟩, ?_⟩
  · refine Reach.out (stepQ.outB b) (Reach.inp (stepQ.inA b b) ?_)
    have : Bool.xor b b = false := by cases b <;> rfl
    rw [← this]
    exact Reach.out (stepQ.outP b b) Reach.nil
  · intro u a v r heq
    rcases u with _ | ⟨l0, u⟩
    · simp at heq
    rcases u with _ | ⟨l1, u⟩
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
      obtain ⟨rfl, heq2, -⟩ := heq
      injection heq2 with ha hv
      subst ha; subst hv; rfl
    · rcases u with _ | ⟨l2, u⟩ <;> simp at heq

/-! ### `Q` is nonetheless coalition-noninterfering -/

theorem seesHi_of {C : Sec.Coalition L3} (h : ∃ d, C d ∧ L3.le L3.Hi d) :
    ∃ d, C d ∧ L3.le L3.Md d := by
  obtain ⟨d, hd, hle⟩ := h
  exact ⟨d, hd, L3.le_trans (Or.inr (Or.inr ⟨rfl, rfl⟩)) hle⟩

theorem eq_on_alp {C : Sec.Coalition L3} {w₁ w₂ : Sc3.coalition.Strategy Bool}
    (hseq : Sc3.coalition.seq C w₁ w₂) (hM : ∃ d, C d ∧ L3.le L3.Md d)
    (t : List (Lbl Ch3 Bool)) : w₁.ω Ch3.alp t = w₂.ω Ch3.alp t := by
  refine (hseq Ch3.alp t).1 ?_
  obtain ⟨d, hd, hle⟩ := hM
  exact fun c hc => ⟨d, hd, by rw [show c = L3.Md from hc]; exact hle⟩

theorem proj_empty {C : Sec.Coalition L3} (hC : ¬ ∃ d, C d)
    (t : List (Lbl Ch3 Bool)) : Sc3.coalition.proj C t = [] := by
  induction t with
  | nil => rfl
  | cons l t ih =>
      refine Eq.trans (Sec.proj_cons_none ?_ t) ih
      rw [Sec.projLbl_eq_none_iff]
      intro h
      exact hC (by obtain ⟨d, hd, -⟩ := h (Sc3.presL (l.chan)) rfl; exact ⟨d, hd⟩)

/-- The empty trace is always produced. -/
theorem produces_nil (w : Sc3.coalition.Strategy Bool) :
    Sc3.coalition.produces stepQ w QState.q0 [] :=
  ⟨⟨QState.q0, Reach.nil⟩, by intro u a v r heq; simp at heq⟩

/-- **`Q` satisfies coalition noninterference.** -/
theorem Q_coalitionNI : Sc3.coalition.StratNI stepQ QState.q0 := by
  intro C w₁ w₂ _ _ hseq t₁ hprod
  obtain ⟨⟨s', hreach⟩, hcons⟩ := hprod
  by_cases hC : ∃ d, C d
  case neg =>
    exact ⟨[], produces_nil w₂,
      by unfold Sec.teq; rw [proj_empty hC, proj_empty hC]⟩
  -- presence is public, so the coalition always sees the shape
  have hpres : ∀ a : Ch3, Sc3.coalition.le (Sc3.coalition.presL a) C := by
    intro a c hc
    obtain ⟨d, hd⟩ := hC
    exact ⟨d, hd, by rw [show c = L3.Bot from hc]; exact Or.inl rfl⟩
  have hdot : ∀ (a : Ch3) (t : List (Lbl Ch3 Bool)), dotEq (w₁.ω a t) (w₂.ω a t) :=
    fun a t => (hseq a t).2 (hpres a)
  rcases reachQ_spec hreach with ⟨rfl, -⟩ | ⟨x, u', rfl, h1⟩
  · exact ⟨[], produces_nil w₂, rfl⟩
  -- `t₁` opens with `out_β(x)`
  rcases h1 with ⟨rfl, -⟩ | ⟨y, u'', rfl, h2⟩
  · refine ⟨[Lbl.out Ch3.bet x], ⟨⟨QState.q1 x, Reach.out (stepQ.outB x) Reach.nil⟩, ?_⟩, rfl⟩
    intro u a v r heq
    rcases u with _ | ⟨l0, u⟩ <;> simp at heq
  -- `t₁` continues with `in_α(y)`
  have hy : w₁.ω Ch3.alp [Lbl.out Ch3.bet x] y := hcons [Lbl.out Ch3.bet x] Ch3.alp y u'' rfl
  by_cases hM : ∃ d, C d ∧ L3.le L3.Md d
  · -- the coalition sees `α`: the two strategies agree there, so replay `t₁`
    refine ⟨_, ⟨⟨s', hreach⟩, ?_⟩, rfl⟩
    intro u a v r heq
    rcases u with _ | ⟨l0, u⟩
    · simp at heq
    rcases u with _ | ⟨l1, u⟩
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
      obtain ⟨rfl, heq2, -⟩ := heq
      injection heq2 with ha hv
      subst ha; subst hv
      rw [← eq_on_alp hseq hM]
      exact hy
    · rcases h2 with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rcases u with _ | ⟨l2, u⟩ <;> simp at heq
  -- the coalition sees neither `α` nor `β`
  have hHi : ¬ ∃ d, C d ∧ L3.le L3.Hi d := fun h => hM (seesHi_of h)
  have hnvA : ¬ Sc3.coalition.le (Sc3.coalition.valL Ch3.alp) C :=
    fun h => hM (by obtain ⟨d, hd, hle⟩ := h L3.Md rfl; exact ⟨d, hd, hle⟩)
  have hnvB : ¬ Sc3.coalition.le (Sc3.coalition.valL Ch3.bet) C :=
    fun h => hHi (by obtain ⟨d, hd, hle⟩ := h L3.Hi rfl; exact ⟨d, hd, hle⟩)
  obtain ⟨y₂, hy₂⟩ : ∃ y₂, w₂.ω Ch3.alp [Lbl.out Ch3.bet x] y₂ := by
    rcases Classical.em (∃ y₂, w₂.ω Ch3.alp [Lbl.out Ch3.bet x] y₂) with h | h
    · exact h
    · exact absurd hy ((hdot Ch3.alp _).mpr (fun v hv => h ⟨v, hv⟩) y)
  rcases h2 with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · -- `t₁ = out_β(x) . in_α(y)`
    refine ⟨[Lbl.out Ch3.bet x, Lbl.inp Ch3.alp y₂],
      ⟨⟨QState.q2 x y₂, Reach.out (stepQ.outB x) (Reach.inp (stepQ.inA x y₂) Reach.nil)⟩, ?_⟩, ?_⟩
    · intro u a v r heq
      rcases u with _ | ⟨l0, u⟩
      · simp at heq
      rcases u with _ | ⟨l1, u⟩
      · simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
        obtain ⟨rfl, heq2, -⟩ := heq
        injection heq2 with ha hv
        subst ha; subst hv
        exact hy₂
      · rcases u with _ | ⟨l2, u⟩ <;> simp at heq
    · unfold Sec.teq
      rw [Sec.proj_cons_some (Sec.projLbl_out_pres (hpres Ch3.bet) hnvB),
          Sec.proj_cons_some (Sec.projLbl_inp_pres (hpres Ch3.alp) hnvA),
          Sec.proj_cons_some (Sec.projLbl_out_pres (hpres Ch3.bet) hnvB),
          Sec.proj_cons_some (Sec.projLbl_inp_pres (hpres Ch3.alp) hnvA)]
  · -- `t₁ = out_β(x) . in_α(y) . out_pub(x ⊕ y)`: rechoose the hidden `β`-output
    obtain ⟨x₂, hx₂⟩ : ∃ x₂ : Bool, Bool.xor x₂ y₂ = Bool.xor x y :=
      ⟨Bool.xor (Bool.xor x y) y₂, by cases x <;> cases y <;> cases y₂ <;> rfl⟩
    have hteqMd : Sc3.coalition.teq (Sc3.coalition.valL Ch3.alp)
        [Lbl.out Ch3.bet x] [Lbl.out Ch3.bet x₂] := by
      have hnb : ¬ Sc3.coalition.le (Sc3.coalition.valL Ch3.bet)
          (Sc3.coalition.valL Ch3.alp) := by
        intro h
        obtain ⟨d, hd, hle⟩ := h L3.Hi rfl
        rw [show d = L3.Md from hd] at hle
        rcases hle with h' | h' | ⟨h', -⟩ <;> simp at h'
      have hpb : Sc3.coalition.le (Sc3.coalition.presL Ch3.bet)
          (Sc3.coalition.valL Ch3.alp) :=
        fun c hc => ⟨L3.Md, rfl, by rw [show c = L3.Bot from hc]; exact Or.inl rfl⟩
      unfold Sec.teq
      rw [Sec.proj_cons_some (Sec.projLbl_out_pres hpb hnb),
          Sec.proj_cons_some (Sec.projLbl_out_pres hpb hnb)]
    have hy₂' : w₂.ω Ch3.alp [Lbl.out Ch3.bet x₂] y₂ := by
      rw [← w₂.resp_val Ch3.alp _ _ hteqMd]; exact hy₂
    refine ⟨[Lbl.out Ch3.bet x₂, Lbl.inp Ch3.alp y₂, Lbl.out Ch3.pub (Bool.xor x y)],
      ⟨⟨QState.q3, ?_⟩, ?_⟩, ?_⟩
    · refine Reach.out (stepQ.outB x₂) (Reach.inp (stepQ.inA x₂ y₂) ?_)
      rw [← hx₂]
      exact Reach.out (stepQ.outP x₂ y₂) Reach.nil
    · intro u a v r heq
      rcases u with _ | ⟨l0, u⟩
      · simp at heq
      rcases u with _ | ⟨l1, u⟩
      · simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
        obtain ⟨rfl, heq2, -⟩ := heq
        injection heq2 with ha hv
        subst ha; subst hv
        exact hy₂'
      · rcases u with _ | ⟨l2, u⟩ <;> simp at heq
    · unfold Sec.teq
      rw [Sec.proj_cons_some (Sec.projLbl_out_pres (hpres Ch3.bet) hnvB),
          Sec.proj_cons_some (Sec.projLbl_inp_pres (hpres Ch3.alp) hnvA),
          Sec.proj_cons_some (Sec.projLbl_out_pres (hpres Ch3.bet) hnvB),
          Sec.proj_cons_some (Sec.projLbl_inp_pres (hpres Ch3.alp) hnvA)]

/-- **The causal-policy lemma fails.**  `Q` is coalition-noninterfering; for each
    opening move there is a legal adversary, indistinguishable at `C⁺` from the
    reference, under which the target becomes unreachable; and each of those
    adversaries admits a winning run of its own.  So there is no single policy
    realising the target against all of them. -/
theorem no_causal_policy (x : Bool) :
    Sc3.coalition.StratNI stepQ QState.q0 ∧
    Sc3.coalition.seq Cp (W (!x)) (W false) ∧
    (∀ (t : List (Lbl Ch3 Bool)) (s' : QState), Reach stepQ QState.q0 t s' →
        Sc3.coalition.consistent (W (!x)) t →
        t.head? = some (Lbl.out Ch3.bet x) → Lbl.out Ch3.pub false ∉ t) ∧
    Sc3.coalition.produces stepQ (W (!x)) QState.q0
      [Lbl.out Ch3.bet (!x), Lbl.inp Ch3.alp (!x), Lbl.out Ch3.pub false] :=
  ⟨Q_coalitionNI, W_seq _ _, fun _ _ hr hc hf => no_policy x hr hc hf, win_exists _⟩

/-! ### Why the failure above is confined to a chain

    `Q` is coalition-noninterfering only because `β` sits at `Hi` and the user of
    `α` -- at `Md` -- cannot see it: `Hi ⋢ Md`.  Lower `β` to `Md` and the user of
    `α` does see it, so the environment can answer `!x` *by itself*; the program
    then outputs `true` no matter what, and coalition noninterference fails
    immediately.

    This is the structural reason a compositionality counterexample cannot simply
    reuse `Q`.  The feedback `Q` needs -- its own `β`-output coming back on `α` --
    is forbidden inside a single component by coalition noninterference itself.
    To supply it from outside, a partner would have to carry the value from `Hi`
    down to `Md`, and Theorem 19 (`NoMaskAttack.no_attack`) shows no
    coalition-noninterfering program can do that. -/

/-- The same channels, but with `β` lowered to `α`'s level. -/
def Sc3f : Sec L3 Ch3 where
  le := L3.le
  le_refl := L3.le_refl
  le_trans := L3.le_trans
  presL := fun _ => L3.Bot
  valL := fun c => match c with | .pub => L3.Ob | .alp => L3.Md | .bet => L3.Md
  pres_le_val := fun _ => Or.inl rfl

/-- The constant adversary, for `Sc3f`. -/
def Wf (b : Bool) : Sc3f.coalition.Strategy Bool where
  ω := fun a _ => match a with
    | Ch3.alp => (fun v => v = b)
    | _ => (fun _ => True)
  resp_val := fun a _ _ _ => by cases a <;> rfl
  resp_pres := fun a _ _ _ => by cases a <;> exact dotEq.refl _

/-- **The relay adversary.**  Legal for `Sc3f`, because the user of `α` now sees
    `β`: it answers the negation of the value the program has emitted there. -/
def R : Sc3f.coalition.Strategy Bool where
  ω := fun a t => match a with
    | Ch3.alp => (fun v => (Lbl.out Ch3.bet true ∈ t ∧ v = false) ∨
                           (Lbl.out Ch3.bet true ∉ t ∧ v = true))
    | _ => (fun _ => True)
  resp_val := by
    intro a t₁ t₂ h
    rw [Sec.teq] at h
    cases a
    · rfl
    · have hp : Sc3f.coalition.le (Sc3f.coalition.presL Ch3.bet)
          (Sc3f.coalition.valL Ch3.alp) :=
        fun c hc => ⟨L3.Md, rfl, by rw [show c = L3.Bot from hc]; exact Or.inl rfl⟩
      have hv : Sc3f.coalition.le (Sc3f.coalition.valL Ch3.bet)
          (Sc3f.coalition.valL Ch3.alp) :=
        fun c hc => ⟨L3.Md, rfl, by rw [show c = L3.Md from hc]; exact L3.le_refl _⟩
      have h₁ := Sec.mem_proj_out_full (S := Sc3f.coalition) (v := true) hp hv t₁
      have h₂ := Sec.mem_proj_out_full (S := Sc3f.coalition) (v := true) hp hv t₂
      rw [h] at h₁
      have hmem : (Lbl.out Ch3.bet true ∈ t₁) = (Lbl.out Ch3.bet true ∈ t₂) :=
        propext (h₁.symm.trans h₂)
      simp only [hmem]
    · rfl
  resp_pres := by
    intro a t₁ t₂ _
    cases a
    · exact dotEq.refl _
    · constructor
      · intro h
        by_cases hb : Lbl.out Ch3.bet true ∈ t₁
        · exact absurd (Or.inl ⟨hb, rfl⟩) (h false)
        · exact absurd (Or.inr ⟨hb, rfl⟩) (h true)
      · intro h
        by_cases hb : Lbl.out Ch3.bet true ∈ t₂
        · exact absurd (Or.inl ⟨hb, rfl⟩) (h false)
        · exact absurd (Or.inr ⟨hb, rfl⟩) (h true)
    · exact dotEq.refl _

def Cpf : Sec.Coalition L3 := Sec.Cplus Sc3f L3.Md

theorem Cpf_Ob : Cpf L3.Ob := by intro h; rcases h with h | h | ⟨-, h⟩ <;> simp at h

theorem f_hidden (a : Ch3) (h : a ≠ Ch3.pub) :
    ¬ Sc3f.coalition.le (Sc3f.coalition.valL a) Cpf := by
  intro hle
  cases a
  · exact h rfl
  · obtain ⟨d, hd, hd'⟩ := hle L3.Md rfl; exact hd hd'
  · obtain ⟨d, hd, hd'⟩ := hle L3.Md rfl; exact hd hd'

theorem f_pres (a : Ch3) : Sc3f.coalition.le (Sc3f.coalition.presL a) Cpf :=
  fun c hc => ⟨L3.Ob, Cpf_Ob, by rw [show c = L3.Bot from hc]; exact Or.inl rfl⟩

theorem f_pub : Sc3f.coalition.le (Sc3f.coalition.valL Ch3.pub) Cpf :=
  fun c hc => ⟨L3.Ob, Cpf_Ob, by rw [show c = L3.Ob from hc]; exact L3.le_refl _⟩

theorem Wf_R_seq (b : Bool) : Sc3f.coalition.seq Cpf (Wf b) R := by
  intro a t
  refine ⟨fun hvis => ?_, fun _ => ?_⟩
  · cases a
    · rfl
    · exact absurd hvis (f_hidden Ch3.alp (by simp))
    · rfl
  · cases a
    · exact dotEq.refl _
    · constructor
      · intro h; exact absurd rfl (h b)
      · intro h
        by_cases hb : Lbl.out Ch3.bet true ∈ t
        · exact absurd (Or.inl ⟨hb, rfl⟩) (h false)
        · exact absurd (Or.inr ⟨hb, rfl⟩) (h true)
    · exact dotEq.refl _

/-- The projection of a complete run at the observing coalition. -/
theorem proj_run (x y : Bool) :
    Sc3f.coalition.proj Cpf
      [Lbl.out Ch3.bet x, Lbl.inp Ch3.alp y, Lbl.out Ch3.pub (Bool.xor x y)]
      = [PLbl.out Ch3.bet none, PLbl.inp Ch3.alp none,
         PLbl.out Ch3.pub (some (Bool.xor x y))] := by
  rw [Sec.proj_cons_some (Sec.projLbl_out_pres (f_pres Ch3.bet) (f_hidden Ch3.bet (by simp))),
      Sec.proj_cons_some (Sec.projLbl_inp_pres (f_pres Ch3.alp) (f_hidden Ch3.alp (by simp))),
      Sec.proj_cons_some (Sec.projLbl_out_full (f_pres Ch3.pub) f_pub)]
  rfl

/-- **With `β` at `α`'s level, `Q` is no longer coalition-noninterfering.**  The
    environment relays the program's own output back to it, and the public output
    is forced. -/
theorem Q_flat_not_coalitionNI : ¬ Sc3f.coalition.StratNI stepQ QState.q0 := by
  intro hNI
  have hprod : Sc3f.coalition.produces stepQ (Wf false) QState.q0
      [Lbl.out Ch3.bet false, Lbl.inp Ch3.alp false, Lbl.out Ch3.pub false] := by
    refine ⟨⟨QState.q3, ?_⟩, ?_⟩
    · refine Reach.out (stepQ.outB false) (Reach.inp (stepQ.inA false false) ?_)
      exact Reach.out (stepQ.outP false false) Reach.nil
    · intro u a v r heq
      rcases u with _ | ⟨l0, u⟩
      · simp at heq
      rcases u with _ | ⟨l1, u⟩
      · simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
        obtain ⟨rfl, heq2, -⟩ := heq
        injection heq2 with ha hv
        subst ha; subst hv; rfl
      · rcases u with _ | ⟨l2, u⟩ <;> simp at heq
  obtain ⟨t₂, ⟨⟨s₂, hr₂⟩, hc₂⟩, hteq⟩ := hNI Cpf (Wf false) R trivial trivial (Wf_R_seq false)
    _ hprod
  have hpi : Sc3f.coalition.proj Cpf
      [Lbl.out Ch3.bet false, Lbl.inp Ch3.alp false, Lbl.out Ch3.pub false] =
      [PLbl.out Ch3.bet none, PLbl.inp Ch3.alp none, PLbl.out Ch3.pub (some false)] := by
    have := proj_run false false
    simpa using this
  rw [Sec.teq, hpi] at hteq
  -- `t₂` must be a complete run, and the relay forces its public output to `true`
  rcases reachQ_spec hr₂ with ⟨rfl, -⟩ | ⟨x, u', rfl, h1⟩
  · simp [Sec.proj] at hteq
  rcases h1 with ⟨rfl, -⟩ | ⟨y, u'', rfl, h2⟩
  · rw [Sec.proj_cons_some
      (Sec.projLbl_out_pres (f_pres Ch3.bet) (f_hidden Ch3.bet (by simp)))] at hteq
    simp [Sec.proj] at hteq
  have hy : (R.ω Ch3.alp [Lbl.out Ch3.bet x]) y :=
    hc₂ [Lbl.out Ch3.bet x] Ch3.alp y u'' rfl
  have hyx : y = !x := by
    rcases hy with ⟨hb, rfl⟩ | ⟨hb, rfl⟩
    · rcases List.mem_cons.mp hb with h | h
      · injection h with _ hv; subst hv; rfl
      · simp at h
    · cases x
      · rfl
      · exact absurd (List.mem_cons.mpr (Or.inl rfl)) hb
  subst hyx
  rcases h2 with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rw [Sec.proj_cons_some
      (Sec.projLbl_out_pres (f_pres Ch3.bet) (f_hidden Ch3.bet (by simp))),
      Sec.proj_cons_some
      (Sec.projLbl_inp_pres (f_pres Ch3.alp) (f_hidden Ch3.alp (by simp)))] at hteq
    simp [Sec.proj] at hteq
  · rw [proj_run] at hteq
    simp only [List.cons.injEq, PLbl.out.injEq, Option.some.injEq] at hteq
    have := hteq.2.2.1.2
    cases x <;> simp at this

end NoPolicy

end InteractiveNI
