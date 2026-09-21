/-
  §4 — Compositionality in the deterministic case (part 1):
  determinism lemmas, the "follow" lemma, Lemma 5 and Lemma 4 of the paper.
-/
import InteractiveNI.Shift

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

/-! ### Elementary consequences of determinism -/

section Det
variable {C V St : Type} {step : St → Act C V → St → Prop}

theorem det_target (hdet : Deterministic step) {s a s' s''}
    (h1 : step s a s') (h2 : step s a s'') : s' = s'' := hdet.target h1 h2

/-- From a state with an output (or τ) transition, no other transition is possible. -/
theorem det_not_inp (hdet : Deterministic step) {s a s' s''} {b : C} {v : V}
    (h1 : step s a s') (h2 : step s (.inp b v) s'') (hne : a ≠ .inp b v) :
    ∃ v', a = .inp b v' := by
  obtain ⟨c, x, y, hax, hbv⟩ := hdet.inputs h1 h2 hne
  injection hbv with hc hv
  exact ⟨x, by rw [hax, hc]⟩

theorem det_out_first (hdet : Deterministic step) {s s' s'' : St} {α : C} {v : V}
    {a : Act C V} (h1 : step s (.out α v) s') (h2 : step s a s'') :
    a = .out α v ∧ s'' = s' := by
  by_cases h : a = .out α v
  · exact ⟨h, by subst h; exact hdet.target h2 h1⟩
  · exfalso
    obtain ⟨c, x, y, hax, hbv⟩ := hdet.inputs h2 h1 (fun hc => h hc)
    exact absurd hbv (by simp)

theorem det_tau_first (hdet : Deterministic step) {s s' s'' : St} {a : Act C V}
    (h1 : step s .tau s') (h2 : step s a s'') : a = .tau ∧ s'' = s' := by
  by_cases h : a = .tau
  · exact ⟨h, by subst h; exact hdet.target h2 h1⟩
  · exfalso
    obtain ⟨c, x, y, hax, hbv⟩ := hdet.inputs h2 h1 (fun hc => h hc)
    exact absurd hbv (by simp)

theorem det_inp_first (hdet : Deterministic step) {s s' s'' : St} {α : C} {v : V}
    {a : Act C V} (h1 : step s (.inp α v) s') (h2 : step s a s'') :
    ∃ v', a = .inp α v' := by
  by_cases h : a = .inp α v
  · exact ⟨v, h⟩
  · obtain ⟨c, x, y, hax, hbv⟩ := hdet.inputs h2 h1 (fun hc => h hc)
    injection hbv with hc hv
    exact ⟨x, by rw [hax, hc]⟩

end Det

namespace Sec

variable {Level Channel Value : Type} {S : Sec Level Channel}

/-! ### Prepending a fixed prefix to a strategy -/

/-- `prependStrat u ω` is `ω` with the history `u` already played. -/
def prependStrat (u : List (Lbl Channel Value)) (w : S.Strategy Value) :
    S.Strategy Value where
  ω := fun b t => w.ω b (u ++ t)
  resp_val := by
    intro b t₁ t₂ ht
    refine w.resp_val b _ _ ?_
    unfold teq at *; rw [proj_append, proj_append, ht]
  resp_pres := by
    intro b t₁ t₂ ht
    refine w.resp_pres b _ _ ?_
    unfold teq at *; rw [proj_append, proj_append, ht]

@[simp] theorem prependStrat_apply {u : List (Lbl Channel Value)} {w : S.Strategy Value}
    (b : Channel) (t : List (Lbl Channel Value)) :
    (prependStrat u w).ω b t = w.ω b (u ++ t) := rfl

theorem teq_append {ℓ : Level} {u u' r r' : List (Lbl Channel Value)}
    (hu : S.teq ℓ u u') (hr : S.teq ℓ r r') : S.teq ℓ (u ++ r) (u' ++ r') := by
  unfold teq at *; rw [proj_append, proj_append, hu, hr]

/-- ℓ-equivalent prefixes give ℓ-equivalent prepended strategies. -/
theorem seq_prependStrat {ℓ : Level} {u u' : List (Lbl Channel Value)}
    {w₁ w₂ : S.Strategy Value} (hww : S.seq ℓ w₁ w₂) (hu : S.teq ℓ u u') :
    S.seq ℓ (prependStrat u w₁) (prependStrat u' w₂) := by
  intro b t
  constructor
  · intro hbl
    have h1 : w₁.ω b (u ++ t) = w₁.ω b (u' ++ t) :=
      w₁.resp_val b _ _ (teq_mono hbl (teq_append hu (rfl : S.teq ℓ t t)))
    rw [prependStrat_apply, prependStrat_apply, h1]
    exact (hww b _).1 hbl
  · intro hbl
    have h1 : dotEq (w₁.ω b (u ++ t)) (w₁.ω b (u' ++ t)) :=
      w₁.resp_pres b _ _ (teq_mono hbl (teq_append hu (rfl : S.teq ℓ t t)))
    rw [prependStrat_apply, prependStrat_apply]
    exact h1.trans ((hww b _).2 hbl)

/-! ### Consistency and concatenation -/

theorem consistent_nil (w : S.Strategy Value) : S.consistent w [] := by
  rintro t₁ a v t₂ heq
  exact absurd heq.symm (by simp [List.append_eq_nil_iff])

theorem consistent_of_cons {w : S.Strategy Value} {l : Lbl Channel Value}
    {t : List (Lbl Channel Value)} (hc : S.consistent w (l :: t)) :
    S.consistent (prependStrat [l] w) t := by
  rintro t₁ a v t₂ rfl
  exact hc (l :: t₁) a v t₂ rfl

theorem consistent_head {w : S.Strategy Value} {a : Channel} {v : Value}
    {t : List (Lbl Channel Value)} (hc : S.consistent w (.inp a v :: t)) :
    w.ω a [] v := hc [] a v t rfl

theorem consistent_append {w : S.Strategy Value} {u r : List (Lbl Channel Value)}
    (hu : S.consistent w u) (hr : S.consistent (prependStrat u w) r) :
    S.consistent w (u ++ r) := by
  rintro t₁ a v t₂ heq
  rcases (List.append_eq_append_iff.mp heq) with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
  · -- t₁ = u ++ c, r = c ++ (α?v . t₂)
    subst hc1
    have := hr c a v t₂ hc2
    rwa [prependStrat_apply] at this
  · -- u = t₁ ++ c, α?v . t₂ = c ++ r
    cases c with
    | nil =>
        have hu' : u = t₁ := by simpa using hc1
        have hr' : r = .inp a v :: t₂ := by simpa using hc2.symm
        have := hr [] a v t₂ (by rw [hr']; rfl)
        rw [prependStrat_apply] at this
        rw [← hu']
        simpa using this
    | cons x c₀ =>
        have hx : x = .inp a v := by
          injection hc2 with h1 h2
          exact h1.symm
        subst hx
        exact hu t₁ a v c₀ hc1

/-! ### Lemma F: a run compatible with `unshift u ω` follows the execution `u` -/

theorem follow {St : Type} {step : St → Act Channel Value → St → Prop}
    (hdet : Deterministic step) {s s'' : St} {u : List (Lbl Channel Value)}
    (hr : Reach step s u s'') :
    ∀ {w : S.Strategy Value} {r : List (Lbl Channel Value)} {s₂ : St},
      Reach step s r s₂ → S.consistent (S.unshift u w) r →
      (∃ rest, u = r ++ rest) ∨ (∃ r₂, r = u ++ r₂ ∧ S.produces step w s'' r₂) := by
  induction hr with
  | @nil s =>
      intro w r s₂ hrr hc
      exact Or.inr ⟨r, by simp, ⟨⟨s₂, hrr⟩, by simpa using hc⟩⟩
  | @tau s s₁ s'' u hs _ ih =>
      intro w r s₂ hrr hc
      cases hrr with
      | nil => exact Or.inl ⟨u, rfl⟩
      | @tau _ s₃ _ _ h1 h2 =>
          have : s₃ = s₁ := hdet.target h1 hs
          subst this
          exact ih h2 hc
      | inp h1 h2 => exact absurd (det_tau_first hdet hs h1).1 (by simp)
      | out h1 h2 => exact absurd (det_tau_first hdet hs h1).1 (by simp)
  | @inp s s₁ s'' a v u₀ hs _ ih =>
      intro w r s₂ hrr hc
      cases hrr with
      | nil => exact Or.inl ⟨_, rfl⟩
      | tau h1 h2 => exact absurd (det_tau_first hdet h1 hs).1 (by simp)
      | out h1 h2 =>
          obtain ⟨v', hv'⟩ := det_inp_first hdet hs h1
          exact absurd hv' (by simp)
      | @inp _ s₃ _ b w' r₀ h1 h2 =>
          obtain ⟨v', hv'⟩ := det_inp_first hdet hs h1
          injection hv' with hb hv2
          subst hb
          rw [unshift_cons] at hc
          have hdv : dOf (Lbl.inp b v) w' := head_of_cons_shift (a := b) hc
          have hw'v : w' = v := dOf_inp_iff.mp hdv
          subst hw'v
          have hs3 : s₃ = s₁ := hdet.target h1 hs
          subst hs3
          have hc' : S.consistent (S.unshift u₀ w) r₀ :=
            consistent_of_cons_shift (l := Lbl.inp b w') rfl hc
          rcases ih h2 hc' with ⟨rest, hrest⟩ | ⟨r₂, hr₂, hp⟩
          · exact Or.inl ⟨rest, by rw [hrest, List.cons_append]⟩
          · exact Or.inr ⟨r₂, by rw [hr₂, List.cons_append], hp⟩
  | @out s s₁ s'' a v u₀ hs _ ih =>
      intro w r s₂ hrr hc
      cases hrr with
      | nil => exact Or.inl ⟨_, rfl⟩
      | tau h1 h2 => exact absurd (det_out_first hdet hs h1).1 (by simp)
      | inp h1 h2 => exact absurd (det_out_first hdet hs h1).1 (by simp)
      | @out _ s₃ _ b w' r₀ h1 h2 =>
          obtain ⟨heq, hst⟩ := det_out_first hdet hs h1
          injection heq with hb hv
          subst hb; subst hv; subst hst
          rw [unshift_cons] at hc
          have hc' : S.consistent (S.unshift u₀ w) r₀ :=
            consistent_of_cons_shift (l := Lbl.out b w') rfl hc
          rcases ih h2 hc' with ⟨rest, hrest⟩ | ⟨r₂, hr₂, hp⟩
          · exact Or.inl ⟨rest, by rw [hrest, List.cons_append]⟩
          · exact Or.inr ⟨r₂, by rw [hr₂, List.cons_append], hp⟩

/-! ### Lemma 5 (indistinguishable states produce indistinguishable runs) -/

/--
**Lemma 5** of the paper.  If `s ⟶^t sC` and `s ⟶^{t'} sE` with `t =_ℓ t'`, then
any run of `sC` under `ω₁` is matched, up to ℓ-equivalence, by a run of `sE`
under any ℓ-equivalent `ω₂`.
-/
theorem indistinguishable_NI {St : Type} {step : St → Act Channel Value → St → Prop}
    (hdet : Deterministic step) {sA sC sE : St} {ℓ : Level}
    {w₁ w₂ : S.Strategy Value} {t t' t₁ : List (Lbl Channel Value)}
    (hNI : S.StratNI step sA)
    (hC : Reach step sA t sC) (hE : Reach step sA t' sE)
    (hrun : S.produces step w₁ sC t₁)
    (htt : S.teq ℓ t t') (hww : S.seq ℓ w₁ w₂) :
    ∃ (t₂ : List (Lbl Channel Value)) (sE' : St),
      Reach step sE t₂ sE' ∧ S.consistent w₂ t₂ ∧ S.teq ℓ t₁ t₂ := by
  have hseq : S.seq ℓ (S.unshift t w₁) (S.unshift t' w₂) := seq_unshift' hww htt
  have hprod : S.produces step (S.unshift t w₁) sA (t ++ t₁) := produces_unshift hC hrun
  obtain ⟨t₂z, ⟨⟨s₂, hreach⟩, hcons⟩, hteq⟩ :=
    hNI ℓ _ _ trivial trivial hseq (t ++ t₁) hprod
  rcases follow hdet hE hreach hcons with ⟨rest, hrest⟩ | ⟨t₂, ht₂, ⟨⟨sE', hE'⟩, hc₂⟩⟩
  · -- the matching run stops inside `t'`: then `t₁` is ℓ-invisible
    refine ⟨[], sE, Reach.nil, consistent_nil _, ?_⟩
    have h1 : S.proj ℓ t' = S.proj ℓ t₂z ++ S.proj ℓ rest := by
      rw [hrest, proj_append]
    have h2 : S.proj ℓ t₂z = S.proj ℓ t ++ S.proj ℓ t₁ := by
      unfold teq at hteq; rw [← hteq, proj_append]
    have h3 : S.proj ℓ t ++ (S.proj ℓ t₁ ++ S.proj ℓ rest) = S.proj ℓ t := by
      rw [← List.append_assoc, ← h2, ← h1]; exact htt.symm
    have h4 : S.proj ℓ t₁ = [] ∧ S.proj ℓ rest = [] := by simpa using h3
    unfold teq
    rw [h4.1, proj_nil]
  · -- the matching run goes past `t'`
    refine ⟨t₂, sE', hE', hc₂, ?_⟩
    unfold teq at *
    rw [ht₂, proj_append, proj_append] at hteq
    rw [← htt] at hteq
    exact List.append_cancel_left hteq


/-! ### Helpers for building and matching concrete runs -/

/-- Matching an input offered by `ω₁` with one offered by an ℓ-equivalent `ω₂`. -/
theorem match_input {ℓ : Level} {a : Channel} {w₁ w₂ : S.Strategy Value}
    (hww : S.seq ℓ w₁ w₂) (hpres : S.le (S.presL a) ℓ)
    {u₁ u₂ : List (Lbl Channel Value)} (hu : S.teq (S.valL a) u₁ u₂)
    {v : Value} (hv : w₁.ω a u₁ v) :
    ∃ v₂, w₂.ω a u₂ v₂ ∧ (S.le (S.valL a) ℓ → v₂ = v) := by
  have h1 : w₁.ω a u₁ = w₁.ω a u₂ := w₁.resp_val a _ _ hu
  rw [h1] at hv
  by_cases hvis : S.le (S.valL a) ℓ
  · refine ⟨v, ?_, fun _ => rfl⟩
    rw [← (hww a u₂).1 hvis]; exact hv
  · obtain ⟨v₂, hv₂⟩ := ((hww a u₂).2 hpres).exists hv
    exact ⟨v₂, hv₂, fun h => absurd h hvis⟩

theorem consistent_cons_out {w : S.Strategy Value} {a : Channel} {v : Value}
    {t : List (Lbl Channel Value)}
    (hc : S.consistent (prependStrat [Lbl.out a v] w) t) :
    S.consistent w (.out a v :: t) := by
  rintro t₁ b u t₂ heq
  cases t₁ with
  | nil => rw [List.nil_append] at heq; injection heq with h1 h2; exact absurd h1 (by simp)
  | cons x xs =>
      rw [List.cons_append] at heq
      injection heq with h1 h2
      subst h1
      have := hc xs b u t₂ h2
      rwa [prependStrat_apply] at this

theorem consistent_cons_inp {w : S.Strategy Value} {a : Channel} {v : Value}
    {t : List (Lbl Channel Value)} (hh : w.ω a [] v)
    (hc : S.consistent (prependStrat [Lbl.inp a v] w) t) :
    S.consistent w (.inp a v :: t) := by
  rintro t₁ b u t₂ heq
  cases t₁ with
  | nil =>
      rw [List.nil_append] at heq
      injection heq with h1 h2
      injection h1 with hb hv
      subst hb; subst hv; exact hh
  | cons x xs =>
      rw [List.cons_append] at heq
      injection heq with h1 h2
      subst h1
      have := hc xs b u t₂ h2
      rwa [prependStrat_apply] at this

/-- **Lemma 4** of the paper: NI is preserved by a single transition. -/
theorem deterministic_step {St : Type} {step : St → Act Channel Value → St → Prop}
    (hdet : Deterministic step) {s s' : St} {e : Act Channel Value}
    (hNI : S.StratNI step s) (hstep : step s e s') :
    S.StratNI step s' := by
  intro ℓ w₁ w₂ _ _ hww t₁ hrun
  have hreach : ∃ u, Reach step s u s' ∧ S.teq ℓ u u := by
    cases e with
    | tau => exact ⟨[], Reach.tau hstep Reach.nil, rfl⟩
    | inp a v => exact ⟨[.inp a v], Reach.inp hstep Reach.nil, rfl⟩
    | out a v => exact ⟨[.out a v], Reach.out hstep Reach.nil, rfl⟩
  obtain ⟨u, hu, huu⟩ := hreach
  obtain ⟨t₂, s₂, hr₂, hc₂, ht₂⟩ :=
    indistinguishable_NI hdet hNI hu hu hrun huu hww
  exact ⟨t₂, ⟨⟨s₂, hr₂⟩, hc₂⟩, ht₂⟩

end Sec

end InteractiveNI
