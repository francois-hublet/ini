/-
  **The layer game.**

  What is missing for compositionality of coalition noninterference over an
  arbitrary lattice is a *causal policy* for each component at a layer of the
  peeling of `Layered.lean`.  This file builds the game that supplies it.

  Two design points make it tractable, and both come from the layer structure.

  * The game runs over **reduced** traces -- pairs (`C`-view, `n`-view) of a run --
    so the subset construction disappears: a component's choices that neither the
    observer nor the adversary can see are already abstracted away by the
    projections, and `Sec.replayStrat` says such choices may be treated as the
    component's own.  Every channel visible at the layer `C ∪ {n}` is visible at
    `C` or at `n`, so the pair carries the whole layer view.
  * A position is the `n`-view, which is exactly the adversary's information.  The
    channels a layer exposes all carry the level `n` (`Sec.layer_flat`), so a
    `π_n`-measurable answer *is* a legal strategy for them.  This replaces the
    `Omniscient` hypothesis of an earlier version of the game, which assumed the users of the
    invisible channels see everything.
-/
import InteractiveNI.Layered

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

/-! ### A list lemma -/

namespace Sec

variable {Level Channel Value : Type} {S : Sec Level Channel}

/-! ### Reduced systems as sets of view pairs -/

/-- The pairs (`C`-view, `n`-view) of the runs of a component. -/
def RedPair (S : Sec Level Channel) {St : Type}
    (step : St → Act Channel Value → St → Prop) (s : St) (C n : Level)
    (dc dn : List (PLbl Channel Value)) : Prop :=
  ∃ (t : List (Lbl Channel Value)) (s' : St),
    Reach step s t s' ∧ S.proj C t = dc ∧ S.proj n t = dn


/-! ### The game is won: from noninterference to `Forced2`

    The adversary is a function of the `n`-view; since the channels it controls
    carry the level `n`, that function *is* a legal strategy.  This is the step
    that needed `Omniscient` there. -/

/-- The strategy the component faces: `w` on the channels the coalition sees, the
    adversary's `π_n`-measurable choice on `N`, and anything elsewhere. -/
noncomputable def advStratL (S : Sec Level Channel) (C n : Level) (N : Channel → Prop)
    (hNn : ∀ a : Channel, N a → S.le n (S.valL a))
    (w : S.Strategy Value) (adv : Channel → List (PLbl Channel Value) → Value) :
    S.Strategy Value where
  ω := fun a t =>
    if S.le (S.valL a) C then w.ω a t
    else if N a then (fun v => v = adv a (S.proj n t))
    else (fun _ => True)
  resp_val := by
    intro a t₁ t₂ h
    by_cases hC : S.le (S.valL a) C
    · simp only [if_pos hC]; exact w.resp_val a t₁ t₂ h
    · simp only [if_neg hC]
      by_cases hN : N a
      · simp only [if_pos hN]
        have : S.proj n t₁ = S.proj n t₂ := teq_mono (hNn a hN) h
        rw [this]
      · simp only [if_neg hN]
  resp_pres := by
    intro a t₁ t₂ h
    by_cases hC : S.le (S.valL a) C
    · simp only [if_pos hC]; exact w.resp_pres a t₁ t₂ h
    · simp only [if_neg hC]
      by_cases hN : N a
      · simp only [if_pos hN]
        exact ⟨fun hx => absurd rfl (hx _), fun hx => absurd rfl (hx _)⟩
      · simp only [if_neg hN]
        exact dotEq.refl _

/-- The adversary's strategy is total when the component's is: it answers with `w`
    on the visible channels, a single value on `N`, and anything elsewhere. -/
theorem advStratL_total {C n : Level} {N : Channel → Prop}
    (hNn : ∀ a : Channel, N a → S.le n (S.valL a))
    {w : S.Strategy Value} (htot : w.total)
    (adv : Channel → List (PLbl Channel Value) → Value) :
    (advStratL S C n N hNn w adv).total := by
  intro a t
  by_cases hC : S.le (S.valL a) C
  · exact ⟨(htot a t).choose, by
      simp only [advStratL, if_pos hC]; exact (htot a t).choose_spec⟩
  · by_cases hN : N a
    · refine ⟨adv a (S.proj n t), ?_⟩
      simp only [advStratL, if_neg hC, if_pos hN]
    · refine ⟨adv a (S.proj n t), ?_⟩
      simp only [advStratL, if_neg hC, if_neg hN]

theorem seq_advStratL {C n : Level} {N : Channel → Prop}
    (hNn : ∀ a : Channel, N a → S.le n (S.valL a))
    {w : S.Strategy Value} (htot : w.total)
    (adv : Channel → List (PLbl Channel Value) → Value) :
    S.seq C w (advStratL S C n N hNn w adv) := by
  intro a t
  refine ⟨fun hC => ?_, fun _ => ?_⟩
  · simp only [advStratL, if_pos hC]
  · by_cases hC : S.le (S.valL a) C
    · simp only [advStratL, if_pos hC]; exact dotEq.refl _
    · by_cases hN : N a
      · simp only [advStratL, if_neg hC, if_pos hN]
        exact dotEq_of_total (htot a t) ⟨adv a (S.proj n t), rfl⟩
      · simp only [advStratL, if_neg hC, if_neg hN]
        exact dotEq_of_total (htot a t) ⟨adv a (S.proj n t), trivial⟩

/-! ### The oracle

    On a channel a layer exposes, the environment's answer depends only on the
    `n`-view, so it can be read off a view rather than a trace. -/

/-- The value `w` offers on `a` at any trace with the given `n`-view. -/
noncomputable def oracleV (S : Sec Level Channel) (n : Level) (w : S.Strategy Value)
    (dflt : Value) (a : Channel) (dn : List (PLbl Channel Value)) : Value :=
  @Classical.epsilon _ ⟨dflt⟩ (fun v => ∀ t, S.proj n t = dn → w.ω a t v)

theorem oracleV_spec {n : Level} {w : S.Strategy Value} (dflt : Value)
    (htot : w.total) {a : Channel} (hNn' : S.le (S.valL a) n)
    {dn : List (PLbl Channel Value)} {t₀ : List (Lbl Channel Value)}
    (h₀ : S.proj n t₀ = dn) :
    ∀ t, S.proj n t = dn → w.ω a t (oracleV S n w dflt a dn) := by
  have hex : ∃ v, ∀ t, S.proj n t = dn → w.ω a t v := by
    obtain ⟨v, hv⟩ := htot a t₀
    refine ⟨v, fun t ht => ?_⟩
    have hteq : S.teq (S.valL a) t t₀ := teq_mono hNn' (by unfold Sec.teq; rw [ht, h₀])
    rw [w.resp_val a t t₀ hteq]
    exact hv
  unfold oracleV
  exact Classical.epsilon_spec hex

/-! ### Assembling the layer step -/

theorem projL_inp_hidden' {ℓ : Level} {a : Channel} {v : Value}
    (hv : ¬ S.le (S.valL a) ℓ) : S.projL ℓ (Lbl.inp a v) = PLbl.inp a none := by
  simp only [projL]; rw [if_neg hv]

/-- The empty coalition observes nothing, not even presence. -/
theorem proj_empty_coalition {S : Sec Level Channel} {C : Coalition Level}
    (hC : ¬ ∃ d, C d) (t : List (Lbl Channel Value)) :
    S.coalition.proj C t = [] := by
  induction t with
  | nil => rfl
  | cons l t ih =>
      refine Eq.trans (Sec.proj_cons_none ?_ t) ih
      rw [Sec.projLbl_eq_none_iff]
      intro h
      exact hC (by obtain ⟨d, hd, -⟩ := h (S.presL (l.chan)) rfl; exact ⟨d, hd⟩)

/-! ### The non-total case

    Section 3.1 works with `Strat`, all strategies, which may block.  That case
    follows from the total one.  Totalise both strategies -- offering a default
    value where they offer none -- apply the total theorem, and observe that the
    run it returns never uses a default: whether a strategy blocks on a channel
    depends only on the *shape* of the trace (presence visible at `C`), `≐`-equivalent
    strategies block on the same shapes, and the run has the same shape as the one
    we started from, at whose inputs the original strategy did offer a value. -/

theorem projL_out_ne_inp {ℓ : Level} {b a : Channel} {x v : Value} :
    S.projL ℓ (Lbl.out b x) ≠ S.projL ℓ (Lbl.inp a v) := by
  by_cases h1 : S.le (S.valL b) ℓ <;> by_cases h2 : S.le (S.valL a) ℓ <;>
    simp [projL, h1, h2]

/-- Totalising a strategy: offer `dflt` where it offers nothing. -/
noncomputable def totalize (S : Sec Level Channel) (dflt : Value)
    (w : S.Strategy Value) : S.Strategy Value where
  ω := fun a t v => w.ω a t v ∨ ((∀ v', ¬ w.ω a t v') ∧ v = dflt)
  resp_val := by
    intro a t₁ t₂ h
    rw [w.resp_val a t₁ t₂ h]
  resp_pres := by
    intro a t₁ t₂ _
    have key : ∀ t : List (Lbl Channel Value),
        ¬ (∀ v : Value, ¬ (w.ω a t v ∨ ((∀ v', ¬ w.ω a t v') ∧ v = dflt))) := by
      intro t hemp
      by_cases hex : ∃ v, w.ω a t v
      · obtain ⟨v, hv⟩ := hex; exact hemp v (Or.inl hv)
      · exact hemp dflt (Or.inr ⟨fun v hv => hex ⟨v, hv⟩, rfl⟩)
    exact ⟨fun h => absurd h (key t₁), fun h => absurd h (key t₂)⟩

theorem totalize_total (dflt : Value) (w : S.Strategy Value) :
    (totalize S dflt w).total := by
  intro a t
  by_cases hex : ∃ v, w.ω a t v
  · obtain ⟨v, hv⟩ := hex; exact ⟨v, Or.inl hv⟩
  · exact ⟨dflt, Or.inr ⟨fun v hv => hex ⟨v, hv⟩, rfl⟩⟩

theorem consistent_totalize {dflt : Value} {w : S.Strategy Value}
    {t : List (Lbl Channel Value)} (h : S.consistent w t) :
    S.consistent (totalize S dflt w) t :=
  fun t₁ a v t₂ heq => Or.inl (h t₁ a v t₂ heq)

theorem produces_totalize {St : Type} {step : St → Act Channel Value → St → Prop}
    {s : St} {dflt : Value} {w : S.Strategy Value} {t : List (Lbl Channel Value)}
    (h : S.produces step w s t) : S.produces step (totalize S dflt w) s t :=
  ⟨h.1, consistent_totalize h.2⟩

theorem seq_totalize {ℓ : Level} (dflt : Value) (hpres : ∀ a : Channel, S.le (S.presL a) ℓ)
    {w₁ w₂ : S.Strategy Value} (h : S.seq ℓ w₁ w₂) :
    S.seq ℓ (totalize S dflt w₁) (totalize S dflt w₂) := by
  intro a t
  refine ⟨fun hvis => ?_, fun _ => ?_⟩
  · show (fun v => w₁.ω a t v ∨ _) = (fun v => w₂.ω a t v ∨ _)
    rw [(h a t).1 hvis]
  · exact dotEq_of_total (totalize_total dflt w₁ a t) (totalize_total dflt w₂ a t)

/-- **The run returned by the total theorem is a run of the original strategy.**
    A blocked input would force the same input to be blocked on the trace we
    started from, where it was not. -/
theorem consistent_of_totalize {C : Coalition Level}
    (hpub : S.coalition.PubAt C) {dflt : Value}
    {w₁ w₂ : S.coalition.Strategy Value} (hseq : S.coalition.seq C w₁ w₂)
    {t₁ t₂ : List (Lbl Channel Value)}
    (hc₁ : S.coalition.consistent w₁ t₁) (hteq : S.coalition.teq C t₁ t₂)
    (hc₂ : S.coalition.consistent (totalize S.coalition dflt w₂) t₂) :
    S.coalition.consistent w₂ t₂ := by
  intro u a v r heq
  rcases hc₂ u a v r heq with hv | ⟨hempty, -⟩
  · exact hv
  exfalso
  -- locate the corresponding input in `t₁`
  have hsplit : S.coalition.proj C t₁
      = S.coalition.proj C u ++ S.coalition.projL C (Lbl.inp a v) :: S.coalition.proj C r := by
    rw [hteq, heq, proj_append, proj_cons_some (projLbl_eq_projL_at hpub _)]
  obtain ⟨u₁, l₁, r₁, hdec, hu₁, hl₁⟩ := proj_split hpub hsplit
  have hchan : ∃ v₁, l₁ = Lbl.inp a v₁ := by
    cases l₁ with
    | inp b x =>
        by_cases hb : S.coalition.le (S.coalition.valL b) C
        · rw [projL_inp_vis hb] at hl₁
          by_cases ha : S.coalition.le (S.coalition.valL a) C
          · rw [projL_inp_vis ha] at hl₁
            injection hl₁ with hb' hx
            exact ⟨x, by rw [hb']⟩
          · rw [projL_inp_hidden' ha] at hl₁
            injection hl₁ with hb' hx
            exact absurd hx (by simp)
        · rw [projL_inp_hidden' hb] at hl₁
          by_cases ha : S.coalition.le (S.coalition.valL a) C
          · rw [projL_inp_vis ha] at hl₁
            injection hl₁ with hb' hx
            exact absurd hx.symm (by simp)
          · rw [projL_inp_hidden' ha] at hl₁
            injection hl₁ with hb' hx
            exact ⟨x, by rw [hb']⟩
    | out b x => exact absurd hl₁ projL_out_ne_inp
  obtain ⟨v₁, rfl⟩ := hchan
  -- the original strategy was not blocked there
  have hne₁ : w₁.ω a u₁ v₁ := hc₁ u₁ a v₁ r₁ hdec
  have hteqp : S.coalition.teq (S.coalition.presL a) u u₁ :=
    teq_mono (hpub a) (by unfold Sec.teq; rw [hu₁])
  have hdot : dotEq (w₁.ω a u) (w₁.ω a u₁) := w₁.resp_pres a u u₁ hteqp
  have hne : ¬ (w₁.ω a u).isEmpty := by
    intro hemp
    exact (hdot.mp hemp) v₁ hne₁
  exact hne ((hseq a u).2 (hpub a) |>.mpr hempty)

end Sec

end InteractiveNI
