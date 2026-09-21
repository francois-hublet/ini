/-
  The game behind Lemma (★) of `two-point-proof.md`.

  `B` plays against the user of the ℓ-invisible channels.  In the two-point
  lattice that user sees the whole trace, so the game has perfect information and
  bounded depth (the target ℓ-view fixes the shape), hence is determined.  This
  file sets up the game and extracts a policy from a winning position; the
  determinacy step itself is `canWin_of_INI`.

  Positions are (set of component states consistent with the play so far,
  remaining target).  The *set* is the subset construction: it defers the
  component's internal choices, which is what makes
  `(x:=0|x:=1); in_H(y); out_L(x⊕y)` -- noninterfering but with no policy
  choosing `x` up front -- harmless.
-/
import InteractiveNI.TwoPoint

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

namespace Sec

variable {Level Channel Value : Type} {S : Sec Level Channel}

/-- States reachable from `S` by ℓ-invisible internal steps. -/
def TauClose {St : Type} (step : St → Act Channel Value → St → Prop)
    (P : St → Prop) : St → Prop :=
  fun s' => ∃ s, P s ∧ Reach step s [] s'

theorem tauClose_mono {St : Type} {step : St → Act Channel Value → St → Prop}
    {P Q : St → Prop} (h : ∀ s, P s → Q s) : ∀ s, TauClose step P s → TauClose step Q s := by
  rintro s ⟨s₀, hs₀, hr⟩
  exact ⟨s₀, h s₀ hs₀, hr⟩

/-- The successor set after a visible label. -/
def stepSet {St : Type} (step : St → Act Channel Value → St → Prop)
    (P : St → Prop) (l : Lbl Channel Value) : St → Prop :=
  fun s' => ∃ s, TauClose step P s ∧ step s l.act s'

/-- `CanWin env tgt P` : from the state set `P`, the component can force a run
    whose ℓ-view is exactly `tgt`.  At an ℓ-invisible input the environment
    chooses the value (universal); everywhere else the component chooses
    (existential).  `env a t v` says the environment may offer `v` on `a`. -/
def CanWin (S : Sec Level Channel) {St : Type} (step : St → Act Channel Value → St → Prop)
    (ℓ : Level)
    -- `env` fixes the offers on ℓ-*visible* channels only; on ℓ-invisible ones the
    -- adversary is unconstrained, which is what makes it as strong as any legal
    -- strategy in the two-point lattice.
    (env : Channel → List (Lbl Channel Value) → Value → Prop) :
    List (PLbl Channel Value) → (St → Prop) → List (Lbl Channel Value) → Prop
  | [], _, _ => True
  | .out a ov :: rest, P, hist =>
      ∃ v : Value, S.projLbl ℓ (Lbl.out a v) = some (.out a ov) ∧
        (∃ s, stepSet step P (.out a v) s) ∧
        CanWin S step ℓ env rest (stepSet step P (.out a v)) (hist ++ [.out a v])
  | .inp a ov :: rest, P, hist =>
      if S.le (S.valL a) ℓ then
        -- the value is ℓ-visible, hence fixed by the target, and the environment
        -- must offer it
        ∃ v : Value, S.projLbl ℓ (Lbl.inp a v) = some (.inp a ov) ∧ env a hist v ∧
          (∃ s, stepSet step P (.inp a v) s) ∧
          CanWin S step ℓ env rest (stepSet step P (.inp a v)) (hist ++ [.inp a v])
      else
        -- ℓ-invisible: the value is hidden in the target, and the adversary picks
        -- *any* value, which the component must both receive and survive
        ov = none ∧ ∀ v : Value,
          (∃ s, stepSet step P (.inp a v) s) ∧
          CanWin S step ℓ env rest (stepSet step P (.inp a v)) (hist ++ [.inp a v])

/-- **Soundness of the game.**  A winning position yields, against *every*
    adversary, an actual run of the component whose ℓ-view is the target, whose
    ℓ-visible inputs are offered by `env`, and whose ℓ-invisible inputs are the
    adversary's choices.  This is what turns a winning strategy into the policy
    of Lemma (★). -/
theorem canWin_sound {St : Type} {step : St → Act Channel Value → St → Prop}
    {ℓ : Level} {env : Channel → List (Lbl Channel Value) → Value → Prop}
    (hpub : PublicPresence S) :
    ∀ (adv : Channel → List (Lbl Channel Value) → Value),
    ∀ (tgt : List (PLbl Channel Value)) (P : St → Prop) (_hP : ∃ s, P s)
      (hist : List (Lbl Channel Value)),
      CanWin S step ℓ env tgt P hist →
      ∃ t : List (Lbl Channel Value),
        S.proj ℓ t = tgt ∧
        (∃ s₀ s, TauClose step P s₀ ∧ Reach step s₀ t s) ∧
        (∀ pre a v post, t = pre ++ .inp a v :: post →
          (S.le (S.valL a) ℓ → env a (hist ++ pre) v) ∧
          (¬ S.le (S.valL a) ℓ → v = adv a pre)) := by
  intro adv tgt
  induction tgt generalizing adv with
  | nil =>
      rintro P ⟨s, hs⟩ hist _
      refine ⟨[], rfl, ⟨s, s, ⟨s, hs, Reach.nil⟩, Reach.nil⟩, ?_⟩
      intro pre a v post heq
      exact absurd heq.symm (by simp [List.append_eq_nil_iff])
  | cons l rest ih =>
      intro P hP hist h
      -- a common continuation step
      have key : ∀ (x : Lbl Channel Value),
          S.projLbl ℓ x = some l →
          (∃ s, stepSet step P x s) →
          CanWin S step ℓ env rest (stepSet step P x) (hist ++ [x]) →
          ∃ t : List (Lbl Channel Value),
            S.proj ℓ t = l :: rest ∧
            (∃ s₀ s, TauClose step P s₀ ∧ Reach step s₀ t s) ∧
            (∀ pre a v post, t = pre ++ .inp a v :: post →
              ((S.le (S.valL a) ℓ → env a (hist ++ pre) v) ∧
               (¬ S.le (S.valL a) ℓ → v = adv a pre)) ∨
              (pre = [] ∧ x = .inp a v)) := by
        intro x hx hne hcw
        obtain ⟨t', hproj', ⟨s₀', s', hTC', hR'⟩, hinp'⟩ :=
          ih (fun a' p => adv a' (x :: p)) _ hne _ hcw
        obtain ⟨s₁, hs₁, hr₁⟩ := hTC'
        obtain ⟨s₂, hs₂, hstep₂⟩ := hs₁
        refine ⟨x :: t', ?_, ⟨s₂, s', hs₂, ?_⟩, ?_⟩
        · rw [proj_cons_some hx, hproj']
        · have : Reach step s₁ t' s' := by
            have := Reach.trans hr₁ hR'
            rwa [List.nil_append] at this
          cases x with
          | inp c w => exact Reach.inp hstep₂ this
          | out c w => exact Reach.out hstep₂ this
        · intro pre a v post heq
          cases pre with
          | nil =>
              right
              rw [List.nil_append] at heq
              injection heq with h1 _
              exact ⟨rfl, h1⟩
          | cons y pre' =>
              left
              rw [List.cons_append] at heq
              injection heq with h1 h2
              subst h1
              have := hinp' pre' a v post h2
              simpa [List.append_assoc] using this
      cases l with
      | out a ov =>
          obtain ⟨v, hx, hne, hcw⟩ := h
          obtain ⟨t, hp, hr, hi⟩ := key (.out a v) hx hne hcw
          refine ⟨t, hp, hr, ?_⟩
          intro pre a' v' post heq
          rcases hi pre a' v' post heq with hgood | ⟨_, hbad⟩
          · exact hgood
          · exact absurd hbad (by simp)
      | inp a ov =>
          by_cases hl : S.le (S.valL a) ℓ
          · rw [CanWin, if_pos hl] at h
            obtain ⟨v, hx, henv, hne, hcw⟩ := h
            obtain ⟨t, hp, hr, hi⟩ := key (.inp a v) hx hne hcw
            refine ⟨t, hp, hr, ?_⟩
            intro pre a' v' post heq
            rcases hi pre a' v' post heq with hgood | ⟨hpre, hbad⟩
            · exact hgood
            · subst hpre
              injection hbad with h1 h2
              subst h1; subst h2
              exact ⟨fun _ => by rwa [List.append_nil], fun hc => absurd hl hc⟩
          · rw [CanWin, if_neg hl] at h
            obtain ⟨hov, h⟩ := h
            obtain ⟨hne, hcw⟩ := h (adv a [])
            have hx : S.projLbl ℓ (Lbl.inp a (adv a [])) = some (.inp a ov) := by
              rw [hov]; exact projLbl_inp_pres (hpub a ℓ) hl
            obtain ⟨t, hp, hr, hi⟩ := key (.inp a (adv a [])) hx hne hcw
            refine ⟨t, hp, hr, ?_⟩
            intro pre a' v' post heq
            rcases hi pre a' v' post heq with hgood | ⟨hpre, hbad⟩
            · exact hgood
            · subst hpre
              injection hbad with h1 h2
              subst h1; subst h2
              exact ⟨fun hc => absurd hc hl, fun _ => rfl⟩


/-- Inversion for `π_ℓ` on a cons, under public presence. -/
theorem proj_cons_inv {ℓ : Level} {x : Lbl Channel Value} {t : List (Lbl Channel Value)}
    {p : PLbl Channel Value} {rest : List (PLbl Channel Value)}
    (hpub : PublicPresence S) (h : S.proj ℓ (x :: t) = p :: rest) :
    S.projLbl ℓ x = some p ∧ S.proj ℓ t = rest := by
  rw [proj_cons_some (projLbl_eq_projL hpub ℓ x)] at h
  injection h with h1 h2
  exact ⟨by rw [projLbl_eq_projL hpub ℓ x, h1], h2⟩

/-- `Forced env tgt P hist`: against *every* adversary, some run from `P` realises
    the target.  This is the hypothesis `Strat-NI` supplies. -/
def Forced (S : Sec Level Channel) {St : Type} (step : St → Act Channel Value → St → Prop)
    (ℓ : Level) (env : Channel → List (Lbl Channel Value) → Value → Prop)
    (tgt : List (PLbl Channel Value)) (P : St → Prop)
    (hist : List (Lbl Channel Value)) : Prop :=
  ∀ adv : Channel → List (Lbl Channel Value) → Value,
    ∃ t : List (Lbl Channel Value),
      S.proj ℓ t = tgt ∧
      (∃ s₀ s, TauClose step P s₀ ∧ Reach step s₀ t s) ∧
      (∀ pre a v post, t = pre ++ .inp a v :: post →
        (S.le (S.valL a) ℓ → env a (hist ++ pre) v) ∧
        (¬ S.le (S.valL a) ℓ → v = adv a pre))

/-- One step of the decomposition: a `Forced` run of a nonempty target starts with
    a label projecting to the head, and its tail is a run from the successor set. -/
theorem forced_step {St : Type} {step : St → Act Channel Value → St → Prop}
    {ℓ : Level} {env : Channel → List (Lbl Channel Value) → Value → Prop}
    (hpub : PublicPresence S) {l : PLbl Channel Value} {rest : List (PLbl Channel Value)}
    {P : St → Prop} {hist : List (Lbl Channel Value)}
    (adv : Channel → List (Lbl Channel Value) → Value)
    (hF : Forced S step ℓ env (l :: rest) P hist) :
    ∃ x : Lbl Channel Value, S.projLbl ℓ x = some l ∧
      (∃ s, stepSet step P x s) ∧
      (∀ a v, x = .inp a v →
        (S.le (S.valL a) ℓ → env a hist v) ∧ (¬ S.le (S.valL a) ℓ → v = adv a [])) ∧
      ∃ t, S.proj ℓ t = rest ∧
        (∃ s₀ s, TauClose step (stepSet step P x) s₀ ∧ Reach step s₀ t s) ∧
        (∀ pre a v post, t = pre ++ .inp a v :: post →
          (S.le (S.valL a) ℓ → env a ((hist ++ [x]) ++ pre) v) ∧
          (¬ S.le (S.valL a) ℓ → v = adv a (x :: pre))) := by
  obtain ⟨t, hproj, ⟨s₀, s, hTC, hR⟩, hinp⟩ := hF adv
  cases t with
  | nil => exact absurd hproj (by simp [proj])
  | cons x t' =>
      obtain ⟨hx, hrest⟩ := proj_cons_inv hpub hproj
      obtain ⟨x₁, x₂, hsil, hstep, hR'⟩ := Reach.cons_inv hR
      refine ⟨x, hx, ⟨x₂, ⟨x₁, ?_, hstep⟩⟩, ?_, t', hrest, ⟨x₂, s, ⟨x₂, ⟨x₁, ?_, hstep⟩, Reach.nil⟩, hR'⟩, ?_⟩
      · obtain ⟨s₁, hs₁, hr₁⟩ := hTC
        exact ⟨s₁, hs₁, Reach.trans hr₁ hsil⟩
      · intro a v hxe
        subst hxe
        have := hinp [] a v t' rfl
        simpa using this
      · obtain ⟨s₁, hs₁, hr₁⟩ := hTC
        exact ⟨s₁, hs₁, Reach.trans hr₁ hsil⟩
      · intro pre a v post heq
        have := hinp (x :: pre) a v post (by rw [heq, List.cons_append])
        simpa [List.append_assoc] using this


theorem projL_inp_inv {ℓ : Level} {c a : Channel} {w : Value} {ov : Option Value}
    (h : S.projL ℓ (Lbl.inp c w) = PLbl.inp a ov) :
    c = a ∧ (if S.le (S.valL c) ℓ then some w else none) = ov := by
  simp only [projL] at h
  by_cases hv : S.le (S.valL c) ℓ
  · rw [if_pos hv] at h ⊢; injection h with h1 h2; exact ⟨h1, h2⟩
  · rw [if_neg hv] at h ⊢; injection h with h1 h2; exact ⟨h1, h2⟩

theorem projL_out_inv {ℓ : Level} {c a : Channel} {w : Value} {ov : Option Value}
    (h : S.projL ℓ (Lbl.out c w) = PLbl.out a ov) :
    c = a ∧ (if S.le (S.valL c) ℓ then some w else none) = ov := by
  simp only [projL] at h
  by_cases hv : S.le (S.valL c) ℓ
  · rw [if_pos hv] at h ⊢; injection h with h1 h2; exact ⟨h1, h2⟩
  · rw [if_neg hv] at h ⊢; injection h with h1 h2; exact ⟨h1, h2⟩

theorem not_forall_exists {α : Sort _} {p : α → Prop} (h : ¬ ∀ x, p x) : ∃ x, ¬ p x :=
  Classical.byContradiction fun hc => h fun x => Classical.byContradiction fun hx => hc ⟨x, hx⟩

/-- **Determinacy.**  If the component can realise the target against *every*
    adversary, then it can *force* it: the game is won.  This is the step that
    turns `Strat-NI` into a policy, and it is where the two-point lattice is
    used -- the adversary constructed here is an arbitrary function of the trace,
    which is a legal strategy exactly when the user of ℓ-invisible channels sees
    everything. -/
theorem forced_canWin {St : Type} {step : St → Act Channel Value → St → Prop}
    {ℓ : Level} {env : Channel → List (Lbl Channel Value) → Value → Prop}
    (hpub : PublicPresence S) (dflt : Value) :
    ∀ (tgt : List (PLbl Channel Value)) (P : St → Prop) (hist : List (Lbl Channel Value)),
      Forced S step ℓ env tgt P hist → CanWin S step ℓ env tgt P hist := by
  intro tgt
  induction tgt with
  | nil => intro _ _ _; trivial
  | cons l rest ih =>
      intro P hist hF
      -- the adversary that punishes a first label `x`, when `x` is not forcing
      have mkAdv : ∀ x : Lbl Channel Value,
          ∃ advx : Channel → List (Lbl Channel Value) → Value,
            ¬ Forced S step ℓ env rest (stepSet step P x) (hist ++ [x]) →
            ¬ ∃ t, S.proj ℓ t = rest ∧
              (∃ s₀ s, TauClose step (stepSet step P x) s₀ ∧ Reach step s₀ t s) ∧
              (∀ pre a' v' post, t = pre ++ .inp a' v' :: post →
                (S.le (S.valL a') ℓ → env a' ((hist ++ [x]) ++ pre) v') ∧
                (¬ S.le (S.valL a') ℓ → v' = advx a' pre)) := by
        intro x
        rcases Classical.em (Forced S step ℓ env rest (stepSet step P x) (hist ++ [x])) with hf | hf
        · exact ⟨fun _ _ => dflt, fun hc => absurd hf hc⟩
        · obtain ⟨advx, hadv⟩ := not_forall_exists hf
          exact ⟨advx, fun _ => hadv⟩
      obtain ⟨advOf, hadvOf⟩ := Classical.axiomOfChoice mkAdv
      let advWith : Value → Channel → List (Lbl Channel Value) → Value := fun v0 a' pre =>
        match pre with
        | [] => v0
        | x :: pre' => advOf x a' pre'
      -- the tail of a `Forced` run is itself `Forced`, since otherwise `advOf`
      -- punishes the first label
      have tailForced : ∀ (v0 : Value) (x : Lbl Channel Value) (t' : List (Lbl Channel Value)),
          S.proj ℓ t' = rest →
          (∃ s₀ s, TauClose step (stepSet step P x) s₀ ∧ Reach step s₀ t' s) →
          (∀ pre a' v' post, t' = pre ++ .inp a' v' :: post →
            (S.le (S.valL a') ℓ → env a' ((hist ++ [x]) ++ pre) v') ∧
            (¬ S.le (S.valL a') ℓ → v' = advWith v0 a' (x :: pre))) →
          Forced S step ℓ env rest (stepSet step P x) (hist ++ [x]) := by
        intro v0 x t' h1 h2 h3
        rcases Classical.em (Forced S step ℓ env rest (stepSet step P x) (hist ++ [x])) with hf | hf
        · exact hf
        · exact absurd ⟨t', h1, h2, h3⟩ (hadvOf x hf)
      cases l with
      | out a ov =>
          obtain ⟨x, hx, hne, _, t', hproj', hrun', hinp'⟩ :=
            forced_step hpub (advWith dflt) hF
          rw [projLbl_eq_projL hpub] at hx
          injection hx with hx'
          cases x with
          | inp c w =>
              exfalso
              simp only [projL] at hx'
              by_cases hv : S.le (S.valL c) ℓ
              · rw [if_pos hv] at hx'; simp at hx'
              · rw [if_neg hv] at hx'; simp at hx'
          | out c w =>
              obtain ⟨hc, hval⟩ := projL_out_inv hx'
              subst hc
              refine ⟨w, ?_, hne, ih _ _ (tailForced dflt _ t' hproj' hrun' hinp')⟩
              rw [projLbl_eq_projL hpub]
              simp only [projL]
              by_cases hv : S.le (S.valL c) ℓ
              · rw [if_pos hv]; rw [if_pos hv] at hval; rw [hval]
              · rw [if_neg hv]; rw [if_neg hv] at hval; rw [hval]
      | inp a ov =>
          by_cases hl : S.le (S.valL a) ℓ
          · rw [CanWin, if_pos hl]
            obtain ⟨x, hx, hne, henv, t', hproj', hrun', hinp'⟩ :=
              forced_step hpub (advWith dflt) hF
            rw [projLbl_eq_projL hpub] at hx
            injection hx with hx'
            cases x with
            | out c w =>
                exfalso
                simp only [projL] at hx'
                by_cases hv : S.le (S.valL c) ℓ
                · rw [if_pos hv] at hx'; simp at hx'
                · rw [if_neg hv] at hx'; simp at hx'
            | inp c w =>
                obtain ⟨hc, hval⟩ := projL_inp_inv hx'
                subst hc
                refine ⟨w, ?_, (henv c w rfl).1 hl, hne,
                  ih _ _ (tailForced dflt _ t' hproj' hrun' hinp')⟩
                rw [projLbl_eq_projL hpub]
                simp only [projL]
                rw [if_pos hl]; rw [if_pos hl] at hval; rw [hval]
          · rw [CanWin, if_neg hl]
            constructor
            · obtain ⟨x, hx, _, _, _⟩ := forced_step hpub (advWith dflt) hF
              rw [projLbl_eq_projL hpub] at hx
              injection hx with hx'
              cases x with
              | out c w =>
                  simp only [projL] at hx'
                  by_cases hv : S.le (S.valL c) ℓ
                  · rw [if_pos hv] at hx'; (exfalso; simp at hx')
                  · rw [if_neg hv] at hx'; (exfalso; simp at hx')
              | inp c w =>
                  simp only [projL] at hx'
                  by_cases hv : S.le (S.valL c) ℓ
                  · rw [if_pos hv] at hx'; injection hx' with h1 _; subst h1; exact absurd hv hl
                  · rw [if_neg hv] at hx'; injection hx' with _ h2; exact h2.symm
            · intro v
              obtain ⟨x, hx, hne, hcond, t', hproj', hrun', hinp'⟩ :=
                forced_step hpub (advWith v) hF
              rw [projLbl_eq_projL hpub] at hx
              injection hx with hx'
              cases x with
              | out c w =>
                  exfalso
                  simp only [projL] at hx'
                  by_cases hv : S.le (S.valL c) ℓ
                  · rw [if_pos hv] at hx'; simp at hx'
                  · rw [if_neg hv] at hx'; simp at hx'
              | inp c w =>
                  obtain ⟨hc, _⟩ := projL_inp_inv hx'
                  subst hc
                  have hw : w = v := (hcond c w rfl).2 hl
                  refine ⟨?_, ?_⟩
                  · rw [← hw]; exact hne
                  · rw [← hw]; exact ih _ _ (tailForced v _ t' hproj' hrun' hinp')

/-- A play of the game is a genuine run of the component. -/
theorem canWin_nil {St : Type} {step : St → Act Channel Value → St → Prop}
    {ℓ : Level} {env : Channel → List (Lbl Channel Value) → Value → Prop}
    {P : St → Prop} {hist : List (Lbl Channel Value)} :
    CanWin S step ℓ env [] P hist := trivial


/-! ### From `Strat-NI` to `Forced` -/

/-- The legal strategy that realises an adversary: on ℓ-invisible channels it
    offers exactly the adversary's choice (and nothing, when `w` offers nothing,
    so that emptiness is preserved); on ℓ-visible channels it follows `w`.
    Legality on the invisible channels is where `Omniscient` is used. -/
noncomputable def advStrat {ℓ : Level} (hom : Omniscient S Value ℓ)
    (w : S.Strategy Value) (adv : Channel → List (Lbl Channel Value) → Value) :
    S.Strategy Value where
  ω := fun a t =>
    if S.le (S.valL a) ℓ then w.ω a t else (fun v => (∃ u, w.ω a t u) ∧ v = adv a t)
  resp_val := by
    intro a t₁ t₂ h
    by_cases hl : S.le (S.valL a) ℓ
    · rw [if_pos hl, if_pos hl]; exact w.resp_val a t₁ t₂ h
    · rw [hom a hl t₁ t₂ h]
  resp_pres := by
    intro a t₁ t₂ h
    by_cases hl : S.le (S.valL a) ℓ
    · rw [if_pos hl, if_pos hl]; exact w.resp_pres a t₁ t₂ h
    · rw [if_neg hl, if_neg hl]
      have hw := w.resp_pres a t₁ t₂ h
      have key : ∀ t : List (Lbl Channel Value),
          VSet.isEmpty (fun v => (∃ u, w.ω a t u) ∧ v = adv a t) ↔ VSet.isEmpty (w.ω a t) := by
        intro t
        constructor
        · intro he u hu; exact he (adv a t) ⟨⟨u, hu⟩, rfl⟩
        · intro he v hv; exact he _ hv.1.choose_spec
      exact (key t₁).trans (hw.trans (key t₂).symm)


theorem seq_advStrat {ℓ : Level} (hom : Omniscient S Value ℓ) (w : S.Strategy Value)
    (adv : Channel → List (Lbl Channel Value) → Value) :
    S.seq ℓ w (advStrat hom w adv) := by
  intro a t
  refine ⟨fun hl => ?_, fun hl => ?_⟩
  · show w.ω a t = (if S.le (S.valL a) ℓ then w.ω a t else _)
    rw [if_pos hl]
  · by_cases hv : S.le (S.valL a) ℓ
    · show dotEq (w.ω a t) (if S.le (S.valL a) ℓ then w.ω a t else _)
      rw [if_pos hv]
    · show dotEq (w.ω a t) (if S.le (S.valL a) ℓ then w.ω a t else _)
      rw [if_neg hv]
      constructor
      · intro he v hv2; exact he _ hv2.1.choose_spec
      · intro he u hu; exact he (adv a t) ⟨⟨u, hu⟩, rfl⟩

/-- **`Strat-NI` gives `Forced`.**  Noninterference says the component realises
    its ℓ-view against every *legal* strategy; `advStrat` turns an arbitrary
    adversary into a legal strategy, so it realises it against every adversary. -/
theorem forced_of_INI {St : Type} {step : St → Act Channel Value → St → Prop}
    {sB : St} {ℓ : Level} (hom : Omniscient S Value ℓ)
    (hB : S.INI step (fun _ => True) sB)
    (w : S.Strategy Value) (b : List (Lbl Channel Value))
    (hb : S.produces step w sB b) :
    Forced S step ℓ (fun a t v => w.ω a t v) (S.proj ℓ b) (fun s => s = sB) [] := by
  intro adv
  obtain ⟨t, hprod, hteq⟩ :=
    hB ℓ w (advStrat hom w adv) trivial trivial (seq_advStrat hom w adv) b hb
  refine ⟨t, hteq.symm, ?_, ?_⟩
  · obtain ⟨s, hr⟩ := hprod.1
    exact ⟨sB, s, ⟨sB, rfl, Reach.nil⟩, hr⟩
  · intro pre a v post heq
    have hc := hprod.2 pre a v post heq
    have hc' : (if S.le (S.valL a) ℓ then w.ω a pre else
        (fun v => (∃ u, w.ω a pre u) ∧ v = adv a pre)) v := hc
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · rw [if_pos hl] at hc'; simpa using hc'
    · rw [if_neg hl] at hc'; exact hc'.2


/-- **Lemma (★).**  A noninterfering component can *force* its ℓ-view: it has a
    winning strategy in the game against the user of the ℓ-invisible channels.
    This is the whole content of the two-point-lattice proof that is not
    bookkeeping, and `Omniscient` -- the H-user seeing everything -- is exactly
    what makes the adversary constructed by determinacy a legal strategy. -/
theorem canWin_of_INI {St : Type} {step : St → Act Channel Value → St → Prop}
    {sB : St} {ℓ : Level} (hpub : PublicPresence S) (hom : Omniscient S Value ℓ)
    (dflt : Value) (hB : S.INI step (fun _ => True) sB)
    (w : S.Strategy Value) (b : List (Lbl Channel Value))
    (hb : S.produces step w sB b) :
    CanWin S step ℓ (fun a t v => w.ω a t v) (S.proj ℓ b) (fun s => s = sB) [] :=
  forced_canWin hpub dflt _ _ _ (forced_of_INI hom hB w b hb)


/-! ### The canonical play of a winning strategy -/

/-- The run the component produces by following its winning strategy against a
    given adversary.  Choices are resolved by `Classical.epsilon`, which is what
    makes the play a *function* of the adversary -- and hence causal, which is
    what `HasPolicy` needs. -/
noncomputable def playB {St : Type} (S : Sec Level Channel)
    (step : St → Act Channel Value → St → Prop) (ℓ : Level)
    (env : Channel → List (Lbl Channel Value) → Value → Prop) (dflt : Value) :
    (Channel → List (Lbl Channel Value) → Value) →
      List (PLbl Channel Value) → (St → Prop) → List (Lbl Channel Value) →
      List (Lbl Channel Value)
  | _, [], _, _ => []
  | adv, .out a ov :: rest, P, hist =>
      haveI : Nonempty Value := ⟨dflt⟩
      let v := Classical.epsilon (fun v =>
        S.projLbl ℓ (Lbl.out a v) = some (.out a ov) ∧
        (∃ s, stepSet step P (Lbl.out a v) s) ∧
        CanWin S step ℓ env rest (stepSet step P (Lbl.out a v)) (hist ++ [Lbl.out a v]))
      Lbl.out a v :: playB S step ℓ env dflt (fun a' q => adv a' (Lbl.out a v :: q)) rest
        (stepSet step P (Lbl.out a v)) (hist ++ [Lbl.out a v])
  | adv, .inp a ov :: rest, P, hist =>
      haveI : Nonempty Value := ⟨dflt⟩
      let v := if S.le (S.valL a) ℓ then
          Classical.epsilon (fun v =>
            S.projLbl ℓ (Lbl.inp a v) = some (.inp a ov) ∧ env a hist v ∧
            (∃ s, stepSet step P (Lbl.inp a v) s) ∧
            CanWin S step ℓ env rest (stepSet step P (Lbl.inp a v)) (hist ++ [Lbl.inp a v]))
        else adv a []
      Lbl.inp a v :: playB S step ℓ env dflt (fun a' q => adv a' (Lbl.inp a v :: q)) rest
        (stepSet step P (Lbl.inp a v)) (hist ++ [Lbl.inp a v])


/-- The canonical play is a genuine run realising the target. -/
theorem playB_spec {St : Type} {step : St → Act Channel Value → St → Prop}
    {ℓ : Level} {env : Channel → List (Lbl Channel Value) → Value → Prop}
    (hpub : PublicPresence S) (dflt : Value) :
    ∀ (tgt : List (PLbl Channel Value)) (P : St → Prop) (_hP : ∃ s, P s)
      (hist : List (Lbl Channel Value)) (adv : Channel → List (Lbl Channel Value) → Value),
      CanWin S step ℓ env tgt P hist →
      S.proj ℓ (playB S step ℓ env dflt adv tgt P hist) = tgt ∧
      (∃ s₀ s, TauClose step P s₀ ∧
        Reach step s₀ (playB S step ℓ env dflt adv tgt P hist) s) ∧
      (∀ pre a v post, playB S step ℓ env dflt adv tgt P hist = pre ++ .inp a v :: post →
        (S.le (S.valL a) ℓ → env a (hist ++ pre) v) ∧
        (¬ S.le (S.valL a) ℓ → v = adv a pre)) := by
  intro tgt
  induction tgt with
  | nil =>
      rintro P ⟨s, hs⟩ hist adv _
      refine ⟨rfl, ⟨s, s, ⟨s, hs, Reach.nil⟩, Reach.nil⟩, ?_⟩
      intro pre a v post heq
      exact absurd heq.symm (by simp [playB, List.append_eq_nil_iff])
  | cons l rest ih =>
      intro P hP hist adv h
      -- the chosen label and the fact that it is a good move
      have key : ∀ (x : Lbl Channel Value),
          S.projLbl ℓ x = some l →
          (∃ s, stepSet step P x s) →
          CanWin S step ℓ env rest (stepSet step P x) (hist ++ [x]) →
          S.proj ℓ (x :: playB S step ℓ env dflt (fun a' q => adv a' (x :: q)) rest
              (stepSet step P x) (hist ++ [x])) = l :: rest ∧
          (∃ s₀ s, TauClose step P s₀ ∧
            Reach step s₀ (x :: playB S step ℓ env dflt (fun a' q => adv a' (x :: q)) rest
              (stepSet step P x) (hist ++ [x])) s) ∧
          (∀ pre a v post,
            x :: playB S step ℓ env dflt (fun a' q => adv a' (x :: q)) rest
              (stepSet step P x) (hist ++ [x]) = pre ++ .inp a v :: post →
            ((S.le (S.valL a) ℓ → env a (hist ++ pre) v) ∧
             (¬ S.le (S.valL a) ℓ → v = adv a pre)) ∨ (pre = [] ∧ x = .inp a v)) := by
        intro x hx hne hcw
        obtain ⟨hproj', ⟨s₀', s', hTC', hR'⟩, hinp'⟩ := ih _ hne _ _ hcw
        obtain ⟨s₁, hs₁, hr₁⟩ := hTC'
        obtain ⟨s₂, hs₂, hstep₂⟩ := hs₁
        refine ⟨by rw [proj_cons_some hx, hproj'], ⟨s₂, s', hs₂, ?_⟩, ?_⟩
        · have hrt : Reach step s₁
              (playB S step ℓ env dflt (fun a' q => adv a' (x :: q)) rest
                (stepSet step P x) (hist ++ [x])) s' := by
            have := Reach.trans hr₁ hR'
            rwa [List.nil_append] at this
          cases x with
          | inp c w => exact Reach.inp hstep₂ hrt
          | out c w => exact Reach.out hstep₂ hrt
        · intro pre a v post heq
          cases pre with
          | nil =>
              right
              rw [List.nil_append] at heq
              injection heq with h1 _
              exact ⟨rfl, h1⟩
          | cons y pre' =>
              left
              rw [List.cons_append] at heq
              injection heq with h1 h2
              subst h1
              have := hinp' pre' a v post h2
              simpa [List.append_assoc] using this
      cases l with
      | out a ov =>
          haveI : Nonempty Value := ⟨dflt⟩
          have hspec := Classical.epsilon_spec (p := fun v =>
            S.projLbl ℓ (Lbl.out a v) = some (.out a ov) ∧
            (∃ s, stepSet step P (Lbl.out a v) s) ∧
            CanWin S step ℓ env rest (stepSet step P (Lbl.out a v)) (hist ++ [Lbl.out a v])) h
          obtain ⟨hx, hne, hcw⟩ := hspec
          obtain ⟨hp, hr, hi⟩ := key _ hx hne hcw
          simp only [playB]
          refine ⟨hp, hr, ?_⟩
          intro pre a' v' post heq
          rcases hi pre a' v' post heq with hgood | ⟨_, hbad⟩
          · exact hgood
          · exact absurd hbad (by simp)
      | inp a ov =>
          haveI : Nonempty Value := ⟨dflt⟩
          by_cases hl : S.le (S.valL a) ℓ
          · rw [CanWin, if_pos hl] at h
            have hspec := Classical.epsilon_spec (p := fun v =>
              S.projLbl ℓ (Lbl.inp a v) = some (.inp a ov) ∧ env a hist v ∧
              (∃ s, stepSet step P (Lbl.inp a v) s) ∧
              CanWin S step ℓ env rest (stepSet step P (Lbl.inp a v)) (hist ++ [Lbl.inp a v])) h
            obtain ⟨hx, henv, hne, hcw⟩ := hspec
            obtain ⟨hp, hr, hi⟩ := key _ hx hne hcw
            simp only [playB, if_pos hl]
            refine ⟨hp, hr, ?_⟩
            intro pre a' v' post heq
            rcases hi pre a' v' post heq with hgood | ⟨hpre, hbad⟩
            · exact hgood
            · subst hpre
              injection hbad with h1 h2
              subst h1; subst h2
              exact ⟨fun _ => by rwa [List.append_nil], fun hc => absurd hl hc⟩
          · rw [CanWin, if_neg hl] at h
            obtain ⟨hov, h⟩ := h
            obtain ⟨hne, hcw⟩ := h (adv a [])
            have hx : S.projLbl ℓ (Lbl.inp a (adv a [])) = some (.inp a ov) := by
              rw [hov]; exact projLbl_inp_pres (hpub a ℓ) hl
            obtain ⟨hp, hr, hi⟩ := key _ hx hne hcw
            simp only [playB, if_neg hl]
            refine ⟨hp, hr, ?_⟩
            intro pre a' v' post heq
            rcases hi pre a' v' post heq with hgood | ⟨hpre, hbad⟩
            · exact hgood
            · subst hpre
              injection hbad with h1 h2
              subst h1; subst h2
              exact ⟨fun hc => absurd hc hl, fun _ => rfl⟩

end Sec

end InteractiveNI
