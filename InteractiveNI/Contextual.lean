/-
  **Strengthening the notion so that it composes unconditionally.**

  Theorem `CexPresence.par_not_NI` shows that coalition noninterference is not
  closed under composition when presence is secret.  The standard repair is to
  ask for the property *in every noninterferent context*:

      `s` is contextually noninterferent  iff  `s ∥ e` is coalition
      noninterferent for every coalition-noninterfering `e`.

  This is not circular -- it quantifies over the base notion -- and it composes
  for free, by associativity: if `e` is noninterferent then so is `s₂ ∥ e`,
  hence so is `s₁ ∥ (s₂ ∥ e) = (s₁ ∥ s₂) ∥ e`.  It excludes `P_p`, it keeps
  `P₁`, and where the composition theorem holds it collapses back to coalition
  noninterference, so nothing is lost.
-/
import InteractiveNI.FiniteUse

namespace InteractiveNI

namespace Sec

variable {Level Channel Value : Type}

/-! ### The idle partner -/

inductive Idle where | idle

def stepIdle (Channel Value : Type) : Idle → Act Channel Value → Idle → Prop :=
  fun _ _ _ => False

theorem reach_idle {t : List (Lbl Channel Value)} {x y : Idle}
    (h : Reach (stepIdle Channel Value) x t y) : t = [] := by
  induction h with
  | nil => rfl
  | tau hs _ _ => exact absurd hs (by simp [stepIdle])
  | inp hs _ _ => exact absurd hs (by simp [stepIdle])
  | out hs _ _ => exact absurd hs (by simp [stepIdle])

theorem stratTNI_idle {S : Sec Level Channel} :
    S.coalition.StratTNI (stepIdle Channel Value) Idle.idle := by
  intro C w₁ w₂ _ _ _ t₁ h₁
  obtain ⟨⟨q, hr⟩, -⟩ := h₁
  have : t₁ = [] := reach_idle hr
  subst this
  exact ⟨[], ⟨⟨Idle.idle, Reach.nil⟩, by intro u a v r heq; simp at heq⟩, rfl⟩

theorem reach_par_idle_of {St : Type} {step : St → Act Channel Value → St → Prop}
    {s s' : St} {t : List (Lbl Channel Value)} (h : Reach step s t s') :
    Reach (parStep step (stepIdle Channel Value)) (s, Idle.idle) t (s', Idle.idle) := by
  induction h with
  | nil => exact Reach.nil
  | @tau x x' x'' u hs _ ih =>
      exact Reach.tau (s' := (x', Idle.idle)) (Or.inl ⟨hs, rfl⟩) ih
  | @inp x x' x'' a v u hs _ ih =>
      exact Reach.inp (s' := (x', Idle.idle)) (Or.inl ⟨hs, rfl⟩) ih
  | @out x x' x'' a v u hs _ ih =>
      exact Reach.out (s' := (x', Idle.idle)) (Or.inl ⟨hs, rfl⟩) ih

theorem reach_of_par_idle {St : Type} {step : St → Act Channel Value → St → Prop} :
    ∀ {x y : St × Idle} {t : List (Lbl Channel Value)},
      Reach (parStep step (stepIdle Channel Value)) x t y → Reach step x.1 t y.1 := by
  intro x y t h
  induction h with
  | nil => exact Reach.nil
  | @tau x x' x'' u hs _ ih =>
      rcases hs with ⟨hs, he⟩ | ⟨hs, -⟩
      · exact Reach.tau hs ih
      · exact absurd hs (by simp [stepIdle])
  | @inp x x' x'' a v u hs _ ih =>
      rcases hs with ⟨hs, he⟩ | ⟨hs, -⟩
      · exact Reach.inp hs ih
      · exact absurd hs (by simp [stepIdle])
  | @out x x' x'' a v u hs _ ih =>
      rcases hs with ⟨hs, he⟩ | ⟨hs, -⟩
      · exact Reach.out hs ih
      · exact absurd hs (by simp [stepIdle])

/-! ### Associativity -/

theorem parStep_assoc {StA StB StC : Type}
    {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop}
    {stepC : StC → Act Channel Value → StC → Prop}
    {x y : (StA × StB) × StC} {e : Act Channel Value}
    (h : parStep (parStep stepA stepB) stepC x e y) :
    parStep stepA (parStep stepB stepC) (x.1.1, (x.1.2, x.2)) e (y.1.1, (y.1.2, y.2)) := by
  rcases h with ⟨h, h2⟩ | ⟨h, h1⟩
  · rcases h with ⟨hA, hB⟩ | ⟨hB, hA⟩
    · exact Or.inl ⟨hA, by rw [hB, h2]⟩
    · exact Or.inr ⟨Or.inl ⟨hB, h2⟩, hA⟩
  · exact Or.inr ⟨Or.inr ⟨h, by rw [h1]⟩, by rw [h1]⟩

theorem parStep_assoc' {StA StB StC : Type}
    {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop}
    {stepC : StC → Act Channel Value → StC → Prop}
    {x y : StA × (StB × StC)} {e : Act Channel Value}
    (h : parStep stepA (parStep stepB stepC) x e y) :
    parStep (parStep stepA stepB) stepC ((x.1, x.2.1), x.2.2) e ((y.1, y.2.1), y.2.2) := by
  rcases h with ⟨hA, h2⟩ | ⟨h, h1⟩
  · exact Or.inl ⟨Or.inl ⟨hA, by rw [h2]⟩, by rw [h2]⟩
  · rcases h with ⟨hB, hC⟩ | ⟨hC, hB⟩
    · exact Or.inl ⟨Or.inr ⟨hB, h1⟩, by rw [hC]⟩
    · exact Or.inr ⟨hC, by rw [hB, h1]⟩

theorem reach_assoc {StA StB StC : Type}
    {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop}
    {stepC : StC → Act Channel Value → StC → Prop} :
    ∀ {x y : (StA × StB) × StC} {t : List (Lbl Channel Value)},
      Reach (parStep (parStep stepA stepB) stepC) x t y →
      Reach (parStep stepA (parStep stepB stepC))
        (x.1.1, (x.1.2, x.2)) t (y.1.1, (y.1.2, y.2)) := by
  intro x y t h
  induction h with
  | nil => exact Reach.nil
  | tau hs _ ih => exact Reach.tau (parStep_assoc hs) ih
  | inp hs _ ih => exact Reach.inp (parStep_assoc hs) ih
  | out hs _ ih => exact Reach.out (parStep_assoc hs) ih

theorem reach_assoc' {StA StB StC : Type}
    {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop}
    {stepC : StC → Act Channel Value → StC → Prop} :
    ∀ {x y : StA × (StB × StC)} {t : List (Lbl Channel Value)},
      Reach (parStep stepA (parStep stepB stepC)) x t y →
      Reach (parStep (parStep stepA stepB) stepC)
        ((x.1, x.2.1), x.2.2) t ((y.1, y.2.1), y.2.2) := by
  intro x y t h
  induction h with
  | nil => exact Reach.nil
  | tau hs _ ih => exact Reach.tau (parStep_assoc' hs) ih
  | inp hs _ ih => exact Reach.inp (parStep_assoc' hs) ih
  | out hs _ ih => exact Reach.out (parStep_assoc' hs) ih

/-! ### Contextual coalition noninterference -/

/-- **Noninterferent in every noninterferent context.** -/
def CompTNI (S : Sec Level Channel) {St : Type}
    (step : St → Act Channel Value → St → Prop) (s : St) : Prop :=
  ∀ (St' : Type) (step' : St' → Act Channel Value → St' → Prop) (e : St'),
    S.coalition.StratTNI step' e → S.coalition.StratTNI (parStep step step') (s, e)

/-- It is a strengthening: take the idle context. -/
theorem stratTNI_of_compTNI {S : Sec Level Channel} {St : Type}
    {step : St → Act Channel Value → St → Prop} {s : St} (h : CompTNI S step s) :
    S.coalition.StratTNI step s := by
  have hpar := h Idle (stepIdle Channel Value) Idle.idle stratTNI_idle
  intro C w₁ w₂ ht₁ ht₂ hseq t₁ h₁
  obtain ⟨⟨q, hr⟩, hc⟩ := h₁
  obtain ⟨t₂, ⟨⟨q₂, hr₂⟩, hc₂⟩, hteq⟩ :=
    hpar C w₁ w₂ ht₁ ht₂ hseq t₁ ⟨⟨(q, Idle.idle), reach_par_idle_of hr⟩, hc⟩
  exact ⟨t₂, ⟨⟨q₂.1, reach_of_par_idle hr₂⟩, hc₂⟩, hteq⟩

/-- **It composes, with no hypothesis whatever.** -/
theorem compTNI_par {S : Sec Level Channel} {StA StB : Type}
    {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    (hA : CompTNI S stepA sA) (hB : CompTNI S stepB sB) :
    CompTNI S (parStep stepA stepB) (sA, sB) := by
  intro St' step' e he
  -- `sB ∥ e` is noninterferent, hence so is `sA ∥ (sB ∥ e)`; associate
  have h1 : S.coalition.StratTNI (parStep stepB step') (sB, e) := hB St' step' e he
  have h2 : S.coalition.StratTNI (parStep stepA (parStep stepB step')) (sA, (sB, e)) :=
    hA _ _ _ h1
  intro C w₁ w₂ ht₁ ht₂ hseq t₁ h₁
  obtain ⟨⟨q, hr⟩, hc⟩ := h₁
  obtain ⟨t₂, ⟨⟨q₂, hr₂⟩, hc₂⟩, hteq⟩ :=
    h2 C w₁ w₂ ht₁ ht₂ hseq t₁ ⟨⟨(q.1.1, (q.1.2, q.2)), reach_assoc hr⟩, hc⟩
  exact ⟨t₂, ⟨⟨((q₂.1, q₂.2.1), q₂.2.2), reach_assoc' hr₂⟩, hc₂⟩, hteq⟩

/-- **Where the composition theorem holds, the strengthening collapses.**  With
    presence public and finitely many levels, coalition noninterference is
    already contextual, so nothing is lost by asking for the stronger notion. -/
theorem compTNI_of_stratTNI {S : Sec Level Channel} (hpubS : PublicPresence S)
    (dflt : Value) (ls : List Level) (hls : ∀ l : Level, l ∈ ls) {St : Type}
    {step : St → Act Channel Value → St → Prop} {s : St}
    (h : S.coalition.StratTNI step s) : CompTNI S step s := fun _ _ _ he =>
  coalition_compositional_total_used hpubS dflt (ls := ls)
    (usesLevels_all hls) (usesLevels_all hls) h he

end Sec

end InteractiveNI
