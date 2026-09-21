/-
  Sequential compositionality for *nondeterministic* components
  (a complete case of Theorem C of `chain-composition.md`).

  Section 4 of the paper obtains compositionality only for deterministic
  components.  Here is a case that needs no determinism at all: if one component
  reads only from channels the ℓ-observer can already see, then it replays
  verbatim under any ℓ-equivalent strategy, and the other component may be
  re-planned around it using its own INI.  No fixed point between the two
  components is required, which is exactly why the argument goes through without
  determinism.

  The interleaving handled here is the sequential one (`B` then `A`); the general
  interleaving needs the same argument plus the pattern bookkeeping of
  `Weave.lean`.
-/
import InteractiveNI.Weave

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

namespace Sec

variable {Level Channel Value : Type} {S : Sec Level Channel}

/-- A trace whose inputs all arrive on ℓ-visible channels is consistent with one
    strategy iff it is consistent with any ℓ-equivalent one: such a trace carries
    no information the observer does not already have. -/
theorem consistent_of_low {w₁ w₂ : S.Strategy Value} {ℓ : Level}
    {b : List (Lbl Channel Value)}
    (hw : S.seq ℓ w₁ w₂) (hbc : S.consistent w₁ b)
    (hblow : ∀ t' α v t'', b = t' ++ .inp α v :: t'' → S.le (S.valL α) ℓ) :
    S.consistent w₂ b := by
  intro t₁ a v t₂ heq
  have h1 : w₁.ω a t₁ v := hbc t₁ a v t₂ heq
  have hlow : S.le (S.valL a) ℓ := hblow t₁ a v t₂ heq
  rwa [← (hw a t₁).1 hlow]

/-- **Sequential compositionality.**  `B` runs first and reads only ℓ-visible
    channels; `A` then runs in the context of `B`'s trace.  If `A` is
    noninterfering, the composition matches at `ℓ`.  Neither component is assumed
    deterministic. -/
theorem sequential_compositional
    {St₁ St₂ : Type} {step₁ : St₁ → Act Channel Value → St₁ → Prop}
    {step₂ : St₂ → Act Channel Value → St₂ → Prop}
    {sA : St₁} {sB : St₂} {ℓ : Level}
    (hA : S.INI step₁ (fun _ => True) sA)
    {w₁ w₂ : S.Strategy Value} (hw : S.seq ℓ w₁ w₂)
    {b a : List (Lbl Channel Value)} {sD : St₂}
    (hb : Reach step₂ sB b sD)
    (hbc : S.consistent w₁ b)
    (hblow : ∀ t' α v t'', b = t' ++ .inp α v :: t'' → S.le (S.valL α) ℓ)
    (ha : S.produces step₁ (prependStrat b w₁) sA a) :
    ∃ t₂, S.produces (parStep step₁ step₂) w₂ (sA, sB) t₂ ∧ S.teq ℓ (b ++ a) t₂ := by
  -- `A` is re-planned in the frozen context `b`; the two frozen strategies are
  -- ℓ-equivalent, which is the freeze lemma in its `prependStrat` instance.
  obtain ⟨a₂, ha₂, hta⟩ :=
    hA ℓ (prependStrat b w₁) (prependStrat b w₂) trivial trivial
      (seq_prependStrat hw (rfl : S.teq ℓ b b)) a ha
  refine ⟨b ++ a₂, ⟨?_, ?_⟩, teq_append (rfl : S.teq ℓ b b) hta⟩
  · -- the composed run exists
    obtain ⟨sC, hreach⟩ := ha₂.1
    exact ⟨(sC, sD), Reach.trans (par_reach_right hb) (par_reach_left hreach)⟩
  · -- and it is consistent with `w₂`
    exact consistent_append (consistent_of_low hw hbc hblow) ha₂.2

/-- If a component only ever inputs on ℓ-visible channels, so does any of its
    runs. -/
theorem reach_inputs_low {St : Type} {step : St → Act Channel Value → St → Prop}
    {ℓ : Level} (hIn : ∀ s a v s', step s (.inp a v) s' → S.le (S.valL a) ℓ)
    {x y : St} {b : List (Lbl Channel Value)} (h : Reach step x b y) :
    ∀ t' α v t'', b = t' ++ .inp α v :: t'' → S.le (S.valL α) ℓ := by
  induction h with
  | nil => intro t' α v t'' heq; exact absurd heq.symm (by simp [List.append_eq_nil_iff])
  | tau _ _ ih => exact ih
  | @inp s s' s'' a v u hs _ ih =>
      intro t' α x t'' heq
      cases t' with
      | nil =>
          rw [List.nil_append] at heq
          injection heq with h1 _
          injection h1 with hc hv
          subst hc; subst hv; exact hIn s a v s' hs
      | cons z t' =>
          rw [List.cons_append] at heq
          injection heq with _ h2
          exact ih t' α x t'' h2
  | @out s s' s'' a v u hs _ ih =>
      intro t' α x t'' heq
      cases t' with
      | nil => rw [List.nil_append] at heq; injection heq with h1 _; exact absurd h1 (by simp)
      | cons z t' =>
          rw [List.cons_append] at heq
          injection heq with _ h2
          exact ih t' α x t'' h2

/-- **Theorem C: asymmetric compositionality.**  If `B` only ever reads on
    channels the ℓ-observer can see, then `B` replays verbatim and `A` may be
    re-planned around it using its own noninterference.  Neither component is
    assumed deterministic, and the interleaving is arbitrary. -/
theorem interleaved_compositional (hpub : PublicPresence S)
    {St₁ St₂ : Type} {step₁ : St₁ → Act Channel Value → St₁ → Prop}
    {step₂ : St₂ → Act Channel Value → St₂ → Prop}
    {sA : St₁} {sB : St₂} {ℓ : Level}
    (hA : S.INI step₁ (fun _ => True) sA)
    (hBin : ∀ s a v s', step₂ s (.inp a v) s' → S.le (S.valL a) ℓ)
    {w₁ w₂ : S.Strategy Value} (hw : S.seq ℓ w₁ w₂)
    {t : List (Lbl Channel Value)}
    (ht : S.produces (parStep step₁ step₂) w₁ (sA, sB) t) :
    ∃ t₂, S.produces (parStep step₁ step₂) w₂ (sA, sB) t₂ ∧ S.teq ℓ t t₂ := by
  obtain ⟨q, hreach⟩ := ht.1
  obtain ⟨a, b, hRa, hRb, hI⟩ := par_decompose hreach
  obtain ⟨p, hp, hE⟩ := hI.exists_weave
  have hcons : S.consistent w₁ (weave p a b) := hp ▸ ht.2
  -- A's trace, seen against the strategy induced by freezing B
  have hAprod : S.produces step₁ ((weaveIns hpub p b).induced w₁) sA a :=
    ⟨⟨q.1, hRa⟩, consistent_weave_left hpub hE hcons⟩
  obtain ⟨a₂, ha₂, hta⟩ :=
    hA ℓ _ _ trivial trivial (seq_weaveIns hpub p b hw) a hAprod
  have hE₂ : Exact p a₂ b := Exact.congr_length p a a₂ b hE (teq_length hpub hta)
  -- B's trace, seen against the strategy induced by freezing A
  have hBold : S.consistent ((weaveIns hpub (p.map not) a).induced w₁) b :=
    consistent_weave_left hpub (Exact.map_not p a b hE)
      (by rw [weave_comm]; exact hcons)
  have hBlow := reach_inputs_low (S := S) hBin hRb
  have hBnew : S.consistent ((weaveIns hpub (p.map not) a₂).induced w₂) b := by
    intro t' β x t'' heq
    have hlow : S.le (S.valL β) ℓ := hBlow t' β x t'' heq
    have h1 : w₁.ω β (weave (p.map not) t' a) x := hBold t' β x t'' heq
    have h2 : w₁.ω β (weave (p.map not) t' a₂) = w₁.ω β (weave (p.map not) t' a) :=
      w₁.resp_val β _ _ (teq_mono hlow (teq_weave hpub (rfl : S.teq ℓ t' t') hta.symm))
    show w₂.ω β (weave (p.map not) t' a₂) x
    rw [← (hw β _).1 hlow, h2]
    exact h1
  obtain ⟨q₂, hRa₂⟩ := ha₂.1
  refine ⟨weave p a₂ b, ⟨⟨(q₂, q.2), ?_⟩, ?_⟩, ?_⟩
  · exact par_reach_interleave (Exact.interleave p a₂ b hE₂) hRa₂ hRb
  · exact consistent_weave hpub p a₂ b w₂ ha₂.2 hBnew
  · rw [hp]; exact teq_weave hpub hta (rfl : S.teq ℓ b b)

/-- **Corollary.**  A component that reads only *public* data composes with any
    noninterfering component: the composition is `Strat-NI`.  This is a genuine
    compositionality result for nondeterministic components, complementing §4,
    which needs determinism. -/
theorem INI_par_of_public_inputs (hpub : PublicPresence S)
    {St₁ St₂ : Type} {step₁ : St₁ → Act Channel Value → St₁ → Prop}
    {step₂ : St₂ → Act Channel Value → St₂ → Prop}
    {sA : St₁} {sB : St₂}
    (hA : S.INI step₁ (fun _ => True) sA)
    (hBin : ∀ s a v s', step₂ s (.inp a v) s' → ∀ ℓ : Level, S.le (S.valL a) ℓ) :
    S.INI (parStep step₁ step₂) (fun _ => True) (sA, sB) := by
  intro ℓ w₁ w₂ _ _ hw t ht
  exact interleaved_compositional hpub hA (fun s a v s' h => hBin s a v s' h ℓ) hw ht

end Sec

end InteractiveNI
