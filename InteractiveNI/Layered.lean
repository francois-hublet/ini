/-
  **The layered proof of compositionality for coalition noninterference.**

  This file formalises the layered proof outline for an arbitrary lattice: the
  coalitions `C₀ ⊆ C₁ ⊆ ... ⊆ C_k` of a peeling, the invariant carried along it
  (`LayerCons`), and the structural lemmas the layer step needs.  The step
  itself is proved in `LayerStepW.lean`.

  The shape of the argument.  After the reductions of `Coalition.lean` we may
  assume the observing coalition is `C⁺ = Cplus S m` and that the two strategies
  agree on `Vis C⁺`.  Enumerate the levels of the invisible channels in a linear
  extension `n₁ ⊑ … ⊑ n_k` and peel them from the *bottom*:

      C₀ = C⁺,   C_i = C⁺ ∪ {n₁, …, n_i}.

  `layer_flat` (in `Coalition.lean`) says that at each step the channels which
  become visible all carry the level `n_i`, so every layer is flat -- the case
  Theorem 20 settles -- whatever the lattice.  `layer_reduces` says a coalition
  below `C_i` reads everything it needs off the `C_i`-observation, so coalition
  noninterference transfers to the reduced systems.  The invariant carried along
  the peeling is `LayerCons`, the formal counterpart of conditions (a), (b), (c)
  of the write-up.
-/
import InteractiveNI.Weave
import InteractiveNI.Coalition

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

namespace Sec

variable {Level Channel Value : Type}

/-! ### Presence, level by level

    `PublicPresence S.coalition` is *false*: the empty coalition sees nothing, not
    even presence.  What the argument needs is presence visible at the particular
    coalitions it uses, which holds of every non-empty coalition as soon as the
    underlying context has public presence.  These are the level-by-level forms of
    the projection lemmas. -/

/-- Presence is visible at the level `ℓ`. -/
def PubAt (S : Sec Level Channel) (ℓ : Level) : Prop := ∀ a : Channel, S.le (S.presL a) ℓ

/-- A non-empty coalition sees presence, when the underlying context does. -/
theorem pubAt_coalition {S : Sec Level Channel} (hpub : PublicPresence S)
    {C : Coalition Level} (hne : ∃ c, C c) : S.coalition.PubAt C := by
  intro a c hc
  obtain ⟨d, hd⟩ := hne
  exact ⟨d, hd, by rw [show c = S.presL a from hc]; exact hpub a d⟩

theorem projLbl_eq_projL_at {S : Sec Level Channel} {ℓ : Level} (h : S.PubAt ℓ)
    (l : Lbl Channel Value) : S.projLbl ℓ l = some (S.projL ℓ l) := by
  cases l with
  | inp a v =>
      by_cases hv : S.le (S.valL a) ℓ
      · rw [projLbl_inp_full (h a) hv]; simp only [projL, if_pos hv]
      · rw [projLbl_inp_pres (h a) hv]; simp only [projL, if_neg hv]
  | out a v =>
      by_cases hv : S.le (S.valL a) ℓ
      · rw [projLbl_out_full (h a) hv]; simp only [projL, if_pos hv]
      · rw [projLbl_out_pres (h a) hv]; simp only [projL, if_neg hv]

theorem proj_eq_map_at {S : Sec Level Channel} {ℓ : Level} (h : S.PubAt ℓ)
    (t : List (Lbl Channel Value)) : S.proj ℓ t = t.map (S.projL ℓ) := by
  induction t with
  | nil => rfl
  | cons l t ih =>
      rw [proj_cons_some (projLbl_eq_projL_at h l), ih, List.map_cons]

/-! ### The layer coalitions -/

/-- `layerC S m ns` is `C⁺(m)` enlarged by the levels in `ns`, the head being the
    level peeled last. -/
def layerC (S : Sec Level Channel) (m : Level) : List Level → Coalition Level
  | [] => Cplus S m
  | n :: ns => addLevel (layerC S m ns) n

theorem layerC_le (S : Sec Level Channel) (m : Level) :
    ∀ ns : List Level, S.coalition.le (Cplus S m) (layerC S m ns)
  | [] => S.coalition.le_refl _
  | n :: ns => S.coalition.le_trans (layerC_le S m ns) (le_addLevel _ _)

/-! ### Observations -/

/-- Reprojection of an observation onto a coarser coalition. -/
noncomputable def down (S : Sec Level Channel) (C : Coalition Level)
    (o : List (PLbl Channel Value)) : List (PLbl Channel Value) :=
  o.filterMap (S.coalition.reproj C)

theorem down_proj {S : Sec Level Channel} {C D : Coalition Level}
    (hle : S.coalition.le D C) (t : List (Lbl Channel Value)) :
    down S D (S.coalition.proj C t) = S.coalition.proj D t :=
  (layer_reduces hle t).symm

/-- The traces of the *reduced system*: the `C`-observations of the runs of
    `step` from `s`.  The run is required to be produced by *some* total legal
    strategy -- which the component always faces in a composition, namely the one
    induced by freezing its partner -- so that coalition noninterference can be
    applied to it at the next layer.  Its agreement with the global strategy is
    imposed separately, and only on what the coalition sees, by `ObsConsistent`. -/
def RedRun (S : Sec Level Channel) {St : Type}
    (step : St → Act Channel Value → St → Prop) (s : St)
    (C : Coalition Level) (o : List (PLbl Channel Value)) : Prop :=
  ∃ (t : List (Lbl Channel Value)) (s' : St) (v : S.coalition.Strategy Value),
    v.total ∧ Reach step s t s' ∧ S.coalition.consistent v t ∧
    S.coalition.proj C t = o

/-- **Consistency of an observation.**  At a layer, the view of a *visible*
    channel is already determined by the observation, by `adapt_vis`; so whether
    an input the coalition can see carries a value the strategy allows is a
    property of the observation alone. -/
def ObsConsistent (S : Sec Level Channel) (w : S.coalition.Strategy Value)
    (C : Coalition Level) (o : List (PLbl Channel Value)) : Prop :=
  ∀ o₁ (a : Channel) (v : Value) o₂, o = o₁ ++ PLbl.inp a (some v) :: o₂ →
    S.coalition.le (sing (S.valL a)) C →
    ∀ t : List (Lbl Channel Value), S.coalition.proj C t = o₁ → w.ω a t v

/-! ### The invariant -/

/-- **Layer consistency**, the invariant of the peeling.  The observation at the
    layer `C` splits, along an interleaving pattern, into two component
    observations that the reduced systems can produce; the merge is consistent
    with the strategy on every channel the layer sees; and it reprojects to the
    prescribed target at `C⁺`. -/
def LayerCons (S : Sec Level Channel) {StA StB : Type}
    (stepA : StA → Act Channel Value → StA → Prop)
    (stepB : StB → Act Channel Value → StB → Prop)
    (sA : StA) (sB : StB) (w : S.coalition.Strategy Value)
    (m : Level) (C : Coalition Level) (τ : List (PLbl Channel Value)) : Prop :=
  ∃ (p : List Bool) (oA oB : List (PLbl Channel Value)),
    Exact p oA oB ∧
    RedRun S stepA sA C oA ∧ RedRun S stepB sB C oB ∧
    ObsConsistent S w C (weave p oA oB) ∧
    down S (Cplus S m) (weave p oA oB) = τ

/-! ### Every run is produced by some total legal strategy

    The invariant asks each component's trace to be produced by a total legal
    strategy.  That costs nothing: replay the values the trace read, as a function
    of the reader's *own* view.  Along a single trace the views before successive
    reads on a channel are distinct -- each contains one more of that channel's
    events -- so the replay is well defined, and defaulting everywhere else makes
    it total.  This is also what licenses treating a component's inputs on
    channels nobody is watching as its own choice. -/

/-- `v` is a value the trace `t` read on `a` at a point its user cannot tell
    from `u`. -/
def Matches (S : Sec Level Channel) (t : List (Lbl Channel Value)) (a : Channel)
    (u : List (Lbl Channel Value)) (v : Value) : Prop :=
  ∃ u' r, t = u' ++ Lbl.inp a v :: r ∧ S.teq (S.valL a) u' u

theorem Matches_congr {S : Sec Level Channel} {t : List (Lbl Channel Value)}
    {a : Channel} {u₁ u₂ : List (Lbl Channel Value)} (h : S.teq (S.valL a) u₁ u₂)
    (v : Value) : S.Matches t a u₁ v ↔ S.Matches t a u₂ v :=
  ⟨fun ⟨u', r, ht, hteq⟩ => ⟨u', r, ht, hteq.trans h⟩,
   fun ⟨u', r, ht, hteq⟩ => ⟨u', r, ht, hteq.trans h.symm⟩⟩

/-- The replay strategy of a trace. -/
noncomputable def replayStrat (S : Sec Level Channel) (dflt : Value)
    (t : List (Lbl Channel Value)) : S.Strategy Value where
  ω := fun a u v => S.Matches t a u v ∨ ((∀ v', ¬ S.Matches t a u v') ∧ v = dflt)
  resp_val := by
    intro a t₁ t₂ h
    funext v
    refine propext ⟨fun hv => ?_, fun hv => ?_⟩
    · rcases hv with hm | ⟨hno, rfl⟩
      · exact Or.inl ((Matches_congr h v).mp hm)
      · exact Or.inr ⟨fun v' hm => hno v' ((Matches_congr h v').mpr hm), rfl⟩
    · rcases hv with hm | ⟨hno, rfl⟩
      · exact Or.inl ((Matches_congr h v).mpr hm)
      · exact Or.inr ⟨fun v' hm => hno v' ((Matches_congr h v').mp hm), rfl⟩
  resp_pres := by
    intro a t₁ t₂ _
    have key : ∀ u : List (Lbl Channel Value),
        ¬ (∀ v : Value, ¬ (S.Matches t a u v ∨
            ((∀ v', ¬ S.Matches t a u v') ∧ v = dflt))) := by
      intro u hemp
      by_cases hex : ∃ v', S.Matches t a u v'
      · obtain ⟨v', hv'⟩ := hex
        exact hemp v' (Or.inl hv')
      · exact hemp dflt (Or.inr ⟨fun v' hm => hex ⟨v', hm⟩, rfl⟩)
    exact ⟨fun h => absurd h (key t₁), fun h => absurd h (key t₂)⟩

theorem replayStrat_total {S : Sec Level Channel} (dflt : Value)
    (t : List (Lbl Channel Value)) : (replayStrat S dflt t).total := by
  intro a u
  by_cases hex : ∃ v', S.Matches t a u v'
  · obtain ⟨v', hv'⟩ := hex
    exact ⟨v', Or.inl hv'⟩
  · exact ⟨dflt, Or.inr ⟨fun v' hm => hex ⟨v', hm⟩, rfl⟩⟩

theorem consistent_replayStrat {S : Sec Level Channel} (dflt : Value)
    (t : List (Lbl Channel Value)) : S.consistent (replayStrat S dflt t) t := by
  intro t₁ a v t₂ heq
  exact Or.inl ⟨t₁, t₂, heq, rfl⟩

theorem projL_inp_vis {S : Sec Level Channel}
    {C : Coalition Level} {a : Channel} {v : Value}
    (h : S.coalition.le (S.coalition.valL a) C) :
    S.coalition.projL C (Lbl.inp a v) = PLbl.inp a (some v) := by
  simp only [projL]
  rw [if_pos h]

/-! ### The base case -/

/-- `Exact` depends on its two lists only through their lengths, so it transfers
    from a trace pair to the pair of their projections. -/
theorem Exact.retype {α β : Type} :
    ∀ (p : List Bool) (u v : List α) (u' v' : List β),
      Exact p u v → u.length = u'.length → v.length = v'.length → Exact p u' v'
  | [], u, v, u', v', hE, hu, hv => by
      refine ⟨?_, ?_⟩
      · rw [hE.1] at hu; exact List.eq_nil_of_length_eq_zero hu.symm
      · rw [hE.2] at hv; exact List.eq_nil_of_length_eq_zero hv.symm
  | true :: _, [], _, _, _, hE, _, _ => absurd hE (by simp [Exact])
  | true :: p, _ :: u, v, u', v', hE, hu, hv => by
      cases u' with
      | nil => exact absurd hu (by simp)
      | cons _ u' => exact Exact.retype p u v u' v' hE (by simpa using hu) hv
  | false :: _, _, [], _, _, hE, _, _ => absurd hE (by simp [Exact])
  | false :: p, u, _ :: v, u', v', hE, hu, hv => by
      cases v' with
      | nil => exact absurd hv (by simp)
      | cons _ v' => exact Exact.retype p u v u' v' hE hu (by simpa using hv)

/-- Under public presence `π_C` is a `map`, so a decomposition of an observation
    lifts to a decomposition of the trace. -/
theorem map_eq_append_cons {α β : Type} (f : α → β) :
    ∀ (t : List α) (o₁ : List β) (q : β) (o₂ : List β),
      t.map f = o₁ ++ q :: o₂ →
      ∃ t₁ l t₂, t = t₁ ++ l :: t₂ ∧ t₁.map f = o₁ ∧ f l = q := by
  intro t
  induction t with
  | nil => intro o₁ q o₂ h; cases o₁ <;> simp at h
  | cons x t ih =>
      intro o₁ q o₂ h
      cases o₁ with
      | nil =>
          simp only [List.map_cons, List.nil_append, List.cons.injEq] at h
          exact ⟨[], x, t, rfl, rfl, h.1⟩
      | cons y o₁ =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
          obtain ⟨t₁, l, t₂, rfl, h2, h3⟩ := ih o₁ q o₂ h.2
          exact ⟨x :: t₁, l, t₂, rfl, by simp only [List.map_cons, h.1, h2], h3⟩

theorem proj_split {S : Sec Level Channel} {C : Coalition Level}
    (hpub : S.coalition.PubAt C) {t : List (Lbl Channel Value)}
    {o₁ o₂ : List (PLbl Channel Value)} {q : PLbl Channel Value}
    (h : S.coalition.proj C t = o₁ ++ q :: o₂) :
    ∃ t₁ l t₂, t = t₁ ++ l :: t₂ ∧ S.coalition.proj C t₁ = o₁ ∧
      S.coalition.projL C l = q := by
  rw [proj_eq_map_at hpub] at h
  obtain ⟨t₁, l, t₂, hsplit, h2, h3⟩ := map_eq_append_cons _ t o₁ q o₂ h
  exact ⟨t₁, l, t₂, hsplit, by rw [proj_eq_map_at hpub]; exact h2, h3⟩

/-! ### Consistency restricted to a set of channels

    The layer step needs to say that a merged trace agrees with the strategy on
    *some* channels only -- those the layer has just exposed -- while the rest is
    governed by the invariant carried from below.  These are the `On` analogues of
    the consistency lemmas of `Det.lean` and `Weave.lean`. -/

/-- Two non-empty offer sets are `≐`-equal. -/
theorem dotEq_of_total {V : Type} {X Y : VSet V} (hx : ∃ v, X v) (hy : ∃ v, Y v) :
    dotEq X Y := by
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  exact ⟨fun h => absurd hx (h x), fun h => absurd hy (h y)⟩

/-! ### Proving the layer step where it does not need determinacy

    The layer step has content only where the layer makes a channel the component
    *reads from* visible: then the value of that input is no longer free, and
    pinning it is the flat case of Theorem 20.  Where the layer makes visible only
    channels the components write to -- or reads they had already exposed -- the
    step is pure bookkeeping, and we prove it. -/

theorem mem_weave {α : Type} (x : α) :
    ∀ (p : List Bool) (u v : List α), x ∈ weave p u v → x ∈ u ∨ x ∈ v := by
  intro p
  induction p with
  | nil => intro u v h; simp [weave] at h
  | cons hd p ih =>
      intro u v h
      cases hd with
      | true =>
          cases u with
          | nil => simp [weave] at h
          | cons y u =>
              rcases List.mem_cons.mp h with rfl | h
              · exact Or.inl (List.mem_cons.mpr (Or.inl rfl))
              · rcases ih u v h with h | h
                · exact Or.inl (List.mem_cons.mpr (Or.inr h))
                · exact Or.inr h
      | false =>
          cases v with
          | nil => simp [weave] at h
          | cons y v =>
              rcases List.mem_cons.mp h with rfl | h
              · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
              · rcases ih u v h with h | h
                · exact Or.inl h
                · exact Or.inr (List.mem_cons.mpr (Or.inr h))

/-- The channels a layer exposes: visible once `n` is added to the coalition,
    invisible before. -/
def NewlyVisible (S : Sec Level Channel) (C : Coalition Level) (n : Level) :
    Channel → Prop := fun a =>
  S.coalition.le (sing (S.valL a)) (addLevel C n) ∧
  ¬ S.coalition.le (sing (S.valL a)) C

end Sec

end InteractiveNI
