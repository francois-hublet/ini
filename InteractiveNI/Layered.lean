/-
  **The layered proof of compositionality for coalition noninterference.**

  This file formalises the proof outline of `coalition-composes.md` for an
  arbitrary lattice.  Everything structural is proved here; the two remaining
  mathematical steps are isolated as the named hypotheses `LayerStep` and
  `LayerFinal`, so that the gap is visible in the statement of the main theorem
  rather than hidden in a `sorry`.

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

theorem pubAt_mono {S : Sec Level Channel} {ℓ ℓ' : Level} (h : S.PubAt ℓ)
    (hle : S.le ℓ ℓ') : S.PubAt ℓ' := fun a => S.le_trans (h a) hle

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

theorem proj_weave_at {S : Sec Level Channel} {ℓ : Level} (h : S.PubAt ℓ)
    (p : List Bool) (u v : List (Lbl Channel Value)) :
    S.proj ℓ (weave p u v) = weave p (S.proj ℓ u) (S.proj ℓ v) := by
  rw [proj_eq_map_at h, proj_eq_map_at h, proj_eq_map_at h, map_weave]

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

theorem layerC_step_le (S : Sec Level Channel) (m n : Level) (ns : List Level) :
    S.coalition.le (layerC S m ns) (layerC S m (n :: ns)) :=
  le_addLevel _ _

/-- Each peeled level must still be invisible to the layers beneath it.  This is
    automatic for a linear extension of the levels of the invisible channels. -/
def Fresh (S : Sec Level Channel) (m : Level) : List Level → Prop
  | [] => True
  | n :: ns => ¬ S.coalition.le (sing n) (layerC S m ns) ∧ Fresh S m ns

/-- **Every layer is flat.**  A channel that the layer `n :: ns` makes visible and
    that sits above `n` sits *at* `n`. -/
theorem layerC_flat {S : Sec Level Channel} {m n : Level} {ns : List Level}
    (h : ¬ S.coalition.le (sing n) (layerC S m ns)) {a : Channel}
    (hvis : S.coalition.le (sing (S.valL a)) (layerC S m (n :: ns)))
    (hup : S.le n (S.valL a)) : S.le (S.valL a) n :=
  layer_flat h hvis hup

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

/-- The definition is unambiguous: `adapt_vis` shows the strategy answers the
    same on any two traces with the same `C`-observation. -/
theorem obsConsistent_wellDefined {S : Sec Level Channel}
    (w : S.coalition.Strategy Value) {C : Coalition Level} {a : Channel}
    (hvis : S.coalition.le (sing (S.valL a)) C)
    {t t' : List (Lbl Channel Value)} (h : S.coalition.proj C t = S.coalition.proj C t') :
    w.ω a t = w.ω a t' :=
  adapt_vis w hvis h

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

/-- So the strategy component of `RedRun` is free: every run of a component is
    produced by *some* total legal strategy. -/
theorem redRun_of_reach {S : Sec Level Channel} {St : Type}
    {step : St → Act Channel Value → St → Prop} {s : St} (dflt : Value)
    {C : Coalition Level} {t : List (Lbl Channel Value)} {s' : St}
    (h : Reach step s t s') : RedRun S step s C (S.coalition.proj C t) :=
  ⟨t, s', replayStrat S.coalition dflt t, replayStrat_total dflt t, h,
    consistent_replayStrat dflt t, rfl⟩

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

/-- **The base case.**  A composed run under `ω₁` yields layer consistency at
    `C⁺` for `ω₂`, with target its own `C⁺`-observation. -/
theorem layerCons_base {S : Sec Level Channel} {m : Level}
    (hpub : S.coalition.PubAt (Cplus S m)) (dflt : Value)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {w₁ w₂ : S.coalition.Strategy Value}
    (hseq : S.coalition.seq (Cplus S m) w₁ w₂)
    {t₁ : List (Lbl Channel Value)}
    (h₁ : S.coalition.produces (parStep stepA stepB) w₁ (sA, sB) t₁) :
    LayerCons S stepA stepB sA sB w₂ m (Cplus S m)
      (S.coalition.proj (Cplus S m) t₁) := by
  obtain ⟨⟨q, hreach⟩, hcons⟩ := h₁
  obtain ⟨tA, tB, hA, hB, hint⟩ := par_decompose hreach
  obtain ⟨p, hw, hE⟩ := hint.exists_weave
  subst hw
  have hlenA : tA.length = (S.coalition.proj (Cplus S m) tA).length := by
    rw [proj_eq_map_at hpub]; simp
  have hlenB : tB.length = (S.coalition.proj (Cplus S m) tB).length := by
    rw [proj_eq_map_at hpub]; simp
  have hEp : Exact p (S.coalition.proj (Cplus S m) tA) (S.coalition.proj (Cplus S m) tB) :=
    Exact.retype p tA tB _ _ hE hlenA hlenB
  have hpw : weave p (S.coalition.proj (Cplus S m) tA) (S.coalition.proj (Cplus S m) tB)
      = S.coalition.proj (Cplus S m) (weave p tA tB) := (proj_weave_at hpub p tA tB).symm
  refine ⟨p, _, _, hEp,
    ⟨tA, q.1, _, replayStrat_total dflt tA, hA, consistent_replayStrat dflt tA, rfl⟩,
    ⟨tB, q.2, _, replayStrat_total dflt tB, hB, consistent_replayStrat dflt tB, rfl⟩, ?_, ?_⟩
  · -- consistency of the observation
    rw [hpw]
    intro o₁ a v o₂ hsplit hvis t ht
    obtain ⟨u, l, r, hdec, hu, hl⟩ := proj_split hpub hsplit
    have hval : S.coalition.le (S.coalition.valL a) (Cplus S m) := hvis
    have hlab : l = Lbl.inp a v := by
      cases l with
      | inp b x =>
          by_cases hb : S.coalition.le (S.coalition.valL b) (Cplus S m)
          · rw [projL_inp_vis hb] at hl
            injection hl with hb' hx
            injection hx with hx
            rw [hb', hx]
          · simp only [projL, hb, if_neg, if_false] at hl
            exact absurd hl (by simp)
      | out b x =>
          simp only [projL] at hl
          by_cases hb : S.coalition.le (S.coalition.valL b) (Cplus S m) <;>
            simp only [hb, if_pos, if_neg, if_false] at hl <;> exact absurd hl (by simp)
    subst hlab
    have h1 : w₁.ω a u v := hcons u a v r hdec
    have h2 : w₂.ω a u v := by rw [← (hseq a u).1 hval]; exact h1
    have h3 : w₂.ω a t = w₂.ω a u := adapt_vis w₂ hvis (by unfold Sec.teq; rw [ht, hu])
    rw [h3]; exact h2
  · rw [hpw]; exact down_proj (S.coalition.le_refl _) _

/-! ### Consistency restricted to a set of channels

    The layer step needs to say that a merged trace agrees with the strategy on
    *some* channels only -- those the layer has just exposed -- while the rest is
    governed by the invariant carried from below.  These are the `On` analogues of
    the consistency lemmas of `Det.lean` and `Weave.lean`. -/

/-- `w`-consistency of the inputs on channels satisfying `Q`. -/
def consistentOn (S : Sec Level Channel) (Q : Channel → Prop)
    (w : S.Strategy Value) (t : List (Lbl Channel Value)) : Prop :=
  ∀ t₁ (a : Channel) (v : Value) t₂, t = t₁ ++ Lbl.inp a v :: t₂ → Q a → w.ω a t₁ v

theorem consistentOn_of_consistent {S : Sec Level Channel} {Q : Channel → Prop}
    {w : S.Strategy Value} {t : List (Lbl Channel Value)} (h : S.consistent w t) :
    S.consistentOn Q w t := fun t₁ a v t₂ heq _ => h t₁ a v t₂ heq

theorem consistentOn_nil {S : Sec Level Channel} (Q : Channel → Prop)
    (w : S.Strategy Value) : S.consistentOn Q w ([] : List (Lbl Channel Value)) := by
  rintro t₁ a v t₂ heq _
  exact absurd heq.symm (by simp [List.append_eq_nil_iff])

theorem consistentOn_of_cons {S : Sec Level Channel} {Q : Channel → Prop}
    {w : S.Strategy Value} {l : Lbl Channel Value} {t : List (Lbl Channel Value)}
    (hc : S.consistentOn Q w (l :: t)) : S.consistentOn Q (prependStrat [l] w) t := by
  rintro t₁ a v t₂ rfl hq
  exact hc (l :: t₁) a v t₂ rfl hq

theorem consistentOn_cons_out {S : Sec Level Channel} {Q : Channel → Prop}
    {w : S.Strategy Value} {a : Channel} {v : Value} {t : List (Lbl Channel Value)}
    (hc : S.consistentOn Q (prependStrat [Lbl.out a v] w) t) :
    S.consistentOn Q w (Lbl.out a v :: t) := by
  rintro t₁ b u t₂ heq hq
  cases t₁ with
  | nil => rw [List.nil_append] at heq; injection heq with h1 h2; exact absurd h1 (by simp)
  | cons x t₁ =>
      rw [List.cons_append] at heq
      injection heq with h1 h2
      subst h1
      exact hc t₁ b u t₂ h2 hq

theorem consistentOn_cons_inp {S : Sec Level Channel} {Q : Channel → Prop}
    {w : S.Strategy Value} {a : Channel} {v : Value} {t : List (Lbl Channel Value)}
    (hh : Q a → w.ω a [] v)
    (hc : S.consistentOn Q (prependStrat [Lbl.inp a v] w) t) :
    S.consistentOn Q w (Lbl.inp a v :: t) := by
  rintro t₁ b u t₂ heq hq
  cases t₁ with
  | nil =>
      rw [List.nil_append] at heq
      injection heq with h1 h2
      injection h1 with hb hv
      subst hb; subst hv
      exact hh hq
  | cons x t₁ =>
      rw [List.cons_append] at heq
      injection heq with h1 h2
      subst h1
      exact hc t₁ b u t₂ h2 hq

theorem consistentOn_congr {S : Sec Level Channel} {Q : Channel → Prop}
    {w₁ w₂ : S.Strategy Value} {t : List (Lbl Channel Value)}
    (h : ∀ a u, w₁.ω a u = w₂.ω a u) (hc : S.consistentOn Q w₁ t) :
    S.consistentOn Q w₂ t := by
  intro t₁ a v t₂ heq hq
  rw [← h a t₁]; exact hc t₁ a v t₂ heq hq

/-- **Weaving preserves restricted consistency.**  The `Q`-restricted analogue of
    `consistent_weave`. -/
theorem consistent_weave_on {S : Sec Level Channel} (hpub : PublicPresence S)
    (Q : Channel → Prop) :
    ∀ (p : List Bool) (u v : List (Lbl Channel Value)) (w : S.Strategy Value),
      S.consistentOn Q ((weaveIns (Value := Value) hpub p v).induced w) u →
      S.consistentOn Q ((weaveIns (Value := Value) hpub (p.map not) u).induced w) v →
      S.consistentOn Q w (weave p u v) := by
  intro p
  induction p with
  | nil => intro u v w _ _; exact consistentOn_nil Q w
  | cons hd p ih =>
      intro u v w hu hv
      cases hd with
      | true =>
          cases u with
          | nil => exact consistentOn_nil Q w
          | cons x u' =>
              have hA : S.consistentOn Q ((weaveIns hpub p v).induced (prependStrat [x] w)) u' :=
                consistentOn_congr (fun _ _ => rfl) (consistentOn_of_cons hu)
              have hB :
                  S.consistentOn Q ((weaveIns hpub (p.map not) u').induced (prependStrat [x] w)) v :=
                consistentOn_congr (fun _ _ => rfl) hv
              have hrest : S.consistentOn Q (prependStrat [x] w) (weave p u' v) := ih u' v _ hA hB
              cases x with
              | out c d => exact consistentOn_cons_out hrest
              | inp c d => exact consistentOn_cons_inp (fun hq => hu [] c d u' rfl hq) hrest
      | false =>
          cases v with
          | nil => exact consistentOn_nil Q w
          | cons y v' =>
              have hA : S.consistentOn Q ((weaveIns hpub p v').induced (prependStrat [y] w)) u :=
                consistentOn_congr (fun _ _ => rfl) hu
              have hB :
                  S.consistentOn Q ((weaveIns hpub (p.map not) u).induced (prependStrat [y] w)) v' :=
                consistentOn_congr (fun _ _ => rfl) (consistentOn_of_cons hv)
              have hrest : S.consistentOn Q (prependStrat [y] w) (weave p u v') := ih u v' _ hA hB
              cases y with
              | out c d => exact consistentOn_cons_out hrest
              | inp c d => exact consistentOn_cons_inp (fun hq => hv [] c d v' rfl hq) hrest

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

/-! ### The two remaining steps, as explicit hypotheses -/

/-- **The layer step.**  Peeling one more level from the bottom: because the
    channels that become visible all carry that level (`layerC_flat`), this is the
    flat case of Theorem 20 applied to the reduced systems. -/
def LayerStep (S : Sec Level Channel) {StA StB : Type}
    (stepA : StA → Act Channel Value → StA → Prop)
    (stepB : StB → Act Channel Value → StB → Prop)
    (sA : StA) (sB : StB) (w : S.coalition.Strategy Value) (m : Level) : Prop :=
  ∀ (ns : List Level) (n : Level) (τ : List (PLbl Channel Value)),
    ¬ S.coalition.le (sing n) (layerC S m ns) →
    LayerCons S stepA stepB sA sB w m (layerC S m ns) τ →
    LayerCons S stepA stepB sA sB w m (layerC S m (n :: ns)) τ

/-- **The final step.**  At a layer that sees every channel, a layer-consistent
    observation is the observation of a genuine composed run. -/
def LayerFinal (S : Sec Level Channel) {StA StB : Type}
    (stepA : StA → Act Channel Value → StA → Prop)
    (stepB : StB → Act Channel Value → StB → Prop)
    (sA : StA) (sB : StB) (w : S.coalition.Strategy Value) (m : Level) : Prop :=
  ∀ (ns : List Level) (τ : List (PLbl Channel Value)),
    (∀ a : Channel, S.coalition.le (sing (S.valL a)) (layerC S m ns)) →
    LayerCons S stepA stepB sA sB w m (layerC S m ns) τ →
    ∃ t, S.coalition.produces (parStep stepA stepB) w (sA, sB) t ∧
      S.coalition.proj (Cplus S m) t = τ

/-- **`LayerStep` outright**, for systems in which no layer ever exposes an input
    the coalition beneath it could not already see.  Then the peeling needs no
    game at all, and `compositional_layered` applies with `LayerStep` discharged. -/
def NewlyVisible (S : Sec Level Channel) (C : Coalition Level) (n : Level) :
    Channel → Prop := fun a =>
  S.coalition.le (sing (S.valL a)) (addLevel C n) ∧
  ¬ S.coalition.le (sing (S.valL a)) C

/-- **The layer step when only one component reads what the layer exposes.**
    There is then no mutual fixed point to solve: freeze the partner, re-plan the
    reader using its own coalition noninterference -- the change of strategy is
    confined to channels invisible at `C`, so its `C`-observation is preserved --
    and the newly exposed inputs come out matching the strategy. -/
theorem layerCons_symm {S : Sec Level Channel} {StA StB : Type}
    {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {w : S.coalition.Strategy Value} {m : Level} {C : Coalition Level}
    {τ : List (PLbl Channel Value)}
    (h : LayerCons S stepA stepB sA sB w m C τ) :
    LayerCons S stepB stepA sB sA w m C τ := by
  obtain ⟨p, oA, oB, hE, hA, hB, hcons, hdown⟩ := h
  refine ⟨p.map not, oB, oA, Exact.map_not p oA oB hE, hB, hA, ?_, ?_⟩
  · rw [weave_comm]; exact hcons
  · rw [weave_comm]; exact hdown

/-! ### What is left of the layer step

    Where a layer *does* expose a new input, the value of that input stops being
    free and must be the one the strategy offers, given a history both components
    contribute to.  Pinning it is the flat case of Theorem 20, and the flatness it
    needs is supplied by `layerC_flat`.  The obstacle to reusing `Game.lean` here
    is `Omniscient`: that development makes the adversary constructed by
    determinacy legal by assuming the users of the invisible channels see
    *everything*, which is true in the two-point lattice but false at a layer,
    where such a user sees only `↓valL a`.  Replacing `Omniscient` by layer
    flatness -- the users of the newly exposed channels share the view `π_n` -- is
    the remaining mathematical work. -/

/-- **`LayerFinal`, proved.**  At a layer that sees every channel the invariant
    already *is* a composed run: the two component runs interleave along the
    recorded pattern, and `ObsConsistent` at a full layer says precisely that
    every input carries a value the strategy offers. -/
theorem layerFinal_holds {S : Sec Level Channel}
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {w : S.coalition.Strategy Value} {m : Level} {ns : List Level}
    (hpub : S.coalition.PubAt (layerC S m ns))
    (τ : List (PLbl Channel Value))
    (hfull : ∀ a : Channel, S.coalition.le (sing (S.valL a)) (layerC S m ns))
    (h : LayerCons S stepA stepB sA sB w m (layerC S m ns) τ) :
    ∃ t, S.coalition.produces (parStep stepA stepB) w (sA, sB) t ∧
      S.coalition.proj (Cplus S m) t = τ := by
  obtain ⟨p, oA, oB, hE, ⟨tA, qA, vA, htA, hrA, hcA, hoA⟩,
    ⟨tB, qB, vB, htB, hrB, hcB, hoB⟩, hcons, hdown⟩ := h
  have hlen : ∀ t : List (Lbl Channel Value),
      (S.coalition.proj (layerC S m ns) t).length = t.length := by
    intro t; rw [proj_eq_map_at hpub, List.length_map]
  have hEt : Exact p tA tB := by
    refine Exact.retype p oA oB tA tB hE ?_ ?_
    · rw [← hoA]; exact hlen tA
    · rw [← hoB]; exact hlen tB
  have hI : Interleave tA tB (weave p tA tB) := Exact.interleave p tA tB hEt
  have hwC : weave p oA oB = S.coalition.proj (layerC S m ns) (weave p tA tB) := by
    rw [← hoA, ← hoB, proj_weave_at hpub]
  refine ⟨weave p tA tB, ⟨⟨(qA, qB), par_reach_interleave hI hrA hrB⟩, ?_⟩, ?_⟩
  · intro u a v r hdec
    refine hcons (S.coalition.proj (layerC S m ns) u) a v
      (S.coalition.proj (layerC S m ns) r) ?_ (hfull a) u rfl
    rw [hwC, hdec, proj_append, proj_cons_some (projLbl_eq_projL_at hpub _),
      projL_inp_vis (hfull a)]
  · rw [← hdown, hwC, down_proj (layerC_le S m ns)]

/-! ### The peeling, and the theorem it yields -/

/-- Iterating the layer step along the whole list of levels. -/
theorem layerCons_peel {S : Sec Level Channel} {StA StB : Type}
    {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {w : S.coalition.Strategy Value} {m : Level}
    (hstep : LayerStep S stepA stepB sA sB w m) {τ : List (PLbl Channel Value)}
    (h₀ : LayerCons S stepA stepB sA sB w m (Cplus S m) τ) :
    ∀ ns : List Level, Fresh S m ns → LayerCons S stepA stepB sA sB w m (layerC S m ns) τ := by
  intro ns
  induction ns with
  | nil => intro _; exact h₀
  | cons n ns ih => intro hfresh; exact hstep ns n τ hfresh.1 (ih hfresh.2)

/-- **Compositionality of coalition noninterference at `C⁺`, layered.**  Given the
    two steps above, a composed run under `ω₁` is matched at `C⁺` by one under
    `ω₂`.  With the reductions of `Coalition.lean` -- the difference set of the
    two strategies is up-closed, hence peelable one channel at a time, each step
    using exactly a coalition of the form `C⁺` -- this is the general case. -/
theorem compositional_layered {S : Sec Level Channel} {m : Level}
    (hpub : S.coalition.PubAt (Cplus S m)) (dflt : Value)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {w₁ w₂ : S.coalition.Strategy Value}
    (hstep : LayerStep S stepA stepB sA sB w₂ m)
    (ns : List Level) (hfresh : Fresh S m ns)
    (hfull : ∀ a : Channel, S.coalition.le (sing (S.valL a)) (layerC S m ns))
    (hseq : S.coalition.seq (Cplus S m) w₁ w₂)
    {t₁ : List (Lbl Channel Value)}
    (h₁ : S.coalition.produces (parStep stepA stepB) w₁ (sA, sB) t₁) :
    ∃ t₂, S.coalition.produces (parStep stepA stepB) w₂ (sA, sB) t₂ ∧
      S.coalition.teq (Cplus S m) t₁ t₂ := by
  have h₀ := layerCons_base hpub dflt hseq h₁
  have hk := layerCons_peel hstep h₀ ns hfresh
  obtain ⟨t₂, hprod, hproj⟩ := layerFinal_holds
    (pubAt_mono hpub (layerC_le S m ns)) _ hfull hk
  exact ⟨t₂, hprod, hproj.symm⟩

end Sec

end InteractiveNI
