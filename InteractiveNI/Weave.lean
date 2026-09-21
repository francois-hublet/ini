/-
  Interleaving patterns, and the `Insertion` they induce (the geometric half of
  Theorem C of `chain-composition.md`).

  A composed run is an interleaving of the two components' runs.  To apply INI to
  one component inside a composed context we must turn the global strategy into a
  strategy for that component, by reinserting the partner's labels.  `weave`
  records the interleaving pattern explicitly, and `weaveIns` packages the
  reinsertion as an `Insertion`, which by `Freeze.seq_induced` preserves `=_ℓ`.

  Everything here assumes *public presence*: `presL a ⊑ c` for every channel and
  every level, i.e. the mere occurrence of a communication is never secret (only
  its value is).  Both counterexamples of the paper satisfy this.  Under it every
  projection keeps every label, so `π_ℓ` is a `map` and commutes with `weave`.
-/
import InteractiveNI.Interp
import InteractiveNI.Compose

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

/-! ### Weaving two lists along a pattern -/

/-- `weave p u v` interleaves `u` and `v` following the pattern `p`
    (`true` = take from `u`, `false` = take from `v`), stopping as soon as the
    pattern calls for a label that is not there.  Truncation is what makes
    `weave p u' v` the *actual* global prefix corresponding to a prefix `u'` of
    the component trace `u`: it stops exactly where the next component label
    would go, after any partner labels interleaved before it. -/
def weave {α : Type} : List Bool → List α → List α → List α
  | [], _, _ => []
  | true :: p,  x :: u, v => x :: weave p u v
  | false :: p, u, y :: v => y :: weave p u v
  | true :: _,  [], _ => []
  | false :: _, _, [] => []

theorem map_weave {α β : Type} (f : α → β) (p : List Bool) :
    ∀ (u v : List α), (weave p u v).map f = weave p (u.map f) (v.map f) := by
  induction p with
  | nil => intro u v; rfl
  | cons b p ih =>
      intro u v
      cases b with
      | true =>
          cases u with
          | nil => simp only [weave, List.map_nil]
          | cons x u => simp only [weave, List.map_cons]; exact congrArg _ (ih u v)
      | false =>
          cases v with
          | nil => simp only [weave, List.map_nil]
          | cons y v => simp only [weave, List.map_cons]; exact congrArg _ (ih u v)

/-- The pattern consumes both lists exactly, never hitting a truncation clause. -/
def Exact {α : Type} : List Bool → List α → List α → Prop
  | [], u, v => u = [] ∧ v = []
  | true :: p,  _ :: u, v => Exact p u v
  | true :: _,  [], _ => False
  | false :: p, u, _ :: v => Exact p u v
  | false :: _, _, [] => False

/-- **Splitting a woven trace at a label of the first component.**  Because
    `weave` truncates, the woven image of a prefix of `u` is exactly the global
    prefix that precedes the corresponding label. -/
theorem weave_split {α : Type} :
    ∀ (p : List Bool) (u' : List α) (l : α) (u'' v : List α),
      Exact p (u' ++ l :: u'') v →
      ∃ rest, weave p (u' ++ l :: u'') v = weave p u' v ++ l :: rest
  | [], u', l, u'', v, hE => by
      exact absurd hE.1 (by cases u' <;> simp)
  | true :: p, [], _, u'', v, _ => ⟨weave p u'' v, rfl⟩
  | true :: p, _ :: u', l, u'', v, hE => by
      obtain ⟨rest, hrest⟩ := weave_split p u' l u'' v hE
      exact ⟨rest, by simp only [List.cons_append, weave]; exact congrArg _ hrest⟩
  | false :: _, _, _, _, [], hE => absurd hE (by simp [Exact])
  | false :: p, u', l, u'', _ :: v, hE => by
      obtain ⟨rest, hrest⟩ := weave_split p u' l u'' v hE
      exact ⟨rest, by simp only [weave]; exact congrArg _ hrest⟩

/-- Every interleaving is realised by some pattern. -/
theorem Interleave.exists_weave {α : Type} {u v w : List α} (h : Interleave u v w) :
    ∃ p : List Bool, w = weave p u v ∧ Exact p u v := by
  induction h with
  | nil => exact ⟨[], rfl, ⟨rfl, rfl⟩⟩
  | @left a u v w _ ih =>
      obtain ⟨p, hp, hE⟩ := ih
      refine ⟨true :: p, ?_, hE⟩
      simp only [weave]
      exact congrArg (fun z => a :: z) hp
  | @right a u v w _ ih =>
      obtain ⟨p, hp, hE⟩ := ih
      refine ⟨false :: p, ?_, hE⟩
      simp only [weave]
      exact congrArg (fun z => a :: z) hp

namespace Sec

variable {Level Channel Value : Type} {S : Sec Level Channel}

/-! ### Public presence -/

/-- Presence is never secret: every label survives every projection. -/
def PublicPresence (S : Sec Level Channel) : Prop := ∀ a ℓ, S.le (S.presL a) ℓ

/-- The total version of `projLbl`, available under public presence. -/
noncomputable def projL (S : Sec Level Channel) (ℓ : Level) :
    Lbl Channel Value → PLbl Channel Value
  | .inp a v => if S.le (S.valL a) ℓ then .inp a (some v) else .inp a none
  | .out a v => if S.le (S.valL a) ℓ then .out a (some v) else .out a none

theorem projLbl_eq_projL (hpub : PublicPresence S) (ℓ : Level) :
    ∀ l : Lbl Channel Value, S.projLbl ℓ l = some (S.projL ℓ l) := by
  intro l
  cases l with
  | inp a v =>
      by_cases hv : S.le (S.valL a) ℓ
      · rw [projLbl_inp_full (hpub a ℓ) hv]; simp [projL, hv]
      · rw [projLbl_inp_pres (hpub a ℓ) hv]; simp [projL, hv]
  | out a v =>
      by_cases hv : S.le (S.valL a) ℓ
      · rw [projLbl_out_full (hpub a ℓ) hv]; simp [projL, hv]
      · rw [projLbl_out_pres (hpub a ℓ) hv]; simp [projL, hv]

/-- Under public presence, `π_ℓ` is a `map`. -/
theorem proj_eq_map (hpub : PublicPresence S) (ℓ : Level) (t : List (Lbl Channel Value)) :
    S.proj ℓ t = t.map (S.projL ℓ) := by
  induction t with
  | nil => rfl
  | cons l t ih =>
      rw [proj_cons_some (projLbl_eq_projL hpub ℓ l), ih, List.map_cons]

/-- `π_ℓ` commutes with weaving. -/
theorem proj_weave (hpub : PublicPresence S) (ℓ : Level)
    (p : List Bool) (u v : List (Lbl Channel Value)) :
    S.proj ℓ (weave p u v) = weave p (S.proj ℓ u) (S.proj ℓ v) := by
  rw [proj_eq_map hpub, proj_eq_map hpub, proj_eq_map hpub, map_weave]

/-- ℓ-equivalent components weave into ℓ-equivalent composites. -/
theorem teq_weave (hpub : PublicPresence S) {ℓ : Level} {p : List Bool}
    {u u' v v' : List (Lbl Channel Value)}
    (hu : S.teq ℓ u u') (hv : S.teq ℓ v v') :
    S.teq ℓ (weave p u v) (weave p u' v') := by
  unfold teq at *
  rw [proj_weave hpub, proj_weave hpub, hu, hv]

/-! ### The insertion induced by an interleaving pattern -/

/-- Reinserting a frozen partner's trace `b` along the pattern `p` is an
    `Insertion`: it is compatible with every projection a strategy may see.
    This is the geometric obligation left open by `Freeze.lean`. -/
noncomputable def weaveIns (hpub : PublicPresence S) (p : List Bool)
    (b : List (Lbl Channel Value)) : Insertion S Value where
  σ := fun _ u => weave p u b
  resp_val  := fun _ _ _ h => teq_weave hpub h (rfl : S.teq _ b b)
  resp_pres := fun _ _ _ h => teq_weave hpub h (rfl : S.teq _ b b)

@[simp] theorem weaveIns_σ (hpub : PublicPresence S) (p : List Bool)
    (b : List (Lbl Channel Value)) (a : Channel) (u : List (Lbl Channel Value)) :
    (weaveIns (Value := Value) hpub p b).σ a u = weave p u b := rfl

/-- **Freezing a partner along an interleaving preserves ℓ-equivalence.**
    Combining `weaveIns` with the freeze lemma: this is what licenses applying
    `INI` of one component inside a composed context. -/
theorem seq_weaveIns (hpub : PublicPresence S) {ℓ : Level} (p : List Bool)
    (b : List (Lbl Channel Value)) {w₁ w₂ : S.Strategy Value} (hw : S.seq ℓ w₁ w₂) :
    S.seq ℓ ((weaveIns hpub p b).induced w₁) ((weaveIns hpub p b).induced w₂) :=
  seq_induced _ hw

/-- Two frozen partners that are ℓ-equivalent induce ℓ-equivalent strategies,
    provided every channel's value level is at or below `ℓ` … -/
theorem seq_weaveIns' (hpub : PublicPresence S) {ℓ : Level} (p : List Bool)
    {b b' : List (Lbl Channel Value)} {w₁ w₂ : S.Strategy Value}
    (hw : S.seq ℓ w₁ w₂) (hb : S.teq ℓ b b')
    (hlow : ∀ a : Channel, S.le (S.valL a) ℓ) :
    S.seq ℓ ((weaveIns hpub p b).induced w₁) ((weaveIns hpub p b').induced w₂) := by
  intro a t
  refine ⟨fun hl => ?_, fun hl => ?_⟩ <;>
    simp only [Insertion.induced_apply, weaveIns_σ]
  · have h1 : w₁.ω a (weave p t b) = w₁.ω a (weave p t b') :=
      w₁.resp_val a _ _ (teq_mono (hlow a) (teq_weave hpub (rfl : S.teq ℓ t t) hb))
    rw [h1]; exact (hw a _).1 hl
  · have h1 : w₁.ω a (weave p t b) = w₁.ω a (weave p t b') :=
      w₁.resp_val a _ _ (teq_mono (hlow a) (teq_weave hpub (rfl : S.teq ℓ t t) hb))
    rw [h1]; exact (hw a _).2 hl

end Sec

/-! ### Composing component runs along an interleaving

    `Compose.par_decompose` splits a run of a composition into runs of the two
    components.  The converse direction -- assembling a composed run from two
    component runs and an interleaving -- is what a compositionality proof needs,
    and is supplied here. -/

namespace Reach

/-- A run producing a nonempty trace splits as: silent steps, the first visible
    step, then the rest. -/
theorem cons_inv {C V St : Type} {step : St → Act C V → St → Prop} {x y : St}
    {l : Lbl C V} {t : List (Lbl C V)} (h : Reach step x (l :: t) y) :
    ∃ x₁ x₂, Reach step x [] x₁ ∧ step x₁ l.act x₂ ∧ Reach step x₂ t y := by
  generalize hlt : l :: t = lt at h
  induction h generalizing l t with
  | nil => exact absurd hlt (by simp)
  | @tau s s' s'' u hs _ ih =>
      obtain ⟨x₁, x₂, h1, h2, h3⟩ := ih hlt
      exact ⟨x₁, x₂, Reach.tau hs h1, h2, h3⟩
  | @inp s s' s'' a v u hs hr _ =>
      cases hlt
      exact ⟨s, s', Reach.nil, hs, hr⟩
  | @out s s' s'' a v u hs hr _ =>
      cases hlt
      exact ⟨s, s', Reach.nil, hs, hr⟩

end Reach

/-- **Assembling a composed run.**  Two component runs and an interleaving of
    their traces yield a run of the parallel composition. -/
theorem par_reach_interleave {C V St₁ St₂ : Type}
    {step₁ : St₁ → Act C V → St₁ → Prop} {step₂ : St₂ → Act C V → St₂ → Prop}
    {x y : St₁} {z w : St₂} {a b t : List (Lbl C V)}
    (hI : Interleave a b t) (h₁ : Reach step₁ x a y) (h₂ : Reach step₂ z b w) :
    Reach (parStep step₁ step₂) (x, z) t (y, w) := by
  induction hI generalizing x z with
  | nil =>
      exact Reach.trans (par_reach_left h₁) (par_reach_right h₂)
  | @left l a b t _ ih =>
      obtain ⟨x₁, x₂, hs, hstep, hrest⟩ := Reach.cons_inv h₁
      refine Reach.trans (par_reach_left (step₂ := step₂) (z := z) hs) ?_
      have hpar : parStep step₁ step₂ (x₁, z) l.act (x₂, z) := Or.inl ⟨hstep, rfl⟩
      cases l with
      | inp c v => exact Reach.inp hpar (ih hrest h₂)
      | out c v => exact Reach.out hpar (ih hrest h₂)
  | @right l a b t _ ih =>
      obtain ⟨z₁, z₂, hs, hstep, hrest⟩ := Reach.cons_inv h₂
      refine Reach.trans (par_reach_right (step₁ := step₁) (x := x) hs) ?_
      have hpar : parStep step₁ step₂ (x, z₁) l.act (x, z₂) := Or.inr ⟨hstep, rfl⟩
      cases l with
      | inp c v => exact Reach.inp hpar (ih h₁ hrest)
      | out c v => exact Reach.out hpar (ih h₁ hrest)


namespace Sec

variable {Level Channel Value : Type} {S : Sec Level Channel}

/-- Consistency only sees a strategy's answers. -/
theorem consistent_congr {w₁ w₂ : S.Strategy Value} {t : List (Lbl Channel Value)}
    (h : ∀ a u, w₁.ω a u = w₂.ω a u) (hc : S.consistent w₁ t) : S.consistent w₂ t := by
  intro t₁ a v t₂ heq
  rw [← h a t₁]
  exact hc t₁ a v t₂ heq

/-- Weaving is symmetric in the two components. -/
theorem weave_comm {α : Type} :
    ∀ (p : List Bool) (u v : List α), weave (p.map not) v u = weave p u v
  | [], _, _ => rfl
  | true :: p, [], v => by simp only [List.map_cons, weave]; cases v <;> rfl
  | true :: p, x :: u, v => by
      simp only [List.map_cons, weave]; exact congrArg _ (weave_comm p u v)
  | false :: p, u, [] => by simp only [List.map_cons, weave]; cases u <;> rfl
  | false :: p, u, y :: v => by
      simp only [List.map_cons, weave]; exact congrArg _ (weave_comm p u v)

/-- **Weaving preserves consistency.**  If each component's trace is consistent
    with the strategy induced by freezing its partner, the woven trace is
    consistent with the global strategy. -/
theorem consistent_weave (hpub : PublicPresence S) :
    ∀ (p : List Bool) (u v : List (Lbl Channel Value)) (w : S.Strategy Value),
      S.consistent ((weaveIns (Value := Value) hpub p v).induced w) u →
      S.consistent ((weaveIns (Value := Value) hpub (p.map not) u).induced w) v →
      S.consistent w (weave p u v) := by
  intro p
  induction p with
  | nil => intro u v w _ _; exact consistent_nil w
  | cons hd p ih =>
      intro u v w hu hv
      cases hd with
      | true =>
          cases u with
          | nil => exact consistent_nil w
          | cons x u' =>
              have hA : S.consistent ((weaveIns hpub p v).induced (prependStrat [x] w)) u' :=
                consistent_congr (fun _ _ => rfl) (consistent_of_cons hu)
              have hB :
                  S.consistent ((weaveIns hpub (p.map not) u').induced (prependStrat [x] w)) v :=
                consistent_congr (fun _ _ => rfl) hv
              have hrest : S.consistent (prependStrat [x] w) (weave p u' v) := ih u' v _ hA hB
              cases x with
              | out c d => exact consistent_cons_out hrest
              | inp c d =>
                  refine consistent_cons_inp ?_ hrest
                  exact hu [] c d u' rfl
      | false =>
          cases v with
          | nil => exact consistent_nil w
          | cons y v' =>
              have hA : S.consistent ((weaveIns hpub p v').induced (prependStrat [y] w)) u :=
                consistent_congr (fun _ _ => rfl) hu
              have hB :
                  S.consistent ((weaveIns hpub (p.map not) u).induced (prependStrat [y] w)) v' :=
                consistent_congr (fun _ _ => rfl) (consistent_of_cons hv)
              have hrest : S.consistent (prependStrat [y] w) (weave p u v') := ih u v' _ hA hB
              cases y with
              | out c d => exact consistent_cons_out hrest
              | inp c d =>
                  refine consistent_cons_inp ?_ hrest
                  exact hv [] c d v' rfl

/-- The converse: a consistent woven trace induces consistency of the first
    component's trace against the frozen-partner strategy. -/
theorem consistent_weave_left (hpub : PublicPresence S) {w : S.Strategy Value}
    {p : List Bool} {u v : List (Lbl Channel Value)}
    (hE : Exact p u v) (h : S.consistent w (weave p u v)) :
    S.consistent ((weaveIns (Value := Value) hpub p v).induced w) u := by
  intro t₁ a x t₂ heq
  subst heq
  obtain ⟨rest, hsplit⟩ := weave_split p t₁ (Lbl.inp a x) t₂ v hE
  exact h (weave p t₁ v) a x rest hsplit

/-- **The freeze lemma, strong form.**  Freezing two *different* but
    ℓ-equivalent partners against two ℓ-equivalent strategies still yields
    ℓ-equivalent induced strategies.  This is what allows *both* components of a
    composition to be re-planned, rather than just one. -/
theorem seq_weaveIns_teq (hpub : PublicPresence S) {ℓ : Level} (p : List Bool)
    {b b' : List (Lbl Channel Value)} {w₁ w₂ : S.Strategy Value}
    (hw : S.seq ℓ w₁ w₂) (hb : S.teq ℓ b b') :
    S.seq ℓ ((weaveIns hpub p b).induced w₁) ((weaveIns hpub p b').induced w₂) := by
  intro a t
  have hteq : S.teq ℓ (weave p t b) (weave p t b') :=
    teq_weave hpub (rfl : S.teq ℓ t t) hb
  refine ⟨fun hl => ?_, fun hl => ?_⟩ <;>
    simp only [Insertion.induced_apply, weaveIns_σ]
  · rw [(hw a (weave p t b)).1 hl]
    exact w₂.resp_val a _ _ (teq_mono hl hteq)
  · exact dotEq.trans ((hw a (weave p t b)).2 hl)
      (w₂.resp_pres a _ _ (teq_mono hl hteq))

/-- Under public presence, ℓ-equivalent traces have the same length. -/
theorem teq_length (hpub : PublicPresence S) {ℓ : Level} {u u' : List (Lbl Channel Value)}
    (h : S.teq ℓ u u') : u.length = u'.length := by
  have := congrArg List.length h
  rwa [proj_eq_map hpub, proj_eq_map hpub, List.length_map, List.length_map] at this

end Sec

/-- Exactness depends on the first list only through its length. -/
theorem Exact.congr_length {α : Type} :
    ∀ (p : List Bool) (u u' v : List α), Exact p u v → u.length = u'.length → Exact p u' v
  | [], u, u', v, hE, hlen => by
      refine ⟨?_, hE.2⟩
      rw [hE.1] at hlen
      exact List.eq_nil_of_length_eq_zero hlen.symm
  | true :: p, [], _, _, hE, _ => absurd hE (by simp [Exact])
  | true :: p, _ :: u, u', v, hE, hlen => by
      cases u' with
      | nil => exact absurd hlen (by simp)
      | cons y u' =>
          exact Exact.congr_length p u u' v hE (by simpa using hlen)
  | false :: p, u, u', [], hE, _ => absurd hE (by simp [Exact])
  | false :: p, u, u', _ :: v, hE, hlen => Exact.congr_length p u u' v hE hlen

/-- Swapping the two components mirrors the pattern. -/
theorem Exact.map_not {α : Type} :
    ∀ (p : List Bool) (u v : List α), Exact p u v → Exact (p.map not) v u
  | [], _, _, hE => ⟨hE.2, hE.1⟩
  | true :: p, [], _, hE => absurd hE (by simp [Exact])
  | true :: p, _ :: u, v, hE => by
      simp only [List.map_cons, Bool.not_true]
      exact Exact.map_not p u v hE
  | false :: p, _, [], hE => absurd hE (by simp [Exact])
  | false :: p, u, _ :: v, hE => by
      simp only [List.map_cons, Bool.not_false]
      exact Exact.map_not p u v hE

/-- An exact pattern really does describe an interleaving. -/
theorem Exact.interleave {α : Type} :
    ∀ (p : List Bool) (u v : List α), Exact p u v → Interleave u v (weave p u v)
  | [], u, v, hE => by rw [hE.1, hE.2]; exact Interleave.nil
  | true :: p, [], _, hE => absurd hE (by simp [Exact])
  | true :: p, x :: u, v, hE => by
      simp only [weave]; exact Interleave.left (Exact.interleave p u v hE)
  | false :: p, _, [], hE => absurd hE (by simp [Exact])
  | false :: p, u, y :: v, hE => by
      simp only [weave]; exact Interleave.right (Exact.interleave p u v hE)

theorem map_not_not (p : List Bool) : (p.map not).map not = p := by
  induction p with
  | nil => rfl
  | cons hd tl ih => cases hd <;> simp only [List.map_cons, Bool.not_true, Bool.not_false, ih]

/-- Exactness depends on the second list only through its length. -/
theorem Exact.congr_length_right {α : Type} (p : List Bool) (u v v' : List α)
    (hE : Exact p u v) (hlen : v.length = v'.length) : Exact p u v' := by
  have h1 : Exact (p.map not) v u := Exact.map_not p u v hE
  have h2 : Exact (p.map not) v' u := Exact.congr_length (p.map not) v v' u h1 hlen
  have h3 : Exact ((p.map not).map not) u v' := Exact.map_not (p.map not) v' u h2
  rwa [map_not_not] at h3

end InteractiveNI
