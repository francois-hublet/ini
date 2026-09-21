/-
  Coalition noninterference (Remark of §3 and follow-up F3).

  Reviewer #4 of the IPL submission observed that the lattice of Theorem 10 is
  "semantically incomplete": it has no level standing for the joint observations of
  two users who pool their knowledge.  The natural repair is to define
  noninterference not for single levels but for *coalitions* -- sets of levels.

  Rather than re-develop projections, strategies and INI for coalitions, we
  observe that a coalition security context is itself a security context:
  `S.coalition` has sets of levels as its levels, ordered by "every member of `C`
  is dominated by some member of `D`", each channel keeping its own levels as
  singletons.  Coalition noninterference for `S` is then literally INI for
  `S.coalition`, and every result proved for an arbitrary `Sec` applies to it.
-/
import InteractiveNI.Proj

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

namespace Sec

variable {Level Channel Value : Type}

/-- A *coalition* is a set of levels: the observers that pool their knowledge. -/
abbrev Coalition (Level : Type) := Level → Prop

/-- The singleton coalition `{ℓ}`. -/
def sing (ℓ : Level) : Coalition Level := fun c => c = ℓ

/-- **The coalition security context.**  Levels are coalitions; `C ⊑ D` iff every
    observer in `C` is dominated by some observer in `D`; a channel keeps its own
    presence and value levels, viewed as singleton coalitions. -/
def coalition (S : Sec Level Channel) : Sec (Coalition Level) Channel where
  le := fun C D => ∀ c, C c → ∃ d, D d ∧ S.le c d
  le_refl := fun _ c hc => ⟨c, hc, S.le_refl c⟩
  le_trans := by
    intro C D E h₁ h₂ c hc
    obtain ⟨d, hd, hcd⟩ := h₁ c hc
    obtain ⟨e, he, hde⟩ := h₂ d hd
    exact ⟨e, he, S.le_trans hcd hde⟩
  presL := fun a => sing (S.presL a)
  valL := fun a => sing (S.valL a)
  pres_le_val := by
    intro a c hc
    refine ⟨S.valL a, rfl, ?_⟩
    rw [show c = S.presL a from hc]
    exact S.pres_le_val a

@[simp] theorem coalition_le (S : Sec Level Channel) (C D : Coalition Level) :
    S.coalition.le C D = ∀ c, C c → ∃ d, D d ∧ S.le c d := rfl

@[simp] theorem coalition_presL (S : Sec Level Channel) (a : Channel) :
    S.coalition.presL a = sing (S.presL a) := rfl

@[simp] theorem coalition_valL (S : Sec Level Channel) (a : Channel) :
    S.coalition.valL a = sing (S.valL a) := rfl

/-- On singletons, the coalition order is the original order. -/
theorem coalition_le_sing {S : Sec Level Channel} (a ℓ : Level) :
    S.coalition.le (sing a) (sing ℓ) ↔ S.le a ℓ := by
  constructor
  · intro h
    obtain ⟨d, hd, had⟩ := h a rfl
    rw [show d = ℓ from hd] at had
    exact had
  · intro h c hc
    exact ⟨ℓ, rfl, by rw [show c = a from hc]; exact h⟩

/-! ### Singleton coalitions recover the original notions -/

theorem coalition_projLbl_sing {S : Sec Level Channel} (ℓ : Level)
    (l : Lbl Channel Value) :
    S.coalition.projLbl (sing ℓ) l = S.projLbl ℓ l := by
  have hp : ∀ a : Channel, S.coalition.le (S.coalition.presL a) (sing ℓ) ↔ S.le (S.presL a) ℓ :=
    fun a => coalition_le_sing _ _
  have hv : ∀ a : Channel, S.coalition.le (S.coalition.valL a) (sing ℓ) ↔ S.le (S.valL a) ℓ :=
    fun a => coalition_le_sing _ _
  cases l with
  | inp a v =>
      by_cases h1 : S.le (S.presL a) ℓ
      · by_cases h2 : S.le (S.valL a) ℓ
        · rw [projLbl_inp_full ((hp a).mpr h1) ((hv a).mpr h2),
              projLbl_inp_full h1 h2]
        · rw [projLbl_inp_pres ((hp a).mpr h1) (fun hc => h2 ((hv a).mp hc)),
              projLbl_inp_pres h1 h2]
      · rw [projLbl_eq_none_iff.mpr (fun hc => h1 ((hp a).mp hc)),
            projLbl_eq_none_iff.mpr h1]
  | out a v =>
      by_cases h1 : S.le (S.presL a) ℓ
      · by_cases h2 : S.le (S.valL a) ℓ
        · rw [projLbl_out_full ((hp a).mpr h1) ((hv a).mpr h2),
              projLbl_out_full h1 h2]
        · rw [projLbl_out_pres ((hp a).mpr h1) (fun hc => h2 ((hv a).mp hc)),
              projLbl_out_pres h1 h2]
      · rw [projLbl_eq_none_iff.mpr (fun hc => h1 ((hp a).mp hc)),
            projLbl_eq_none_iff.mpr h1]

theorem coalition_proj_sing {S : Sec Level Channel} (ℓ : Level)
    (t : List (Lbl Channel Value)) :
    S.coalition.proj (sing ℓ) t = S.proj ℓ t := by
  induction t with
  | nil => rfl
  | cons l t ih =>
      cases h : S.projLbl ℓ l with
      | none =>
          rw [proj_cons_none (by rw [coalition_projLbl_sing]; exact h),
              proj_cons_none h, ih]
      | some p =>
          rw [proj_cons_some (by rw [coalition_projLbl_sing]; exact h),
              proj_cons_some h, ih]

theorem coalition_teq_sing {S : Sec Level Channel} (ℓ : Level)
    (t t' : List (Lbl Channel Value)) :
    S.coalition.teq (sing ℓ) t t' ↔ S.teq ℓ t t' := by
  unfold teq
  rw [coalition_proj_sing, coalition_proj_sing]


/-! ### Strategies transport between `S` and `S.coalition` -/

/-- An `S`-strategy is an `S.coalition`-strategy: the two legality conditions are
    the same condition, by `coalition_teq_sing`. -/
def Strategy.toCoalition {S : Sec Level Channel} (w : S.Strategy Value) :
    S.coalition.Strategy Value where
  ω := w.ω
  resp_val  := fun a t₁ t₂ h => w.resp_val  a t₁ t₂ ((coalition_teq_sing _ _ _).mp h)
  resp_pres := fun a t₁ t₂ h => w.resp_pres a t₁ t₂ ((coalition_teq_sing _ _ _).mp h)

/-- …and conversely. -/
def Strategy.ofCoalition {S : Sec Level Channel} (w : S.coalition.Strategy Value) :
    S.Strategy Value where
  ω := w.ω
  resp_val  := fun a t₁ t₂ h => w.resp_val  a t₁ t₂ ((coalition_teq_sing _ _ _).mpr h)
  resp_pres := fun a t₁ t₂ h => w.resp_pres a t₁ t₂ ((coalition_teq_sing _ _ _).mpr h)

@[simp] theorem toCoalition_ω {S : Sec Level Channel} (w : S.Strategy Value) :
    (Strategy.toCoalition w).ω = w.ω := rfl

@[simp] theorem ofCoalition_ω {S : Sec Level Channel} (w : S.coalition.Strategy Value) :
    (Strategy.ofCoalition w).ω = w.ω := rfl

theorem seq_toCoalition {S : Sec Level Channel} {ℓ : Level} {w₁ w₂ : S.Strategy Value}
    (h : S.seq ℓ w₁ w₂) :
    S.coalition.seq (sing ℓ) (Strategy.toCoalition w₁) (Strategy.toCoalition w₂) := by
  intro a t
  refine ⟨fun hl => (h a t).1 ?_, fun hl => (h a t).2 ?_⟩
  · exact (coalition_le_sing _ _).mp hl
  · exact (coalition_le_sing _ _).mp hl

theorem consistent_toCoalition {S : Sec Level Channel} {w : S.Strategy Value}
    {t : List (Lbl Channel Value)} (h : S.consistent w t) :
    S.coalition.consistent (Strategy.toCoalition w) t := h

theorem produces_toCoalition {S : Sec Level Channel} {St : Type}
    {step : St → Act Channel Value → St → Prop} {w : S.Strategy Value} {s : St}
    {t : List (Lbl Channel Value)} (h : S.produces step w s t) :
    S.coalition.produces step (Strategy.toCoalition w) s t :=
  ⟨h.1, consistent_toCoalition h.2⟩

/-! ### Coalition noninterference is stronger than INI -/

/-- **Coalition noninterference implies INI.**  Taking singleton coalitions
    recovers the original notion, so the coalition-based property is at least as
    strong.  Theorem `A_not_coalitionNI` of `Cex1Coalition.lean` shows that it is
    *strictly* stronger. -/
theorem StratNI_of_coalition {S : Sec Level Channel} {St : Type}
    {step : St → Act Channel Value → St → Prop} {s : St}
    (h : S.coalition.StratNI step s) : S.StratNI step s := by
  intro ℓ w₁ w₂ _ _ hseq t₁ hp
  obtain ⟨t₂, hp₂, ht⟩ :=
    h (sing ℓ) (Strategy.toCoalition w₁) (Strategy.toCoalition w₂) trivial trivial
      (seq_toCoalition hseq) t₁ (produces_toCoalition hp)
  exact ⟨t₂, ⟨hp₂.1, hp₂.2⟩, (coalition_teq_sing _ _ _).mp ht⟩


/-- The total version: coalition `Strat_T`-noninterference implies `Strat_T`-INI. -/
theorem StratTNI_of_coalition {S : Sec Level Channel} {St : Type}
    {step : St → Act Channel Value → St → Prop} {s : St}
    (h : S.coalition.StratTNI step s) : S.StratTNI step s := by
  intro ℓ w₁ w₂ ht₁ ht₂ hseq t₁ hp
  obtain ⟨t₂, hp₂, ht⟩ :=
    h (sing ℓ) (Strategy.toCoalition w₁) (Strategy.toCoalition w₂) ht₁ ht₂
      (seq_toCoalition hseq) t₁ (produces_toCoalition hp)
  exact ⟨t₂, ⟨hp₂.1, hp₂.2⟩, (coalition_teq_sing _ _ _).mp ht⟩

/-- Strategies transport back, and `seq` with them. -/
theorem seq_ofCoalition {S : Sec Level Channel} {ℓ : Level}
    {w₁ w₂ : S.coalition.Strategy Value} (h : S.coalition.seq (sing ℓ) w₁ w₂) :
    S.seq ℓ (Strategy.ofCoalition w₁) (Strategy.ofCoalition w₂) := fun a t =>
  ⟨fun hl => (h a t).1 ((coalition_le_sing _ _).mpr hl),
   fun hl => (h a t).2 ((coalition_le_sing _ _).mpr hl)⟩

/-! ### The splitting used by the compositionality proof

    Perturbing the strategies on the channels at a level `m` is invisible to the
    coalition `Cplus m` of all levels *not* above `m`; and the channels invisible
    to that coalition are exactly those whose level is above `m`.  Over a flat
    lattice these are the channels at level `m` itself, so they all share the
    single view `π_m` -- which is what makes the game of `coalition-composes.md`
    one of perfect information. -/

/-- The coalition of every level that does **not** dominate `m`. -/
def Cplus (S : Sec Level Channel) (m : Level) : Coalition Level := fun q => ¬ S.le m q

/-- **Splitting.**  A channel is visible to `Cplus m` exactly when its level does
    not dominate `m`.  In particular the channels made adversarial by a
    perturbation at `m` are precisely those at levels above `m`. -/
theorem vis_Cplus {S : Sec Level Channel} (m : Level) (a : Channel) :
    S.coalition.le (sing (S.valL a)) (Cplus S m) ↔ ¬ S.le m (S.valL a) := by
  constructor
  · intro h hm
    obtain ⟨q, hq, hle⟩ := h (S.valL a) rfl
    exact hq (S.le_trans hm hle)
  · intro h c hc
    exact ⟨S.valL a, h, by rw [show c = S.valL a from hc]; exact S.le_refl _⟩

/-- `C ⊆ Cplus m` whenever `m` is invisible to `C`: the hybrid of the proof is
    therefore a *strengthening* of the observation coalition. -/
theorem le_Cplus {S : Sec Level Channel} {C : Coalition Level} {m : Level}
    (h : ¬ ∃ c, C c ∧ S.le m c) : S.coalition.le C (Cplus S m) := by
  intro c hc
  exact ⟨c, fun hm => h ⟨c, hc, hm⟩, S.le_refl c⟩

/-- Over a **flat** lattice -- distinct levels incomparable -- the channels above
    `m` are exactly those at level `m`, so they share the single view `π_m`.
    This is the hypothesis the perfect-information game needs. -/
theorem flat_above {S : Sec Level Channel}
    (hflat : ∀ x y : Level, S.le x y → x = y) (m : Level) (a : Channel) :
    S.le m (S.valL a) ↔ S.valL a = m :=
  ⟨fun h => (hflat _ _ h).symm, fun h => by rw [h]; exact S.le_refl m⟩

/-! ### The hypothesis the game really needs

    Flatness of the whole lattice is far more than the argument uses -- and, in a
    join-semilattice, it is unsatisfiable as soon as there are two levels, since
    `x ⊑ x ⊔ y`.  What the perfect-information game needs is only that the levels
    **carrying channels** are pairwise incomparable.  The lattice itself may be
    arbitrary: it may have a bottom, a top, and any number of levels that no
    channel is assigned to. -/

/-- The levels in the image of `valL` are pairwise incomparable. -/
def ChannelAntichain (S : Sec Level Channel) : Prop :=
  ∀ a b : Channel, S.le (S.valL a) (S.valL b) → S.le (S.valL b) (S.valL a)

/-- A flat lattice is a (degenerate) instance. -/
theorem channelAntichain_of_flat {S : Sec Level Channel}
    (hflat : ∀ x y : Level, S.le x y → x = y) : S.ChannelAntichain := by
  intro a b h
  rw [hflat _ _ h]
  exact S.le_refl _

/-- Under the antichain hypothesis, the channels made adversarial by a
    perturbation at `d` -- those invisible to `Cplus (valL d)`, i.e. at a level
    above `valL d` -- are exactly the channels visible to `d`'s *own* user. -/
theorem anti_adversarial {S : Sec Level Channel} (h : S.ChannelAntichain)
    (d a : Channel) :
    ¬ S.coalition.le (sing (S.valL a)) (Cplus S (S.valL d))
      ↔ S.le (S.valL a) (S.valL d) := by
  rw [vis_Cplus, not_not]
  exact ⟨h d a, h a d⟩

/-- **A single view.**  All those channels moreover share one and the same view:
    a channel `b` is visible to the user of an adversarial channel `a` exactly
    when it is visible to the user of `d`.  This is the fact that turns the
    policy game into one of perfect information. -/
theorem anti_sameView {S : Sec Level Channel} (h : S.ChannelAntichain)
    {d a : Channel} (ha : S.le (S.valL d) (S.valL a)) (b : Channel) :
    S.le (S.valL b) (S.valL a) ↔ S.le (S.valL b) (S.valL d) :=
  ⟨fun hb => S.le_trans hb (h d a ha), fun hb => S.le_trans hb ha⟩

/-! ### Uniformity: coalition noninterference determines the winning moves

    The step that the policy argument of `coalition-composes.md` really needs is
    not determinacy but the following.  Let `h` be the history a component has
    already produced and let `D` be any coalition that sees every channel
    occurring in `h`.  Then whether a given continuation exists depends on the
    strategy *only through its restriction to* `Vis D`.

    The order-theoretic content is the lemma below: when presence is public and
    every channel of a trace is visible at `ℓ`, the projection `π_ℓ` loses
    nothing, so `π_ℓ t = π_ℓ t'` forces `t = t'`.  Coalition noninterference at
    `D` then transports a run witnessing a continuation of `h` from one strategy
    to the other, and the transported run still extends `h` -- which is exactly
    what an incremental construction of the policy needs, and what the projection
    alone does not give when some channel of `h` is hidden at `D`.

    Note that `D` may always be *chosen* large enough: take
    `D = C⁺ ∪ {valL α | α occurs in h}`.  This is why the obstruction identified
    for the game formulation -- a component committing to a move that the user it
    next reads from cannot see -- is not fatal: the coalition that does see that
    move is itself available, and coalition noninterference holds at it too. -/

/-- A label is fully visible at `ℓ`: both its presence and its value. -/
def VisLbl (S : Sec Level Channel) (ℓ : Level) : Lbl Channel Value → Prop
  | .inp a _ => S.le (S.presL a) ℓ ∧ S.le (S.valL a) ℓ
  | .out a _ => S.le (S.presL a) ℓ ∧ S.le (S.valL a) ℓ

/-- Every label of the trace is fully visible at `ℓ`. -/
def VisTrace (S : Sec Level Channel) (ℓ : Level) (t : List (Lbl Channel Value)) : Prop :=
  ∀ l ∈ t, S.VisLbl ℓ l

theorem proj_cons_vis {S : Sec Level Channel} {ℓ : Level} {a : Channel} {v : Value}
    {t : List (Lbl Channel Value)} (h : S.VisLbl ℓ (Lbl.inp a v)) :
    S.proj ℓ (Lbl.inp a v :: t) = PLbl.inp a (some v) :: S.proj ℓ t := by
  simp [proj, projLbl, h.1, h.2]

theorem proj_cons_vis' {S : Sec Level Channel} {ℓ : Level} {a : Channel} {v : Value}
    {t : List (Lbl Channel Value)} (h : S.VisLbl ℓ (Lbl.out a v)) :
    S.proj ℓ (Lbl.out a v :: t) = PLbl.out a (some v) :: S.proj ℓ t := by
  simp [proj, projLbl, h.1, h.2]

/-- **Projections lose nothing on fully visible traces.**  If every channel used
    by `t` and by `t'` is visible at `ℓ` -- presence *and* value -- then
    `t =_ℓ t'` forces `t = t'`. -/
theorem eq_of_teq_vis {S : Sec Level Channel} {ℓ : Level} :
    ∀ {t t' : List (Lbl Channel Value)}, S.VisTrace ℓ t → S.VisTrace ℓ t' →
      S.teq ℓ t t' → t = t' := by
  intro t
  induction t with
  | nil =>
      intro t' _ ht' h
      cases t' with
      | nil => rfl
      | cons l' u' =>
          exfalso
          have hl' : S.VisLbl ℓ l' := ht' l' (by simp)
          cases l' with
          | inp a v => rw [teq, proj_cons_vis hl'] at h; simp [proj] at h
          | out a v => rw [teq, proj_cons_vis' hl'] at h; simp [proj] at h
  | cons l u ih =>
      intro t' ht ht' h
      have hl : S.VisLbl ℓ l := ht l (by simp)
      cases t' with
      | nil =>
          exfalso
          cases l with
          | inp a v => rw [teq, proj_cons_vis hl] at h; simp [proj] at h
          | out a v => rw [teq, proj_cons_vis' hl] at h; simp [proj] at h
      | cons l' u' =>
          have hl' : S.VisLbl ℓ l' := ht' l' (by simp)
          have hu : S.VisTrace ℓ u := fun x hx => ht x (by simp [hx])
          have hu' : S.VisTrace ℓ u' := fun x hx => ht' x (by simp [hx])
          cases l with
          | inp a v =>
              cases l' with
              | inp b w =>
                  rw [teq, proj_cons_vis hl, proj_cons_vis hl'] at h
                  simp only [List.cons.injEq] at h
                  obtain ⟨he, ht2⟩ := h
                  simp only [PLbl.inp.injEq, Option.some.injEq] at he
                  rw [he.1, he.2, ih hu hu' ht2]
              | out b w =>
                  rw [teq, proj_cons_vis hl, proj_cons_vis' hl'] at h
                  simp at h
          | out a v =>
              cases l' with
              | inp b w =>
                  rw [teq, proj_cons_vis' hl, proj_cons_vis hl'] at h
                  simp at h
              | out b w =>
                  rw [teq, proj_cons_vis' hl, proj_cons_vis' hl'] at h
                  simp only [List.cons.injEq] at h
                  obtain ⟨he, ht2⟩ := h
                  simp only [PLbl.out.injEq, Option.some.injEq] at he
                  rw [he.1, he.2, ih hu hu' ht2]

/-- The coalition form: a trace all of whose channels are seen by some member of
    the coalition `D` -- with presence public -- is determined by `π_D`. -/
theorem eq_of_coalition_teq_vis {S : Sec Level Channel} {D : Coalition Level}
    {t t' : List (Lbl Channel Value)}
    (ht : S.coalition.VisTrace D t) (ht' : S.coalition.VisTrace D t')
    (h : S.coalition.teq D t t') : t = t' :=
  eq_of_teq_vis ht ht' h

/-! ### Adaptation preserves the visible inputs

    In the composition, what each component faces is the strategy `ω` relativised
    to the *other* component's trace.  The lemma below says that this relativised
    strategy, on the channels the coalition can see, depends on the partner only
    through what the coalition can see of it.

    Consequently the mutual-adaptation iteration behind Theorem 20 stays inside a
    single `=_C` class: adapt `A` to `B`'s trace, then `B` to the new `A`-trace,
    and so on; every strategy that arises along the way is `=_C`-equivalent to the
    one before, so coalition noninterference applies at *every* step, and every
    adaptation leaves the inputs on `Vis C` untouched.  The whole difficulty of
    the general case is therefore concentrated in one place: whether the iteration
    has a fixed point.  All the discrepancy between successive rounds lives on the
    channels invisible at `C`. -/

/-- A channel visible to the coalition has a *down-closed* view: its user sees
    only channels the coalition sees.  Hence two traces the coalition cannot tell
    apart are indistinguishable to that user as well. -/
theorem teq_of_vis {S : Sec Level Channel} {C : Coalition Level} {a : Channel}
    (hvis : S.coalition.le (sing (S.valL a)) C)
    {t t' : List (Lbl Channel Value)} (h : S.coalition.teq C t t') :
    S.coalition.teq (S.coalition.valL a) t t' :=
  Sec.teq_mono hvis h

/-- **Adaptation is invisible at `C`.**  On a channel the coalition sees, a legal
    strategy answers the same on any two traces the coalition cannot tell apart --
    so replacing the partner's trace by a `C`-equivalent one changes no visible
    input. -/
theorem adapt_vis {S : Sec Level Channel} {C : Coalition Level}
    (w : S.coalition.Strategy Value) {a : Channel}
    (hvis : S.coalition.le (sing (S.valL a)) C)
    {t t' : List (Lbl Channel Value)} (h : S.coalition.teq C t t') :
    w.ω a t = w.ω a t' :=
  w.resp_val a t t' (teq_of_vis hvis h)

/-! ### Layering: peeling the invisible channels from the *bottom*

    Peeling the levels above `m` from the top fails, because preserving the levels
    above `m` makes the level-`m` channels visible. Peeling from the bottom does
    not: enlarging the observing coalition `Cplus m` by a single level `n ⊒ m`
    keeps invisible exactly the channels whose level is above `m` and **not**
    below `n`.

    That is the order-theoretic content of a triangular decomposition. Writing
    `C_n = Cplus m ∪ {n}`, coalition noninterference at `C_n` says that a
    component's behaviour on `Vis(Cplus m) ∪ ↓n` does not depend on the strategy
    at levels `⋢ n`. So the layers can be solved bottom-up: the level-`m` layer is
    closed (an input at level `m` reads only the history at levels `⊑ m`), and
    each further layer sees all the layers already fixed and nothing above it.

    Within a single layer every newly adversarial channel carries the same level,
    which is the situation Theorem 20 already handles. This is why the
    counterexample `NoPolicy.Q` is not fatal: the answer on `α` belongs to the
    lower layer and is fixed *before* the value emitted on `β`, which belongs to
    the upper one -- the program has no policy, but the run still exists. -/

/-- Add one level to a coalition. -/
def addLevel (C : Coalition Level) (n : Level) : Coalition Level := fun q => C q ∨ q = n

/-- **Bottom-up splitting.** A channel is visible to `Cplus m ∪ {n}` exactly when
    its level fails to dominate `m`, or is dominated by `n`.  Equivalently: the
    channels still invisible are those at levels above `m` and not below `n`. -/
theorem vis_Cplus_add {S : Sec Level Channel} (m n : Level) (a : Channel) :
    S.coalition.le (sing (S.valL a)) (addLevel (Cplus S m) n)
      ↔ (¬ S.le m (S.valL a) ∨ S.le (S.valL a) n) := by
  constructor
  · intro h
    obtain ⟨d, hd, hle⟩ := h (S.valL a) rfl
    rcases hd with hd | rfl
    · exact Or.inl fun hm => hd (S.le_trans hm hle)
    · exact Or.inr hle
  · intro h
    rcases h with h | h
    · exact fun c hc => ⟨S.valL a, Or.inl h, by rw [show c = S.valL a from hc]; exact S.le_refl _⟩
    · exact fun c hc => ⟨n, Or.inr rfl, by rw [show c = S.valL a from hc]; exact h⟩

/-- The layer is genuinely new: the coalition only grows. -/
theorem le_addLevel {S : Sec Level Channel} (C : Coalition Level) (n : Level) :
    S.coalition.le C (addLevel C n) :=
  fun c hc => ⟨c, Or.inl hc, S.le_refl c⟩

/-- **The bottom layer is closed.**  A channel visible to `Cplus m ∪ {m}` has a
    view contained in that same set: an input at level `m` reads only what the
    coalition `Cplus m ∪ {m}` already sees.  So the level-`m` layer can be solved
    without reference to anything above it. -/
theorem layer_closed {S : Sec Level Channel} (m : Level) (a b : Channel)
    (ha : S.coalition.le (sing (S.valL a)) (addLevel (Cplus S m) m))
    (hb : S.le (S.valL b) (S.valL a)) :
    S.coalition.le (sing (S.valL b)) (addLevel (Cplus S m) m) := by
  rw [vis_Cplus_add] at ha ⊢
  rcases ha with ha | ha
  · exact Or.inl fun hm => ha (S.le_trans hm hb)
  · exact Or.inr (S.le_trans hb ha)

/-- **Layer flatness.**  Suppose the level `n` is not yet visible to the coalition
    `C`.  Then, inside the layer `C ∪ {n}`, every channel *above* `n` is at `n`:
    the channels that the layer makes adversarial all carry one and the same
    level, hence -- by `anti_sameView` -- one and the same view.

    This is the hypothesis Theorem 20's argument consumes, and the point of
    peeling from the bottom is that it now holds **by construction** at every
    layer, whatever the lattice.  It is what the unlayered argument could not
    obtain: there, the channels above the perturbed level spanned several levels
    with mutually incomparable views. -/
theorem layer_flat {S : Sec Level Channel} {C : Coalition Level} {n : Level}
    (hn : ¬ S.coalition.le (sing n) C) {a : Channel}
    (hvis : S.coalition.le (sing (S.valL a)) (addLevel C n))
    (hup : S.le n (S.valL a)) : S.le (S.valL a) n := by
  obtain ⟨d, hd, hle⟩ := hvis (S.valL a) rfl
  rcases hd with hd | rfl
  · exact absurd (fun c hc => ⟨d, hd, by rw [show c = n from hc]; exact S.le_trans hup hle⟩) hn
  · exact hle

/-- Consequently the channels a layer makes adversarial share a single view: for
    any two of them, a channel is visible to one exactly when it is visible to the
    other. -/
theorem layer_sameView {S : Sec Level Channel} {C : Coalition Level} {n : Level}
    (hn : ¬ S.coalition.le (sing n) C) {a b : Channel}
    (hva : S.coalition.le (sing (S.valL a)) (addLevel C n)) (hua : S.le n (S.valL a))
    (hvb : S.coalition.le (sing (S.valL b)) (addLevel C n)) (hub : S.le n (S.valL b))
    (c : Channel) :
    S.le (S.valL c) (S.valL a) ↔ S.le (S.valL c) (S.valL b) :=
  ⟨fun h => S.le_trans (S.le_trans h (layer_flat hn hva hua)) hub,
   fun h => S.le_trans (S.le_trans h (layer_flat hn hvb hub)) hua⟩

/-! ### The reduced system carries everything a lower coalition needs

    Layer `i` works with the *reduced system* `R_i(P) = {π_{C_i}(t) | t a run of
    P}`.  For this to be a legitimate object of the argument, coalition
    noninterference of `P` must transfer to it -- and it does, because for any
    coalition `D` below `C_i` the `D`-observation is already computable from the
    `C_i`-observation.  So the `D`-observations of the reduced system *are* the
    `D`-observations of `P`, and depend only on `ω` restricted to `Vis D`.

    Together with `layer_flat` this is what makes the layered induction work: at
    layer `i` the only channels carrying a value invisible at `C_{i-1}` are those
    at level `n_i`, every higher channel having been erased to a silent, publicly
    present tick. -/
theorem layer_reduces {S : Sec Level Channel} {C D : Coalition Level}
    (hle : S.coalition.le D C) (t : List (Lbl Channel Value)) :
    S.coalition.proj D t
      = (S.coalition.proj C t).filterMap (S.coalition.reproj D) :=
  Sec.proj_reproj hle t

/-- Two traces a layer cannot separate are separated by no coalition below it. -/
theorem layer_teq {S : Sec Level Channel} {C D : Coalition Level}
    (hle : S.coalition.le D C) {t t' : List (Lbl Channel Value)}
    (h : S.coalition.teq C t t') : S.coalition.teq D t t' :=
  Sec.teq_mono hle h

end Sec

end InteractiveNI
