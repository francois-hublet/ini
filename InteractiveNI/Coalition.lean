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

/-- `=_ℓ` on coalition strategies transfers to the strategies they induce. -/
theorem seq_ofCoalition {S : Sec Level Channel} {ℓ : Level}
    {w₁ w₂ : S.coalition.Strategy Value} (h : S.coalition.seq (sing ℓ) w₁ w₂) :
    S.seq ℓ (Strategy.ofCoalition w₁) (Strategy.ofCoalition w₂) := fun a t =>
  ⟨fun hl => (h a t).1 ((coalition_le_sing _ _).mpr hl),
   fun hl => (h a t).2 ((coalition_le_sing _ _).mpr hl)⟩

/-- The total version: coalition `Strat_T`-noninterference implies `Strat_T`-INI. -/
theorem StratTNI_of_coalition {S : Sec Level Channel} {St : Type}
    {step : St → Act Channel Value → St → Prop} {s : St}
    (h : S.coalition.StratTNI step s) : S.StratTNI step s := by
  intro ℓ w₁ w₂ ht₁ ht₂ hseq t₁ hp
  obtain ⟨t₂, hp₂, ht⟩ :=
    h (sing ℓ) (Strategy.toCoalition w₁) (Strategy.toCoalition w₂) ht₁ ht₂
      (seq_toCoalition hseq) t₁ (produces_toCoalition hp)
  exact ⟨t₂, ⟨hp₂.1, hp₂.2⟩, (coalition_teq_sing _ _ _).mp ht⟩

/-! ### The splitting used by the compositionality proof

    Perturbing the strategies on the channels at a level `m` is invisible to the
    coalition `Cplus m` of all levels *not* above `m`; and the channels invisible
    to that coalition are exactly those whose level is above `m`.  Over a flat
    lattice these are the channels at level `m` itself, so they all share the
    single view `π_m` -- which is what makes the layer game
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
    the absence of a causal policy is not fatal: the answer on `α` belongs to the
    lower layer and is fixed *before* the value emitted on `β`, which belongs to
    the upper one -- the program has no policy, but the run still exists. -/

/-- Add one level to a coalition. -/
def addLevel (C : Coalition Level) (n : Level) : Coalition Level := fun q => C q ∨ q = n

/-- The layer is genuinely new: the coalition only grows. -/
theorem le_addLevel {S : Sec Level Channel} (C : Coalition Level) (n : Level) :
    S.coalition.le C (addLevel C n) :=
  fun c hc => ⟨c, Or.inl hc, S.le_refl c⟩

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

end Sec

end InteractiveNI
