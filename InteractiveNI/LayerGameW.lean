/-
  **The layer game, without a bound on the play.**

  `LayerGame.lean` walks the target: positions are pairs (`C`-view, `n`-view)
  aligned entry by entry, and determinacy is an induction on the target, which
  bounds the play.  Both rest on presence being public, which makes `π_C` keep
  every label.

  Here the game is recast so that neither is needed.

  * A position is the `n`-view alone -- the adversary's own information.  The
    `C`-progress is the component's business and stays hidden; realisability is
    checked once, at the end, so announcing an impossible move simply loses.
  * The component's winning strategies form an inductive **type**, so a play can be
    read off one by recursion, and the type being inductive is exactly the
    well-foundedness that the target used to supply.
  * Determinacy is then a least-fixed-point argument rather than an induction on
    the target: from a position with no winning strategy the adversary can stay
    outside forever, and a *finite* run realising the target contradicts that.  No
    reasoning about infinite plays is needed, because the contradiction comes from
    the component's side, where runs are finite by construction.
-/
import InteractiveNI.LayerGame

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

namespace Sec

variable {Level Channel Value : Type}

/-! ### Positions of an observation lift to positions of a trace

    This is the one positional fact that survives without public presence: `π_ℓ`
    is a `filterMap`, and a decomposition of a `filterMap` lifts, only to a
    different index. -/

theorem filterMap_eq_append_cons {α β : Type} (f : α → Option β) :
    ∀ (t : List α) (o₁ : List β) (q : β) (o₂ : List β),
      t.filterMap f = o₁ ++ q :: o₂ →
      ∃ t₁ l t₂, t = t₁ ++ l :: t₂ ∧ t₁.filterMap f = o₁ ∧ f l = some q := by
  intro t
  induction t with
  | nil => intro o₁ q o₂ h; cases o₁ <;> simp at h
  | cons x t ih =>
      intro o₁ q o₂ h
      rcases hx : f x with _ | y
      · rw [List.filterMap_cons_none hx] at h
        obtain ⟨t₁, l, t₂, rfl, h2, h3⟩ := ih o₁ q o₂ h
        exact ⟨x :: t₁, l, t₂, rfl, by rw [List.filterMap_cons_none hx]; exact h2, h3⟩
      · rw [List.filterMap_cons_some hx] at h
        cases o₁ with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at h
            exact ⟨[], x, t, rfl, rfl, by rw [hx, h.1]⟩
        | cons z o₁ =>
            simp only [List.cons_append, List.cons.injEq] at h
            obtain ⟨t₁, l, t₂, rfl, h2, h3⟩ := ih o₁ q o₂ h.2
            exact ⟨x :: t₁, l, t₂, rfl,
              by rw [List.filterMap_cons_some hx, h2, h.1], h3⟩

theorem proj_split_gen {S : Sec Level Channel} {ℓ : Level}
    {t : List (Lbl Channel Value)} {o₁ o₂ : List (PLbl Channel Value)}
    {q : PLbl Channel Value} (h : S.proj ℓ t = o₁ ++ q :: o₂) :
    ∃ t₁ l t₂, t = t₁ ++ l :: t₂ ∧ S.proj ℓ t₁ = o₁ ∧ S.projLbl ℓ l = some q :=
  filterMap_eq_append_cons _ t o₁ q o₂ h

theorem projLbl_inp_inv {S : Sec Level Channel} {ℓ : Level} {x : Lbl Channel Value}
    {a : Channel} {ov : Option Value}
    (h : S.projLbl ℓ x = some (PLbl.inp a ov)) : ∃ v, x = Lbl.inp a v := by
  cases x with
  | inp b v =>
      by_cases hp : S.le (S.presL b) ℓ
      · by_cases hv : S.le (S.valL b) ℓ
        · rw [projLbl_inp_full hp hv] at h
          injection h with h; injection h with hb _; exact ⟨v, by rw [hb]⟩
        · rw [projLbl_inp_pres hp hv] at h
          injection h with h; injection h with hb _; exact ⟨v, by rw [hb]⟩
      · rw [projLbl_inp_hidden hp] at h; exact absurd h (by simp)
  | out b v =>
      by_cases hp : S.le (S.presL b) ℓ
      · by_cases hv : S.le (S.valL b) ℓ
        · rw [projLbl_out_full hp hv] at h; injection h with h; exact absurd h (by simp)
        · rw [projLbl_out_pres hp hv] at h; injection h with h; exact absurd h (by simp)
      · rw [projLbl_out_hidden hp] at h; exact absurd h (by simp)

/-! ### The game -/

/-- The labels the adversary controls: inputs on channels the layer exposes. -/
def AdvLbl {Channel Value : Type} (N : Channel → Prop) (q : PLbl Channel Value) : Prop :=
  ∃ (a : Channel) (ov : Option Value), q = PLbl.inp a ov ∧ N a

/-- **A winning strategy for the component**, as data.  `R` says the `n`-view
    reached is one the component can realise together with its target. -/
inductive WinStrat {Channel Value : Type} (N : Channel → Prop)
    (R : List (PLbl Channel Value) → Prop)
    (env : Channel → List (PLbl Channel Value) → Value → Prop) :
    List (PLbl Channel Value) → Type where
  | done {dn} : R dn → WinStrat N R env dn
  | move {dn} (q : PLbl Channel Value) : ¬ AdvLbl N q →
      WinStrat N R env (dn ++ [q]) → WinStrat N R env dn
  | read {dn} (a : Channel) : N a →
      (∀ v : Value, env a dn v → WinStrat N R env (dn ++ [PLbl.inp a (some v)])) →
      WinStrat N R env dn

/-- What noninterference supplies: against every environment-compatible adversary
    the component has a play reaching a realisable `n`-view. -/
def ForcedW {Channel Value : Type} (N : Channel → Prop)
    (R : List (PLbl Channel Value) → Prop)
    (env : Channel → List (PLbl Channel Value) → Value → Prop)
    (dn : List (PLbl Channel Value)) : Prop :=
  ∀ adv : Channel → List (PLbl Channel Value) → Value,
    (∀ a q, env a q (adv a q)) →
    ∃ o : List (PLbl Channel Value), R (dn ++ o) ∧
      (∀ pre e post, o = pre ++ e :: post → ∀ (a : Channel) (ov : Option Value),
        e = PLbl.inp a ov → N a → e = PLbl.inp a (some (adv a (dn ++ pre))))

/-! ### Determinacy -/

/-- Positions with no winning strategy. -/
def Out {Channel Value : Type} (N : Channel → Prop)
    (R : List (PLbl Channel Value) → Prop)
    (env : Channel → List (PLbl Channel Value) → Value → Prop)
    (dn : List (PLbl Channel Value)) : Prop :=
  ¬ Nonempty (WinStrat N R env dn)

theorem Out.not_R {N : Channel → Prop} {R env} {dn : List (PLbl Channel Value)}
    (h : Out N R env dn) : ¬ R dn := fun hr => h ⟨WinStrat.done hr⟩

theorem Out.move {N : Channel → Prop} {R env} {dn : List (PLbl Channel Value)}
    (h : Out N R env dn) {q : PLbl Channel Value} (hq : ¬ AdvLbl N q) :
    Out N R env (dn ++ [q]) := fun ⟨w⟩ => h ⟨WinStrat.move q hq w⟩

/-- At a position with no winning strategy the adversary has, on every channel it
    controls, an answer that keeps the component outside. -/
theorem Out.read {N : Channel → Prop} {R env} {dn : List (PLbl Channel Value)}
    (h : Out N R env dn) {a : Channel} (ha : N a) :
    ∃ v, env a dn v ∧ Out N R env (dn ++ [PLbl.inp a (some v)]) := by
  refine Classical.byContradiction fun hc => ?_
  refine h ⟨WinStrat.read a ha (fun v hv => ?_)⟩
  have hno : ¬ Out N R env (dn ++ [PLbl.inp a (some v)]) := fun ho => hc ⟨v, hv, ho⟩
  exact Classical.choice (Classical.byContradiction hno)

/-- The adversary that punishes: at a position with no winning strategy it plays,
    on each channel it controls, an answer keeping the component outside; anywhere
    else it plays whatever the environment allows. -/
noncomputable def punish {Channel Value : Type} (N : Channel → Prop)
    (R : List (PLbl Channel Value) → Prop)
    (env : Channel → List (PLbl Channel Value) → Value → Prop) (dflt : Value)
    (a : Channel) (dn : List (PLbl Channel Value)) : Value :=
  @Classical.epsilon _ ⟨dflt⟩ (fun v => env a dn v ∧
    (N a → Out N R env dn → Out N R env (dn ++ [PLbl.inp a (some v)])))

theorem punish_spec {N : Channel → Prop} {R env} (hne : ∀ a q, ∃ v, env a q v)
    (dflt : Value) (a : Channel) (dn : List (PLbl Channel Value)) :
    env a dn (punish N R env dflt a dn) ∧
    (N a → Out N R env dn →
      Out N R env (dn ++ [PLbl.inp a (some (punish N R env dflt a dn))])) := by
  have hex : ∃ v, env a dn v ∧
      (N a → Out N R env dn → Out N R env (dn ++ [PLbl.inp a (some v)])) := by
    by_cases hc : N a ∧ Out N R env dn
    · obtain ⟨v, hv, ho⟩ := hc.2.read hc.1
      exact ⟨v, hv, fun _ _ => ho⟩
    · obtain ⟨v, hv⟩ := hne a dn
      exact ⟨v, hv, fun hN hO => absurd ⟨hN, hO⟩ hc⟩
  unfold punish
  exact Classical.epsilon_spec hex

/-- **The complement is a trap.**  Against the punishing adversary, a position with
    no winning strategy stays one, however long the play. -/
theorem out_append {N : Channel → Prop} {R env} (hne : ∀ a q, ∃ v, env a q v)
    (dflt : Value) :
    ∀ (o dn : List (PLbl Channel Value)), Out N R env dn →
      (∀ pre e post, o = pre ++ e :: post → ∀ (a : Channel) (ov : Option Value),
        e = PLbl.inp a ov → N a →
        e = PLbl.inp a (some (punish N R env dflt a (dn ++ pre)))) →
      Out N R env (dn ++ o) := by
  intro o
  induction o with
  | nil => intro dn h _; simpa using h
  | cons e o ih =>
      intro dn hout hcons
      have hstep : Out N R env (dn ++ [e]) := by
        by_cases hadv : AdvLbl N e
        · obtain ⟨a, ov, rfl, hN⟩ := hadv
          have := hcons [] _ o rfl a ov rfl hN
          simp only [List.append_nil] at this
          rw [this]
          exact (punish_spec hne dflt a dn).2 hN hout
        · exact hout.move hadv
      have := ih (dn ++ [e]) hstep (by
        intro pre e' post hsp a ov he hN
        have := hcons (e :: pre) e' post (by rw [hsp]; rfl) a ov he hN
        simpa [List.append_assoc] using this)
      simpa [List.append_assoc] using this

/-- **Determinacy.**  A component that can realise its target against every
    adversary has a winning strategy.  No bound on the play is needed: the
    contradiction comes from the component's side, where runs are finite. -/
theorem nonempty_winStrat_of_forced {N : Channel → Prop} {R env}
    (hne : ∀ a q, ∃ v, env a q v) (dflt : Value)
    {dn : List (PLbl Channel Value)} (h : ForcedW N R env dn) :
    Nonempty (WinStrat N R env dn) := by
  refine Classical.byContradiction fun hout => ?_
  obtain ⟨o, hR, hcons⟩ := h (punish N R env dflt)
    (fun a q => (punish_spec hne dflt a q).1)
  exact (out_append hne dflt o dn hout hcons).not_R hR

/-! ### The game is won: from noninterference to `ForcedW`

    Compare `forced2_of_INI`: there the play was a list of *pairs* of labels,
    aligned entry by entry with the trace, which forced `π_C` and `π_n` to keep
    every label -- i.e. presence public at both levels.  Here the play is the
    `n`-view itself, and the only positional fact needed is `proj_split_gen`,
    which holds for an arbitrary projection.  The presence of a channel the layer
    exposes is visible at `n` for free, since `ℓ₂(α) ⊑ ℓ₁(α) ⊑ n` there. -/

theorem forcedW_of_INI {St : Type} {step : St → Act Channel Value → St → Prop} {s : St}
    {C n : Level} {N : Channel → Prop} {w : S.Strategy Value}
    (htot : w.total)
    (hNn : ∀ a : Channel, N a → S.le n (S.valL a))
    (hNn' : ∀ a : Channel, N a → S.le (S.valL a) n)
    (hNC : ∀ a : Channel, N a → ¬ S.le (S.valL a) C)
    (hINI : S.StratTNI step s)
    {b : List (Lbl Channel Value)} (hb : S.produces step w s b) :
    ForcedW N (RedPair S step s C n (S.proj C b)) (fun _ _ _ => True) [] := by
  intro adv _
  obtain ⟨t, hprod, hteq⟩ := hINI C w (advStratL S C n N hNn w adv) htot
    (advStratL_total hNn htot adv) (seq_advStratL hNn htot adv) b hb
  obtain ⟨⟨s', hreach⟩, hcons⟩ := hprod
  refine ⟨S.proj n t, ⟨t, s', hreach, hteq.symm, rfl⟩, ?_⟩
  intro pre e post hsplit a ov he1 hN
  obtain ⟨t₁, x, t₂, hdec, hu, hx⟩ := proj_split_gen hsplit
  rw [he1] at hx
  obtain ⟨v, rfl⟩ := projLbl_inp_inv hx
  have hpres : S.le (S.presL a) n := S.le_trans (S.pres_le_val a) (hNn' a hN)
  rw [projLbl_inp_full hpres (hNn' a hN)] at hx
  have hev : e = PLbl.inp a (some v) := by injection hx with h; exact he1.trans h.symm
  have hval : (advStratL S C n N hNn w adv).ω a t₁ v := hcons t₁ a v t₂ hdec
  simp only [advStratL, if_neg (hNC a hN), if_pos hN] at hval
  rw [hev, hval, hu, List.nil_append]

/-- **Lemma (★) with no assumption on presence.**  A noninterfering component has
    a winning strategy in the layer game: it can realise its `C`-view against
    every adversary on the channels the layer exposes. -/
noncomputable def winStrat_of_INI {St : Type} {step : St → Act Channel Value → St → Prop}
    {s : St} {C n : Level} {N : Channel → Prop} {w : S.Strategy Value} (dflt : Value)
    (htot : w.total)
    (hNn : ∀ a : Channel, N a → S.le n (S.valL a))
    (hNn' : ∀ a : Channel, N a → S.le (S.valL a) n)
    (hNC : ∀ a : Channel, N a → ¬ S.le (S.valL a) C)
    (hINI : S.StratTNI step s)
    {b : List (Lbl Channel Value)} (hb : S.produces step w s b) :
    WinStrat N (RedPair S step s C n (S.proj C b)) (fun _ _ _ => True) [] :=
  Classical.choice (nonempty_winStrat_of_forced (fun _ _ => ⟨dflt, trivial⟩) dflt
    (forcedW_of_INI htot hNn hNn' hNC hINI hb))

end Sec

end InteractiveNI
