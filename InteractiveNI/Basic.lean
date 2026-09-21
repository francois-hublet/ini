/-
  Interactive Noninterference Does Not (Always) Compose
  -----------------------------------------------------
  §2 of the paper: the model.

  Everything here is a transcription of the definitions in
  `elsarticle-template-num.tex`, Section 2.
-/

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

/-! ## Sets of values and the relation `≐` -/

/-- A subset of values, represented as a predicate. -/
abbrev VSet (V : Type) := V → Prop

/-- `S = ∅`. -/
def VSet.isEmpty {V : Type} (s : VSet V) : Prop := ∀ v, ¬ s v

/-- The paper's `S₁ ≐ S₂ := (S₁ = ∅ ↔ S₂ = ∅)`. -/
def dotEq {V : Type} (a b : VSet V) : Prop := a.isEmpty ↔ b.isEmpty

@[refl] theorem dotEq.refl {V} (a : VSet V) : dotEq a a := Iff.rfl
theorem dotEq.symm {V} {a b : VSet V} (h : dotEq a b) : dotEq b a := Iff.symm h
theorem dotEq.trans {V} {a b c : VSet V} (h₁ : dotEq a b) (h₂ : dotEq b c) :
    dotEq a c := Iff.trans h₁ h₂
theorem dotEq.of_eq {V} {a b : VSet V} (h : a = b) : dotEq a b := by subst h; rfl

/-- If `a ≐ b` and `a` is inhabited, so is `b`. -/
theorem dotEq.exists {V} {a b : VSet V} (h : dotEq a b) {v : V} (hv : a v) :
    ∃ v', b v' := by
  rcases Classical.em (∃ v', b v') with hc | hc
  · exact hc
  · exact absurd hv (h.mpr (fun v' hv' => hc ⟨v', hv'⟩) v)

/-! ## Input-output labels -/

/-- Transition actions: `α?v`, `α!v`, or `τ`. -/
inductive Act (C V : Type) where
  | inp : C → V → Act C V
  | out : C → V → Act C V
  | tau : Act C V

/-- Visible labels appearing in traces (τ is erased): `α : v` with `: ∈ {?,!}`. -/
inductive Lbl (C V : Type) where
  | inp : C → V → Lbl C V
  | out : C → V → Lbl C V

/-- Projected labels: the value may be hidden (`□`, here `none`). -/
inductive PLbl (C V : Type) where
  | inp : C → Option V → PLbl C V
  | out : C → Option V → PLbl C V

/-- The channel a label acts on. -/
def Lbl.chan {C V} : Lbl C V → C
  | .inp a _ => a
  | .out a _ => a

/-- The action corresponding to a visible label. -/
def Lbl.act {C V} : Lbl C V → Act C V
  | .inp a v => .inp a v
  | .out a v => .out a v

/-! ## §2.1 The security context -/

/--
A security context: a preordered set of levels `(𝓛, ⊑)` and the level map
`γ : ℂ → 𝓛²`, split into the *presence* level `ℓ₂ = presL α` and the *value*
level `ℓ₁ = valL α` of each channel, with `ℓ₂ ⊑ ℓ₁`.
-/
structure Sec (Level Channel : Type) where
  le       : Level → Level → Prop
  le_refl  : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  /-- presence level `ℓ₂` of a channel -/
  presL    : Channel → Level
  /-- value level `ℓ₁` of a channel -/
  valL     : Channel → Level
  /-- presence is at most value: `ℓ₂ ⊑ ℓ₁` -/
  pres_le_val : ∀ a, le (presL a) (valL a)

namespace Sec

variable {Level Channel Value : Type} (S : Sec Level Channel)

/-! ### Traces and ℓ-equivalence -/

/-- Projection of a single label at level `ℓ` (the `π_ℓ` clauses of the paper). -/
noncomputable def projLbl (ℓ : Level) :
    Lbl Channel Value → Option (PLbl Channel Value)
  | .inp a v =>
      if S.le (S.presL a) ℓ then
        (if S.le (S.valL a) ℓ then some (.inp a (some v)) else some (.inp a none))
      else none
  | .out a v =>
      if S.le (S.presL a) ℓ then
        (if S.le (S.valL a) ℓ then some (.out a (some v)) else some (.out a none))
      else none

/-- `π_ℓ(t)`. -/
noncomputable def proj (ℓ : Level) (t : List (Lbl Channel Value)) :
    List (PLbl Channel Value) :=
  t.filterMap (S.projLbl ℓ)

/-- `t =_ℓ t'`. -/
def teq (ℓ : Level) (t t' : List (Lbl Channel Value)) : Prop :=
  S.proj ℓ t = S.proj ℓ t'

@[refl] theorem teq.refl (ℓ : Level) (t : List (Lbl Channel Value)) : S.teq ℓ t t := rfl
theorem teq.symm {S : Sec Level Channel} {ℓ : Level} {t t' : List (Lbl Channel Value)}
    (h : S.teq ℓ t t') : S.teq ℓ t' t := Eq.symm h
theorem teq.trans {S : Sec Level Channel} {ℓ : Level} {t t' t'' : List (Lbl Channel Value)}
    (h₁ : S.teq ℓ t t') (h₂ : S.teq ℓ t' t'') : S.teq ℓ t t'' := Eq.trans h₁ h₂

/-! ### §2.2 Strategies -/

/-- A strategy: `ω_α(t) ⊆ 𝕍`, subject to the two non-leakage constraints. -/
structure Strategy (Value : Type) where
  ω : Channel → List (Lbl Channel Value) → VSet Value
  resp_val  : ∀ a t₁ t₂, S.teq (S.valL a) t₁ t₂ → ω a t₁ = ω a t₂
  resp_pres : ∀ a t₁ t₂, S.teq (S.presL a) t₁ t₂ → dotEq (ω a t₁) (ω a t₂)

/-- Total strategies (`Strat_T`). -/
def Strategy.total (w : S.Strategy Value) : Prop := ∀ a t, ∃ v, w.ω a t v

/-- ℓ-equivalence of strategies, `ω =_ℓ ω'` (also written `∼_ℓ` in §4). -/
def seq (ℓ : Level) (w w' : S.Strategy Value) : Prop :=
  ∀ a t,
    (S.le (S.valL a) ℓ  → w.ω a t = w'.ω a t) ∧
    (S.le (S.presL a) ℓ → dotEq (w.ω a t) (w'.ω a t))

@[refl] theorem seq.refl (ℓ : Level) (w : S.Strategy Value) : S.seq ℓ w w :=
  fun _ _ => ⟨fun _ => rfl, fun _ => dotEq.refl _⟩

theorem seq.symm {S : Sec Level Channel} {ℓ : Level} {w w' : S.Strategy Value} (h : S.seq ℓ w w') :
    S.seq ℓ w' w := fun a t =>
  ⟨fun hl => ((h a t).1 hl).symm, fun hl => ((h a t).2 hl).symm⟩

theorem seq.trans {S : Sec Level Channel} {ℓ : Level} {w w' w'' : S.Strategy Value}
    (h₁ : S.seq ℓ w w') (h₂ : S.seq ℓ w' w'') : S.seq ℓ w w'' := fun a t =>
  ⟨fun hl => ((h₁ a t).1 hl).trans ((h₂ a t).1 hl),
   fun hl => ((h₁ a t).2 hl).trans ((h₂ a t).2 hl)⟩

end Sec

/-! ## §2.1 IOLTS -/

namespace Sec
variable {Level Channel : Type}

/-- The levels of `S` form a join-semilattice (as required in §2). -/
def IsJoinSemilattice (S : Sec Level Channel) : Prop :=
  ∃ join : Level → Level → Level, ∀ a b,
    S.le a (join a b) ∧ S.le b (join a b) ∧ ∀ d, S.le a d → S.le b d → S.le (join a b) d

end Sec

/-- Input-neutrality. -/
def InputNeutral {C V St : Type} (step : St → Act C V → St → Prop) : Prop :=
  ∀ s s' a v, step s (.inp a v) s' → ∀ v', ∃ s'', step s (.inp a v') s''

/-- `s ⟶^t s'`: the IOLTS goes from `s` to `s'` emitting the visible trace `t`. -/
inductive Reach {C V St : Type} (step : St → Act C V → St → Prop) :
    St → List (Lbl C V) → St → Prop where
  | nil  {s} : Reach step s [] s
  | tau  {s s' s'' t}     : step s .tau s'        → Reach step s' t s'' → Reach step s t s''
  | inp  {s s' s'' a v t} : step s (.inp a v) s'  → Reach step s' t s'' →
                              Reach step s (.inp a v :: t) s''
  | out  {s s' s'' a v t} : step s (.out a v) s'  → Reach step s' t s'' →
                              Reach step s (.out a v :: t) s''

/-- A single visible step. -/
theorem Reach.one {C V St : Type} {step : St → Act C V → St → Prop}
    {s s' : St} {l : Lbl C V} (h : step s l.act s') : Reach step s [l] s' := by
  cases l with
  | inp a v => exact Reach.inp h Reach.nil
  | out a v => exact Reach.out h Reach.nil

theorem Reach.trans {C V St : Type} {step : St → Act C V → St → Prop}
    {s s' s'' : St} {t t' : List (Lbl C V)}
    (h : Reach step s t s') (h' : Reach step s' t' s'') :
    Reach step s (t ++ t') s'' := by
  induction h with
  | nil => simpa using h'
  | tau hs _ ih => exact Reach.tau hs (ih h')
  | inp hs _ ih => exact Reach.inp hs (ih h')
  | out hs _ ih => exact Reach.out hs (ih h')

/--
Determinism (Definition in §2.1): whenever `s ⟶^a s'` and `s ⟶^{a'} s''`,
(i) if `a ≠ a'` then `a = α?v` and `a' = α?v'` for a common channel `α`, and
(ii) if `a = a'` then `s' = s''`.
(Packaged as a structure so that unification never unfolds it.)
-/
structure Deterministic {C V St : Type} (step : St → Act C V → St → Prop) : Prop where
  inputs : ∀ {s a a' s' s''}, step s a s' → step s a' s'' → a ≠ a' →
    ∃ c v v', a = .inp c v ∧ a' = .inp c v'
  target : ∀ {s a s' s''}, step s a s' → step s a s'' → s' = s''

/-- Binary parallel composition. -/
def parStep {C V St₁ St₂ : Type}
    (step₁ : St₁ → Act C V → St₁ → Prop) (step₂ : St₂ → Act C V → St₂ → Prop) :
    (St₁ × St₂) → Act C V → (St₁ × St₂) → Prop :=
  fun p a q => (step₁ p.1 a q.1 ∧ q.2 = p.2) ∨ (step₂ p.2 a q.2 ∧ q.1 = p.1)

/-- Parallel composition of an arbitrary family. -/
def parStepFam {I C V : Type} {St : I → Type}
    (step : ∀ i, St i → Act C V → St i → Prop) :
    (∀ i, St i) → Act C V → (∀ i, St i) → Prop :=
  fun p a q => ∃ i, step i (p i) a (q i) ∧ ∀ j, j ≠ i → q j = p j

/-! ## §2.3 Consistency, runs, and INI -/

namespace Sec

variable {Level Channel Value : Type} (S : Sec Level Channel)

/-- `ω ⊨ t`: every input in `t` was offered by `ω` at the corresponding history. -/
def consistent (w : S.Strategy Value) (t : List (Lbl Channel Value)) : Prop :=
  ∀ t₁ a v t₂, t = t₁ ++ .inp a v :: t₂ → w.ω a t₁ v

/-- `ω ⊨ s ⟶^t`. -/
def produces {St : Type} (step : St → Act Channel Value → St → Prop)
    (w : S.Strategy Value) (s : St) (t : List (Lbl Channel Value)) : Prop :=
  (∃ s', Reach step s t s') ∧ S.consistent w t

/-- Interactive Noninterference, parameterized by a class of strategies `W`. -/
def INI {St : Type} (step : St → Act Channel Value → St → Prop)
    (W : S.Strategy Value → Prop) (s : St) : Prop :=
  ∀ (ℓ : Level) (w₁ w₂ : S.Strategy Value), W w₁ → W w₂ → S.seq ℓ w₁ w₂ →
    ∀ t₁, S.produces step w₁ s t₁ →
      ∃ t₂, S.produces step w₂ s t₂ ∧ S.teq ℓ t₁ t₂

/-- INI for a larger class of strategies implies INI for a smaller one. -/
theorem INI_mono {S : Sec Level Channel} {St : Type}
    {step : St → Act Channel Value → St → Prop}
    {W W' : S.Strategy Value → Prop} {s : St} (h : ∀ w, W' w → W w)
    (hNI : S.INI step W s) : S.INI step W' s :=
  fun ℓ w₁ w₂ h₁ h₂ hs t₁ hp => hNI ℓ w₁ w₂ (h w₁ h₁) (h w₂ h₂) hs t₁ hp

/-- `Strat-NI`: INI w.r.t. all strategies. -/
abbrev StratNI {St} (step : St → Act Channel Value → St → Prop) (s : St) : Prop :=
  S.INI step (fun _ => True) s

/-- `Strat_T-NI`: INI w.r.t. total strategies. -/
abbrev StratTNI {St} (step : St → Act Channel Value → St → Prop) (s : St) : Prop :=
  S.INI step (fun w => w.total) s

end Sec

end InteractiveNI
