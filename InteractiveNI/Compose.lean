/-
  §4 — Compositionality in the deterministic case (part 2):
  the composition theorems (Theorems 3 and 6 of the paper).
-/
import InteractiveNI.Det

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

/-! ### Lifting component executions to the composition -/

theorem par_reach_left {C V St₁ St₂ : Type}
    {step₁ : St₁ → Act C V → St₁ → Prop} {step₂ : St₂ → Act C V → St₂ → Prop}
    {x y : St₁} {z : St₂} {t : List (Lbl C V)} (h : Reach step₁ x t y) :
    Reach (parStep step₁ step₂) (x, z) t (y, z) := by
  induction h with
  | nil => exact Reach.nil
  | tau hs _ ih => refine Reach.tau ?_ ih; exact Or.inl ⟨hs, rfl⟩
  | inp hs _ ih => refine Reach.inp ?_ ih; exact Or.inl ⟨hs, rfl⟩
  | out hs _ ih => refine Reach.out ?_ ih; exact Or.inl ⟨hs, rfl⟩

theorem par_reach_right {C V St₁ St₂ : Type}
    {step₁ : St₁ → Act C V → St₁ → Prop} {step₂ : St₂ → Act C V → St₂ → Prop}
    {x : St₁} {y z : St₂} {t : List (Lbl C V)} (h : Reach step₂ y t z) :
    Reach (parStep step₁ step₂) (x, y) t (x, z) := by
  induction h with
  | nil => exact Reach.nil
  | tau hs _ ih => refine Reach.tau ?_ ih; exact Or.inr ⟨hs, rfl⟩
  | inp hs _ ih => refine Reach.inp ?_ ih; exact Or.inr ⟨hs, rfl⟩
  | out hs _ ih => refine Reach.out ?_ ih; exact Or.inr ⟨hs, rfl⟩


/-! ### Decomposing a run of a binary composition -/

/-- `Interleave u v w`: `w` is an interleaving of `u` and `v`. -/
inductive Interleave {α : Type} : List α → List α → List α → Prop where
  | nil : Interleave [] [] []
  | left  {a : α} {u v w} : Interleave u v w → Interleave (a :: u) v (a :: w)
  | right {a : α} {u v w} : Interleave u v w → Interleave u (a :: v) (a :: w)

theorem Interleave.length {α : Type} {u v w : List α} (h : Interleave u v w) :
    w.length = u.length + v.length := by
  induction h with
  | nil => rfl
  | left _ ih => simp [ih]; omega
  | right _ ih => simp [ih]; omega

theorem Interleave.mem_left {α : Type} {u v w : List α} (h : Interleave u v w) {x : α}
    (hx : x ∈ u) : x ∈ w := by
  induction h with
  | nil => exact absurd hx (by simp)
  | left _ ih =>
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hx')
  | right _ ih => exact List.mem_cons_of_mem _ (ih hx)

theorem Interleave.mem_right {α : Type} {u v w : List α} (h : Interleave u v w) {x : α}
    (hx : x ∈ v) : x ∈ w := by
  induction h with
  | nil => exact absurd hx (by simp)
  | left _ ih => exact List.mem_cons_of_mem _ (ih hx)
  | right _ ih =>
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hx')

/-- Every run of a composition decomposes into runs of the two components. -/
theorem par_decompose {C V St₁ St₂ : Type}
    {step₁ : St₁ → Act C V → St₁ → Prop} {step₂ : St₂ → Act C V → St₂ → Prop}
    {p q : St₁ × St₂} {t : List (Lbl C V)} (h : Reach (parStep step₁ step₂) p t q) :
    ∃ tA tB, Reach step₁ p.1 tA q.1 ∧ Reach step₂ p.2 tB q.2 ∧ Interleave tA tB t := by
  induction h with
  | nil => exact ⟨[], [], Reach.nil, Reach.nil, Interleave.nil⟩
  | @tau p p' q t hs _ ih =>
      obtain ⟨tA, tB, h1, h2, h3⟩ := ih
      rcases hs with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact ⟨tA, tB, Reach.tau hx h1, by rw [← hy]; exact h2, h3⟩
      · exact ⟨tA, tB, by rw [← hy]; exact h1, Reach.tau hx h2, h3⟩
  | @inp p p' q a v t hs _ ih =>
      obtain ⟨tA, tB, h1, h2, h3⟩ := ih
      rcases hs with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact ⟨_, tB, Reach.inp hx h1, by rw [← hy]; exact h2, Interleave.left h3⟩
      · exact ⟨tA, _, by rw [← hy]; exact h1, Reach.inp hx h2, Interleave.right h3⟩
  | @out p p' q a v t hs _ ih =>
      obtain ⟨tA, tB, h1, h2, h3⟩ := ih
      rcases hs with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact ⟨_, tB, Reach.out hx h1, by rw [← hy]; exact h2, Interleave.left h3⟩
      · exact ⟨tA, _, by rw [← hy]; exact h1, Reach.out hx h2, Interleave.right h3⟩

namespace Sec

variable {Level Channel Value : Type} {S : Sec Level Channel}

theorem consistent_prefix1 {w : S.Strategy Value} {l : Lbl Channel Value}
    {t : List (Lbl Channel Value)} (hc : S.consistent w (l :: t)) :
    S.consistent w [l] := by
  rintro t₁ a v t₂ heq
  cases t₁ with
  | cons x xs =>
      exfalso
      rw [List.cons_append] at heq
      injection heq with h1 h2
      exact absurd h2.symm (by simp)
  | nil =>
      rw [List.nil_append] at heq
      injection heq with h1 h2
      subst h1
      exact hc [] a v t rfl

/-! ### The inductive step of the composition theorem -/

section Binary

variable {St₁ St₂ : Type}
  {step₁ : St₁ → Act Channel Value → St₁ → Prop}
  {step₂ : St₂ → Act Channel Value → St₂ → Prop}

/-- The statement proved by induction in Theorem 17. -/
def ComposeGoal (S : Sec Level Channel)
    (step₁ : St₁ → Act Channel Value → St₁ → Prop)
    (step₂ : St₂ → Act Channel Value → St₂ → Prop)
    (sA : St₁) (sB : St₂) (p : St₁ × St₂) (t₁ : List (Lbl Channel Value)) : Prop :=
  ∀ {sE : St₁} {sF : St₂} {ℓ : Level} {w₁ w₂ : S.Strategy Value}
    {tA t'A tB t'B : List (Lbl Channel Value)},
    Reach step₁ sA tA p.1 → Reach step₁ sA t'A sE →
    Reach step₂ sB tB p.2 → Reach step₂ sB t'B sF →
    S.teq ℓ tA t'A → S.teq ℓ tB t'B → S.seq ℓ w₁ w₂ → S.consistent w₁ t₁ →
    ∃ t₂, S.produces (parStep step₁ step₂) w₂ (sE, sF) t₂ ∧ S.teq ℓ t₁ t₂

theorem compose_labelled (hdet₁ : Deterministic step₁) (hdet₂ : Deterministic step₂)
    {sA : St₁} {sB : St₂} (hA : S.StratNI step₁ sA) (hB : S.StratNI step₂ sB)
    {p q : St₁ × St₂} {l : Lbl Channel Value} {t₁' : List (Lbl Channel Value)}
    (hs : parStep step₁ step₂ p l.act q)
    (ih : ComposeGoal S step₁ step₂ sA sB q t₁') :
    ComposeGoal S step₁ step₂ sA sB p (l :: t₁') := by
  intro sE sF ℓ w₁ w₂ tA t'A tB t'B hCA hEA hDB hFB hAeq hBeq hww hc
  have hc1 : S.consistent w₁ [l] := consistent_prefix1 hc
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- the first component moves
    have hrun1 : S.produces step₁ w₁ p.1 [l] := ⟨⟨q.1, Reach.one h1⟩, hc1⟩
    obtain ⟨t'', sE'', hre, hcons'', hteq''⟩ :=
      indistinguishable_NI hdet₁ hA hCA hEA hrun1 hAeq hww
    have hseq' : S.seq ℓ (prependStrat [l] w₁) (prependStrat t'' w₂) :=
      seq_prependStrat hww hteq''
    have hCA' : Reach step₁ sA (tA ++ [l]) q.1 := Reach.trans hCA (Reach.one h1)
    have hEA' : Reach step₁ sA (t'A ++ t'') sE'' := Reach.trans hEA hre
    have hDB' : Reach step₂ sB tB q.2 := by rw [h2]; exact hDB
    obtain ⟨t'₂, hprod', hteq'⟩ :=
      ih hCA' hEA' hDB' hFB (teq_append hAeq hteq'') hBeq hseq' (consistent_of_cons hc)
    refine ⟨t'' ++ t'₂, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact hprod'.1.choose
    · exact Reach.trans (par_reach_left hre) hprod'.1.choose_spec
    · exact consistent_append hcons'' hprod'.2
    · exact teq_append hteq'' hteq'
  · -- the second component moves
    have hrun1 : S.produces step₂ w₁ p.2 [l] := ⟨⟨q.2, Reach.one h1⟩, hc1⟩
    obtain ⟨t'', sF'', hre, hcons'', hteq''⟩ :=
      indistinguishable_NI hdet₂ hB hDB hFB hrun1 hBeq hww
    have hseq' : S.seq ℓ (prependStrat [l] w₁) (prependStrat t'' w₂) :=
      seq_prependStrat hww hteq''
    have hDB' : Reach step₂ sB (tB ++ [l]) q.2 := Reach.trans hDB (Reach.one h1)
    have hFB' : Reach step₂ sB (t'B ++ t'') sF'' := Reach.trans hFB hre
    have hCA' : Reach step₁ sA tA q.1 := by rw [h2]; exact hCA
    obtain ⟨t'₂, hprod', hteq'⟩ :=
      ih hCA' hEA hDB' hFB' hAeq (teq_append hBeq hteq'') hseq' (consistent_of_cons hc)
    refine ⟨t'' ++ t'₂, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact hprod'.1.choose
    · exact Reach.trans (par_reach_right hre) hprod'.1.choose_spec
    · exact consistent_append hcons'' hprod'.2
    · exact teq_append hteq'' hteq'

/-- **Lemma 16** of the paper, the binary case. -/
theorem compose_helper (hdet₁ : Deterministic step₁) (hdet₂ : Deterministic step₂)
    {sA : St₁} {sB : St₂} (hA : S.StratNI step₁ sA) (hB : S.StratNI step₂ sB)
    {p q : St₁ × St₂} {t₁ : List (Lbl Channel Value)}
    (hr : Reach (parStep step₁ step₂) p t₁ q) :
    ComposeGoal S step₁ step₂ sA sB p t₁ := by
  induction hr with
  | @nil p =>
      intro sE sF ℓ w₁ w₂ tA t'A tB t'B _ _ _ _ _ _ _ _
      exact ⟨[], ⟨⟨(sE, sF), Reach.nil⟩, consistent_nil _⟩, rfl⟩
  | @tau p p' q t hs _ ih =>
      intro sE sF ℓ w₁ w₂ tA t'A tB t'B hCA hEA hDB hFB hAeq hBeq hww hc
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hCA' : Reach step₁ sA tA p'.1 := by
          have := Reach.trans hCA (Reach.tau h1 Reach.nil)
          rwa [List.append_nil] at this
        have hDB' : Reach step₂ sB tB p'.2 := by rw [h2]; exact hDB
        exact ih hCA' hEA hDB' hFB hAeq hBeq hww hc
      · have hDB' : Reach step₂ sB tB p'.2 := by
          have := Reach.trans hDB (Reach.tau h1 Reach.nil)
          rwa [List.append_nil] at this
        have hCA' : Reach step₁ sA tA p'.1 := by rw [h2]; exact hCA
        exact ih hCA' hEA hDB' hFB hAeq hBeq hww hc
  | @inp p p' q a v t hs _ ih =>
      exact compose_labelled hdet₁ hdet₂ hA hB (l := Lbl.inp a v) hs ih
  | @out p p' q a v t hs _ ih =>
      exact compose_labelled hdet₁ hdet₂ hA hB (l := Lbl.out a v) hs ih

/-- **Theorem 17**: INI composes for two deterministic IOLTS. -/
theorem deterministic_compositional (hdet₁ : Deterministic step₁)
    (hdet₂ : Deterministic step₂) {sA : St₁} {sB : St₂}
    (hA : S.StratNI step₁ sA) (hB : S.StratNI step₂ sB) :
    S.StratNI (parStep step₁ step₂) (sA, sB) := by
  intro ℓ w₁ w₂ _ _ hww t₁ hrun
  obtain ⟨⟨q, hr⟩, hc⟩ := hrun
  exact compose_helper hdet₁ hdet₂ hA hB hr Reach.nil Reach.nil Reach.nil Reach.nil
    (rfl : S.teq ℓ [] []) (rfl : S.teq ℓ [] []) hww hc

end Binary

/-! ### Arbitrary families -/

section Family

variable {I : Type} {St : I → Type}
  {step : ∀ i, St i → Act Channel Value → St i → Prop}

/-- Update one component of a state vector. -/
noncomputable def upd {I : Type} {St : I → Type} (f : ∀ i, St i) (i : I) (x : St i) :
    ∀ j, St j :=
  fun j => if h : j = i then cast (congrArg St h.symm) x else f j

theorem upd_self {f : ∀ i, St i} {i : I} {x : St i} : upd f i x i = x := by
  simp [upd]

theorem upd_ne {f : ∀ i, St i} {i j : I} {x : St i} (h : j ≠ i) : upd f i x j = f j := by
  simp [upd, h]

theorem upd_eq_self {f : ∀ i, St i} {i : I} {x : St i} (h : f i = x) : upd f i x = f := by
  funext j
  by_cases hj : j = i
  · subst hj; rw [upd_self, h]
  · rw [upd_ne hj]

theorem upd_upd {f : ∀ i, St i} {i : I} {x y : St i} : upd (upd f i x) i y = upd f i y := by
  funext j
  by_cases hj : j = i
  · subst hj; rw [upd_self, upd_self]
  · rw [upd_ne hj, upd_ne hj, upd_ne hj]

/-- Update one entry of a family of traces. -/
noncomputable def updT (f : I → List (Lbl Channel Value)) (i : I)
    (x : List (Lbl Channel Value)) : I → List (Lbl Channel Value) :=
  fun j => if j = i then x else f j

theorem updT_self {f : I → List (Lbl Channel Value)} {i : I} {x} : updT f i x i = x := by
  simp [updT]

theorem updT_ne {f : I → List (Lbl Channel Value)} {i j : I} {x} (h : j ≠ i) :
    updT f i x j = f j := by simp [updT, h]

/-- A component execution lifts to the composition of the family. -/
theorem par_reach_fam {i : I} :
    ∀ {x y : St i} {t : List (Lbl Channel Value)}, Reach (step i) x t y →
      ∀ (p : ∀ j, St j), p i = x → Reach (parStepFam step) p t (upd p i y) := by
  intro x y t h
  induction h with
  | @nil x =>
      intro p hp
      rw [upd_eq_self hp]
      exact Reach.nil
  | @tau x x' y t hs _ ih =>
      intro p hp
      have hstep : parStepFam step p .tau (upd p i x') :=
        ⟨i, by rw [upd_self, hp]; exact hs, fun j hj => upd_ne hj⟩
      have := ih (upd p i x') upd_self
      rw [upd_upd] at this
      exact Reach.tau hstep this
  | @inp x x' y a v t hs _ ih =>
      intro p hp
      have hstep : parStepFam step p (.inp a v) (upd p i x') :=
        ⟨i, by rw [upd_self, hp]; exact hs, fun j hj => upd_ne hj⟩
      have := ih (upd p i x') upd_self
      rw [upd_upd] at this
      exact Reach.inp hstep this
  | @out x x' y a v t hs _ ih =>
      intro p hp
      have hstep : parStepFam step p (.out a v) (upd p i x') :=
        ⟨i, by rw [upd_self, hp]; exact hs, fun j hj => upd_ne hj⟩
      have := ih (upd p i x') upd_self
      rw [upd_upd] at this
      exact Reach.out hstep this

/-- The statement proved by induction in Theorem 18. -/
def ComposeGoalFam (S : Sec Level Channel)
    (step : ∀ i, St i → Act Channel Value → St i → Prop)
    (sA : ∀ i, St i) (p : ∀ i, St i) (t₁ : List (Lbl Channel Value)) : Prop :=
  ∀ {sE : ∀ i, St i} {ℓ : Level} {w₁ w₂ : S.Strategy Value}
    {tA t'A : I → List (Lbl Channel Value)},
    (∀ i, Reach (step i) (sA i) (tA i) (p i)) →
    (∀ i, Reach (step i) (sA i) (t'A i) (sE i)) →
    (∀ i, S.teq ℓ (tA i) (t'A i)) →
    S.seq ℓ w₁ w₂ → S.consistent w₁ t₁ →
    ∃ t₂, S.produces (parStepFam step) w₂ sE t₂ ∧ S.teq ℓ t₁ t₂

theorem compose_labelled_fam (hdet : ∀ i, Deterministic (step i))
    {sA : ∀ i, St i} (hA : ∀ i, S.StratNI (step i) (sA i))
    {p q : ∀ i, St i} {l : Lbl Channel Value} {t₁' : List (Lbl Channel Value)}
    (hs : parStepFam step p l.act q)
    (ih : ComposeGoalFam S step sA q t₁') :
    ComposeGoalFam S step sA p (l :: t₁') := by
  intro sE ℓ w₁ w₂ tA t'A hCA hEA hAeq hww hc
  have hc1 : S.consistent w₁ [l] := consistent_prefix1 hc
  obtain ⟨i, h1, h2⟩ := hs
  have hrun1 : S.produces (step i) w₁ (p i) [l] := ⟨⟨q i, Reach.one h1⟩, hc1⟩
  obtain ⟨t'', sE'', hre, hcons'', hteq''⟩ :=
    indistinguishable_NI (hdet i) (hA i) (hCA i) (hEA i) hrun1 (hAeq i) hww
  have hseq' : S.seq ℓ (prependStrat [l] w₁) (prependStrat t'' w₂) :=
    seq_prependStrat hww hteq''
  have hCA' : ∀ j, Reach (step j) (sA j) (updT tA i (tA i ++ [l]) j) (q j) := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [updT_self]; exact Reach.trans (hCA j) (Reach.one h1)
    · rw [updT_ne hj, h2 j hj]; exact hCA j
  have hEA' : ∀ j, Reach (step j) (sA j) (updT t'A i (t'A i ++ t'') j) (upd sE i sE'' j) := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [updT_self, upd_self]; exact Reach.trans (hEA j) hre
    · rw [updT_ne hj, upd_ne hj]; exact hEA j
  have hAeq' : ∀ j, S.teq ℓ (updT tA i (tA i ++ [l]) j) (updT t'A i (t'A i ++ t'') j) := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [updT_self, updT_self]; exact teq_append (hAeq j) hteq''
    · rw [updT_ne hj, updT_ne hj]; exact hAeq j
  obtain ⟨t'₂, hprod', hteq'⟩ := ih hCA' hEA' hAeq' hseq' (consistent_of_cons hc)
  refine ⟨t'' ++ t'₂, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact hprod'.1.choose
  · exact Reach.trans (par_reach_fam hre sE rfl) hprod'.1.choose_spec
  · exact consistent_append hcons'' hprod'.2
  · exact teq_append hteq'' hteq'

/-- **Theorem (helper)** of §4, arbitrary families. -/
theorem compose_helper_fam (hdet : ∀ i, Deterministic (step i))
    {sA : ∀ i, St i} (hA : ∀ i, S.StratNI (step i) (sA i))
    {p q : ∀ i, St i} {t₁ : List (Lbl Channel Value)}
    (hr : Reach (parStepFam step) p t₁ q) :
    ComposeGoalFam S step sA p t₁ := by
  induction hr with
  | @nil p =>
      intro sE ℓ w₁ w₂ tA t'A _ _ _ _ _
      exact ⟨[], ⟨⟨sE, Reach.nil⟩, consistent_nil _⟩, rfl⟩
  | @tau p p' q t hs _ ih =>
      intro sE ℓ w₁ w₂ tA t'A hCA hEA hAeq hww hc
      obtain ⟨i, h1, h2⟩ := hs
      have hCA' : ∀ j, Reach (step j) (sA j) (tA j) (p' j) := by
        intro j
        by_cases hj : j = i
        · subst hj
          have := Reach.trans (hCA j) (Reach.tau h1 Reach.nil)
          rwa [List.append_nil] at this
        · rw [h2 j hj]; exact hCA j
      exact ih hCA' hEA hAeq hww hc
  | @inp p p' q a v t hs _ ih =>
      exact compose_labelled_fam hdet hA (l := Lbl.inp a v) hs ih
  | @out p p' q a v t hs _ ih =>
      exact compose_labelled_fam hdet hA (l := Lbl.out a v) hs ih

/-- **Theorem 18**: INI composes for arbitrary families of deterministic IOLTS. -/
theorem deterministic_compositional_family (hdet : ∀ i, Deterministic (step i))
    {s : ∀ i, St i} (hNI : ∀ i, S.StratNI (step i) (s i)) :
    S.StratNI (parStepFam step) s := by
  intro ℓ w₁ w₂ _ _ hww t₁ hrun
  obtain ⟨⟨q, hr⟩, hc⟩ := hrun
  exact compose_helper_fam hdet hNI hr (tA := fun _ => []) (t'A := fun _ => [])
    (fun _ => Reach.nil) (fun _ => Reach.nil) (fun _ => rfl) hww hc

end Family

end Sec

end InteractiveNI
