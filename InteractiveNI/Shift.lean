/-
  Strategy transformations used in the proofs of §4.

  The paper's proof of Lemma "deterministic step" defines an auxiliary strategy
  `ω'` obtained from `ω` by "shifting away" the first transition.  Its published
  definition is faulty (the clause `ω'_{α'}(t) = ω_{α'}(t)` for `α' ≠ α` is not
  compatible with the intended property `ω' ⊨ s ⟶^{α:v.t}`: the prefix `α:v`
  must be removed for *all* channels, not only for `α`).  We use instead the
  transformation

      ω'_{α'}(t) = ω_{α'}(removeFirst α t)   (with a constant default on `α`),

  which enjoys all properties needed in the paper's arguments.
-/
import InteractiveNI.Proj

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

/-- Is the label an input? -/
def Lbl.isInp {C V} : Lbl C V → Bool
  | .inp _ _ => true
  | .out _ _ => false

/-- The value carried by a label. -/
def Lbl.val {C V} : Lbl C V → V
  | .inp _ v => v
  | .out _ v => v

def PLbl.isInp {C V} : PLbl C V → Bool
  | .inp _ _ => true
  | .out _ _ => false

def PLbl.val {C V} : PLbl C V → Option V
  | .inp _ o => o
  | .out _ o => o

/-- `t` contains a label on channel `a`. -/
def hasChan {C V} (a : C) (t : List (Lbl C V)) : Prop := ∃ l ∈ t, l.chan = a

/-- Same, for projected traces. -/
def hasChanP {C V} (a : C) (t : List (PLbl C V)) : Prop := ∃ l ∈ t, l.chan = a

/-- Remove the first label on channel `a`. -/
noncomputable def removeFirst {C V} (a : C) : List (Lbl C V) → List (Lbl C V)
  | [] => []
  | l :: t => if l.chan = a then t else l :: removeFirst a t

/-- Same, for projected traces. -/
noncomputable def removeFirstP {C V} (a : C) : List (PLbl C V) → List (PLbl C V)
  | [] => []
  | l :: t => if l.chan = a then t else l :: removeFirstP a t

namespace Sec

variable {Level Channel Value : Type} {S : Sec Level Channel}

local notation:50 a " ⊑ " b => S.le a b

/-! ### `projLbl` preserves channel, direction, and (visible) values -/

theorem projLbl_chan {ℓ : Level} {l : Lbl Channel Value} {p : PLbl Channel Value}
    (h : S.projLbl ℓ l = some p) : p.chan = l.chan := by
  cases l with
  | inp a v =>
      by_cases hp : S.presL a ⊑ ℓ
      · by_cases hv : S.valL a ⊑ ℓ
        · rw [projLbl_inp_full hp hv] at h; injection h with h; subst h; rfl
        · rw [projLbl_inp_pres hp hv] at h; injection h with h; subst h; rfl
      · rw [projLbl_inp_hidden hp] at h; exact absurd h (by simp)
  | out a v =>
      by_cases hp : S.presL a ⊑ ℓ
      · by_cases hv : S.valL a ⊑ ℓ
        · rw [projLbl_out_full hp hv] at h; injection h with h; subst h; rfl
        · rw [projLbl_out_pres hp hv] at h; injection h with h; subst h; rfl
      · rw [projLbl_out_hidden hp] at h; exact absurd h (by simp)

theorem projLbl_isInp {ℓ : Level} {l : Lbl Channel Value} {p : PLbl Channel Value}
    (h : S.projLbl ℓ l = some p) : p.isInp = l.isInp := by
  cases l with
  | inp a v =>
      by_cases hp : S.presL a ⊑ ℓ
      · by_cases hv : S.valL a ⊑ ℓ
        · rw [projLbl_inp_full hp hv] at h; injection h with h; subst h; rfl
        · rw [projLbl_inp_pres hp hv] at h; injection h with h; subst h; rfl
      · rw [projLbl_inp_hidden hp] at h; exact absurd h (by simp)
  | out a v =>
      by_cases hp : S.presL a ⊑ ℓ
      · by_cases hv : S.valL a ⊑ ℓ
        · rw [projLbl_out_full hp hv] at h; injection h with h; subst h; rfl
        · rw [projLbl_out_pres hp hv] at h; injection h with h; subst h; rfl
      · rw [projLbl_out_hidden hp] at h; exact absurd h (by simp)

theorem projLbl_val {ℓ : Level} {l : Lbl Channel Value} {p : PLbl Channel Value}
    (h : S.projLbl ℓ l = some p) (hv : S.valL l.chan ⊑ ℓ) : p.val = some l.val := by
  cases l with
  | inp a v =>
      have hv' : S.valL a ⊑ ℓ := hv
      have hp : S.presL a ⊑ ℓ := S.le_trans (S.pres_le_val a) hv'
      rw [projLbl_inp_full hp hv'] at h; injection h with h; subst h; rfl
  | out a v =>
      have hv' : S.valL a ⊑ ℓ := hv
      have hp : S.presL a ⊑ ℓ := S.le_trans (S.pres_le_val a) hv'
      rw [projLbl_out_full hp hv'] at h; injection h with h; subst h; rfl

theorem projLbl_some_of_pres {ℓ : Level} {l : Lbl Channel Value}
    (h : S.presL l.chan ⊑ ℓ) : ∃ p, S.projLbl ℓ l = some p := by
  cases hl : S.projLbl ℓ l with
  | none => exact absurd h (projLbl_eq_none_iff.mp hl)
  | some p => exact ⟨p, rfl⟩

/-! ### `hasChan` and `removeFirst` under projection -/

theorem hasChan_iff {ℓ : Level} {a : Channel} (h : S.presL a ⊑ ℓ)
    (t : List (Lbl Channel Value)) : hasChan a t ↔ hasChanP a (S.proj ℓ t) := by
  induction t with
  | nil => simp [hasChan, hasChanP]
  | cons l t ih =>
      cases hl : S.projLbl ℓ l with
      | none =>
          have hne : l.chan ≠ a := fun hc => (projLbl_eq_none_iff.mp hl) (hc ▸ h)
          rw [proj_cons_none hl]
          simp only [hasChan, hasChanP, List.mem_cons] at *
          constructor
          · rintro ⟨x, (rfl | hx), hxa⟩
            · exact absurd hxa hne
            · exact ih.mp ⟨x, hx, hxa⟩
          · intro hh; obtain ⟨x, hx, hxa⟩ := ih.mpr hh; exact ⟨x, Or.inr hx, hxa⟩
      | some p =>
          have hpc : p.chan = l.chan := projLbl_chan hl
          rw [proj_cons_some hl]
          simp only [hasChan, hasChanP, List.mem_cons] at *
          constructor
          · rintro ⟨x, (rfl | hx), hxa⟩
            · exact ⟨p, Or.inl rfl, hpc ▸ hxa⟩
            · obtain ⟨y, hy, hya⟩ := ih.mp ⟨x, hx, hxa⟩; exact ⟨y, Or.inr hy, hya⟩
          · rintro ⟨x, (rfl | hx), hxa⟩
            · exact ⟨l, Or.inl rfl, hpc ▸ hxa⟩
            · obtain ⟨y, hy, hya⟩ := ih.mpr ⟨x, hx, hxa⟩; exact ⟨y, Or.inr hy, hya⟩

theorem proj_removeFirst_vis {ℓ : Level} {a : Channel} (h : S.presL a ⊑ ℓ)
    (t : List (Lbl Channel Value)) :
    S.proj ℓ (removeFirst a t) = removeFirstP a (S.proj ℓ t) := by
  induction t with
  | nil => simp [removeFirst, removeFirstP]
  | cons l t ih =>
      by_cases hc : l.chan = a
      · obtain ⟨p, hp⟩ := projLbl_some_of_pres (S := S) (l := l) (by rw [hc]; exact h)
        have hpc : p.chan = a := by rw [projLbl_chan hp, hc]
        rw [proj_cons_some hp]
        simp only [removeFirst, if_pos hc, removeFirstP, if_pos hpc]
      · cases hl : S.projLbl ℓ l with
        | none =>
            rw [proj_cons_none hl]
            simp only [removeFirst, if_neg hc]
            rw [proj_cons_none hl]; exact ih
        | some p =>
            have hpc : p.chan ≠ a := by rw [projLbl_chan hl]; exact hc
            rw [proj_cons_some hl]
            simp only [removeFirst, if_neg hc]
            rw [proj_cons_some hl, removeFirstP, if_neg hpc, ih]

theorem proj_removeFirst_inv {ℓ : Level} {a : Channel} (h : ¬ (S.presL a ⊑ ℓ))
    (t : List (Lbl Channel Value)) :
    S.proj ℓ (removeFirst a t) = S.proj ℓ t := by
  induction t with
  | nil => simp [removeFirst]
  | cons l t ih =>
      by_cases hc : l.chan = a
      · have hn : S.projLbl ℓ l = none := projLbl_eq_none_iff.mpr (by rw [hc]; exact h)
        simp only [removeFirst, if_pos hc]
        rw [proj_cons_none hn]
      · cases hl : S.projLbl ℓ l with
        | none =>
            simp only [removeFirst, if_neg hc]
            rw [proj_cons_none hl, proj_cons_none hl]; exact ih
        | some p =>
            simp only [removeFirst, if_neg hc]
            rw [proj_cons_some hl, proj_cons_some hl, ih]

theorem teq_removeFirst {ℓ : Level} (a : Channel) {t t' : List (Lbl Channel Value)}
    (h : S.teq ℓ t t') : S.teq ℓ (removeFirst a t) (removeFirst a t') := by
  by_cases hp : S.presL a ⊑ ℓ
  · unfold teq at *
    rw [proj_removeFirst_vis hp, proj_removeFirst_vis hp, h]
  · unfold teq at *
    rw [proj_removeFirst_inv hp, proj_removeFirst_inv hp, h]

/-! ### The shifted strategy -/

/-- `shiftStrat a d ω` behaves like `ω` after deleting the first `a`-label of the
    history; before that label appears it offers the constant set `d` on `a`. -/
noncomputable def shiftStrat (a : Channel) (d : VSet Value) (w : S.Strategy Value) :
    S.Strategy Value where
  ω := fun a' t => if a' = a ∧ ¬ hasChan a t then d else w.ω a' (removeFirst a t)
  resp_val := by
    intro b t₁ t₂ ht
    show (if b = a ∧ ¬ hasChan a t₁ then d else w.ω b (removeFirst a t₁))
        = (if b = a ∧ ¬ hasChan a t₂ then d else w.ω b (removeFirst a t₂))
    by_cases hb : b = a
    · subst hb
      have hpb : S.presL b ⊑ S.valL b := S.pres_le_val b
      have hiff : hasChan b t₁ ↔ hasChan b t₂ := by
        rw [hasChan_iff hpb t₁, hasChan_iff hpb t₂]
        unfold teq at ht; rw [ht]
      by_cases h1 : hasChan b t₁
      · have h2 : hasChan b t₂ := hiff.mp h1
        rw [if_neg (fun hx => hx.2 h1), if_neg (fun hx => hx.2 h2)]
        exact w.resp_val b _ _ (teq_removeFirst b ht)
      · have h2 : ¬ hasChan b t₂ := fun hc => h1 (hiff.mpr hc)
        rw [if_pos ⟨rfl, h1⟩, if_pos ⟨rfl, h2⟩]
    · rw [if_neg (fun hx => hb hx.1), if_neg (fun hx => hb hx.1)]
      exact w.resp_val b _ _ (teq_removeFirst a ht)
  resp_pres := by
    intro b t₁ t₂ ht
    show dotEq (if b = a ∧ ¬ hasChan a t₁ then d else w.ω b (removeFirst a t₁))
        (if b = a ∧ ¬ hasChan a t₂ then d else w.ω b (removeFirst a t₂))
    by_cases hb : b = a
    · subst hb
      have hpb : S.presL b ⊑ S.presL b := S.le_refl _
      have hiff : hasChan b t₁ ↔ hasChan b t₂ := by
        rw [hasChan_iff hpb t₁, hasChan_iff hpb t₂]
        unfold teq at ht; rw [ht]
      by_cases h1 : hasChan b t₁
      · have h2 : hasChan b t₂ := hiff.mp h1
        rw [if_neg (fun hx => hx.2 h1), if_neg (fun hx => hx.2 h2)]
        exact w.resp_pres b _ _ (teq_removeFirst b ht)
      · have h2 : ¬ hasChan b t₂ := fun hc => h1 (hiff.mpr hc)
        rw [if_pos ⟨rfl, h1⟩, if_pos ⟨rfl, h2⟩]
    · rw [if_neg (fun hx => hb hx.1), if_neg (fun hx => hb hx.1)]
      exact w.resp_pres b _ _ (teq_removeFirst a ht)

theorem shiftStrat_apply {a : Channel} {d : VSet Value} {w : S.Strategy Value}
    (b : Channel) (t : List (Lbl Channel Value)) :
    (shiftStrat a d w).ω b t
      = if b = a ∧ ¬ hasChan a t then d else w.ω b (removeFirst a t) := rfl

/-- Key computation rule: after a label on `a`, the shifted strategy is `ω` again. -/
theorem shiftStrat_cons {a : Channel} {d : VSet Value} {w : S.Strategy Value}
    {l : Lbl Channel Value} (hl : l.chan = a) (b : Channel)
    (t : List (Lbl Channel Value)) :
    (shiftStrat a d w).ω b (l :: t) = w.ω b t := by
  have hh : hasChan a (l :: t) := ⟨l, List.mem_cons_self .., hl⟩
  rw [shiftStrat_apply, if_neg (fun hx => hx.2 hh)]
  simp only [removeFirst, if_pos hl]

theorem shiftStrat_nil_self {a : Channel} {d : VSet Value} {w : S.Strategy Value}
    (t : List (Lbl Channel Value)) (hn : ¬ hasChan a t) :
    (shiftStrat a d w).ω a t = d := by
  rw [shiftStrat_apply, if_pos ⟨rfl, hn⟩]

theorem not_hasChan_nil {a : Channel} : ¬ hasChan (V := Value) a [] := by
  rintro ⟨l, hl, -⟩; exact absurd hl (by simp)

/-- ℓ-equivalence is preserved by shifting. -/
theorem seq_shiftStrat {ℓ : Level} {a : Channel} {d d' : VSet Value}
    {w₁ w₂ : S.Strategy Value} (hw : S.seq ℓ w₁ w₂)
    (hd : dotEq d d') (hd' : (S.valL a ⊑ ℓ) → d = d') :
    S.seq ℓ (shiftStrat a d w₁) (shiftStrat a d' w₂) := by
  intro b t
  rw [shiftStrat_apply, shiftStrat_apply]
  by_cases hb : b = a ∧ ¬ hasChan a t
  · rw [if_pos hb, if_pos hb]
    exact ⟨fun hbl => hd' (hb.1 ▸ hbl), fun _ => hd⟩
  · rw [if_neg hb, if_neg hb]
    exact ⟨fun hbl => (hw b _).1 hbl, fun hbl => (hw b _).2 hbl⟩

/-- Shifting on a channel invisible at `ℓ` does not change the strategy up to `=_ℓ`. -/
theorem seq_shiftStrat_inv {ℓ : Level} {a : Channel} {d : VSet Value}
    {w : S.Strategy Value} (ha : ¬ (S.presL a ⊑ ℓ)) :
    S.seq ℓ (shiftStrat a d w) w := by
  intro b t
  have hbne : ∀ (m : Level), (S.presL a ⊑ m) → (m ⊑ ℓ) → False :=
    fun m h1 h2 => ha (S.le_trans h1 h2)
  rw [shiftStrat_apply]
  constructor
  · intro hbl
    have hba : b ≠ a := by rintro rfl; exact hbne (S.valL b) (S.pres_le_val b) hbl
    rw [if_neg (fun hx => hba hx.1)]
    exact w.resp_val b _ _ (proj_removeFirst_inv (fun hc => hbne _ hc hbl) t)
  · intro hbl
    have hba : b ≠ a := by rintro rfl; exact hbne (S.presL b) (S.le_refl _) hbl
    rw [if_neg (fun hx => hba hx.1)]
    exact w.resp_pres b _ _ (proj_removeFirst_inv (fun hc => hbne _ hc hbl) t)

/-! ### Consistency and shifting -/

/-- The set of values forced by a label (a singleton for inputs, `∅` for outputs). -/
def dOf {C V} (l : Lbl C V) : VSet V := fun x => l.isInp = true ∧ x = l.val

theorem dOf_inp {C V} (a : C) (v : V) : dOf (Lbl.inp a v) v := ⟨rfl, rfl⟩

theorem dOf_inp_iff {C V} {a : C} {v x : V} : dOf (Lbl.inp a v) x ↔ x = v :=
  ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem consistent_cons_shift {a : Channel} {d : VSet Value} {w : S.Strategy Value}
    {l : Lbl Channel Value} {t : List (Lbl Channel Value)} (hl : l.chan = a)
    (hv : ∀ v, l.isInp = true → l.val = v → d v) (hc : S.consistent w t) :
    S.consistent (shiftStrat a d w) (l :: t) := by
  rintro t₁ b v t₂ heq
  cases t₁ with
  | nil =>
      rw [List.nil_append] at heq
      injection heq with h1 h2
      subst h1
      have hba : b = a := hl
      subst hba
      rw [shiftStrat_nil_self [] not_hasChan_nil]
      exact hv v rfl rfl
  | cons x t₁ =>
      rw [List.cons_append] at heq
      injection heq with h1 h2
      subst h1
      rw [shiftStrat_cons hl]
      exact hc t₁ b v t₂ h2

theorem consistent_of_cons_shift {a : Channel} {d : VSet Value} {w : S.Strategy Value}
    {l : Lbl Channel Value} {t : List (Lbl Channel Value)} (hl : l.chan = a)
    (hc : S.consistent (shiftStrat a d w) (l :: t)) : S.consistent w t := by
  rintro t₁ b v t₂ heq
  have := hc (l :: t₁) b v t₂ (by rw [List.cons_append, heq])
  rwa [shiftStrat_cons hl] at this

theorem head_of_cons_shift {a : Channel} {d : VSet Value} {w : S.Strategy Value}
    {v : Value} {t : List (Lbl Channel Value)}
    (hc : S.consistent (shiftStrat a d w) (.inp a v :: t)) : d v := by
  have := hc [] a v t rfl
  rwa [shiftStrat_nil_self [] not_hasChan_nil] at this

/-! ### Iterated shifting: `unshift` -/

/-- `unshift u ω` forces the trace `u` and then behaves like `ω`. -/
noncomputable def unshift (S : Sec Level Channel) :
    List (Lbl Channel Value) → S.Strategy Value → S.Strategy Value
  | [], w => w
  | l :: u, w => shiftStrat l.chan (dOf l) (S.unshift u w)

@[simp] theorem unshift_nil (w : S.Strategy Value) : S.unshift [] w = w := rfl

theorem unshift_cons (l : Lbl Channel Value) (u : List (Lbl Channel Value))
    (w : S.Strategy Value) :
    S.unshift (l :: u) w = shiftStrat l.chan (dOf l) (S.unshift u w) := rfl

/-- **Lemma U**: a run of `s''` under `ω` extends backwards to a run of `s` under
    `unshift u ω`, along any execution `s ⟶^u s''`. -/
theorem produces_unshift {St : Type} {step : St → Act Channel Value → St → Prop}
    {s s'' : St} {u t₁ : List (Lbl Channel Value)} {w : S.Strategy Value}
    (hr : Reach step s u s'') (hp : S.produces step w s'' t₁) :
    S.produces step (S.unshift u w) s (u ++ t₁) := by
  induction hr with
  | nil => simpa using hp
  | tau hs _ ih =>
      obtain ⟨⟨sx, hx⟩, hc⟩ := ih hp
      exact ⟨⟨sx, Reach.tau hs hx⟩, hc⟩
  | @inp s s' s'' a v t hs _ ih =>
      obtain ⟨⟨sx, hx⟩, hc⟩ := ih hp
      refine ⟨⟨sx, Reach.inp hs hx⟩, ?_⟩
      rw [unshift_cons]
      exact consistent_cons_shift (l := .inp a v) rfl (fun v' _ hv => hv ▸ dOf_inp a v) hc
  | @out s s' s'' a v t hs _ ih =>
      obtain ⟨⟨sx, hx⟩, hc⟩ := ih hp
      refine ⟨⟨sx, Reach.out hs hx⟩, ?_⟩
      rw [unshift_cons]
      refine consistent_cons_shift (l := .out a v) rfl (fun v' hi _ => ?_) hc
      exact absurd hi (by simp [Lbl.isInp])

/-- ℓ-equivalent prefixes yield ℓ-equivalent `unshift`ed strategies. -/
theorem seq_unshift {ℓ : Level} {w₁ w₂ : S.Strategy Value} (hw : S.seq ℓ w₁ w₂) :
    ∀ (n : Nat) (u u' : List (Lbl Channel Value)), u.length + u'.length ≤ n →
      S.teq ℓ u u' → S.seq ℓ (S.unshift u w₁) (S.unshift u' w₂) := by
  intro n
  induction n with
  | zero =>
      intro u u' hn ht
      cases u with
      | cons x xs => simp at hn
      | nil =>
        cases u' with
        | cons x xs => simp at hn
        | nil => simpa using hw
  | succ n ih =>
      intro u u' hn ht
      cases hu : u with
      | nil =>
          subst hu
          cases hu' : u' with
          | nil => subst hu'; simpa using hw
          | cons l' u'₀ =>
              subst hu'
              have hp' : ¬ (S.presL l'.chan ⊑ ℓ) := by
                intro hp'
                obtain ⟨q, hq⟩ := projLbl_some_of_pres (S := S) (l := l') hp'
                unfold teq at ht
                rw [proj_nil, proj_cons_some hq] at ht
                exact absurd ht.symm (by simp)
              have hnone : S.projLbl ℓ l' = none := projLbl_eq_none_iff.mpr hp'
              have ht' : S.teq ℓ [] u'₀ := by
                unfold teq at *; rw [ht, proj_cons_none hnone]
              have hrec := ih [] u'₀
                (by simp only [List.length_nil, List.length_cons, Nat.zero_add] at hn ⊢; omega) ht'
              rw [unshift_cons]
              exact seq.trans (by simpa using hrec) (seq.symm (seq_shiftStrat_inv hp'))
      | cons l u₀ =>
          subst hu
          by_cases hp : S.presL l.chan ⊑ ℓ
          · obtain ⟨p, hpe⟩ := projLbl_some_of_pres (S := S) (l := l) hp
            cases hu' : u' with
            | nil =>
                subst hu'
                exfalso
                unfold teq at ht
                rw [proj_nil, proj_cons_some hpe] at ht
                exact absurd ht (by simp)
            | cons l' u'₀ =>
                subst hu'
                by_cases hp' : S.presL l'.chan ⊑ ℓ
                · obtain ⟨q, hqe⟩ := projLbl_some_of_pres (S := S) (l := l') hp'
                  unfold teq at ht
                  rw [proj_cons_some hpe, proj_cons_some hqe] at ht
                  have hpq : p = q := (List.cons.injEq .. ▸ ht).1
                  have htail : S.teq ℓ u₀ u'₀ := (List.cons.injEq .. ▸ ht).2
                  subst hpq
                  have hchan : l'.chan = l.chan := by
                    rw [← projLbl_chan hpe, ← projLbl_chan hqe]
                  have hinp : l'.isInp = l.isInp := by
                    rw [← projLbl_isInp hpe, ← projLbl_isInp hqe]
                  have hrec := ih u₀ u'₀
                    (by simp only [List.length_cons] at hn; omega) htail
                  rw [unshift_cons, unshift_cons, hchan]
                  refine seq_shiftStrat hrec ?_ ?_
                  · constructor
                    · intro he x hx
                      exact he l.val ⟨hinp ▸ hx.1, rfl⟩
                    · intro he x hx
                      exact he l'.val ⟨hinp ▸ hx.1, rfl⟩
                  · intro hvis
                    have hvl : S.valL l.chan ⊑ ℓ := hvis
                    have hvl' : S.valL l'.chan ⊑ ℓ := by rw [hchan]; exact hvl
                    have hval : l'.val = l.val := by
                      have h1 := projLbl_val hpe hvl
                      have h2 := projLbl_val hqe hvl'
                      rw [h1] at h2; injection h2.symm
                    funext x
                    simp only [dOf, hinp, hval]
                · have hnone : S.projLbl ℓ l' = none := projLbl_eq_none_iff.mpr hp'
                  have ht' : S.teq ℓ (l :: u₀) u'₀ := by
                    unfold teq at *; rw [ht, proj_cons_none hnone]
                  have hrec := ih (l :: u₀) u'₀
                    (by simp only [List.length_cons] at hn ⊢; omega) ht'
                  rw [unshift_cons]
                  exact seq.trans hrec (seq.symm (seq_shiftStrat_inv hp'))
          · have hnone : S.projLbl ℓ l = none := projLbl_eq_none_iff.mpr hp
            have ht' : S.teq ℓ u₀ u' := by
              unfold teq at *; rw [← ht, proj_cons_none hnone]
            have hrec := ih u₀ u' (by simp only [List.length_cons] at hn; omega) ht'
            rw [unshift_cons]
            exact seq.trans (seq_shiftStrat_inv hp) hrec

/-- Convenient form of `seq_unshift`. -/
theorem seq_unshift' {ℓ : Level} {w₁ w₂ : S.Strategy Value} (hw : S.seq ℓ w₁ w₂)
    {u u' : List (Lbl Channel Value)} (ht : S.teq ℓ u u') :
    S.seq ℓ (S.unshift u w₁) (S.unshift u' w₂) :=
  seq_unshift hw (u.length + u'.length) u u' (Nat.le_refl _) ht

end Sec

end InteractiveNI
