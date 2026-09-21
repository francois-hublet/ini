/-
  Basic properties of the projection `π_ℓ` and of ℓ-equivalence of traces.
-/
import InteractiveNI.Basic

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

/-- The channel of a projected label. -/
def PLbl.chan {C V} : PLbl C V → C
  | .inp a _ => a
  | .out a _ => a

namespace Sec

variable {Level Channel Value : Type} {S : Sec Level Channel}

local notation:50 a " ⊑ " b => S.le a b

@[simp] theorem proj_nil (ℓ : Level) : S.proj (Value := Value) ℓ [] = [] := rfl

theorem proj_cons_some {ℓ : Level} {l : Lbl Channel Value} {p : PLbl Channel Value}
    (h : S.projLbl ℓ l = some p) (t : List (Lbl Channel Value)) :
    S.proj ℓ (l :: t) = p :: S.proj ℓ t := by
  simp [proj, h]

theorem proj_cons_none {ℓ : Level} {l : Lbl Channel Value}
    (h : S.projLbl ℓ l = none) (t : List (Lbl Channel Value)) :
    S.proj ℓ (l :: t) = S.proj ℓ t := by
  simp [proj, h]

theorem proj_append (ℓ : Level) (t t' : List (Lbl Channel Value)) :
    S.proj ℓ (t ++ t') = S.proj ℓ t ++ S.proj ℓ t' := by
  simp [proj, List.filterMap_append]

/-! ### Reduction lemmas for `projLbl` -/

theorem projLbl_inp_hidden {ℓ : Level} {a : Channel} {v : Value}
    (h : ¬ (S.presL a ⊑ ℓ)) : S.projLbl ℓ (.inp a v) = none := by
  simp [projLbl, h]

theorem projLbl_out_hidden {ℓ : Level} {a : Channel} {v : Value}
    (h : ¬ (S.presL a ⊑ ℓ)) : S.projLbl ℓ (.out a v) = none := by
  simp [projLbl, h]

theorem projLbl_inp_pres {ℓ : Level} {a : Channel} {v : Value}
    (h : S.presL a ⊑ ℓ) (h' : ¬ (S.valL a ⊑ ℓ)) :
    S.projLbl ℓ (.inp a v) = some (.inp a none) := by
  simp [projLbl, h, h']

theorem projLbl_out_pres {ℓ : Level} {a : Channel} {v : Value}
    (h : S.presL a ⊑ ℓ) (h' : ¬ (S.valL a ⊑ ℓ)) :
    S.projLbl ℓ (.out a v) = some (.out a none) := by
  simp [projLbl, h, h']

theorem projLbl_inp_full {ℓ : Level} {a : Channel} {v : Value}
    (h : S.presL a ⊑ ℓ) (h' : S.valL a ⊑ ℓ) :
    S.projLbl ℓ (.inp a v) = some (.inp a (some v)) := by
  simp [projLbl, h, h']

theorem projLbl_out_full {ℓ : Level} {a : Channel} {v : Value}
    (h : S.presL a ⊑ ℓ) (h' : S.valL a ⊑ ℓ) :
    S.projLbl ℓ (.out a v) = some (.out a (some v)) := by
  simp [projLbl, h, h']

/-- A label is erased by `π_ℓ` exactly when its presence level is not below `ℓ`. -/
theorem projLbl_eq_none_iff {ℓ : Level} {l : Lbl Channel Value} :
    S.projLbl ℓ l = none ↔ ¬ (S.presL l.chan ⊑ ℓ) := by
  cases l with
  | inp a v =>
      by_cases h : S.presL a ⊑ ℓ
      · by_cases h' : S.valL a ⊑ ℓ <;>
          simp [Lbl.chan, projLbl_inp_full, projLbl_inp_pres, h, h']
      · simp [Lbl.chan, projLbl_inp_hidden h, h]
  | out a v =>
      by_cases h : S.presL a ⊑ ℓ
      · by_cases h' : S.valL a ⊑ ℓ <;>
          simp [Lbl.chan, projLbl_out_full, projLbl_out_pres, h, h']
      · simp [Lbl.chan, projLbl_out_hidden h, h]

/-! ### ℓ-equivalence is monotone in ℓ -/

/-- Re-projection of an already projected label at a lower level. -/
noncomputable def reproj (S : Sec Level Channel) (ℓ : Level) :
    PLbl Channel Value → Option (PLbl Channel Value)
  | .inp a o => if S.le (S.presL a) ℓ then
      (if S.le (S.valL a) ℓ then some (.inp a o) else some (.inp a none)) else none
  | .out a o => if S.le (S.presL a) ℓ then
      (if S.le (S.valL a) ℓ then some (.out a o) else some (.out a none)) else none

theorem projLbl_reproj {ℓ ℓ' : Level} (hle : S.le ℓ ℓ') (l : Lbl Channel Value) :
    S.projLbl ℓ l = (S.projLbl ℓ' l).bind (S.reproj ℓ) := by
  have key : ∀ (a : Channel), (S.valL a ⊑ ℓ) → (S.valL a ⊑ ℓ') := fun a h => S.le_trans h hle
  have keyp : ∀ (a : Channel), (S.presL a ⊑ ℓ) → (S.presL a ⊑ ℓ') := fun a h => S.le_trans h hle
  cases l with
  | inp a v =>
      by_cases hp' : S.presL a ⊑ ℓ'
      · by_cases hv' : S.valL a ⊑ ℓ'
        · rw [projLbl_inp_full hp' hv']
          by_cases hp : S.presL a ⊑ ℓ
          · by_cases hv : S.valL a ⊑ ℓ
            · simp [projLbl_inp_full hp hv, reproj, hp, hv]
            · simp [projLbl_inp_pres hp hv, reproj, hp, hv]
          · simp [projLbl_inp_hidden hp, reproj, hp]
        · rw [projLbl_inp_pres hp' hv']
          have hv : ¬ (S.valL a ⊑ ℓ) := fun h => hv' (key a h)
          by_cases hp : S.presL a ⊑ ℓ
          · simp [projLbl_inp_pres hp hv, reproj, hp, hv]
          · simp [projLbl_inp_hidden hp, reproj, hp]
      · have hp : ¬ (S.presL a ⊑ ℓ) := fun h => hp' (keyp a h)
        simp [projLbl_inp_hidden hp, projLbl_inp_hidden hp']
  | out a v =>
      by_cases hp' : S.presL a ⊑ ℓ'
      · by_cases hv' : S.valL a ⊑ ℓ'
        · rw [projLbl_out_full hp' hv']
          by_cases hp : S.presL a ⊑ ℓ
          · by_cases hv : S.valL a ⊑ ℓ
            · simp [projLbl_out_full hp hv, reproj, hp, hv]
            · simp [projLbl_out_pres hp hv, reproj, hp, hv]
          · simp [projLbl_out_hidden hp, reproj, hp]
        · rw [projLbl_out_pres hp' hv']
          have hv : ¬ (S.valL a ⊑ ℓ) := fun h => hv' (key a h)
          by_cases hp : S.presL a ⊑ ℓ
          · simp [projLbl_out_pres hp hv, reproj, hp, hv]
          · simp [projLbl_out_hidden hp, reproj, hp]
      · have hp : ¬ (S.presL a ⊑ ℓ) := fun h => hp' (keyp a h)
        simp [projLbl_out_hidden hp, projLbl_out_hidden hp']

theorem proj_reproj {ℓ ℓ' : Level} (hle : S.le ℓ ℓ') (t : List (Lbl Channel Value)) :
    S.proj ℓ t = (S.proj ℓ' t).filterMap (S.reproj ℓ) := by
  have hfun : S.projLbl (Value := Value) ℓ = fun l => (S.projLbl ℓ' l).bind (S.reproj ℓ) :=
    funext (projLbl_reproj hle)
  simp only [proj, List.filterMap_filterMap, hfun]

/-- ℓ-equivalence is coarser at lower levels. -/
theorem teq_mono {ℓ ℓ' : Level} (hle : S.le ℓ ℓ') {t t' : List (Lbl Channel Value)}
    (h : S.teq ℓ' t t') : S.teq ℓ t t' := by
  unfold teq at *
  rw [proj_reproj hle t, proj_reproj hle t', h]

/-! ### Membership in projections -/

theorem mem_proj_out_full {ℓ : Level} {a : Channel} {v : Value}
    (h : S.presL a ⊑ ℓ) (h' : S.valL a ⊑ ℓ) (t : List (Lbl Channel Value)) :
    (PLbl.out a (some v)) ∈ S.proj ℓ t ↔ (Lbl.out a v) ∈ t := by
  induction t with
  | nil => simp
  | cons l t ih =>
      cases l with
      | inp b w =>
          by_cases hp : S.presL b ⊑ ℓ
          · by_cases hv : S.valL b ⊑ ℓ
            · simp [proj_cons_some (projLbl_inp_full hp hv), ih]
            · simp [proj_cons_some (projLbl_inp_pres hp hv), ih]
          · simp [proj_cons_none (projLbl_inp_hidden hp), ih]
      | out b w =>
          by_cases hp : S.presL b ⊑ ℓ
          · by_cases hv : S.valL b ⊑ ℓ
            · simp only [proj_cons_some (projLbl_out_full hp hv), List.mem_cons, ih]
              constructor
              · rintro (heq | hm)
                · injection heq with hb hw; injection hw with hw; subst hb; subst hw
                  exact Or.inl rfl
                · exact Or.inr hm
              · rintro (heq | hm)
                · injection heq with hb hw; subst hb; subst hw; exact Or.inl rfl
                · exact Or.inr hm
            · simp only [proj_cons_some (projLbl_out_pres hp hv), List.mem_cons, ih]
              constructor
              · rintro (heq | hm)
                · injection heq with hb hw; exact absurd hw (by simp)
                · exact Or.inr hm
              · rintro (heq | hm)
                · injection heq with hb hw; subst hb; exact absurd h' hv
                · exact Or.inr hm
          · simp only [proj_cons_none (projLbl_out_hidden hp), ih, List.mem_cons]
            constructor
            · exact fun hm => Or.inr hm
            · rintro (heq | hm)
              · injection heq with hb hw; subst hb; exact absurd h hp
              · exact hm

theorem mem_proj_out_pres {ℓ : Level} {a : Channel}
    (h : S.presL a ⊑ ℓ) (h' : ¬ (S.valL a ⊑ ℓ)) (t : List (Lbl Channel Value)) :
    (PLbl.out a none) ∈ S.proj ℓ t ↔ ∃ v, (Lbl.out a v) ∈ t := by
  induction t with
  | nil => simp
  | cons l t ih =>
      cases l with
      | inp b w =>
          by_cases hp : S.presL b ⊑ ℓ
          · by_cases hv : S.valL b ⊑ ℓ
            · simp [proj_cons_some (projLbl_inp_full hp hv), ih]
            · simp [proj_cons_some (projLbl_inp_pres hp hv), ih]
          · simp [proj_cons_none (projLbl_inp_hidden hp), ih]
      | out b w =>
          by_cases hp : S.presL b ⊑ ℓ
          · by_cases hv : S.valL b ⊑ ℓ
            · simp only [proj_cons_some (projLbl_out_full hp hv), List.mem_cons, ih]
              constructor
              · rintro (heq | hm)
                · injection heq with hb hw; exact absurd hw.symm (by simp)
                · obtain ⟨v, hv'⟩ := hm; exact ⟨v, Or.inr hv'⟩
              · rintro ⟨v, (heq | hm)⟩
                · injection heq with hb hw; subst hb; exact absurd hv h'
                · exact Or.inr ⟨v, hm⟩
            · simp only [proj_cons_some (projLbl_out_pres hp hv), List.mem_cons, ih]
              constructor
              · rintro (heq | hm)
                · injection heq with hb _; subst hb; exact ⟨w, Or.inl rfl⟩
                · obtain ⟨v, hv'⟩ := hm; exact ⟨v, Or.inr hv'⟩
              · rintro ⟨v, (heq | hm)⟩
                · injection heq with hb _; subst hb; exact Or.inl rfl
                · exact Or.inr ⟨v, hm⟩
          · simp only [proj_cons_none (projLbl_out_hidden hp), ih, List.mem_cons]
            constructor
            · rintro ⟨v, hv'⟩; exact ⟨v, Or.inr hv'⟩
            · rintro ⟨v, (heq | hm)⟩
              · injection heq with hb _; subst hb; exact absurd h hp
              · exact ⟨v, hm⟩

end Sec

end InteractiveNI
