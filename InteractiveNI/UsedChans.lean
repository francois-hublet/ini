/-
  **Finiteness belongs to the programs, not to the context.**

  Both compositionality theorems were stated for a finite set of channels.  That
  hypothesis is doing real work -- the hybrid peels the channels on which the two
  strategies differ one at a time, and the peeling has to exhaust the levels the
  channels carry -- but it is a hypothesis about the *universe*, which is odd: a
  program is a finite object and uses finitely many channels, whatever else
  exists.

  Here the hypothesis is moved where it belongs.  Everything is relativised to a
  list `cs` of channels that the two components actually use: channels outside it
  never occur in a run, so nothing the theorem says about them matters.
-/
import InteractiveNI.PeelExists

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

namespace Sec

variable {Level Channel Value : Type}

/-- Every label of `t` is on a channel whose level is in `ls`. -/
def OnLevels (S : Sec Level Channel) (ls : List Level)
    (t : List (Lbl Channel Value)) : Prop := ∀ x ∈ t, S.valL x.chan ∈ ls

/-- The component only ever uses channels at the levels in `ls`.  A program uses
    finitely many channels, hence finitely many levels; but infinitely many
    channels at finitely many levels are fine too. -/
def UsesLevels (S : Sec Level Channel) {St : Type}
    (step : St → Act Channel Value → St → Prop) (s : St) (ls : List Level) : Prop :=
  ∀ (t : List (Lbl Channel Value)) (s' : St), Reach step s t s' → OnLevels S ls t

theorem OnLevels.weave {S : Sec Level Channel} {ls : List Level} {p : List Bool}
    {t t' : List (Lbl Channel Value)} (h : OnLevels S ls t) (h' : OnLevels S ls t') :
    OnLevels S ls (weave p t t') := by
  intro x hx
  rcases mem_weave x p t t' hx with hx | hx
  · exact h x hx
  · exact h' x hx

/-! ### Projection lemmas, relativised -/

theorem proj_eq_map_at_on {S : Sec Level Channel} {ℓ : Level}
    {t : List (Lbl Channel Value)} (h : ∀ x ∈ t, S.le (S.presL x.chan) ℓ) :
    S.proj ℓ t = t.map (S.projL ℓ) := by
  induction t with
  | nil => rfl
  | cons l t ih =>
      have hl : S.projLbl ℓ l = some (S.projL ℓ l) := by
        cases l with
        | inp a v =>
            have hpres : S.le (S.presL a) ℓ := h (Lbl.inp a v) (by simp)
            by_cases hv : S.le (S.valL a) ℓ
            · rw [projLbl_inp_full hpres hv]; simp only [projL, if_pos hv]
            · rw [projLbl_inp_pres hpres hv]; simp only [projL, if_neg hv]
        | out a v =>
            have hpres : S.le (S.presL a) ℓ := h (Lbl.out a v) (by simp)
            by_cases hv : S.le (S.valL a) ℓ
            · rw [projLbl_out_full hpres hv]; simp only [projL, if_pos hv]
            · rw [projLbl_out_pres hpres hv]; simp only [projL, if_neg hv]
      rw [proj_cons_some hl, ih (fun x hx => h x (by simp [hx])), List.map_cons]

theorem proj_weave_at_on {S : Sec Level Channel} {ℓ : Level} (p : List Bool)
    {u v : List (Lbl Channel Value)}
    (hu : ∀ x ∈ u, S.le (S.presL x.chan) ℓ) (hv : ∀ x ∈ v, S.le (S.presL x.chan) ℓ) :
    S.proj ℓ (weave p u v) = weave p (S.proj ℓ u) (S.proj ℓ v) := by
  rw [proj_eq_map_at_on hu, proj_eq_map_at_on hv,
    proj_eq_map_at_on (t := weave p u v) (fun x hx => by
      rcases mem_weave x p u v hx with hx | hx
      · exact hu x hx
      · exact hv x hx), map_weave]

theorem projLbl_eq_projL_at_on {S : Sec Level Channel} {ℓ : Level}
    {l : Lbl Channel Value} (h : S.le (S.presL l.chan) ℓ) :
    S.projLbl ℓ l = some (S.projL ℓ l) := by
  cases l with
  | inp a v =>
      have hpres : S.le (S.presL a) ℓ := h
      by_cases hv : S.le (S.valL a) ℓ
      · rw [projLbl_inp_full hpres hv]; simp only [projL, if_pos hv]
      · rw [projLbl_inp_pres hpres hv]; simp only [projL, if_neg hv]
  | out a v =>
      have hpres : S.le (S.presL a) ℓ := h
      by_cases hv : S.le (S.valL a) ℓ
      · rw [projLbl_out_full hpres hv]; simp only [projL, if_pos hv]
      · rw [projLbl_out_pres hpres hv]; simp only [projL, if_neg hv]

/-! ### The last layer, relativised -/

theorem layerFinal_holds_on {S : Sec Level Channel}
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {w : S.coalition.Strategy Value} {m : Level} {ns : List Level} {ls : List Level}
    (hcsA : UsesLevels S stepA sA ls) (hcsB : UsesLevels S stepB sB ls)
    (τ : List (PLbl Channel Value))
    (hfull : ∀ a : Channel, S.valL a ∈ ls → S.coalition.le (sing (S.valL a)) (layerC S m ns))
    (h : LayerCons S stepA stepB sA sB w m (layerC S m ns) τ) :
    ∃ t, S.coalition.produces (parStep stepA stepB) w (sA, sB) t ∧
      S.coalition.proj (Cplus S m) t = τ := by
  obtain ⟨p, oA, oB, hE, ⟨tA, qA, vA, htA, hrA, hcA, hoA⟩,
    ⟨tB, qB, vB, htB, hrB, hcB, hoB⟩, hcons, hdown⟩ := h
  have hUA : OnLevels S ls tA := hcsA _ _ hrA
  have hUB : OnLevels S ls tB := hcsB _ _ hrB
  have hpres : ∀ t : List (Lbl Channel Value), OnLevels S ls t →
      ∀ x ∈ t, S.coalition.le (S.coalition.presL x.chan) (layerC S m ns) := by
    intro t ht x hx
    exact S.coalition.le_trans (S.coalition.pres_le_val x.chan) (hfull _ (ht x hx))
  have hlen : ∀ t : List (Lbl Channel Value), OnLevels S ls t →
      (S.coalition.proj (layerC S m ns) t).length = t.length := by
    intro t ht; rw [proj_eq_map_at_on (hpres t ht), List.length_map]
  have hEt : Exact p tA tB := by
    refine Exact.retype p oA oB tA tB hE ?_ ?_
    · rw [← hoA]; exact hlen tA hUA
    · rw [← hoB]; exact hlen tB hUB
  have hI : Interleave tA tB (weave p tA tB) := Exact.interleave p tA tB hEt
  have hUw : OnLevels S ls (weave p tA tB) := OnLevels.weave hUA hUB
  have hwC : weave p oA oB = S.coalition.proj (layerC S m ns) (weave p tA tB) := by
    rw [← hoA, ← hoB, proj_weave_at_on p (hpres tA hUA) (hpres tB hUB)]
  refine ⟨weave p tA tB, ⟨⟨(qA, qB), par_reach_interleave hI hrA hrB⟩, ?_⟩, ?_⟩
  · intro u a v r hdec
    have hmem : Lbl.inp a v ∈ weave p tA tB := by rw [hdec]; simp
    have hacs : S.valL a ∈ ls := hUw _ hmem
    refine hcons (S.coalition.proj (layerC S m ns) u) a v
      (S.coalition.proj (layerC S m ns) r) ?_ (hfull a hacs) u rfl
    rw [hwC, hdec, proj_append,
      proj_cons_some (projLbl_eq_projL_at_on (l := Lbl.inp a v)
        (S.coalition.le_trans (S.coalition.pres_le_val a) (hfull a hacs))),
      projL_inp_vis (hfull a hacs)]
  · rw [← hdown, hwC, down_proj (layerC_le S m ns)]

/-! ### The peeling, relativised to the channels in use -/

/-- Flatness, asked only of the channels in `cs`. -/
def PeelFlatOn (S : Sec Level Channel) (m : Level) (ls : List Level) :
    List Level → Prop
  | [] => True
  | n :: ns => (∀ a : Channel, S.valL a ∈ ls →
      NewlyVisible S (layerC S m ns) n a → S.le n (S.valL a)) ∧ PeelFlatOn S m ls ns

/-- A peeling that exhausts the levels in `ls`, flat along the way. -/
def PeelableOn (S : Sec Level Channel) (m : Level) (ls : List Level) : Prop :=
  ∃ ns : List Level,
    (∀ a : Channel, S.valL a ∈ ls → S.coalition.le (sing (S.valL a)) (layerC S m ns)) ∧
    PeelFlatOn S m ls ns

theorem peelFlatOn_of_ext {S : Sec Level Channel} {m : Level} {ls : List Level}
    {L : List Level} (hL : ∀ a : Channel, S.valL a ∈ ls → S.valL a ∈ L) :
    ∀ ns : List Level, Ext S L ns → PeelFlatOn S m ls ns := by
  intro ns
  induction ns with
  | nil => intro _; trivial
  | cons n ns ih =>
      intro hE
      refine ⟨?_, ih hE.2⟩
      intro a hacs ha
      refine Classical.byContradiction fun hcon => ?_
      obtain ⟨d, hd, hle⟩ := ha.1 (S.valL a) rfl
      rcases hd with hd | rfl
      · exact ha.2 (fun c hc => ⟨d, hd, by rw [show c = S.valL a from hc]; exact hle⟩)
      · exact ha.2 (vis_of_mem (mem_layerC ns _ (hE.1 (S.valL a) (hL a hacs) ⟨hle, hcon⟩)))

/-- **A peeling of the channels in use always exists.**  Only the levels those
    channels carry have to be peeled, and there are finitely many of them. -/
theorem peelableOn_of_list {S : Sec Level Channel} (ls : List Level) (m : Level) :
    PeelableOn S m ls := by
  classical
  obtain ⟨ns, hcov, -, hE⟩ := exists_ext (S := S) ls.length ls (Nat.le_refl _)
  exact ⟨ns, fun a ha => vis_of_mem (mem_layerC ns _ (hcov _ ha)),
    peelFlatOn_of_ext (fun a ha => ha) ns hE⟩

theorem Interleave.mem_or {α : Type} {u v w : List α} (h : Interleave u v w) {x : α}
    (hx : x ∈ w) : x ∈ u ∨ x ∈ v := by
  induction h with
  | nil => exact absurd hx (by simp)
  | @left b u' v' w' _ ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl (by simp)
      · exact (ih hx).imp (fun h => List.mem_cons.mpr (Or.inr h)) id
  | @right b u' v' w' _ ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr (by simp)
      · exact (ih hx).imp id (fun h => List.mem_cons.mpr (Or.inr h))

theorem consistent_congr_on {S : Sec Level Channel} {w₁ w₂ : S.Strategy Value}
    {t : List (Lbl Channel Value)}
    (h : ∀ (a : Channel) (v : Value), Lbl.inp a v ∈ t → ∀ u, w₁.ω a u = w₂.ω a u)
    (hc : S.consistent w₁ t) : S.consistent w₂ t := by
  intro u a v r hsplit
  rw [← h a v (by rw [hsplit]; simp) u]
  exact hc u a v r hsplit

/-- A composition uses the channels its components use. -/
theorem usesLevels_par {S : Sec Level Channel} {StA StB : Type}
    {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {ls : List Level} (hA : UsesLevels S stepA sA ls) (hB : UsesLevels S stepB sB ls) :
    UsesLevels S (parStep stepA stepB) (sA, sB) ls := by
  intro t q hreach x hx
  obtain ⟨tA, tB, hrA, hrB, hI⟩ := par_decompose hreach
  rcases Interleave.mem_or hI hx with hm | hm
  · exact hA _ _ hrA x hm
  · exact hB _ _ hrB x hm


end Sec

end InteractiveNI
