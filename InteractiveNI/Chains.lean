/-
  **What the coalition notion buys: INI composes over a total order.**

  Over a finite total order every non-empty
  coalition has a greatest element, so coalition noninterference collapses to
  INI; the composition theorem then applies and gives INI of the composition.
  Over a total order, therefore, INI *does* compose.
-/
import InteractiveNI.FiniteUse

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

namespace Sec

variable {Level Channel Value : Type}

/-- A total order. -/
def IsTotal (S : Sec Level Channel) : Prop := ∀ a b : Level, S.le a b ∨ S.le b a

/-- Over a total order, a non-empty coalition drawn from a finite set of levels
    has a greatest element. -/
theorem exists_greatest {S : Sec Level Channel} (htot : S.IsTotal)
    (ls : List Level) (hls : ∀ l : Level, l ∈ ls) {C : Coalition Level} (hne : ∃ c, C c) :
    ∃ c : Level, C c ∧ ∀ d : Level, C d → S.le d c := by
  classical
  obtain ⟨c₀, hc₀⟩ := hne
  have hmem : c₀ ∈ ls.filter (fun l => decide (C l)) :=
    List.mem_filter.mpr ⟨hls c₀, by simp only [decide_eq_true_eq]; exact hc₀⟩
  obtain ⟨M, hM, hmax⟩ := exists_maximal (S := S) (ls.filter (fun l => decide (C l)))
    (fun h => absurd (h ▸ hmem) (by simp))
  refine ⟨M, (by simpa using (List.mem_filter.mp hM).2), ?_⟩
  intro d hd
  have hdmem : d ∈ ls.filter (fun l => decide (C l)) :=
    List.mem_filter.mpr ⟨hls d, by simp only [decide_eq_true_eq]; exact hd⟩
  have hnlt := hmax d hdmem
  refine Classical.byContradiction fun hdm => ?_
  rcases htot M d with h | h
  · exact hnlt ⟨h, hdm⟩
  · exact hdm h

/-! ### A coalition with a greatest element is that element -/

theorem le_greatest_iff {S : Sec Level Channel} {C : Coalition Level} {c : Level}
    (hc : C c) (hmax : ∀ d : Level, C d → S.le d c) (x : Level) :
    S.coalition.le (sing x) C ↔ S.le x c := by
  constructor
  · intro h
    obtain ⟨d, hd, hxd⟩ := h x rfl
    exact S.le_trans hxd (hmax d hd)
  · intro h y hy
    exact ⟨c, hc, by rw [show y = x from hy]; exact h⟩

theorem projLbl_greatest {S : Sec Level Channel} {C : Coalition Level} {c : Level}
    (hc : C c) (hmax : ∀ d : Level, C d → S.le d c) (l : Lbl Channel Value) :
    S.coalition.projLbl C l = S.coalition.projLbl (sing c) l := by
  have key : ∀ x : Level, S.coalition.le (sing x) C ↔ S.coalition.le (sing x) (sing c) := by
    intro x
    rw [le_greatest_iff hc hmax, coalition_le_sing]
  cases l with
  | inp a v =>
      have hp := key (S.presL a)
      have hv := key (S.valL a)
      by_cases h1 : S.coalition.le (S.coalition.presL a) C
      · by_cases h2 : S.coalition.le (S.coalition.valL a) C
        · rw [projLbl_inp_full h1 h2,
            projLbl_inp_full (a := a) (v := v) (hp.mp h1) (hv.mp h2)]
        · rw [projLbl_inp_pres h1 h2,
            projLbl_inp_pres (a := a) (v := v) (hp.mp h1) (fun hc' => h2 (hv.mpr hc'))]
      · rw [projLbl_inp_hidden h1,
          projLbl_inp_hidden (a := a) (v := v) (fun hc' => h1 (hp.mpr hc'))]
  | out a v =>
      have hp := key (S.presL a)
      have hv := key (S.valL a)
      by_cases h1 : S.coalition.le (S.coalition.presL a) C
      · by_cases h2 : S.coalition.le (S.coalition.valL a) C
        · rw [projLbl_out_full h1 h2,
            projLbl_out_full (a := a) (v := v) (hp.mp h1) (hv.mp h2)]
        · rw [projLbl_out_pres h1 h2,
            projLbl_out_pres (a := a) (v := v) (hp.mp h1) (fun hc' => h2 (hv.mpr hc'))]
      · rw [projLbl_out_hidden h1,
          projLbl_out_hidden (a := a) (v := v) (fun hc' => h1 (hp.mpr hc'))]

theorem proj_greatest {S : Sec Level Channel} {C : Coalition Level} {c : Level}
    (hc : C c) (hmax : ∀ d : Level, C d → S.le d c) (t : List (Lbl Channel Value)) :
    S.coalition.proj C t = S.proj c t := by
  rw [← coalition_proj_sing (S := S) c t]
  simp only [proj]
  exact congrArg (fun f => List.filterMap f t) (funext (projLbl_greatest hc hmax))

/-! ### Over a total order, INI is coalition noninterference -/

theorem coalition_of_INI {S : Sec Level Channel} (htot : S.IsTotal)
    (ls : List Level) (hls : ∀ l : Level, l ∈ ls) {St : Type}
    {step : St → Act Channel Value → St → Prop} {s : St}
    (h : S.StratTNI step s) : S.coalition.StratTNI step s := by
  intro C w₁ w₂ ht₁ ht₂ hseq t₁ h₁
  by_cases hCne : ∃ c, C c
  case neg =>
    refine ⟨[], ⟨⟨s, Reach.nil⟩, by intro u a v r heq; simp at heq⟩, ?_⟩
    unfold Sec.teq
    rw [proj_empty_coalition hCne, proj_empty_coalition hCne]
  obtain ⟨c, hc, hmax⟩ := exists_greatest htot ls hls hCne
  have hseq' : S.seq c (Strategy.ofCoalition w₁) (Strategy.ofCoalition w₂) := by
    intro a t
    refine ⟨fun hvis => (hseq a t).1 ?_, fun hvis => (hseq a t).2 ?_⟩
    · exact (le_greatest_iff hc hmax _).mpr hvis
    · exact (le_greatest_iff hc hmax _).mpr hvis
  obtain ⟨t₂, hp₂, hteq⟩ :=
    h c (Strategy.ofCoalition w₁) (Strategy.ofCoalition w₂) ht₁ ht₂ hseq' t₁ h₁
  refine ⟨t₂, hp₂, ?_⟩
  show S.coalition.proj C t₁ = S.coalition.proj C t₂
  rw [proj_greatest hc hmax, proj_greatest hc hmax]
  exact hteq

/-! ### Over a total order the peeling is presence-monotone for free -/

theorem peelFlatOn_of_ext_filter {S : Sec Level Channel} {m : Level} {ls : List Level}
    {Lst : List Level}
    (hLst : ∀ a : Channel, S.valL a ∈ ls → S.le m (S.valL a) → S.valL a ∈ Lst) :
    ∀ ns : List Level, Ext S Lst ns → PeelFlatOn S m ls ns := by
  intro ns
  induction ns with
  | nil => intro _; trivial
  | cons n ns ih =>
      intro hE
      refine ⟨?_, ih hE.2⟩
      intro a ha hnv
      refine Classical.byContradiction fun hcon => ?_
      obtain ⟨d, hd, hle⟩ := hnv.1 (S.valL a) rfl
      rcases hd with hd | rfl
      · exact hnv.2 (fun c hc => ⟨d, hd, by rw [show c = S.valL a from hc]; exact hle⟩)
      · by_cases hm : S.le m (S.valL a)
        · exact hnv.2 (vis_of_mem (mem_layerC ns _ (hE.1 (S.valL a) (hLst a ha hm) ⟨hle, hcon⟩)))
        · exact hnv.2 (S.coalition.le_trans ((vis_Cplus m a).mpr hm) (layerC_le S m ns))

theorem peelMono_of_desc {S : Sec Level Channel} (htot : S.IsTotal) {m : Level}
    {ls : List Level} :
    ∀ ns : List Level, (∀ n ∈ ns, S.le m n) → Desc S ns → PeelMono S m ls ns := by
  intro ns
  induction ns with
  | nil => intro _ _; trivial
  | cons n ns ih =>
      intro hmn hD
      refine ⟨?_, ih (fun n' hn' => hmn n' (List.mem_cons.mpr (Or.inr hn'))) hD.2⟩
      intro b _ hpres
      obtain ⟨c, hc, hbc⟩ := hpres (S.presL b) rfl
      rcases layerC_inv ns c hc with hc' | hc'
      · have hcm : S.le c m := by
          rcases htot m c with h | h
          · exact absurd h hc'
          · exact h
        exact S.le_trans hbc (S.le_trans hcm (hmn n (by simp)))
      · exact S.le_trans hbc (hD.1 c hc')

/-- **Over a total order the peeling is presence-monotone for free.**  The levels
    the coalition can already detect are below the perturbation level, and every
    level the peeling still has to expose is above it. -/
theorem peelableM_of_total {S : Sec Level Channel} (htot : S.IsTotal)
    (ls : List Level) (m : Level) : PeelableM S m ls := by
  classical
  obtain ⟨ns, hcov, hsub, hE, hD⟩ :=
    exists_ext_desc (S := S) htot (ls.filter (fun n => decide (S.le m n))).length
      (ls.filter (fun n => decide (S.le m n))) (Nat.le_refl _)
  have hmn : ∀ n ∈ ns, S.le m n := by
    intro n hn
    have := List.mem_filter.mp (hsub n hn)
    simpa using this.2
  refine ⟨ns, ?_, peelFlatOn_of_ext_filter ?_ ns hE, peelMono_of_desc htot ns hmn hD⟩
  · intro a ha
    by_cases hm : S.le m (S.valL a)
    · exact vis_of_mem (mem_layerC ns _
        (hcov _ (List.mem_filter.mpr ⟨ha, by simpa using hm⟩)))
    · exact S.coalition.le_trans ((vis_Cplus m a).mpr hm) (layerC_le S m ns)
  · intro a ha hm
    exact List.mem_filter.mpr ⟨ha, by simpa using hm⟩

/-- **Coalition noninterference composes over a total order**, with no
    hypothesis on presence at all. -/
theorem coalition_compositional_of_total {S : Sec Level Channel} (htot : S.IsTotal)
    (dflt : Value) {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {ls : List Level} (hcsA : UsesLevels S stepA sA ls) (hcsB : UsesLevels S stepB sB ls)
    (hNIA : S.coalition.StratTNI stepA sA) (hNIB : S.coalition.StratTNI stepB sB) :
    S.coalition.StratTNI (parStep stepA stepB) (sA, sB) :=
  coalition_compositional_totalW dflt hcsA hcsB
    (fun m => peelableM_of_total htot ls m) hNIA hNIB

/-- **INI composes over a total order**, with no hypothesis on presence. -/
theorem INI_compositional_of_total' {S : Sec Level Channel} (htot : S.IsTotal)
    (dflt : Value) (ls : List Level) (hls : ∀ l : Level, l ∈ ls)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    (hA : S.StratTNI stepA sA) (hB : S.StratTNI stepB sB) :
    S.StratTNI (parStep stepA stepB) (sA, sB) :=
  StratTNI_of_coalition
    (coalition_compositional_of_total htot dflt (ls := ls)
      (usesLevels_all hls) (usesLevels_all hls)
      (coalition_of_INI htot ls hls hA) (coalition_of_INI htot ls hls hB))

end Sec

end InteractiveNI
