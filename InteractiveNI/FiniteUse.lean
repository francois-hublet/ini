/-
  **The compositionality theorems, with finiteness moved to the programs.**
-/
import InteractiveNI.LayerStepW

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

namespace Sec

variable {Level Channel Value : Type}

/-! ### The theorems, with finiteness moved to the programs

    Neither theorem needs the *universe* of channels to be finite.  What the
    proof uses is that the two components between them use finitely many
    channels -- which a program, being a finite object, always does. -/

/-- **Coalition `Strat_T`-noninterference composes**: presence public, and the
    two components use finitely many channels. -/
theorem coalition_compositional_total_used {S : Sec Level Channel}
    (hpubS : PublicPresence S) (dflt : Value)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {ls : List Level} (hcsA : UsesLevels S stepA sA ls) (hcsB : UsesLevels S stepB sB ls)
    (hNIA : S.coalition.StratTNI stepA sA) (hNIB : S.coalition.StratTNI stepB sB) :
    S.coalition.StratTNI (parStep stepA stepB) (sA, sB) :=
  coalition_compositional_totalW dflt hcsA hcsB
    (fun m => peelableM_of_pub hpubS m ls) hNIA hNIB

/-- **Coalition `Strat`-noninterference composes**, under the same hypotheses. -/
theorem coalition_compositional_strat_used {S : Sec Level Channel}
    (hpubS : PublicPresence S) (dflt : Value)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {ls : List Level} (hcsA : UsesLevels S stepA sA ls) (hcsB : UsesLevels S stepB sB ls)
    (hNIA : S.coalition.StratNI stepA sA) (hNIB : S.coalition.StratNI stepB sB) :
    S.coalition.StratNI (parStep stepA stepB) (sA, sB) := by
  intro C w₁ w₂ _ _ hseq t₁ h₁
  by_cases hCne : ∃ c, C c
  case neg =>
    refine ⟨[], ⟨⟨(sA, sB), Reach.nil⟩, by intro u a v r heq; simp at heq⟩, ?_⟩
    unfold Sec.teq
    rw [proj_empty_coalition hCne, proj_empty_coalition hCne]
  have hpubC : S.coalition.PubAt C := pubAt_coalition hpubS hCne
  obtain ⟨t₂, h₂, hteq⟩ := coalition_compositional_total_used hpubS dflt hcsA hcsB
    (INI_mono (fun _ _ => trivial) hNIA) (INI_mono (fun _ _ => trivial) hNIB)
    C (totalize S.coalition dflt w₁) (totalize S.coalition dflt w₂)
    (totalize_total dflt w₁) (totalize_total dflt w₂)
    (seq_totalize dflt hpubC hseq) t₁ (produces_totalize h₁)
  exact ⟨t₂, ⟨h₂.1, consistent_of_totalize hpubC hseq h₁.2 hteq h₂.2⟩, hteq⟩

/-- A component using finitely many channels uses finitely many levels -- the
    case of any program, which is a finite object.  In particular `ℂ` finite
    suffices, but it is not needed: infinitely many channels at finitely many
    levels are fine. -/
theorem usesLevels_of_chans {S : Sec Level Channel} {St : Type}
    {step : St → Act Channel Value → St → Prop} {s : St} {cs : List Channel}
    (h : ∀ (t : List (Lbl Channel Value)) (s' : St), Reach step s t s' →
      ∀ x ∈ t, x.chan ∈ cs) :
    UsesLevels S step s (cs.map S.valL) :=
  fun t s' hr x hx => List.mem_map.mpr ⟨x.chan, h t s' hr x hx, rfl⟩

theorem usesLevels_all {S : Sec Level Channel} {St : Type}
    {step : St → Act Channel Value → St → Prop} {s : St} {ls : List Level}
    (hls : ∀ l : Level, l ∈ ls) : UsesLevels S step s ls := fun _ _ _ x _ => hls _

theorem usesLevels_of_finite {S : Sec Level Channel} {St : Type}
    {step : St → Act Channel Value → St → Prop} {s : St} {cs : List Channel}
    (h : ∀ a : Channel, a ∈ cs) : UsesLevels S step s (cs.map S.valL) :=
  usesLevels_of_chans (fun _ _ _ x _ => h x.chan)

end Sec

end InteractiveNI
