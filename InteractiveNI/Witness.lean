/-
  **The general theorem is not vacuous, and it applies where spreadness fails.**

  We instantiate it on the security context of `NoPolicy.lean` -- levels
  `⊥ ⊑ Ob`, `⊥ ⊑ Md ⊑ Hi` with `Ob` incomparable to `Md` and `Hi`, channels
  `pub, α, β` at `Ob, Md, Hi`.  The labelling is **not** spread: `α` and `β` sit at
  `Md ⊑ Hi`.  It is also the context in which `NoPolicy.no_causal_policy` shows a
  coalition-noninterfering component with no causal policy.
-/
import InteractiveNI.LayerGame
import InteractiveNI.NoPolicy

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

namespace NoPolicy

/-- Presence is public in the underlying context. -/
theorem pub_Sc3 : Sec.PublicPresence Sc3 := fun _ _ => Or.inl rfl

/-- `γ` is *not* spread here: `α` and `β` are comparable. -/
theorem not_spread : ¬ Sc3.ChannelAntichain := by
  intro h
  have := h Ch3.alp Ch3.bet (Or.inr (Or.inr ⟨rfl, rfl⟩))
  rcases this with h' | h' | ⟨-, h'⟩ <;> exact absurd h' (by decide)

/-- The peeling for a perturbation at `Md`. -/
theorem full_Md : ∀ a : Ch3,
    Sc3.coalition.le (Sec.sing (Sc3.valL a)) (Sec.layerC Sc3 L3.Md [L3.Hi, L3.Md]) := by
  intro a c hc
  cases a
  · exact ⟨L3.Ob, Or.inl (Or.inl (by intro h; rcases h with h | h | ⟨-, h⟩ <;> exact absurd h (by decide))),
      by rw [show c = L3.Ob from hc]; exact L3.le_refl _⟩
  · exact ⟨L3.Md, Or.inl (Or.inr rfl), by rw [show c = L3.Md from hc]; exact L3.le_refl _⟩
  · exact ⟨L3.Hi, Or.inr rfl, by rw [show c = L3.Hi from hc]; exact L3.le_refl _⟩

theorem cplus_Ob_Hi : Sec.Cplus Sc3 L3.Hi L3.Ob := by
  intro h; rcases h with h | h | ⟨-, h⟩ <;> exact absurd h (by decide)

theorem cplus_Md_Hi : Sec.Cplus Sc3 L3.Hi L3.Md := by
  intro h; rcases h with h | h | ⟨-, h⟩ <;> exact absurd h (by decide)

theorem cplus_Ob : Sec.Cplus Sc3 L3.Md L3.Ob := by
  intro h; rcases h with h | h | ⟨-, h⟩ <;> exact absurd h (by decide)

theorem pub_vis_Cplus :
    Sc3.coalition.le (Sec.sing (Sc3.valL Ch3.pub)) (Sec.Cplus Sc3 L3.Md) :=
  fun c hc => ⟨L3.Ob, cplus_Ob, by rw [show c = L3.Ob from hc]; exact L3.le_refl _⟩

theorem alp_vis_add :
    Sc3.coalition.le (Sec.sing (Sc3.valL Ch3.alp))
      (Sec.addLevel (Sec.Cplus Sc3 L3.Md) L3.Md) :=
  fun c hc => ⟨L3.Md, Or.inr rfl, by rw [show c = L3.Md from hc]; exact L3.le_refl _⟩

/-- The peeling of the layers above `Md` is flat, by construction. -/
theorem peelFlat_Md : Sec.PeelFlat Sc3 L3.Md [L3.Hi, L3.Md] := by
  refine ⟨?_, ?_, trivial⟩
  · intro a ha
    cases a
    · exact absurd (fun c hc => ⟨L3.Ob, Or.inl cplus_Ob,
        by rw [show c = L3.Ob from hc]; exact L3.le_refl _⟩) ha.2
    · exact absurd alp_vis_add ha.2
    · exact L3.le_refl _
  · intro a ha
    cases a
    · exact absurd pub_vis_Cplus ha.2
    · exact L3.le_refl _
    · exfalso
      obtain ⟨d, hd, hle⟩ := ha.1 L3.Hi rfl
      have hdHi : d = L3.Hi := by
        rcases hle with h | h | ⟨h, -⟩ <;> first
          | exact absurd h (by decide)
          | exact h.symm
      subst hdHi
      rcases hd with hd | hd
      · exact hd (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · exact absurd hd (by decide)

/-! ### The peeling exists at every level -/

theorem le_false {x y : L3} (h1 : x ≠ L3.Bot) (h2 : x ≠ y)
    (h3 : ¬ (x = L3.Md ∧ y = L3.Hi)) : ¬ L3.le x y := by
  rintro (h | h | h)
  · exact h1 h
  · exact h2 h
  · exact h3 h

theorem vis_of {C : Sec.Coalition L3} {a : Ch3} {d : L3} (hd : C d)
    (hle : L3.le (Sc3.valL a) d) : Sc3.coalition.le (Sec.sing (Sc3.valL a)) C :=
  fun c hc => ⟨d, hd, by rw [show c = Sc3.valL a from hc]; exact hle⟩

theorem not_vis {C : Sec.Coalition L3} {a : Ch3}
    (h : ∀ d, C d → ¬ L3.le (Sc3.valL a) d) :
    ¬ Sc3.coalition.le (Sec.sing (Sc3.valL a)) C := by
  intro hh
  obtain ⟨d, hd, hle⟩ := hh _ rfl
  exact h d hd hle

/-- Every level admits a peeling, so the hypothesis of the general theorem is
    satisfiable here -- the theorem is not vacuous. -/
theorem peelable_Sc3 : ∀ m : L3, Sec.Peelable Sc3 m := by
  have hBot : ∀ d : L3, ¬ Sec.Cplus Sc3 L3.Bot d := fun d h => h (Or.inl rfl)
  intro m
  cases m
  · -- `⊥`: nothing is visible at `C⁺`; peel `Ob`, then `Md`, then `Hi`
    refine ⟨[L3.Hi, L3.Md, L3.Ob], ?_, ?_, ?_, ?_, trivial⟩
    · intro a
      cases a
      · exact vis_of (Or.inl (Or.inl (Or.inr rfl))) (L3.le_refl _)
      · exact vis_of (Or.inl (Or.inr rfl)) (L3.le_refl _)
      · exact vis_of (Or.inr rfl) (L3.le_refl _)
    · intro a ha
      cases a
      · exact absurd (vis_of (Or.inl (Or.inr rfl)) (L3.le_refl _)) ha.2
      · exact absurd (vis_of (Or.inr rfl) (L3.le_refl _)) ha.2
      · exact L3.le_refl _
    · intro a ha
      cases a
      · exact absurd (vis_of (Or.inr rfl) (L3.le_refl _)) ha.2
      · exact L3.le_refl _
      · exact absurd ha.1 (not_vis (by
          rintro d ((hd | rfl) | rfl) hle
          · exact hBot d hd
          · exact absurd hle (le_false (by decide) (by decide) (by decide))
          · exact absurd hle (le_false (by decide) (by decide) (by decide))))
    · intro a ha
      cases a
      · exact L3.le_refl _
      · exact absurd ha.1 (not_vis (by
          rintro d (hd | rfl) hle
          · exact hBot d hd
          · exact absurd hle (le_false (by decide) (by decide) (by decide))))
      · exact absurd ha.1 (not_vis (by
          rintro d (hd | rfl) hle
          · exact hBot d hd
          · exact absurd hle (le_false (by decide) (by decide) (by decide))))
  · -- `Ob`: only `pub` is hidden at `C⁺`
    refine ⟨[L3.Ob], ?_, ?_, trivial⟩
    · intro a
      cases a
      · exact vis_of (Or.inr rfl) (L3.le_refl _)
      · exact vis_of (Or.inl (le_false (by decide) (by decide) (by decide))) (L3.le_refl _)
      · exact vis_of (Or.inl (le_false (by decide) (by decide) (by decide))) (L3.le_refl _)
    · intro a ha
      cases a
      · exact L3.le_refl _
      · exact absurd (vis_of (a := Ch3.alp) (le_false (by decide) (by decide) (by decide)) (L3.le_refl _)) ha.2
      · exact absurd (vis_of (a := Ch3.bet) (le_false (by decide) (by decide) (by decide)) (L3.le_refl _)) ha.2
  · exact ⟨[L3.Hi, L3.Md], full_Md, peelFlat_Md⟩
  · -- `Hi`: only `bet` is hidden at `C⁺`
    refine ⟨[L3.Hi], ?_, ?_, trivial⟩
    · intro a
      cases a
      · exact vis_of (Or.inl cplus_Ob_Hi) (L3.le_refl _)
      · exact vis_of (Or.inl cplus_Md_Hi) (L3.le_refl _)
      · exact vis_of (Or.inr rfl) (L3.le_refl _)
    · intro a ha
      cases a
      · exact absurd (vis_of (a := Ch3.pub) cplus_Ob_Hi (L3.le_refl _)) ha.2
      · exact absurd (vis_of (a := Ch3.alp) cplus_Md_Hi (L3.le_refl _)) ha.2
      · exact L3.le_refl _

/-- **The general theorem, instantiated where spreadness fails.**  Two copies of
    the program `Q` -- coalition-noninterfering, and with *no* causal policy
    (`no_causal_policy`) -- compose, over a labelling that is not spread. -/
theorem Q_par_Q_compositional_at_Md
    {w₁ w₂ : Sc3.coalition.Strategy Bool} (htot₁ : w₁.total) (htot₂ : w₂.total)
    (hseq : Sc3.coalition.seq (Sec.Cplus Sc3 L3.Md) w₁ w₂)
    {t₁ : List (Lbl Ch3 Bool)}
    (h₁ : Sc3.coalition.produces (parStep stepQ stepQ) w₁ (QState.q0, QState.q0) t₁) :
    ∃ t₂, Sc3.coalition.produces (parStep stepQ stepQ) w₂ (QState.q0, QState.q0) t₂ ∧
      Sc3.coalition.teq (Sec.Cplus Sc3 L3.Md) t₁ t₂ :=
  Sec.coalition_compositional_layered pub_Sc3 false htot₁ htot₂
    (Sec.INI_mono (fun _ _ => trivial) Q_coalitionNI)
    (Sec.INI_mono (fun _ _ => trivial) Q_coalitionNI)
    ⟨L3.Ob, cplus_Ob⟩ [L3.Hi, L3.Md] full_Md peelFlat_Md hseq h₁

theorem all_channels : ∀ a : Ch3, a ∈ [Ch3.pub, Ch3.alp, Ch3.bet] := by
  intro a; cases a <;> simp

/-- **The general theorem itself, instantiated where spreadness fails** -- the
    total case.  Two copies of `Q` compose, over a labelling that is not spread. -/
theorem Q_par_Q_total :
    Sc3.coalition.StratTNI (parStep stepQ stepQ) (QState.q0, QState.q0) :=
  Sec.coalition_compositional_total pub_Sc3 false [Ch3.pub, Ch3.alp, Ch3.bet]
    all_channels peelable_Sc3
    (Sec.INI_mono (fun _ _ => trivial) Q_coalitionNI)
    (Sec.INI_mono (fun _ _ => trivial) Q_coalitionNI)

/-- The same in the non-total case. -/
theorem Q_par_Q_strat :
    Sc3.coalition.StratNI (parStep stepQ stepQ) (QState.q0, QState.q0) :=
  Sec.coalition_compositional_strat pub_Sc3 false [Ch3.pub, Ch3.alp, Ch3.bet]
    all_channels peelable_Sc3 Q_coalitionNI Q_coalitionNI

end NoPolicy

end InteractiveNI
