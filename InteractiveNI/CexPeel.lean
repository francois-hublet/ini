/-
  **Why the counterexample's context admits no presence-monotone peeling.**

  Perturbing at `Ob` starts the peeling from `C⁺(Ob) = \{Hi\}`, because `Hi` does
  not dominate `Ob`: the coalition can detect the presence of `a` before the
  peeling begins.  The channels `p` and `q`, on the other hand, are invisible
  there, so the peeling has to expose their level; flatness forces the level it
  exposes them at to be `Ob` itself, and presence-monotonicity then asks for
  `Hi ⊑ Ob`.

  So the hypothesis of Theorem~23 fails exactly where Theorem~21 holds -- the two
  results do not collide.
-/
import InteractiveNI.CexPresence
import InteractiveNI.LayerStepW

namespace InteractiveNI

namespace CexPresence

open Classical

/-- `Hi` does not dominate `Ob`, so it is in `C⁺(Ob)` from the start. -/
theorem hi_cplus : Sec.Cplus Sc Lv.Ob Lv.Hi := by
  intro h; rcases h with h | h <;> exact Lv.noConfusion h

/-- `p` cannot become visible without a layer that exposes `Ob`. -/
theorem no_peel_aux : ∀ ns : List Lv,
    Sec.PeelFlatOn Sc Lv.Ob [Lv.Ob, Lv.Hi] ns →
    Sec.PeelMono Sc Lv.Ob [Lv.Ob, Lv.Hi] ns →
    ¬ Sc.coalition.le (Sec.sing (Sc.valL Chan.p)) (Sec.layerC Sc Lv.Ob ns) := by
  intro ns
  induction ns with
  | nil =>
      intro _ _ hvis
      obtain ⟨d, hd, hle⟩ := hvis (Sc.valL Chan.p) rfl
      exact hd hle
  | cons n ns ih =>
      intro hflat hmono hvis
      by_cases hprev : Sc.coalition.le (Sec.sing (Sc.valL Chan.p)) (Sec.layerC Sc Lv.Ob ns)
      · exact ih hflat.2 hmono.2 hprev
      · -- `p` is newly visible here, so flatness pins the level to `Ob`
        have hn : Sc.le n (Sc.valL Chan.p) :=
          hflat.1 Chan.p (by left) ⟨hvis, hprev⟩
        have hnOb : n = Lv.Ob := by
          rcases hn with h | h
          · exact h
          · exact absurd h (fun hc => Lv.noConfusion hc)
        -- but the coalition already detects the presence of `a`
        have hpres : Sc.coalition.le (Sec.sing (Sc.presL Chan.a)) (Sec.layerC Sc Lv.Ob ns) :=
          fun c hc => ⟨Lv.Hi, Sec.layerC_of_cplus ns Lv.Hi hi_cplus,
            by rw [show c = Lv.Hi from hc]; exact Or.inl rfl⟩
        have hmm : Sc.le (Sc.presL Chan.a) n := hmono.1 Chan.a (by right; left) hpres
        rw [hnOb] at hmm
        rcases hmm with h | h <;> exact Lv.noConfusion h

/-- **No presence-monotone peeling exists at `Ob`**, so the hypothesis of the
    generalised theorem fails in the context of the counterexample. -/
theorem not_peelableM : ¬ Sec.PeelableM Sc Lv.Ob [Lv.Ob, Lv.Hi] := by
  rintro ⟨ns, hfull, hflat, hmono⟩
  exact no_peel_aux ns hflat hmono (hfull Chan.p (by left))

end CexPresence

end InteractiveNI
