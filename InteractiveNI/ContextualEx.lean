/-
  **The strengthening, on the two examples that matter.**

  `P_p` is coalition noninterfering but not contextually so -- `P_q` is the
  context that defeats it.  `P₁`, on the other hand, is contextually
  noninterferent, so the strengthening still answers requirement (b) of the
  conclusion.
-/
import InteractiveNI.Contextual
import InteractiveNI.CexPresence
import InteractiveNI.CexSelf
import InteractiveNI.P1Coalition

namespace InteractiveNI

open Classical

namespace CexPresence

/-- **The counterexample is excluded.** -/
theorem not_compTNI : ¬ Sec.CompTNI Sc (prog Chan.p) St.s0 := by
  intro h
  exact par_not_NI (h St (prog Chan.q) St.s0 progs_NI.2)

end CexPresence

namespace CexSelf

/-- A single program that is not contextually noninterferent -- witnessed by
    itself as the context. -/
theorem not_compTNI : ¬ Sec.CompTNI CexPresence.Sc rprog RSt.s0 := by
  intro h
  exact rprog_par_not_NI (h RSt rprog RSt.s0 rprog_NI)

end CexSelf

namespace P1

theorem pub_Sc2 : Sec.PublicPresence Sc2 := fun _ _ => Or.inl rfl

theorem all_levels : ∀ l : L2, l ∈ [L2.Lo, L2.Hi] := by intro l; cases l <;> simp

/-- **`P₁` is contextually noninterferent**, so requirement (b) survives the
    strengthening. -/
theorem P1_compTNI : Sec.CompTNI Sc2 stepP1 P1State.p0 :=
  Sec.compTNI_of_stratTNI pub_Sc2 false [L2.Lo, L2.Hi] all_levels
    (Sec.INI_mono (fun _ _ => trivial) P1_coalitionNI)

end P1

end InteractiveNI
