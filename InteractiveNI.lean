/-
  ==========================================================================
  Interactive Noninterference Does Not (Always) Compose
  Lean 4 formalization of the paper by François Hublet (ETH Zürich).
  ==========================================================================

  The development is self-contained (no external dependencies), has no
  `sorry`, and uses no axiom beyond Lean's three standard ones (`propext`,
  `Classical.choice`, `Quot.sound`); see the `#print axioms` commands below.

  Every numbered item of the paper that carries a `[Lean: ...]` annotation is
  listed here, in the order in which it appears.

    §2   Definition 1  IOLTS, input-neutrality   `Reach`, `InputNeutral`
         Definition 3  π_ℓ and =_ℓ               `Sec.proj`, `Sec.teq`
         Definition 5  strategies               `Sec.Strategy`
         Definition 8  INI                      `Sec.INI`, `Sec.StratNI`
    §3   Theorem 10                             `noncompositional`
         Definition 11 CINI                     `Sec.coalition`
         Theorem 12                             `Cex1.coalitionNI_strictly_stronger`
         Theorem 13                             `noncompositional_total`
    §4   Lemma 14                               `Sec.deterministic_step`
         Lemma 15                               `Sec.indistinguishable_NI`
         Lemma 16                               `Sec.compose_helper`
         Theorem 17                             `Sec.deterministic_compositional`
         Theorem 18                             `Sec.deterministic_compositional_family`
    §5   Definition 19 comparable labelling     `Sec.Cmp`
         Definition 20 peeling                  `Sec.PeelableM`
         Proposition 21                         `Sec.peelableM_iff_cmp`
         Theorem 22                             `Sec.coalition_compositional_of_cmp`
         Theorem 23                             `CexPresence.progs_NI`,
                                                `CexPresence.par_not_NI`
         Corollary 24                           `Sec.coalition_compositional_total_used`,
                                                `Sec.coalition_compositional_strat_used`,
                                                `Sec.consistent_of_totalize`
         Corollary 25                           `Sec.coalition_of_INI`,
                                                `Sec.StratTNI_of_coalition`,
                                                `Sec.INI_compositional_of_total'`

  Claims the text makes in prose rather than as numbered statements are also
  proved:

    §5    `P₁` is coalition noninterfering        `P1.P1_coalitionNI`
    §5.2  the components are input-neutral        `CexPresence.prog_neutral`
    §5.2  no peeling at `H₁` is presence-monotone `CexPresence.not_peelableM`
    §5.2  the same example refutes INI            `CexPresence.progs_INI`,
                                                  `CexPresence.par_not_INI`
-/

import InteractiveNI.Basic
import InteractiveNI.Proj
import InteractiveNI.Shift
import InteractiveNI.Det
import InteractiveNI.Compose
import InteractiveNI.Cex1
import InteractiveNI.Cex2
import InteractiveNI.Coalition
import InteractiveNI.Cex1Coalition
import InteractiveNI.P1Coalition
import InteractiveNI.Layered
import InteractiveNI.Freeze
import InteractiveNI.Interp
import InteractiveNI.Weave
import InteractiveNI.LayerGame
import InteractiveNI.LayerGameW
import InteractiveNI.JointW
import InteractiveNI.UsedChans
import InteractiveNI.PeelExists
import InteractiveNI.LayerStepW
import InteractiveNI.FiniteUse
import InteractiveNI.Chains
import InteractiveNI.Comparable
import InteractiveNI.CexPresence
import InteractiveNI.CexPeel

/-! ### Every result the paper cites, with its axioms -/

-- §3
#print axioms InteractiveNI.noncompositional
#print axioms InteractiveNI.Sec.coalition
#print axioms InteractiveNI.Cex1.coalitionNI_strictly_stronger
#print axioms InteractiveNI.noncompositional_total

-- §4
#print axioms InteractiveNI.Sec.deterministic_step
#print axioms InteractiveNI.Sec.indistinguishable_NI
#print axioms InteractiveNI.Sec.compose_helper
#print axioms InteractiveNI.Sec.deterministic_compositional
#print axioms InteractiveNI.Sec.deterministic_compositional_family

-- §5.1
#print axioms InteractiveNI.Sec.Cmp
#print axioms InteractiveNI.Sec.PeelableM
#print axioms InteractiveNI.Sec.peelableM_iff_cmp
#print axioms InteractiveNI.Sec.coalition_compositional_of_cmp

-- §5.2
#print axioms InteractiveNI.CexPresence.progs_NI
#print axioms InteractiveNI.CexPresence.par_not_NI
#print axioms InteractiveNI.CexPresence.prog_neutral
#print axioms InteractiveNI.CexPresence.not_peelableM
#print axioms InteractiveNI.CexPresence.progs_INI
#print axioms InteractiveNI.CexPresence.par_not_INI

-- §5.3
#print axioms InteractiveNI.Sec.coalition_compositional_total_used
#print axioms InteractiveNI.Sec.coalition_compositional_strat_used
#print axioms InteractiveNI.Sec.consistent_of_totalize
#print axioms InteractiveNI.Sec.coalition_of_INI
#print axioms InteractiveNI.Sec.StratTNI_of_coalition
#print axioms InteractiveNI.Sec.INI_compositional_of_total'

-- §5, in prose
#print axioms InteractiveNI.P1.P1_coalitionNI
