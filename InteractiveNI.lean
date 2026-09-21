/-
  ==========================================================================
  Interactive Noninterference Does Not (Always) Compose
  A complete Lean 4 formalization of the paper by François Hublet (ETH Zürich)
  (`elsarticle-template-num.tex`).
  ==========================================================================

  The development is fully machine-checked: there is no `sorry` and no extra
  axiom beyond Lean's three standard ones (`propext`, `Classical.choice`,
  `Quot.sound`); see the `#print axioms` commands at the end of this file.

  Contents
  --------
  * `InteractiveNI/Basic.lean`   §2   the model: security contexts, traces,
                                      ℓ-equivalence, strategies, IOLTS,
                                      determinism, composition, runs, INI.
  * `InteractiveNI/Proj.lean`         properties of `π_ℓ`.
  * `InteractiveNI/Shift.lean`        the strategy transformations used in §4.
  * `InteractiveNI/Det.lean`     §4   Lemmas "deterministic step" and
                                      "indistinguishable NI".
  * `InteractiveNI/Compose.lean` §4   Theorems 3 and 6 (compositionality).
  * `InteractiveNI/Cex1.lean`    §3.1 Theorem 1 (non-compositionality).
  * `InteractiveNI/Cex2.lean`    §3.3 Theorem 2 (non-compositionality, total).

  Verdict on the paper
  --------------------
  All results claimed in the paper are TRUE and are proved here:

    Theorem 1  (§3.1)  `InteractiveNI.noncompositional`
    Theorem 2  (§3.3)  `InteractiveNI.noncompositional_total`
    Lemma 4    (§4)    `InteractiveNI.Sec.deterministic_step`
    Lemma 5    (§4)    `InteractiveNI.Sec.indistinguishable_NI`
    Theorem 3  (§4)    `InteractiveNI.Sec.deterministic_compositional`
    Theorem 6  (§4)    `InteractiveNI.Sec.deterministic_compositional_family`
    Definition (§3)    `InteractiveNI.Sec.coalition`       (coalition noninterference)
    Theorem (§3)       `InteractiveNI.Cex1.coalitionNI_strictly_stronger`
    Theorem (§5)       `InteractiveNI.P1.P1_coalitionNI`
    Theorem (§5)       `InteractiveNI.NoMaskAttack.no_attack`
      No mask-and-cancel attack defeats coalition noninterference, over any
      preorder, with any number of masks and any timing.
    Splitting (§5)     `InteractiveNI.Sec.vis_Cplus`, `...le_Cplus`, `...flat_above`
      The order-theoretic core of the compositionality proof for coalition
      noninterference over a flat lattice (coalition-composes.md).

  Beyond the paper:
    Freeze lemma       `InteractiveNI.Sec.seq_induced`, `...seq_induced'`
      Freezing one component of a composition induces a *legal* strategy on the
      other and preserves `=_ℓ`.
    Interpolation      `InteractiveNI.Sec.interpolate_step`
      Compositionality over a chain reduces to the single-layer case: matching at
      a level follows from matching one level up plus a single-layer statement.
    Weaving            `InteractiveNI.Sec.seq_weaveIns`, `...consistent_weave`
      The interleaving pattern of a composed run, and the `Insertion` it induces.
    Assembling runs    `InteractiveNI.par_reach_interleave`
      Converse of `par_decompose`: two component runs plus an interleaving give a
      run of the composition.
    Theorem C          `InteractiveNI.Sec.interleaved_compositional`
                       `InteractiveNI.Sec.INI_par_of_public_inputs`
      A component reading only ℓ-visible channels composes with any noninterfering
      component, for arbitrary interleavings and *without* determinism.
    Freeze lemma, strong `InteractiveNI.Sec.seq_weaveIns_teq`
      Freezing two different but ℓ-equivalent partners against two ℓ-equivalent
      strategies yields ℓ-equivalent induced strategies: *both* components of a
      composition may be re-planned.
    Chain compositionality, modulo one property
                       `InteractiveNI.Sec.compositional_of_mutualAdapt`
      Parallel composition preserves Strat-NI given `MutualAdapt` (separately
      re-plannable implies jointly re-plannable).  Every other step is proved.
      `MutualAdapt` is false in general -- §3's counterexample is exactly a pair
      whose re-planning oscillates -- and conjectured over a total order.
    Two-point lattice, half (b)
                       `InteractiveNI.Sec.compositional_of_policy`
      Given a causal policy for one component (Lemma (*) of two-point-proof.md,
      which follows from Strat-NI by determinacy of a finite perfect-information
      game), the composition matches.  Lemma (*) itself is not yet formalised.
      See chain-composition.md and two-point-proof.md.

  Two proofs of §4, however, are *not* correct as published, and had to be
  repaired (the statements are unaffected):

  (a) In the proof of Lemma "deterministic step" (and again in Lemma
      "indistinguishable NI"), the auxiliary strategy `ω'` is defined by
      `ω'_{α'}(t) = ω_{α'}(t)` for every channel `α' ≠ α`.  With that
      definition the very next step of the proof — "`ω'₁ ⊨ s ⟶^{α:v.t₁}`" —
      does not follow: consistency of `α:v.t₁` requires `ω'₁_β(α:v.u) ∋ w` for
      every input `β?w` occurring in `t₁` after `u`, whereas the hypothesis only
      gives `ω₁_β(u) ∋ w`, and `ω₁_β(α:v.u) ≠ ω₁_β(u)` in general.  The prefix
      must be removed on *all* channels.  Here (`InteractiveNI/Shift.lean`) we
      use `ω'_{α'}(t) = ω_{α'}(removeFirst α t)`, which is a legal strategy
      (`shiftStrat`) and has all the properties the paper needs.

  (b) The proof of Lemma "indistinguishable NI" is by induction on the sum of
      the lengths of the two executions; in the case `e = α?v` with
      `ℓ₂ ⊑ ℓ` it concludes `ω₂ ⊨ sE ⟶^{t₂}` from a run of the state reached
      *before* the trailing ℓ-invisible part `u'` of `t'`, which is a different
      state than `sE`.  We give a different, non-inductive proof: the prefixes
      `t` and `t'` are forced by the strategies `unshift t ω₁` and
      `unshift t' ω₂` (which are ℓ-equivalent because `t =_ℓ t'`), and
      determinism makes every matching run follow `t'` (`Sec.follow`).

  (c) The proof of the "helper" theorem for composition needs an extra
      hypothesis that the published statement does not record: ℓ-equivalence of
      the *component* histories.  (`t =_ℓ t'` for the interleaved traces does
      not imply it: the same visible label may be emitted by either component.)
      Our `Sec.compose_helper` carries it; it is trivially available where
      Theorem 3 is deduced from it.

  One further gap of §3, closed here: §2 requires the levels to form a
  semilattice, but the posets `{L,H,H₁,H₂,H₃}` and `{L₁,L₂,H,H₁,H₂,H₃}` used in
  the counterexamples have no joins for incomparable elements.  We therefore add
  a top level `⊤` to both (`L5.Top`, `L6.Top`); `L5.join_*` / `L6.join_*` show
  the results are genuine (bounded) lattices, and the extra level is part of the
  statements of Theorems 1 and 2 via `Sec.IsJoinSemilattice`.

  Internal consistency checks
  ---------------------------
  * `Cex1.stepA_not_det`, `Cex1.stepB_not_det` (and the `Cex2` analogues): the
    counterexample programs are non-deterministic, as Theorem 3 requires them to
    be — Theorems 1/2 and 3/6 are therefore not in conflict.
  * `Cex1.tcex_produces` exhibits a concrete run, so the model is not vacuous;
    `Cex1.A_NI` and `Cex1.par_not_NI` show INI is neither trivially true nor
    trivially false.
-/
import InteractiveNI.Basic
import InteractiveNI.Proj
import InteractiveNI.Shift
import InteractiveNI.Det
import InteractiveNI.Compose
import InteractiveNI.Freeze
import InteractiveNI.Interp
import InteractiveNI.Weave
import InteractiveNI.SeqCompose
import InteractiveNI.Chain
import InteractiveNI.TwoPoint
import InteractiveNI.Game
import InteractiveNI.Coalition
import InteractiveNI.Cex1Coalition
import InteractiveNI.P1Coalition
import InteractiveNI.NoMaskAttack
import InteractiveNI.NoPolicy
import InteractiveNI.Layered
import InteractiveNI.Policy
import InteractiveNI.LayerGame
import InteractiveNI.LayerGameW
import InteractiveNI.JointW
import InteractiveNI.LayerStepW
import InteractiveNI.PeelExists
import InteractiveNI.NoPeelMono
import InteractiveNI.Comparable
import InteractiveNI.CexPresence
import InteractiveNI.UsedChans
import InteractiveNI.FiniteUse
import InteractiveNI.Contextual
import InteractiveNI.ContextualEx
import InteractiveNI.Chains
import InteractiveNI.CexPeel
import InteractiveNI.CexSelf
import InteractiveNI.Witness
import InteractiveNI.WitnessW
import InteractiveNI.Cex1
import InteractiveNI.Cex2

namespace InteractiveNI

/-! ## The results of the paper, collected -/

section Summary

variable {Level Channel Value : Type} {S : Sec Level Channel}

/-- §4, Lemma "deterministic step": `Strat-NI` is preserved by a transition. -/
example {St : Type} {step : St → Act Channel Value → St → Prop}
    (hdet : Deterministic step) {s s' : St} {e : Act Channel Value}
    (hNI : S.StratNI step s) (hstep : step s e s') : S.StratNI step s' :=
  Sec.deterministic_step hdet hNI hstep

/-- §4, Theorem 3: `Strat-NI` composes for deterministic IOLTS. -/
example {St₁ St₂ : Type}
    {step₁ : St₁ → Act Channel Value → St₁ → Prop}
    {step₂ : St₂ → Act Channel Value → St₂ → Prop}
    (hdet₁ : Deterministic step₁) (hdet₂ : Deterministic step₂)
    {sA : St₁} {sB : St₂} (hA : S.StratNI step₁ sA) (hB : S.StratNI step₂ sB) :
    S.StratNI (parStep step₁ step₂) (sA, sB) :=
  Sec.deterministic_compositional hdet₁ hdet₂ hA hB

/-- §4, Theorem 6: `Strat-NI` composes for arbitrary families. -/
example {I : Type} {St : I → Type}
    {step : ∀ i, St i → Act Channel Value → St i → Prop}
    (hdet : ∀ i, Deterministic (step i)) {s : ∀ i, St i}
    (hNI : ∀ i, S.StratNI (step i) (s i)) : S.StratNI (parStepFam step) s :=
  Sec.deterministic_compositional_family hdet hNI

end Summary

end InteractiveNI

/-! ## Axiom audit -/

#print axioms InteractiveNI.noncompositional
#print axioms InteractiveNI.noncompositional_total
#print axioms InteractiveNI.Sec.deterministic_step
#print axioms InteractiveNI.Sec.indistinguishable_NI
#print axioms InteractiveNI.Sec.compose_helper
#print axioms InteractiveNI.Sec.deterministic_compositional
#print axioms InteractiveNI.Sec.deterministic_compositional_family
#print axioms InteractiveNI.Sec.seq_induced
#print axioms InteractiveNI.Sec.seq_induced'
#print axioms InteractiveNI.Sec.interpolate_step
#print axioms InteractiveNI.Sec.seq_weaveIns
#print axioms InteractiveNI.par_reach_interleave
#print axioms InteractiveNI.Sec.sequential_compositional
#print axioms InteractiveNI.Sec.interleaved_compositional
#print axioms InteractiveNI.Sec.INI_par_of_public_inputs
#print axioms InteractiveNI.Sec.seq_weaveIns_teq
#print axioms InteractiveNI.Sec.StratNI_of_coalition
#print axioms InteractiveNI.Cex1.A_not_coalitionNI
#print axioms InteractiveNI.Cex1.coalitionNI_strictly_stronger
#print axioms InteractiveNI.P1.P1_coalitionNI
#print axioms InteractiveNI.NoMaskAttack.no_attack
#print axioms InteractiveNI.NoPolicy.Q_coalitionNI
#print axioms InteractiveNI.NoPolicy.no_policy
#print axioms InteractiveNI.NoPolicy.win_exists
#print axioms InteractiveNI.NoPolicy.no_causal_policy
#print axioms InteractiveNI.NoPolicy.Q_flat_not_coalitionNI
#print axioms InteractiveNI.Sec.vis_Cplus
#print axioms InteractiveNI.Sec.le_Cplus
#print axioms InteractiveNI.Sec.flat_above
#print axioms InteractiveNI.Sec.channelAntichain_of_flat
#print axioms InteractiveNI.Sec.anti_adversarial
#print axioms InteractiveNI.Sec.anti_sameView
#print axioms InteractiveNI.Sec.eq_of_teq_vis
#print axioms InteractiveNI.Sec.eq_of_coalition_teq_vis
#print axioms InteractiveNI.Sec.teq_of_vis
#print axioms InteractiveNI.Sec.adapt_vis
#print axioms InteractiveNI.Sec.vis_Cplus_add
#print axioms InteractiveNI.Sec.le_addLevel
#print axioms InteractiveNI.Sec.layer_closed
#print axioms InteractiveNI.Sec.layer_flat
#print axioms InteractiveNI.Sec.layer_sameView
#print axioms InteractiveNI.Sec.layer_reduces
#print axioms InteractiveNI.Sec.layer_teq
#print axioms InteractiveNI.Sec.layerC_le
#print axioms InteractiveNI.Sec.layerC_flat
#print axioms InteractiveNI.Sec.down_proj
#print axioms InteractiveNI.Sec.obsConsistent_wellDefined
#print axioms InteractiveNI.Sec.proj_split
#print axioms InteractiveNI.Sec.replayStrat_total
#print axioms InteractiveNI.Sec.consistent_replayStrat
#print axioms InteractiveNI.Sec.redRun_of_reach
#print axioms InteractiveNI.Sec.layerCons_base
#print axioms InteractiveNI.Sec.layerCons_peel
#print axioms InteractiveNI.Sec.mem_weave
#print axioms InteractiveNI.Sec.consistent_weave_on
#print axioms InteractiveNI.Sec.layerFinal_holds
#print axioms InteractiveNI.Sec.respectful_of_omniscient
#print axioms InteractiveNI.Sec.hasPolicy'_of_hasPolicy
#print axioms InteractiveNI.Sec.compositional_of_policy'
#print axioms InteractiveNI.Sec.coalition_compositional_of_policy
#print axioms InteractiveNI.Sec.hasPolicy'_of_inputFree
#print axioms InteractiveNI.Sec.coalition_compositional_inputFree
#print axioms InteractiveNI.Sec.forced2_canWin2
#print axioms InteractiveNI.Sec.forced2_of_INI
#print axioms InteractiveNI.Sec.canWin2_of_INI
#print axioms InteractiveNI.Sec.play2_spec
#print axioms InteractiveNI.Sec.play2_adv
#print axioms InteractiveNI.Sec.joint2_spec
#print axioms InteractiveNI.Sec.layerStep_of_game
#print axioms InteractiveNI.Sec.coalition_compositional_layered
#print axioms InteractiveNI.Sec.compositional_of_list
#print axioms InteractiveNI.Sec.coalition_compositional_total
#print axioms InteractiveNI.Sec.coalition_compositional_strat
#print axioms InteractiveNI.Sec.totalize_total
#print axioms InteractiveNI.Sec.consistent_of_totalize
#print axioms InteractiveNI.NoPolicy.not_spread
#print axioms InteractiveNI.NoPolicy.Q_par_Q_compositional_at_Md
#print axioms InteractiveNI.NoPolicy.peelable_Sc3
#print axioms InteractiveNI.NoPolicy.Q_par_Q_total
#print axioms InteractiveNI.NoPolicy.Q_par_Q_strat
#print axioms InteractiveNI.Sec.compositional_layered
#print axioms InteractiveNI.Sec.compositional_of_mutualAdapt
#print axioms InteractiveNI.Sec.compositional_of_policy
#print axioms InteractiveNI.Sec.canWin_sound
#print axioms InteractiveNI.Sec.forced_step
#print axioms InteractiveNI.Sec.forced_canWin
#print axioms InteractiveNI.Sec.forced_of_INI
#print axioms InteractiveNI.Sec.canWin_of_INI

-- The presence-free redesign of the layer game (§5, generalisation)
#print axioms InteractiveNI.Sec.nonempty_winStrat_of_forced
#print axioms InteractiveNI.Sec.out_append
#print axioms InteractiveNI.Sec.punish_spec
#print axioms InteractiveNI.Sec.forcedW_of_INI
#print axioms InteractiveNI.Sec.winStrat_of_INI
#print axioms InteractiveNI.Interleave.lift
#print axioms InteractiveNI.Tag.lift_tagged
#print axioms InteractiveNI.Sec.jointPlay
#print axioms InteractiveNI.Sec.layerStep_of_gameW
#print axioms InteractiveNI.Sec.layerCons_baseW
#print axioms InteractiveNI.Sec.coalition_compositional_layeredW
#print axioms InteractiveNI.Sec.coalition_compositional_totalW
#print axioms InteractiveNI.SecretPresence.not_pub
#print axioms InteractiveNI.SecretPresence.peelableM_Sc2
#print axioms InteractiveNI.SecretPresence.E_par_E_total
#print axioms InteractiveNI.Sec.peelable_of_finite
#print axioms InteractiveNI.Sec.coalition_compositional_total_fin
#print axioms InteractiveNI.Sec.coalition_compositional_strat_fin
#print axioms InteractiveNI.NoPeelMono.not_peelableM
#print axioms InteractiveNI.NoPeelMono.peelable
#print axioms InteractiveNI.Sec.peelableM_of_cmp
#print axioms InteractiveNI.Sec.not_peelableM_of_incmp
#print axioms InteractiveNI.Sec.peelableM_iff_cmp
#print axioms InteractiveNI.Sec.coalition_compositional_of_cmp
#print axioms InteractiveNI.Sec.cmp_of_pub
#print axioms InteractiveNI.Sec.cmp_of_total
#print axioms InteractiveNI.CexPresence.prog_neutral
#print axioms InteractiveNI.CexPresence.progs_NI
#print axioms InteractiveNI.CexPresence.par_not_NI
#print axioms InteractiveNI.CexPresence.no_general_composition
#print axioms InteractiveNI.CexPresence.progs_INI
#print axioms InteractiveNI.CexPresence.par_not_INI
#print axioms InteractiveNI.CexPresence.INI_not_compositional
#print axioms InteractiveNI.CexPresence.not_pub
#print axioms InteractiveNI.Sec.coalition_compositional_total_used
#print axioms InteractiveNI.Sec.coalition_compositional_strat_used
#print axioms InteractiveNI.Sec.peelableOn_of_list
#print axioms InteractiveNI.Sec.compositional_of_levelsW
#print axioms InteractiveNI.Sec.usesLevels_of_chans
#print axioms InteractiveNI.Sec.compTNI_par
#print axioms InteractiveNI.Sec.stratTNI_of_compTNI
#print axioms InteractiveNI.Sec.compTNI_of_stratTNI
#print axioms InteractiveNI.CexPresence.not_compTNI
#print axioms InteractiveNI.P1.P1_compTNI
#print axioms InteractiveNI.Sec.coalition_of_INI
#print axioms InteractiveNI.Sec.INI_compositional_of_total
#print axioms InteractiveNI.Sec.peelableM_of_total
#print axioms InteractiveNI.Sec.coalition_compositional_of_total
#print axioms InteractiveNI.Sec.INI_compositional_of_total'
#print axioms InteractiveNI.CexPresence.not_peelableM
#print axioms InteractiveNI.CexSelf.rprog_NI
#print axioms InteractiveNI.CexSelf.self_composition_fails
