/-
  Compositionality over a chain, reduced to a single property.

  Everything in the compositionality argument is proved here except one step.
  Freezing either component turns the global strategy into a legal strategy for
  the other and preserves `=_ℓ` (`seq_weaveIns_teq`), so *each* component can be
  re-planned against any ℓ-equivalent version of its partner's trace.  What does
  not follow is that they can be re-planned *simultaneously*: A's new trace
  changes the answers B receives on channels invisible at ℓ, and conversely.

  `MutualAdapt` below is exactly that missing step -- separately solvable implies
  jointly solvable -- and `compositional_of_mutualAdapt` derives compositionality
  from it.  The property is *false* without a chain hypothesis: the counterexample
  of §3 of the paper is precisely a pair of components whose re-planning
  oscillates (`x = u⊕r⊕¬x'`, `x' = v⊕¬x`, solvable iff `u⊕v = r`).  Over a total
  order it is conjectured to hold; see `chain-composition.md` §4-§5 for the
  argument and the exhaustive verification in small cases.
-/
import InteractiveNI.SeqCompose

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

namespace Sec

variable {Level Channel Value : Type} {S : Sec Level Channel}

/-- **The joint re-planning property.**  If each component can be re-planned
    against every ℓ-equivalent version of its partner's trace, then the two can
    be re-planned simultaneously. -/
def MutualAdapt (hpub : PublicPresence S) {St₁ St₂ : Type}
    (step₁ : St₁ → Act Channel Value → St₁ → Prop)
    (step₂ : St₂ → Act Channel Value → St₂ → Prop)
    (sA : St₁) (sB : St₂) (m : Level) : Prop :=
  ∀ (w : S.Strategy Value) (p : List Bool) (a b : List (Lbl Channel Value)),
    (∀ b', S.teq m b b' →
      ∃ a', S.produces step₁ ((weaveIns hpub p b').induced w) sA a' ∧ S.teq m a a') →
    (∀ a', S.teq m a a' →
      ∃ b', S.produces step₂ ((weaveIns hpub (p.map not) a').induced w) sB b' ∧ S.teq m b b') →
    ∃ a' b', S.teq m a a' ∧ S.teq m b b' ∧
      S.produces step₁ ((weaveIns hpub p b').induced w) sA a' ∧
      S.produces step₂ ((weaveIns hpub (p.map not) a').induced w) sB b'

/-- **Compositionality from joint re-planning.**  Given `MutualAdapt`, parallel
    composition preserves `Strat-NI`, with no determinism assumption. -/
theorem compositional_of_mutualAdapt (hpub : PublicPresence S)
    {St₁ St₂ : Type} {step₁ : St₁ → Act Channel Value → St₁ → Prop}
    {step₂ : St₂ → Act Channel Value → St₂ → Prop} {sA : St₁} {sB : St₂}
    (hA : S.INI step₁ (fun _ => True) sA)
    (hB : S.INI step₂ (fun _ => True) sB)
    (hfix : ∀ m, MutualAdapt hpub step₁ step₂ sA sB m) :
    S.INI (parStep step₁ step₂) (fun _ => True) (sA, sB) := by
  intro m w₁ w₂ _ _ hw t ht
  obtain ⟨q, hreach⟩ := ht.1
  obtain ⟨a, b, hRa, hRb, hI⟩ := par_decompose hreach
  obtain ⟨p, hp, hE⟩ := hI.exists_weave
  have hcons : S.consistent w₁ (weave p a b) := hp ▸ ht.2
  -- each component's trace, seen against the strategy induced by freezing the other
  have hAprod : S.produces step₁ ((weaveIns hpub p b).induced w₁) sA a :=
    ⟨⟨q.1, hRa⟩, consistent_weave_left hpub hE hcons⟩
  have hBprod : S.produces step₂ ((weaveIns hpub (p.map not) a).induced w₁) sB b :=
    ⟨⟨q.2, hRb⟩,
      consistent_weave_left hpub (Exact.map_not p a b hE) (by rw [weave_comm]; exact hcons)⟩
  -- each can be re-planned against any m-equivalent version of its partner
  have prem₁ : ∀ b', S.teq m b b' →
      ∃ a', S.produces step₁ ((weaveIns hpub p b').induced w₂) sA a' ∧ S.teq m a a' :=
    fun b' hb' => hA m _ _ trivial trivial (seq_weaveIns_teq hpub p hw hb') a hAprod
  have prem₂ : ∀ a', S.teq m a a' →
      ∃ b', S.produces step₂ ((weaveIns hpub (p.map not) a').induced w₂) sB b' ∧ S.teq m b b' :=
    fun a' ha' => hB m _ _ trivial trivial (seq_weaveIns_teq hpub (p.map not) hw ha') b hBprod
  -- the missing step: do it simultaneously
  obtain ⟨a', b', hta, htb, hAp, hBp⟩ := hfix m w₂ p a b prem₁ prem₂
  -- and reassemble
  have hE' : Exact p a' b' :=
    Exact.congr_length_right p a' b b'
      (Exact.congr_length p a a' b hE (teq_length hpub hta)) (teq_length hpub htb)
  obtain ⟨qA, hRa'⟩ := hAp.1
  obtain ⟨qB, hRb'⟩ := hBp.1
  refine ⟨weave p a' b', ⟨⟨(qA, qB), ?_⟩, ?_⟩, ?_⟩
  · exact par_reach_interleave (Exact.interleave p a' b' hE') hRa' hRb'
  · exact consistent_weave hpub p a' b' w₂ hAp.2 hBp.2
  · rw [hp]; exact teq_weave hpub hta htb

end Sec

end InteractiveNI
