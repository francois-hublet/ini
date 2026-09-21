/-
  No mask-and-cancel attack defeats coalition noninterference.

  Every counterexample to compositionality known to us -- ours of §3, and the one
  of [2] it repairs -- has the same shape: each component masks its contribution
  to the observed output with fresh non-deterministic bits, discloses them on
  channels the other component reads from, and the masks cancel in the sum.  This
  file shows that no such attack can defeat coalition noninterference, over *any*
  lattice, with *any* number of masks, and with arbitrary timing.

  The statement is purely order-theoretic.  `Vis L` is the set of levels some
  member of the coalition `L` is cleared for; an attack consists of

  * masks `MA`, `MB` (levels at which each component discloses a mask) and reads
    `PA`, `QB` (levels of the channels each component reads from), each event
    carrying a time;
  * `SA ⊆ MA`, `SB ⊆ MB`: the masks that no user the component reads from can
    cancel -- either the level does not flow to that user, or the read happens
    before the disclosure (`hUA`, `hUB`);
  * the masks must be hidden from the observer (`h1A`, `h1B`);
  * each component must learn the other's masks (`hrelA`, `hrelB`);
  * and coalition security: at the coalition `L ∪ SA` every uncancellable mask is
    visible, so the component has no freedom left and its reads must be visible
    too (`h4A`, `h4B`).

  These are contradictory.  The proof is a descent: from the uncancellable mask of
  `A` with least time one builds another with a strictly smaller time.
-/
import InteractiveNI.Coalition

namespace InteractiveNI

namespace NoMaskAttack

open Classical
attribute [local instance] Classical.propDecidable

variable {Lvl E : Type}

/-- The levels some member of the coalition `L` is cleared for. -/
def Vis (le : Lvl → Lvl → Prop) (L : List Lvl) (x : Lvl) : Prop := ∃ c ∈ L, le x c

/-- A non-empty list has an element of least weight. -/
theorem exists_min (f : E → Nat) :
    ∀ l : List E, l ≠ [] → ∃ a ∈ l, ∀ b ∈ l, f a ≤ f b := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons x l ih =>
      intro _
      by_cases hl : l = []
      · subst hl
        refine ⟨x, List.mem_cons_self .., ?_⟩
        intro b hb
        cases hb with
        | head => exact Nat.le_refl _
        | tail _ h => nomatch h
      · obtain ⟨a, ha, hmin⟩ := ih hl
        by_cases hx : f x ≤ f a
        · refine ⟨x, List.mem_cons_self .., ?_⟩
          intro b hb
          cases hb with
          | head => exact Nat.le_refl _
          | tail _ h => exact Nat.le_trans hx (hmin b h)
        · refine ⟨a, List.mem_cons_of_mem _ ha, ?_⟩
          intro b hb
          cases hb with
          | head => exact Nat.le_of_lt (Nat.lt_of_not_le hx)
          | tail _ h => exact hmin b h

/-- **No mask-and-cancel attack on coalition noninterference.** -/
theorem no_attack
    (le : Lvl → Lvl → Prop) (trans : ∀ {x y z}, le x y → le y z → le x z)
    (lvl : E → Lvl) (t : E → Nat)
    (L : List Lvl) (MA MB PA QB SA SB : List E)
    (h1A : ∀ a ∈ MA, ¬ Vis le L (lvl a))
    (h1B : ∀ b ∈ MB, ¬ Vis le L (lvl b))
    (hSA : ∀ a ∈ SA, a ∈ MA) (hSB : ∀ b ∈ SB, b ∈ MB)
    (hSAne : SA ≠ [])
    (hrelA : ∀ a ∈ MA, ∃ q ∈ QB, le (lvl a) (lvl q) ∧ t a < t q)
    (hrelB : ∀ b ∈ MB, ∃ p ∈ PA, le (lvl b) (lvl p) ∧ t b < t p)
    (h4A : ∀ p ∈ PA, Vis le (L ++ SA.map lvl) (lvl p))
    (h4B : ∀ q ∈ QB, Vis le (L ++ SB.map lvl) (lvl q))
    (hUA : ∀ a ∈ SA, ∀ p ∈ PA, le (lvl a) (lvl p) → t p < t a)
    (hUB : ∀ b ∈ SB, ∀ q ∈ QB, le (lvl b) (lvl q) → t q < t b) :
    False := by
  obtain ⟨a₀, ha₀, hmin⟩ := exists_min t SA hSAne
  -- (1) `B` learns `a₀`, on some read `q₁`
  obtain ⟨q₁, hq₁, hlq₁, htq₁⟩ := hrelA a₀ (hSA a₀ ha₀)
  -- (2) that read is visible at `L ∪ SB`; it cannot be visible to `L`, or `a₀` would be
  obtain ⟨c, hc, hlec⟩ := h4B q₁ hq₁
  rcases List.mem_append.mp hc with hcL | hcS
  · exact h1A a₀ (hSA a₀ ha₀) ⟨c, hcL, trans hlq₁ hlec⟩
  obtain ⟨b₁, hb₁, hb₁eq⟩ := List.mem_map.mp hcS
  rw [← hb₁eq] at hlec
  -- (3) `A` learns `b₁`, on some read `p₁`
  obtain ⟨p₁, hp₁, hlp₁, htp₁⟩ := hrelB b₁ (hSB b₁ hb₁)
  -- (4) that read is visible at `L ∪ SA`; not to `L`, or `b₁` would be
  obtain ⟨c', hc', hlec'⟩ := h4A p₁ hp₁
  rcases List.mem_append.mp hc' with hc'L | hc'S
  · exact h1B b₁ (hSB b₁ hb₁) ⟨c', hc'L, trans hlp₁ hlec'⟩
  obtain ⟨a₁, ha₁, ha₁eq⟩ := List.mem_map.mp hc'S
  rw [← ha₁eq] at hlec'
  -- (5) `a₀ ⊑ p₁`, so `A`'s protection of `a₀` puts `p₁` before it
  have hstep5 : t p₁ < t a₀ :=
    hUA a₀ ha₀ p₁ hp₁ (trans (trans hlq₁ hlec) hlp₁)
  -- (6) `B` learns `a₁`, on some read `q₂`
  obtain ⟨q₂, hq₂, hlq₂, htq₂⟩ := hrelA a₁ (hSA a₁ ha₁)
  -- (7) `b₁ ⊑ q₂`, so `B`'s protection of `b₁` puts `q₂` before it
  have hstep7 : t q₂ < t b₁ :=
    hUB b₁ hb₁ q₂ hq₂ (trans (trans hlp₁ hlec') hlq₂)
  -- (8) `t a₁ < t q₂ < t b₁ < t p₁ < t a₀`, contradicting minimality of `a₀`
  exact absurd (hmin a₁ ha₁)
    (Nat.not_le_of_gt (Nat.lt_trans htq₂ (Nat.lt_trans hstep7 (Nat.lt_trans htp₁ hstep5))))

end NoMaskAttack

end InteractiveNI
