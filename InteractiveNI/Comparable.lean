/-
  **The peeling condition, in closed form.**

  A peeling at `m` exists for every `m` exactly when the labelling satisfies one
  condition that mentions no peeling at all:

      the presence level of every channel in use is comparable
      with the value level of every channel in use.

  Sufficiency is `peelableM_of_cmp`: peel the used levels above `m` in
  increasing order.  Necessity is `not_peelableM_of_incmp`: if the presence level
  `b` of one channel and the value level `c` of another are incomparable, then no
  peeling at `c` is presence-monotone, since `b` is visible from the start while
  flatness pins to `c` the layer that first exposes it.

  Public presence and total orders are the two special cases (`cmp_of_pub`,
  `cmp_of_total`).
-/
import InteractiveNI.Chains

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

namespace Sec

variable {Level Channel Value : Type}

/-- **The comparability condition.**  Every presence level of a channel in use is
    comparable with every level in use. -/
def Cmp (S : Sec Level Channel) (ls : List Level) : Prop :=
  ∀ a : Channel, S.valL a ∈ ls → ∀ x ∈ ls, S.le (S.presL a) x ∨ S.le x (S.presL a)

/-! ### Sufficiency -/

/-- Peeling used levels above `m` in increasing order is presence-monotone. -/
theorem peelMono_of_cmp {S : Sec Level Channel} {m : Level} {ls : List Level}
    (hcmp : Cmp S ls) :
    ∀ ns : List Level, (∀ n ∈ ns, S.le m n) → (∀ n ∈ ns, n ∈ ls) → Above S ns →
      PeelMono S m ls ns := by
  intro ns
  induction ns with
  | nil => intro _ _ _; trivial
  | cons n ns ih =>
      intro hmn hls hA
      refine ⟨?_, ih (fun n' hn' => hmn n' (List.mem_cons.mpr (Or.inr hn')))
        (fun n' hn' => hls n' (List.mem_cons.mpr (Or.inr hn'))) hA.2⟩
      intro a ha hpres
      obtain ⟨c, hc, hbc⟩ := hpres (S.presL a) rfl
      rcases hcmp a ha n (hls n (by simp)) with h | h
      · exact h
      · rcases layerC_inv ns c hc with hc' | hc'
        · -- `c` is invisible to `m`, yet `m ⊑ n ⊑ presL a ⊑ c`
          exact absurd (S.le_trans (hmn n (by simp)) (S.le_trans h hbc)) hc'
        · -- `c` was peeled earlier, so it is not strictly above `n`
          have hnc : S.le n c := S.le_trans h hbc
          have hcn : S.le c n :=
            Classical.byContradiction fun hcon => hA.1 c hc' ⟨hnc, hcon⟩
          exact S.le_trans hbc hcn

/-- **Comparability yields a peeling at every level.** -/
theorem peelableM_of_cmp {S : Sec Level Channel} (ls : List Level) (hcmp : Cmp S ls)
    (m : Level) : PeelableM S m ls := by
  classical
  obtain ⟨ns, hcov, hsub, hE, hA⟩ :=
    exists_ext_above (S := S) (ls.filter (fun n => decide (S.le m n))).length
      (ls.filter (fun n => decide (S.le m n))) (Nat.le_refl _)
  have hmn : ∀ n ∈ ns, S.le m n := by
    intro n hn
    have := List.mem_filter.mp (hsub n hn)
    simpa using this.2
  have hnls : ∀ n ∈ ns, n ∈ ls := fun n hn => (List.mem_filter.mp (hsub n hn)).1
  refine ⟨ns, ?_, peelFlatOn_of_ext_filter ?_ ns hE, peelMono_of_cmp hcmp ns hmn hnls hA⟩
  · intro a ha
    by_cases hm : S.le m (S.valL a)
    · exact vis_of_mem (mem_layerC ns _
        (hcov _ (List.mem_filter.mpr ⟨ha, by simpa using hm⟩)))
    · exact S.coalition.le_trans ((vis_Cplus m a).mpr hm) (layerC_le S m ns)
  · intro a ha hm
    exact List.mem_filter.mpr ⟨ha, by simpa using hm⟩

/-- **Coalition noninterference composes under comparability.** -/
theorem coalition_compositional_of_cmp {S : Sec Level Channel} {ls : List Level}
    (hcmp : Cmp S ls) (dflt : Value) {StA StB : Type}
    {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    (hcsA : UsesLevels S stepA sA ls) (hcsB : UsesLevels S stepB sB ls)
    (hNIA : S.coalition.StratTNI stepA sA) (hNIB : S.coalition.StratTNI stepB sB) :
    S.coalition.StratTNI (parStep stepA stepB) (sA, sB) :=
  coalition_compositional_totalW dflt hcsA hcsB
    (fun m => peelableM_of_cmp ls hcmp m) hNIA hNIB

/-! ### The two special cases -/

theorem cmp_of_pub {S : Sec Level Channel} (hpubS : PublicPresence S) (ls : List Level) :
    Cmp S ls := fun a _ x _ => Or.inl (hpubS a x)

theorem cmp_of_total {S : Sec Level Channel} (htot : S.IsTotal) (ls : List Level) :
    Cmp S ls := fun a _ x _ => htot (S.presL a) x

/-! ### Necessity -/

/-- With `b` invisible to nobody at the start and `c` exposed by a flat layer,
    presence-monotonicity would force `b ⊑ c`. -/
theorem no_peel_of_incmp {S : Sec Level Channel} {ls : List Level} {a b : Channel}
    (ha : S.valL a ∈ ls) (hb : S.valL b ∈ ls)
    (h₁ : ¬ S.le (S.presL a) (S.valL b)) (h₂ : ¬ S.le (S.valL b) (S.presL a)) :
    ∀ ns : List Level, PeelFlatOn S (S.valL b) ls ns → PeelMono S (S.valL b) ls ns →
      ¬ S.coalition.le (sing (S.valL b)) (layerC S (S.valL b) ns) := by
  intro ns
  induction ns with
  | nil =>
      intro _ _ hvis
      obtain ⟨d, hd, hle⟩ := hvis (S.valL b) rfl
      exact hd hle
  | cons n ns ih =>
      intro hflat hmono hvis
      by_cases hprev : S.coalition.le (sing (S.valL b)) (layerC S (S.valL b) ns)
      · exact ih hflat.2 hmono.2 hprev
      · -- `b` is newly visible here, so flatness pins the layer below its level
        have hn : S.le n (S.valL b) := hflat.1 b hb ⟨hvis, hprev⟩
        -- the presence of `a` is visible from the start
        have hpres : S.coalition.le (sing (S.presL a)) (layerC S (S.valL b) ns) :=
          fun c hc => ⟨S.presL a, layerC_of_cplus ns (S.presL a) h₂,
            by rw [show c = S.presL a from hc]; exact S.le_refl _⟩
        exact h₁ (S.le_trans (hmono.1 a ha hpres) hn)

/-- **Comparability is necessary.**  Two channels whose presence and value levels
    are incomparable leave no peeling at all. -/
theorem not_peelableM_of_incmp {S : Sec Level Channel} {ls : List Level} {a b : Channel}
    (ha : S.valL a ∈ ls) (hb : S.valL b ∈ ls)
    (h₁ : ¬ S.le (S.presL a) (S.valL b)) (h₂ : ¬ S.le (S.valL b) (S.presL a)) :
    ¬ PeelableM S (S.valL b) ls := by
  rintro ⟨ns, hfull, hflat, hmono⟩
  exact no_peel_of_incmp ha hb h₁ h₂ ns hflat hmono (hfull b hb)

/-- **The condition of the composition theorem, in closed form.**  Where the
    levels in play are exactly those the channels carry, a peeling exists at
    every level precisely when the labelling is comparable. -/
theorem peelableM_iff_cmp {S : Sec Level Channel} (ls : List Level)
    (hls : ∀ x ∈ ls, ∃ b : Channel, S.valL b = x) :
    (∀ m : Level, PeelableM S m ls) ↔ Cmp S ls := by
  constructor
  · intro hpeel a ha x hx
    refine Classical.byContradiction fun hcon => ?_
    obtain ⟨b, rfl⟩ := hls x hx
    exact not_peelableM_of_incmp ha hx
      (fun h => hcon (Or.inl h)) (fun h => hcon (Or.inr h)) (hpeel (S.valL b))
  · intro hcmp m; exact peelableM_of_cmp ls hcmp m

end Sec

end InteractiveNI
