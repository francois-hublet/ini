/-
  **A peeling always exists.**

  `Peelable` -- a finite list of levels that exhausts the channels and whose every
  layer is flat -- was carried as a hypothesis.  It is not one: with finitely many
  channels it is a *theorem*.  Order the levels the channels carry by a linear
  extension of `⊑` and peel them upwards; a channel becomes visible exactly when
  its own level is added, which is flatness.

  The presence-monotone clause of `PeelableM` is a different matter: it is not
  always satisfiable, and `NoPeelMono.lean` exhibits a context where it fails.
-/
import InteractiveNI.LayerGame

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

namespace Sec

variable {Level Channel Value : Type}

/-! ### Strict order -/

/-- `x ⊏ y`: below and not above. -/
def lt (S : Sec Level Channel) (x y : Level) : Prop := S.le x y ∧ ¬ S.le y x

theorem lt_irrefl {S : Sec Level Channel} (x : Level) : ¬ S.lt x x :=
  fun h => h.2 (S.le_refl x)

theorem lt_trans {S : Sec Level Channel} {x y z : Level}
    (h₁ : S.lt x y) (h₂ : S.lt y z) : S.lt x z :=
  ⟨S.le_trans h₁.1 h₂.1, fun h => h₁.2 (S.le_trans h₂.1 h)⟩

theorem lt_ne {S : Sec Level Channel} {x y : Level} (h : S.lt x y) : x ≠ y := by
  intro he; exact h.2 (by rw [he]; exact S.le_refl y)

/-- A finite nonempty list has a maximal element. -/
theorem exists_maximal {S : Sec Level Channel} :
    ∀ (L : List Level), L ≠ [] → ∃ M, M ∈ L ∧ ∀ x ∈ L, ¬ S.lt M x := by
  intro L
  induction L with
  | nil => intro h; exact absurd rfl h
  | cons a L ih =>
      intro _
      cases L with
      | nil =>
          refine ⟨a, by simp, ?_⟩
          intro x hx
          rw [show x = a by simpa using hx]
          exact lt_irrefl a
      | cons b L =>
          obtain ⟨M, hM, hmax⟩ := ih (by simp)
          by_cases hlt : S.lt M a
          · refine ⟨a, by simp, ?_⟩
            intro x hx hax
            rcases List.mem_cons.mp hx with rfl | hx
            · exact lt_irrefl x hax
            · exact hmax x hx (lt_trans hlt hax)
          · exact ⟨M, List.mem_cons.mpr (Or.inr hM), by
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact hlt
              · exact hmax x hx⟩

/-! ### Linear extensions -/

/-- `Ext L ns`: along `ns`, read from the head, every level of `L` strictly below
    the one being added has been added already.  The head of `ns` is the level
    added *last*, as in `layerC`. -/
def Ext (S : Sec Level Channel) (L : List Level) : List Level → Prop
  | [] => True
  | n :: ns => (∀ x ∈ L, S.lt x n → x ∈ ns) ∧ Ext S L ns

theorem ext_weaken {S : Sec Level Channel} {L L' : List Level} :
    ∀ ns : List Level, (∀ x ∈ L, x ∈ L' ∨ (∀ n ∈ ns, ¬ S.lt x n)) →
      Ext S L' ns → Ext S L ns := by
  intro ns
  induction ns with
  | nil => intro _ _; trivial
  | cons n ns ih =>
      intro h hE
      refine ⟨?_, ih (fun x hx => (h x hx).imp id
        (fun hh n' hn' => hh n' (List.mem_cons.mpr (Or.inr hn')))) hE.2⟩
      intro x hx hlt
      rcases h x hx with hx' | hx'
      · exact hE.1 x hx' hlt
      · exact absurd hlt (hx' n (by simp))

theorem length_filter_ne {α : Type} [DecidableEq α] :
    ∀ (L : List α) (x : α), x ∈ L →
      (L.filter (fun y => decide (y ≠ x))).length < L.length := by
  intro L
  induction L with
  | nil => intro x hx; exact absurd hx (by simp)
  | cons a L ih =>
      intro x hx
      by_cases hax : a = x
      · subst hax
        have : (List.filter (fun y => decide (y ≠ a)) (a :: L)).length
            = (List.filter (fun y => decide (y ≠ a)) L).length := by
          simp [List.filter_cons]
        rw [this, List.length_cons]
        have : (List.filter (fun y => decide (y ≠ a)) L).length ≤ L.length :=
          List.length_filter_le _ _
        omega
      · have hmem : x ∈ L := by
          rcases List.mem_cons.mp hx with rfl | h
          · exact absurd rfl hax
          · exact h
        have : (List.filter (fun y => decide (y ≠ x)) (a :: L)).length
            = (List.filter (fun y => decide (y ≠ x)) L).length + 1 := by
          simp [List.filter_cons, hax]
        rw [this, List.length_cons]
        have := ih x hmem
        omega

/-- **Every finite list of levels has a linear extension**, greatest first. -/
theorem exists_ext {S : Sec Level Channel} :
    ∀ (k : Nat) (L : List Level), L.length ≤ k →
      ∃ ns : List Level, (∀ x ∈ L, x ∈ ns) ∧ (∀ x ∈ ns, x ∈ L) ∧ Ext S L ns := by
  intro k
  induction k with
  | zero =>
      intro L hL
      have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      exact ⟨[], by simp, by simp, trivial⟩
  | succ k ih =>
      intro L hL
      by_cases hne : L = []
      · subst hne; exact ⟨[], by simp, by simp, trivial⟩
      obtain ⟨M, hM, hmax⟩ := exists_maximal (S := S) L hne
      have hlen := length_filter_ne L M hM
      obtain ⟨ns, hcov, hsub, hE⟩ :=
        ih (L.filter (fun y => decide (y ≠ M))) (by omega)
      refine ⟨M :: ns, ?_, ?_, ?_, ?_⟩
      · intro x hx
        by_cases hxM : x = M
        · exact List.mem_cons.mpr (Or.inl hxM)
        · exact List.mem_cons.mpr (Or.inr (hcov x (List.mem_filter.mpr ⟨hx, by simp [hxM]⟩)))
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hM
        · exact (List.mem_filter.mp (hsub x hx)).1
      · intro x hx hlt
        have hxM : x ≠ M := lt_ne hlt
        exact hcov x (List.mem_filter.mpr ⟨hx, by simp [hxM]⟩)
      · refine ext_weaken (L' := L.filter (fun y => decide (y ≠ M))) ns ?_ hE
        intro x hx
        by_cases hxM : x = M
        · refine Or.inr ?_
          intro n hn
          subst hxM
          exact hmax n (List.mem_filter.mp (hsub n hn)).1
        · exact Or.inl (List.mem_filter.mpr ⟨hx, by simp [hxM]⟩)

/-- `Above ns`: no level of `ns` is strictly above one that precedes it.  The
    linear extension built below has this property, since its head is always
    chosen maximal. -/
def Above (S : Sec Level Channel) : List Level → Prop
  | [] => True
  | n :: ns => (∀ x ∈ ns, ¬ S.lt n x) ∧ Above S ns

/-- **The same linear extension, with maximality recorded.** -/
theorem exists_ext_above {S : Sec Level Channel} :
    ∀ (k : Nat) (L : List Level), L.length ≤ k →
      ∃ ns : List Level, (∀ x ∈ L, x ∈ ns) ∧ (∀ x ∈ ns, x ∈ L) ∧ Ext S L ns ∧ Above S ns := by
  intro k
  induction k with
  | zero =>
      intro L hL
      have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      exact ⟨[], by simp, by simp, trivial, trivial⟩
  | succ k ih =>
      intro L hL
      by_cases hne : L = []
      · subst hne; exact ⟨[], by simp, by simp, trivial, trivial⟩
      obtain ⟨M, hM, hmax⟩ := exists_maximal (S := S) L hne
      have hlen := length_filter_ne L M hM
      obtain ⟨ns, hcov, hsub, hE, hA⟩ :=
        ih (L.filter (fun y => decide (y ≠ M))) (by omega)
      refine ⟨M :: ns, ?_, ?_, ⟨?_, ?_⟩, ?_, hA⟩
      · intro x hx
        by_cases hxM : x = M
        · exact List.mem_cons.mpr (Or.inl hxM)
        · exact List.mem_cons.mpr (Or.inr (hcov x (List.mem_filter.mpr ⟨hx, by simp [hxM]⟩)))
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hM
        · exact (List.mem_filter.mp (hsub x hx)).1
      · intro x hx hlt
        have hxM : x ≠ M := lt_ne hlt
        exact hcov x (List.mem_filter.mpr ⟨hx, by simp [hxM]⟩)
      · refine ext_weaken (L' := L.filter (fun y => decide (y ≠ M))) ns ?_ hE
        intro x hx
        by_cases hxM : x = M
        · refine Or.inr ?_
          intro n hn
          subst hxM
          exact hmax n (List.mem_filter.mp (hsub n hn)).1
        · exact Or.inl (List.mem_filter.mpr ⟨hx, by simp [hxM]⟩)
      · intro x hx
        exact hmax x (List.mem_filter.mp (hsub x hx)).1

/-! ### From a linear extension to a peeling -/

theorem vis_of_mem {S : Sec Level Channel} {C : Coalition Level} {a : Channel}
    (h : C (S.valL a)) : S.coalition.le (sing (S.valL a)) C :=
  fun c hc => ⟨S.valL a, h, by rw [show c = S.valL a from hc]; exact S.le_refl _⟩

theorem mem_layerC {S : Sec Level Channel} {m : Level} :
    ∀ (ns : List Level) (n : Level), n ∈ ns → layerC S m ns n := by
  intro ns
  induction ns with
  | nil => intro n hn; exact absurd hn (by simp)
  | cons n' ns ih =>
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact Or.inr rfl
      · exact Or.inl (ih n hn)

/-- A linear extension of the levels the channels carry *is* a flat peeling. -/
theorem peelFlat_of_ext {S : Sec Level Channel} {m : Level} {L : List Level}
    (hL : ∀ a : Channel, S.valL a ∈ L) :
    ∀ ns : List Level, Ext S L ns → PeelFlat S m ns := by
  intro ns
  induction ns with
  | nil => intro _; trivial
  | cons n ns ih =>
      intro hE
      refine ⟨?_, ih hE.2⟩
      intro a ha
      refine Classical.byContradiction fun hcon => ?_
      obtain ⟨d, hd, hle⟩ := ha.1 (S.valL a) rfl
      rcases hd with hd | rfl
      · exact ha.2 (fun c hc => ⟨d, hd, by rw [show c = S.valL a from hc]; exact hle⟩)
      · exact ha.2 (vis_of_mem (mem_layerC ns _ (hE.1 (S.valL a) (hL a) ⟨hle, hcon⟩)))

/-- **A peeling always exists.**  With finitely many channels, `Peelable` is not a
    hypothesis but a theorem: order the levels the channels carry by a linear
    extension of `⊑` and peel them upwards. -/
theorem peelable_of_finite {S : Sec Level Channel}
    (cs : List Channel) (hcs : ∀ a : Channel, a ∈ cs) (m : Level) : Peelable S m := by
  classical
  obtain ⟨ns, hcov, -, hE⟩ :=
    exists_ext (S := S) (cs.map (fun a => S.valL a)).length (cs.map (fun a => S.valL a))
      (Nat.le_refl _)
  have hL : ∀ a : Channel, S.valL a ∈ cs.map (fun a => S.valL a) :=
    fun a => List.mem_map.mpr ⟨a, hcs a, rfl⟩
  exact ⟨ns, fun a => vis_of_mem (mem_layerC ns _ (hcov _ (hL a))), peelFlat_of_ext hL ns hE⟩

/-! ### The peeling hypothesis discharged

    Both compositionality theorems were stated with the peeling as an assumption.
    With finitely many channels it is now a theorem, so the assumption goes. -/

/-- **Coalition `Strat_T`-noninterference composes**: presence public and finitely
    many channels, nothing else. -/
theorem coalition_compositional_total_fin {S : Sec Level Channel}
    (hpubS : PublicPresence S) (dflt : Value)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    (cs : List Channel) (hcs : ∀ a : Channel, a ∈ cs)
    (hNIA : S.coalition.StratTNI stepA sA) (hNIB : S.coalition.StratTNI stepB sB) :
    S.coalition.StratTNI (parStep stepA stepB) (sA, sB) :=
  coalition_compositional_total hpubS dflt cs hcs (peelable_of_finite cs hcs) hNIA hNIB

/-- **Coalition `Strat`-noninterference composes**: the non-total case, same
    hypotheses. -/
theorem coalition_compositional_strat_fin {S : Sec Level Channel}
    (hpubS : PublicPresence S) (dflt : Value)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    (cs : List Channel) (hcs : ∀ a : Channel, a ∈ cs)
    (hNIA : S.coalition.StratNI stepA sA) (hNIB : S.coalition.StratNI stepB sB) :
    S.coalition.StratNI (parStep stepA stepB) (sA, sB) :=
  coalition_compositional_strat hpubS dflt cs hcs (peelable_of_finite cs hcs) hNIA hNIB

/-! ### Descending order, for total orders -/

/-- Every level is below the one added after it. -/
def Desc (S : Sec Level Channel) : List Level → Prop
  | [] => True
  | n :: ns => (∀ x ∈ ns, S.le x n) ∧ Desc S ns

/-- The same construction, over a total order, also comes out descending. -/
theorem exists_ext_desc {S : Sec Level Channel} (htot : ∀ a b : Level, S.le a b ∨ S.le b a) :
    ∀ (k : Nat) (L : List Level), L.length ≤ k →
      ∃ ns : List Level, (∀ x ∈ L, x ∈ ns) ∧ (∀ x ∈ ns, x ∈ L) ∧ Ext S L ns ∧ Desc S ns := by
  intro k
  induction k with
  | zero =>
      intro L hL
      have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      exact ⟨[], by simp, by simp, trivial, trivial⟩
  | succ k ih =>
      intro L hL
      by_cases hne : L = []
      · subst hne; exact ⟨[], by simp, by simp, trivial, trivial⟩
      obtain ⟨M, hM, hmax⟩ := exists_maximal (S := S) L hne
      have hlen := length_filter_ne L M hM
      obtain ⟨ns, hcov, hsub, hE, hD⟩ :=
        ih (L.filter (fun y => decide (y ≠ M))) (by omega)
      refine ⟨M :: ns, ?_, ?_, ⟨?_, ?_⟩, ?_, hD⟩
      · intro x hx
        by_cases hxM : x = M
        · exact List.mem_cons.mpr (Or.inl hxM)
        · exact List.mem_cons.mpr (Or.inr (hcov x (List.mem_filter.mpr ⟨hx, by simp [hxM]⟩)))
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hM
        · exact (List.mem_filter.mp (hsub x hx)).1
      · intro x hx hlt
        have hxM : x ≠ M := lt_ne hlt
        exact hcov x (List.mem_filter.mpr ⟨hx, by simp [hxM]⟩)
      · refine ext_weaken (L' := L.filter (fun y => decide (y ≠ M))) ns ?_ hE
        intro x hx
        by_cases hxM : x = M
        · refine Or.inr ?_
          intro n hn
          subst hxM
          exact hmax n (List.mem_filter.mp (hsub n hn)).1
        · exact Or.inl (List.mem_filter.mpr ⟨hx, by simp [hxM]⟩)
      · -- descending: everything left is below the maximum
        intro x hx
        have hxL : x ∈ L := (List.mem_filter.mp (hsub x hx)).1
        refine Classical.byContradiction fun hxM => ?_
        rcases htot M x with h | h
        · exact hmax x hxL ⟨h, hxM⟩
        · exact hxM h

end Sec

end InteractiveNI
