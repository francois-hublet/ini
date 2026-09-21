/-
  **The layer step without public presence.**

  `LayerGame.lean` assumes that every label survives every projection: the game's
  positions pair the coalition's view with the layer's view entry by entry, and
  the interleaving pattern is carried between a trace and its view by counting
  labels.  Both are replaced here.

  What remains is one genuine hypothesis, and it is exactly the point where
  secret presence bites.  The game is played at the level the layer exposes, so
  the schedule of the joint play can only be read off the *layer's* view; for the
  coalition's view to be scheduled by it, a label the coalition can already see
  must also be visible at the layer.  That is `PresMono` below.  It is implied by
  public presence, and it is free when the channels with secret presence are ones
  the coalition cannot detect at all.
-/
import InteractiveNI.JointW
import InteractiveNI.UsedChans

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

namespace Sec

variable {Level Channel Value : Type}

theorem projLbl_isSome {S : Sec Level Channel} {ℓ : Level} {l : Lbl Channel Value}
    (h : S.le (S.presL l.chan) ℓ) : ∃ q, S.projLbl ℓ l = some q := by
  rcases hq : S.projLbl (Value := Value) ℓ l with _ | q
  · exact absurd (projLbl_eq_none_iff.mp hq) (fun hc => hc h)
  · exact ⟨q, rfl⟩

/-- **A tagged merge of an interleaving.** -/
theorem Interleave.tagged {α : Type} {u v w : List α} (h : Interleave u v w) :
    ∃ x : List (Bool × α),
      Tag.plays true x = u ∧ Tag.plays false x = v ∧ Tag.merged x = w := by
  induction h with
  | nil => exact ⟨[], rfl, rfl, rfl⟩
  | @left a u v w _ ih =>
      obtain ⟨x, h1, h2, h3⟩ := ih
      exact ⟨(true, a) :: x, by rw [Tag.plays_cons_self, h1],
        by rw [Tag.plays_cons_other (by simp), h2], congrArg _ h3⟩
  | @right a u v w _ ih =>
      obtain ⟨x, h1, h2, h3⟩ := ih
      exact ⟨(false, a) :: x, by rw [Tag.plays_cons_other (by simp), h1],
        by rw [Tag.plays_cons_self, h2], congrArg _ h3⟩

/-! ### The coalition's key

    The scheduler needs to recognise, inside the layer's view, the labels the
    coalition can see.  Presence-visibility depends on the channel alone, so the
    layer's view carries that information. -/

/-- The channel of a label, where the coalition can see the label at all. -/
noncomputable def keyOf (S : Sec Level Channel) (C : Coalition Level) :
    PLbl Channel Value → Option Channel :=
  fun q => if S.coalition.le (sing (S.presL q.chan)) C then some q.chan else none

theorem pres_sing {S : Sec Level Channel} {a : Channel} {n : Level}
    (h : S.le (S.presL a) n) : S.coalition.le (sing (S.presL a)) (sing n) := by
  intro c hc; exact ⟨n, rfl, by rw [show c = S.presL a from hc]; exact h⟩

/-- The pointwise form of the key lemma: the coalition's key reads the same
    through the layer's view as through the coalition's own. -/
theorem key_bind' {S : Sec Level Channel} {C : Coalition Level} {n : Level}
    (l : Lbl Channel Value)
    (hm : S.coalition.le (sing (S.presL l.chan)) C → S.le (S.presL l.chan) n) :
    ((S.coalition.projLbl (sing n) l).bind (keyOf S C))
      = ((S.coalition.projLbl C l).bind (keyOf S C)) := by
  by_cases hC : S.coalition.le (sing (S.presL l.chan)) C
  · obtain ⟨q, hq⟩ := projLbl_isSome (S := S.coalition) (ℓ := C) (l := l) hC
    obtain ⟨q', hq'⟩ := projLbl_isSome (S := S.coalition) (ℓ := sing n) (l := l)
      (pres_sing (hm hC))
    rw [hq, hq']
    simp only [Option.bind_some, keyOf, projLbl_chan hq, projLbl_chan hq', if_pos hC]
  · have hnone : S.coalition.projLbl (Value := Value) C l = none :=
      projLbl_eq_none_iff.mpr hC
    rw [hnone]
    rcases hq' : S.coalition.projLbl (Value := Value) (sing n) l with _ | q'
    · rfl
    · simp only [Option.bind_some, keyOf, projLbl_chan hq', if_neg hC]; rfl

theorem keyOf_vis {S : Sec Level Channel} {C : Coalition Level}
    {l : Lbl Channel Value} {q : PLbl Channel Value}
    (h : S.coalition.projLbl C l = some q) : keyOf S C q = some q.chan := by
  have hvis : S.coalition.le (sing (S.presL q.chan)) C := by
    rw [projLbl_chan h]
    refine Classical.byContradiction fun hc => ?_
    rw [projLbl_eq_none_iff.mpr hc] at h
    exact absurd h (by simp)
  simp only [keyOf, if_pos hvis]

/-- On the coalition's own view the key keeps every label. -/
theorem key_view {S : Sec Level Channel} {C : Coalition Level}
    (t : List (Lbl Channel Value)) :
    (S.coalition.proj C t).filterMap (keyOf S C)
      = (S.coalition.proj C t).map PLbl.chan := by
  induction t with
  | nil => rfl
  | cons l t ih =>
      rcases hl : S.coalition.projLbl (Value := Value) C l with _ | q
      · rw [proj_cons_none hl]; exact ih
      · rw [proj_cons_some hl, List.filterMap_cons_some (keyOf_vis hl), List.map_cons, ih]

/-- The tagged form of `key_view`. -/
theorem key_push {S : Sec Level Channel} {C : Coalition Level}
    (x : List (Bool × Lbl Channel Value)) :
    Tag.push (keyOf S C) (Tag.push (S.coalition.projLbl C) x)
      = Tag.mapTag PLbl.chan (Tag.push (S.coalition.projLbl C) x) := by
  induction x with
  | nil => rfl
  | cons e x ih =>
      obtain ⟨c, l⟩ := e
      rcases hl : S.coalition.projLbl (Value := Value) C l with _ | q
      · rw [Tag.push_cons_none hl, ih]
      · rw [Tag.push_cons_some hl, Tag.push_cons_some (keyOf_vis hl), ih]
        simp only [Tag.mapTag, List.map_cons]

theorem reproj_inp_full {S : Sec Level Channel} {C : Coalition Level} {a : Channel}
    {v : Value} (hv : S.coalition.le (S.coalition.valL a) C) :
    S.coalition.reproj C (PLbl.inp a (some v)) = some (PLbl.inp a (some v)) := by
  have hp : S.coalition.le (S.coalition.presL a) C :=
    S.coalition.le_trans (S.coalition.pres_le_val a) hv
  simp only [reproj]
  rw [if_pos hp, if_pos hv]

theorem proj_merged {S : Sec Level Channel} (ℓ : Level)
    (x : List (Bool × Lbl Channel Value)) :
    S.proj ℓ (Tag.merged x) = Tag.merged (Tag.push (S.projLbl ℓ) x) :=
  (Tag.merged_push _ _).symm

theorem proj_plays {S : Sec Level Channel} (ℓ : Level) (b : Bool)
    (x : List (Bool × Lbl Channel Value)) :
    S.proj ℓ (Tag.plays b x) = Tag.plays b (Tag.push (S.projLbl ℓ) x) :=
  (Tag.plays_push _ _ _).symm

theorem down_split {S : Sec Level Channel} {C : Coalition Level} {a : Channel} {v : Value}
    (hv : S.coalition.le (S.coalition.valL a) C) (o₁ o₂ : List (PLbl Channel Value)) :
    down S C (o₁ ++ PLbl.inp a (some v) :: o₂)
      = down S C o₁ ++ PLbl.inp a (some v) :: down S C o₂ := by
  simp only [down, List.filterMap_append,
    List.filterMap_cons_some (reproj_inp_full (S := S) (C := C) (v := v) hv)]

theorem filterMap_congr_on {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x l ih =>
      intro h
      rcases hx : f x with _ | y
      · rw [List.filterMap_cons_none hx,
          List.filterMap_cons_none (by rw [← h x (by simp)]; exact hx),
          ih (fun z hz => h z (by simp [hz]))]
      · rw [List.filterMap_cons_some hx,
          List.filterMap_cons_some (by rw [← h x (by simp)]; exact hx),
          ih (fun z hz => h z (by simp [hz]))]

/-- The key lemma, asked only of the channels in use. -/
theorem key_proj_on {S : Sec Level Channel} {C : Coalition Level} {n : Level}
    {ls : List Level}
    (hm : ∀ a : Channel, S.valL a ∈ ls →
      S.coalition.le (sing (S.presL a)) C → S.le (S.presL a) n)
    {t : List (Lbl Channel Value)} (ht : OnLevels S ls t) :
    (S.coalition.proj (sing n) t).filterMap (keyOf S C)
      = (S.coalition.proj C t).filterMap (keyOf S C) := by
  simp only [proj, List.filterMap_filterMap]
  exact filterMap_congr_on (fun x hx => key_bind' x (hm x.chan (ht x hx)))

/-! ### The layer step -/

/-- **The two-sided layer step, with no assumption on presence beyond
    `PresMono`.**  Both components may read from the channels the layer exposes:
    each has a winning strategy by `winStrat_of_INI`, and `jointPlay` plays the
    two together against the environment, scheduled by the coalition's own view. -/
theorem layerStep_of_gameW {S : Sec Level Channel} (dflt : Value)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {w : S.coalition.Strategy Value} (htotw : w.total)
    {m n : Level} {C : Coalition Level} {ls : List Level}
    (hcsA : UsesLevels S stepA sA ls) (hcsB : UsesLevels S stepB sB ls)
    (hmono : ∀ a : Channel, S.valL a ∈ ls →
      S.coalition.le (sing (S.presL a)) C → S.le (S.presL a) n)
    (hCle : S.coalition.le (Cplus S m) C)
    (hNIA : S.coalition.StratTNI stepA sA) (hNIB : S.coalition.StratTNI stepB sB)
    (hflat : ∀ a : Channel, S.valL a ∈ ls → NewlyVisible S C n a → S.le n (S.valL a))
    {τ : List (PLbl Channel Value)}
    (h : LayerCons S stepA stepB sA sB w m C τ) :
    LayerCons S stepA stepB sA sB w m (addLevel C n) τ := by
  classical
  obtain ⟨p, oA, oB, hE, ⟨tA, qA, vA, htA, hrA, hcA, hoA⟩,
    ⟨tB, qB, vB, htB, hrB, hcB, hoB⟩, hcons, hdown⟩ := h
  -- the exposed channels
  have hNn : ∀ a : Channel, (NewlyVisible S C n a ∧ S.valL a ∈ ls) →
      S.coalition.le (sing n) (S.coalition.valL a) := by
    intro a ha c hc
    exact ⟨S.valL a, rfl, by rw [show c = n from hc]; exact hflat a ha.2 ha.1⟩
  have hNn'0 : ∀ a : Channel, (NewlyVisible S C n a ∧ S.valL a ∈ ls) → S.le (S.valL a) n := by
    intro a ha
    obtain ⟨d, hd, hle⟩ := ha.1.1 (S.valL a) rfl
    rcases hd with hd | rfl
    · exact absurd (fun c hc => ⟨d, hd, by rw [show c = S.valL a from hc]; exact hle⟩) ha.1.2
    · exact hle
  have hNn' : ∀ a : Channel, (NewlyVisible S C n a ∧ S.valL a ∈ ls) →
      S.coalition.le (S.coalition.valL a) (sing n) := by
    intro a ha c hc
    exact ⟨n, rfl, by rw [show c = S.valL a from hc]; exact hNn'0 a ha⟩
  have hNC : ∀ a : Channel, (NewlyVisible S C n a ∧ S.valL a ∈ ls) →
      ¬ S.coalition.le (S.coalition.valL a) C := fun a ha => ha.1.2
  -- both components have a winning strategy
  have hwA : Nonempty (WinStrat (fun a => NewlyVisible S C n a ∧ S.valL a ∈ ls)
      (RedPair S.coalition stepA sA C (sing n) oA) (fun _ _ _ => True) []) := by
    refine ⟨?_⟩
    have := winStrat_of_INI (S := S.coalition) (N := fun a => NewlyVisible S C n a ∧ S.valL a ∈ ls) dflt htA
      hNn hNn' hNC hNIA (b := tA) ⟨⟨qA, hrA⟩, hcA⟩
    rw [hoA] at this; exact this
  have hwB : Nonempty (WinStrat (fun a => NewlyVisible S C n a ∧ S.valL a ∈ ls)
      (RedPair S.coalition stepB sB C (sing n) oB) (fun _ _ _ => True) []) := by
    refine ⟨?_⟩
    have := winStrat_of_INI (S := S.coalition) (N := fun a => NewlyVisible S C n a ∧ S.valL a ∈ ls) dflt htB
      hNn hNn' hNC hNIB (b := tB) ⟨⟨qB, hrB⟩, hcB⟩
    rw [hoB] at this; exact this
  -- the key hypotheses of the joint play
  have hkey : ∀ {St : Type} {step : St → Act Channel Value → St → Prop} {s : St},
      UsesLevels S step s ls → ∀ (o : List (PLbl Channel Value)),
      (∀ d, RedPair S.coalition step s C (sing n) o d →
        d.filterMap (keyOf S C) = [] ++ o.filterMap (keyOf S C)) := by
    intro St step s hu o d hd
    obtain ⟨t, s', hreach, hC, hn⟩ := hd
    rw [List.nil_append, ← hn, ← hC, key_proj_on hmono (hu _ _ hreach)]
  obtain ⟨blkT, hRA, hRB, hpush, hadv⟩ :=
    jointPlay (N := fun a => NewlyVisible S C n a ∧ S.valL a ∈ ls)
      (RA := RedPair S.coalition stepA sA C (sing n) oA)
      (RB := RedPair S.coalition stepB sB C (sing n) oB)
      (oracleV S.coalition (sing n) w dflt) (keyOf S C)
      (Tag.mapTag PLbl.chan (Tag.tag p oA oB)) [] [] [] [] []
      hwA hwB
      (by
        intro d hd
        rw [hkey hcsA oA d hd, List.nil_append, Tag.plays_mapTag, (Tag.plays_tag p oA oB hE).1,
          ← hoA, key_view, List.nil_append])
      (by
        intro d hd
        rw [hkey hcsB oB d hd, List.nil_append, Tag.plays_mapTag, (Tag.plays_tag p oA oB hE).2,
          ← hoB, key_view, List.nil_append])
      rfl rfl
  simp only [List.nil_append] at hRA hRB hadv
  obtain ⟨tA', qA', hrA', hcA'', hnA'⟩ := hRA
  obtain ⟨tB', qB', hrB', hcB'', hnB'⟩ := hRB
  -- lift the merge of the views to a merge of the traces
  obtain ⟨tT, hpt, hpf, hpp⟩ :=
    Tag.lift_tagged (S.coalition.projLbl (sing n)) tA' tB' _ hnA'.symm hnB'.symm
  have hUtT : ∀ e ∈ tT, S.valL e.2.chan ∈ ls := by
    intro e he
    have hm := Tag.mem_plays tT he
    cases he1 : e.1 with
    | true => rw [he1, hpt] at hm; exact hcsA _ _ hrA' _ hm
    | false => rw [he1, hpf] at hm; exact hcsB _ _ hrB' _ hm
  have hI : Interleave tA' tB' (Tag.merged tT) := by
    rw [← hpt, ← hpf]; exact Tag.interleave_plays tT
  have hnt : S.coalition.proj (sing n) (Tag.merged tT) = Tag.merged blkT := by
    rw [proj_merged, hpp]
  -- the coalition's view of the merge is the prescribed one
  have hcT : Tag.push (S.coalition.projLbl C) tT = Tag.tag p oA oB := by
    refine Tag.eq_of_sides _ _ ?_ ?_ ?_
    · have h1 : Tag.mapTag PLbl.chan (Tag.push (S.coalition.projLbl C) tT)
          = Tag.mapTag PLbl.chan (Tag.tag p oA oB) := by
        rw [← key_push, Tag.push_push, ← hpush, ← hpp, Tag.push_push]
        exact Tag.push_congr_on tT
          (fun e he => (key_bind' e.2 (hmono e.2.chan (hUtT e he))).symm)
      have h2 := congrArg Tag.sides h1
      rw [Tag.sides_mapTag, Tag.sides_mapTag] at h2
      exact h2
    · rw [← proj_plays, hpt, (Tag.plays_tag p oA oB hE).1]; exact hcA''
    · rw [← proj_plays, hpf, (Tag.plays_tag p oA oB hE).2]; exact hcB''
  have hcv : S.coalition.proj C (Tag.merged tT) = weave p oA oB := by
    rw [proj_merged, hcT, Tag.merged_tag]
  -- assemble
  have hDC : S.coalition.le C (addLevel C n) := le_addLevel C n
  have hDn : S.coalition.le (sing n) (addLevel C n) := fun c hc =>
    ⟨n, Or.inr rfl, by rw [show c = n from hc]; exact S.le_refl n⟩
  have hCplusD : S.coalition.le (Cplus S m) (addLevel C n) := S.coalition.le_trans hCle hDC
  have hwD : weave (Tag.sides (Tag.push (S.coalition.projLbl (addLevel C n)) tT))
      (S.coalition.proj (addLevel C n) tA') (S.coalition.proj (addLevel C n) tB')
      = S.coalition.proj (addLevel C n) (Tag.merged tT) := by
    rw [← hpt, ← hpf, proj_plays, proj_plays, proj_merged, Tag.weave_sides]
  refine ⟨Tag.sides (Tag.push (S.coalition.projLbl (addLevel C n)) tT),
    S.coalition.proj (addLevel C n) tA', S.coalition.proj (addLevel C n) tB', ?_,
    ⟨tA', qA', _, replayStrat_total dflt tA', hrA', consistent_replayStrat dflt tA', rfl⟩,
    ⟨tB', qB', _, replayStrat_total dflt tB', hrB', consistent_replayStrat dflt tB', rfl⟩,
    ?_, ?_⟩
  · rw [← hpt, ← hpf, proj_plays, proj_plays]
    exact Tag.exact_sides _
  · rw [hwD]
    intro o₁ a v o₂ hsplit hvis t'' ht''
    by_cases hvC : S.coalition.le (S.coalition.valL a) C
    · refine hcons (down S C o₁) a v (down S C o₂) ?_ hvC t'' ?_
      · rw [← hcv, ← down_proj hDC, hsplit, down_split hvC]
      · rw [← down_proj hDC t'', ht'']
    · obtain ⟨u₁, l, u₂, hdec, -, hl⟩ := proj_split_gen hsplit
      have hchan : a = l.chan := projLbl_chan hl
      have hacs : S.valL a ∈ ls := by
        rcases Interleave.mem_or hI (show l ∈ Tag.merged tT by rw [hdec]; simp) with hm | hm
        · rw [hchan]; exact hcsA _ _ hrA' l hm
        · rw [hchan]; exact hcsB _ _ hrB' l hm
      have hN : (NewlyVisible S C n a ∧ S.valL a ∈ ls) := ⟨⟨hvis, hvC⟩, hacs⟩
      have hpos : Tag.merged blkT
          = down S (sing n) o₁ ++ PLbl.inp a (some v) :: down S (sing n) o₂ := by
        rw [← hnt, ← down_proj hDn, hsplit, down_split (hNn' a hN)]
      have hkeyv := hadv (down S (sing n) o₁) (PLbl.inp a (some v))
        (down S (sing n) o₂) hpos a (some v) rfl hN
      have hv : v = oracleV S.coalition (sing n) w dflt a (down S (sing n) o₁) := by
        simp only [List.nil_append, PLbl.inp.injEq, Option.some.injEq] at hkeyv
        exact hkeyv.2
      rw [hv]
      have ht2 : S.coalition.proj (sing n) t'' = down S (sing n) o₁ := by
        rw [← down_proj hDn t'', ht'']
      exact oracleV_spec dflt htotw (hNn' a hN) (t₀ := t'') ht2 t'' ht2
  · rw [hwD, down_proj hCplusD, ← down_proj hCle, hcv]
    exact hdown

/-! ### The base of the peeling, without public presence

    The old base case matches the interleaving of the traces with the
    interleaving of their views by counting labels.  Here the tagged merge of the
    traces is simply pushed through the projection. -/

theorem layerCons_baseW {S : Sec Level Channel} {m : Level} (dflt : Value)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {w₁ w₂ : S.coalition.Strategy Value}
    (hseq : S.coalition.seq (Cplus S m) w₁ w₂)
    {t₁ : List (Lbl Channel Value)}
    (h₁ : S.coalition.produces (parStep stepA stepB) w₁ (sA, sB) t₁) :
    LayerCons S stepA stepB sA sB w₂ m (Cplus S m)
      (S.coalition.proj (Cplus S m) t₁) := by
  classical
  obtain ⟨⟨q, hreach⟩, hcons⟩ := h₁
  obtain ⟨tA, tB, hA, hB, hint⟩ := par_decompose hreach
  obtain ⟨x, hxA, hxB, hxm⟩ := Interleave.tagged hint
  have hmA : S.coalition.proj (Cplus S m) tA
      = Tag.plays true (Tag.push (S.coalition.projLbl (Cplus S m)) x) := by
    rw [← hxA, proj_plays]
  have hmB : S.coalition.proj (Cplus S m) tB
      = Tag.plays false (Tag.push (S.coalition.projLbl (Cplus S m)) x) := by
    rw [← hxB, proj_plays]
  have hw : weave (Tag.sides (Tag.push (S.coalition.projLbl (Cplus S m)) x))
      (S.coalition.proj (Cplus S m) tA) (S.coalition.proj (Cplus S m) tB)
      = S.coalition.proj (Cplus S m) t₁ := by
    rw [hmA, hmB, Tag.weave_sides, ← hxm, proj_merged]
  refine ⟨Tag.sides (Tag.push (S.coalition.projLbl (Cplus S m)) x),
    S.coalition.proj (Cplus S m) tA, S.coalition.proj (Cplus S m) tB, ?_,
    ⟨tA, q.1, _, replayStrat_total dflt tA, hA, consistent_replayStrat dflt tA, rfl⟩,
    ⟨tB, q.2, _, replayStrat_total dflt tB, hB, consistent_replayStrat dflt tB, rfl⟩,
    ?_, ?_⟩
  · rw [hmA, hmB]; exact Tag.exact_sides _
  · rw [hw]
    intro o₁ a v o₂ hsplit hvis t ht
    obtain ⟨u, l, r, hdec, hu, hl⟩ := proj_split_gen hsplit
    obtain ⟨v', rfl⟩ := projLbl_inp_inv hl
    have hp : S.coalition.le (S.coalition.presL a) (Cplus S m) :=
      S.coalition.le_trans (S.coalition.pres_le_val a) hvis
    rw [projLbl_inp_full hp hvis] at hl
    injection hl with hl
    injection hl with _ hvv
    injection hvv with hvv
    subst hvv
    have h1 : w₁.ω a u v' := hcons u a v' r hdec
    have h2 : w₂.ω a u v' := by rw [← (hseq a u).1 hvis]; exact h1
    have h3 : w₂.ω a t = w₂.ω a u := adapt_vis w₂ hvis (by unfold Sec.teq; rw [ht, hu])
    rw [h3]; exact h2
  · rw [hw]; exact down_proj (S.coalition.le_refl _) _

/-! ### The peeling -/

/-- **Presence monotonicity along the peeling.**  At each layer, a label the
    coalition can already see is visible at the level the layer exposes.  This is
    *not* "presence is public": it constrains only the pairs the peeling actually
    touches, and it is vacuous for channels the coalition cannot detect. -/
def PeelMono (S : Sec Level Channel) (m : Level) (ls : List Level) :
    List Level → Prop
  | [] => True
  | n :: ns => (∀ a : Channel, S.valL a ∈ ls →
      S.coalition.le (sing (S.presL a)) (layerC S m ns) → S.le (S.presL a) n) ∧
      PeelMono S m ls ns

theorem peelMono_of_pub {S : Sec Level Channel} (hpubS : PublicPresence S) (m : Level)
    (ls : List Level) : ∀ ns : List Level, PeelMono S m ls ns
  | [] => trivial
  | _ :: ns => ⟨fun a _ _ => hpubS a _, peelMono_of_pub hpubS m ls ns⟩

theorem layerCons_peelW {S : Sec Level Channel} (dflt : Value)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {w : S.coalition.Strategy Value} (htotw : w.total) {m : Level} {ls : List Level}
    (hcsA : UsesLevels S stepA sA ls) (hcsB : UsesLevels S stepB sB ls)
    (hNIA : S.coalition.StratTNI stepA sA) (hNIB : S.coalition.StratTNI stepB sB)
    {τ : List (PLbl Channel Value)}
    (h₀ : LayerCons S stepA stepB sA sB w m (Cplus S m) τ) :
    ∀ ns : List Level, PeelFlatOn S m ls ns → PeelMono S m ls ns →
      LayerCons S stepA stepB sA sB w m (layerC S m ns) τ := by
  intro ns
  induction ns with
  | nil => intro _ _; exact h₀
  | cons n ns ih =>
      intro hflat hpm
      exact layerStep_of_gameW dflt htotw hcsA hcsB hpm.1 (layerC_le S m ns) hNIA hNIB
        hflat.1 (ih hflat.2 hpm.2)

/-- **Compositionality of coalition noninterference at `C⁺`, with no assumption
    on the channel labelling and none on presence beyond the peeling.** -/
theorem coalition_compositional_layeredW {S : Sec Level Channel} (dflt : Value)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {m : Level} {w₁ w₂ : S.coalition.Strategy Value} {ls : List Level}
    (hcsA : UsesLevels S stepA sA ls) (hcsB : UsesLevels S stepB sB ls)
    (htot₂ : w₂.total)
    (hNIA : S.coalition.StratTNI stepA sA) (hNIB : S.coalition.StratTNI stepB sB)
    (ns : List Level)
    (hfull : ∀ a : Channel, S.valL a ∈ ls → S.coalition.le (sing (S.valL a)) (layerC S m ns))
    (hflat : PeelFlatOn S m ls ns) (hmono : PeelMono S m ls ns)
    (hseq : S.coalition.seq (Cplus S m) w₁ w₂)
    {t₁ : List (Lbl Channel Value)}
    (h₁ : S.coalition.produces (parStep stepA stepB) w₁ (sA, sB) t₁) :
    ∃ t₂, S.coalition.produces (parStep stepA stepB) w₂ (sA, sB) t₂ ∧
      S.coalition.teq (Cplus S m) t₁ t₂ := by
  obtain ⟨t₂, hprod, hproj⟩ := layerFinal_holds_on hcsA hcsB _ hfull
    (layerCons_peelW dflt htot₂ hcsA hcsB hNIA hNIB (layerCons_baseW dflt hseq h₁)
      ns hflat hmono)
  exact ⟨t₂, hprod, hproj.symm⟩


/-- The peeling data, with presence monotone along it, for the channels in use. -/
def PeelableM (S : Sec Level Channel) (m : Level) (ls : List Level) : Prop :=
  ∃ ns : List Level,
    (∀ a : Channel, S.valL a ∈ ls → S.coalition.le (sing (S.valL a)) (layerC S m ns)) ∧
    PeelFlatOn S m ls ns ∧ PeelMono S m ls ns

/-- With presence public, the peeling that always exists will do. -/
theorem peelableM_of_pub {S : Sec Level Channel} (hpubS : PublicPresence S) (m : Level)
    (ls : List Level) : PeelableM S m ls := by
  obtain ⟨ns, hfull, hflat⟩ := peelableOn_of_list (S := S) ls m
  exact ⟨ns, hfull, hflat, peelMono_of_pub hpubS m ls ns⟩

/-- **The hybrid, over levels.**  Transport a composed run along a list of
    *levels* on which the two strategies may differ.  Each step replaces the
    strategy on every channel above one level `m` at once, which is invisible to
    `C⁺(m)`; peeling channel by channel is unnecessary, and would need the
    channels themselves to be finitely many. -/
theorem compositional_of_levelsW {S : Sec Level Channel} (dflt : Value)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {ls : List Level} (hcsA : UsesLevels S stepA sA ls) (hcsB : UsesLevels S stepB sB ls)
    (hNIA : S.coalition.StratTNI stepA sA) (hNIB : S.coalition.StratTNI stepB sB)
    (hpeel : ∀ m : Level, PeelableM S m ls) {C : Coalition Level} :
    ∀ (ms : List Level) (w₁ w₂ : S.coalition.Strategy Value),
      w₁.total → w₂.total →
      (∀ a : Channel, S.valL a ∈ ls → S.valL a ∉ ms → ∀ t, w₁.ω a t = w₂.ω a t) →
      (∀ m ∈ ms, S.coalition.le C (Cplus S m)) →
      ∀ t₁, S.coalition.produces (parStep stepA stepB) w₁ (sA, sB) t₁ →
        ∃ t₂, S.coalition.produces (parStep stepA stepB) w₂ (sA, sB) t₂ ∧
          S.coalition.teq C t₁ t₂ := by
  intro ms
  induction ms with
  | nil =>
      intro w₁ w₂ _ _ hagree _ t₁ h₁
      obtain ⟨q, hreach⟩ := h₁.1
      exact ⟨t₁, ⟨h₁.1, consistent_congr_on
        (fun a v hmem u => hagree a (usesLevels_par hcsA hcsB _ _ hreach _ hmem)
          (by simp) u) h₁.2⟩, rfl⟩
  | cons m ms ih =>
      intro w₁ w₂ htot₁ htot₂ hagree hinv t₁ h₁
      -- the intermediate strategy: `w₂` above `m`, `w₁` elsewhere
      have htot' : (mixStrat (fun a => S.le m (S.valL a)) w₁ w₂).total := by
        intro a t
        by_cases hp : S.le m (S.valL a)
        · rw [mixStrat_pos (P := fun a => S.le m (S.valL a)) hp]; exact htot₂ a t
        · rw [mixStrat_neg (P := fun a => S.le m (S.valL a)) hp]; exact htot₁ a t
      have hseq : S.coalition.seq (Cplus S m) w₁
          (mixStrat (fun a => S.le m (S.valL a)) w₁ w₂) := by
        intro a t
        refine ⟨fun hvis => ?_, fun _ => ?_⟩
        · have hne : ¬ S.le m (S.valL a) := (vis_Cplus m a).mp hvis
          exact (mixStrat_neg (P := fun a => S.le m (S.valL a)) hne t).symm
        · by_cases hp : S.le m (S.valL a)
          · rw [mixStrat_pos (P := fun a => S.le m (S.valL a)) hp]
            exact dotEq_of_total (htot₁ a t) (htot₂ a t)
          · exact dotEq.of_eq (mixStrat_neg (P := fun a => S.le m (S.valL a)) hp t).symm
      obtain ⟨ns, hfull, hflat, hmono⟩ := hpeel m
      obtain ⟨t', h', hteq'⟩ := coalition_compositional_layeredW dflt hcsA hcsB htot'
        hNIA hNIB ns hfull hflat hmono hseq h₁
      obtain ⟨t₂, h₂, hteq₂⟩ := ih (mixStrat (fun a => S.le m (S.valL a)) w₁ w₂) w₂
        htot' htot₂
        (fun a hals hams u => by
          by_cases hp : S.le m (S.valL a)
          · rw [mixStrat_pos (P := fun a => S.le m (S.valL a)) hp]
          · rw [mixStrat_neg (P := fun a => S.le m (S.valL a)) hp]
            refine hagree a hals (fun hc => ?_) u
            rcases List.mem_cons.mp hc with hc | hc
            · exact hp (by rw [hc]; exact S.le_refl _)
            · exact hams hc)
        (fun m' hm' => hinv m' (List.mem_cons.mpr (Or.inr hm'))) t' h'
      exact ⟨t₂, h₂, (teq_mono (hinv m (by simp)) hteq').trans hteq₂⟩

/-- **Coalition `Strat_T`-noninterference composes, over an arbitrary lattice,
    with no assumption that presence is public and none that `ℂ` is finite.**
    The components have to use finitely many *levels* -- a program uses finitely
    many channels, hence finitely many levels -- and the peeling has to be
    presence-monotone (`PeelMono`, inside `PeelableM`), which public presence
    gives for free. -/
theorem coalition_compositional_totalW {S : Sec Level Channel} (dflt : Value)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {ls : List Level} (hcsA : UsesLevels S stepA sA ls) (hcsB : UsesLevels S stepB sB ls)
    (hpeel : ∀ m : Level, PeelableM S m ls)
    (hNIA : S.coalition.StratTNI stepA sA) (hNIB : S.coalition.StratTNI stepB sB) :
    S.coalition.StratTNI (parStep stepA stepB) (sA, sB) := by
  classical
  intro C w₁ w₂ htot₁ htot₂ hseq t₁ h₁
  by_cases hCne : ∃ c, C c
  case neg =>
    -- the empty coalition observes nothing at all
    refine ⟨[], ⟨⟨(sA, sB), Reach.nil⟩, by intro u a v r heq; simp at heq⟩, ?_⟩
    unfold Sec.teq
    rw [proj_empty_coalition hCne, proj_empty_coalition hCne]
  refine compositional_of_levelsW dflt hcsA hcsB hNIA hNIB hpeel
    (ls.filter (fun m => decide (¬ S.coalition.le (sing m) C))) w₁ w₂ htot₁ htot₂ ?_ ?_ t₁ h₁
  · -- outside those levels the two strategies agree on the channels in use
    intro a hals hams u
    have hvis : S.coalition.le (S.coalition.valL a) C := by
      by_cases hv : S.coalition.le (sing (S.valL a)) C
      · exact hv
      · exact absurd (List.mem_filter.mpr ⟨hals, by simp only [decide_eq_true_eq]; exact hv⟩)
          hams
    exact (hseq a u).1 hvis
  · -- and each of them is invisible to `C`
    intro m hm
    have h2 := (List.mem_filter.mp hm).2
    simp only [decide_eq_true_eq] at h2
    exact le_Cplus (fun hc => h2 (fun c hc' => by
      rw [show c = m from hc']
      obtain ⟨d, hd, hle⟩ := hc
      exact ⟨d, hd, hle⟩))

/-! ### Reading a peeling -/

theorem layerC_inv {S : Sec Level Channel} {m : Level} :
    ∀ (ns : List Level) (q : Level), layerC S m ns q → Cplus S m q ∨ q ∈ ns := by
  intro ns
  induction ns with
  | nil => intro q h; exact Or.inl h
  | cons n ns ih =>
      intro q h
      rcases h with h | rfl
      · exact (ih q h).imp id (fun hm => List.mem_cons.mpr (Or.inr hm))
      · exact Or.inr (by simp)

theorem layerC_of_cplus {S : Sec Level Channel} {m : Level} :
    ∀ (ns : List Level) (q : Level), Cplus S m q → layerC S m ns q := by
  intro ns
  induction ns with
  | nil => intro q h; exact h
  | cons n ns ih => intro q h; exact Or.inl (ih q h)

end Sec

end InteractiveNI
