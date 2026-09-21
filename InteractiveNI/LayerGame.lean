/-
  **The layer game.**

  What is missing for compositionality of coalition noninterference over an
  arbitrary lattice is a *causal policy* for each component at a layer of the
  peeling of `Layered.lean`.  This file builds the game that supplies it.

  Two design points make it tractable, and both come from the layer structure.

  * The game runs over **reduced** traces -- pairs (`C`-view, `n`-view) of a run --
    so the subset construction disappears: a component's choices that neither the
    observer nor the adversary can see are already abstracted away by the
    projections, and `Sec.replayStrat` says such choices may be treated as the
    component's own.  Every channel visible at the layer `C ∪ {n}` is visible at
    `C` or at `n`, so the pair carries the whole layer view.
  * A position is the `n`-view, which is exactly the adversary's information.  The
    channels a layer exposes all carry the level `n` (`Sec.layer_flat`), so a
    `π_n`-measurable answer *is* a legal strategy for them.  This replaces the
    `Omniscient` hypothesis of `Game.lean`, which assumed the users of the
    invisible channels see everything.
-/
import InteractiveNI.Layered

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

/-! ### A list lemma -/

theorem getD_append_cons {α : Type} (u : List α) (x : α) (v : List α) (d : α) :
    (u ++ x :: v).getD u.length d = x := by
  induction u with
  | nil => rfl
  | cons y u ih => simpa using ih

namespace Sec

variable {Level Channel Value : Type} {S : Sec Level Channel}

/-! ### Reduced systems as sets of view pairs -/

/-- The pairs (`C`-view, `n`-view) of the runs of a component. -/
def RedPair (S : Sec Level Channel) {St : Type}
    (step : St → Act Channel Value → St → Prop) (s : St) (C n : Level)
    (dc dn : List (PLbl Channel Value)) : Prop :=
  ∃ (t : List (Lbl Channel Value)) (s' : St),
    Reach step s t s' ∧ S.proj C t = dc ∧ S.proj n t = dn

/-! ### The game

    The script is the `C`-view the component must realise; a position is the pair
    (`C`-view produced so far, `n`-view produced so far).  At an input on an
    adversarial channel the environment chooses the value -- universally, and as a
    function of the `n`-view alone.  Everywhere else the component chooses the
    `n`-observable content of its next label. -/
def CanWin2 {Channel Value : Type} (N : Channel → Prop)
    (R : List (PLbl Channel Value) → List (PLbl Channel Value) → Prop)
    (env : Channel → List (PLbl Channel Value) → Value → Prop) :
    List (PLbl Channel Value) → List (PLbl Channel Value) →
      List (PLbl Channel Value) → Prop
  | [], dc, dn => R dc dn
  | (PLbl.inp a ov) :: rest, dc, dn =>
      if N a then
        ∀ v : Value, env a dn v →
          CanWin2 N R env rest (dc ++ [PLbl.inp a ov]) (dn ++ [PLbl.inp a (some v)])
      else
        ∃ qn : PLbl Channel Value,
          CanWin2 N R env rest (dc ++ [PLbl.inp a ov]) (dn ++ [qn])
  | (PLbl.out a ov) :: rest, dc, dn =>
      ∃ qn : PLbl Channel Value,
        CanWin2 N R env rest (dc ++ [PLbl.out a ov]) (dn ++ [qn])

/-- Against every environment-compatible adversary some reduced run realises the
    target.  This is what noninterference supplies. -/
def Forced2 {Channel Value : Type} (N : Channel → Prop)
    (R : List (PLbl Channel Value) → List (PLbl Channel Value) → Prop)
    (env : Channel → List (PLbl Channel Value) → Value → Prop)
    (tgt dc dn : List (PLbl Channel Value)) : Prop :=
  ∀ adv : Channel → List (PLbl Channel Value) → Value,
    (∀ a q, env a q (adv a q)) →
    ∃ o : List (PLbl Channel Value × PLbl Channel Value),
      o.map Prod.fst = tgt ∧
      R (dc ++ o.map Prod.fst) (dn ++ o.map Prod.snd) ∧
      (∀ pre e post, o = pre ++ e :: post → ∀ (a : Channel) (ov : Option Value),
        e.1 = PLbl.inp a ov → N a →
        e.2 = PLbl.inp a (some (adv a (dn ++ pre.map Prod.snd))))

/-! ### Determinacy -/

/-- **The game is determined.**  A component that can realise its target against
    every adversary can *force* it: this is the `∀∃ → ∃∀` swap, and the reason it
    goes through without `Omniscient` is that a position is the adversary's own
    view, so the punishing adversary built here is `π_n`-measurable. -/
theorem forced2_canWin2 {Channel Value : Type} {N : Channel → Prop}
    {R : List (PLbl Channel Value) → List (PLbl Channel Value) → Prop}
    {env : Channel → List (PLbl Channel Value) → Value → Prop}
    (hne : ∀ a q, ∃ v, env a q v) :
    ∀ (tgt dc dn : List (PLbl Channel Value)),
      Forced2 N R env tgt dc dn → CanWin2 N R env tgt dc dn := by
  have hdefault : ∃ adv : Channel → List (PLbl Channel Value) → Value,
      ∀ a q, env a q (adv a q) :=
    ⟨fun a q => Classical.choose (hne a q), fun a q => Classical.choose_spec (hne a q)⟩
  intro tgt
  induction tgt with
  | nil =>
      intro dc dn hF
      obtain ⟨adv, hadv⟩ := hdefault
      obtain ⟨o, ho, hR, -⟩ := hF adv hadv
      have ho0 : o = [] := by
        cases o with
        | nil => rfl
        | cons e o' => simp at ho
      subst ho0
      simpa [CanWin2] using hR
  | cons l rest ih =>
      intro dc dn hF
      cases l with
      | inp a ov =>
          by_cases hN : N a
          · simp only [CanWin2, if_pos hN]
            intro v hv
            refine ih _ _ ?_
            intro adv' hadv'
            -- the adversary that plays `v` here and then punishes
            have hcompat : ∀ a'' q, env a'' q
                (if a'' = a ∧ q = dn then v else adv' a'' q) := by
              intro a'' q
              by_cases hc : a'' = a ∧ q = dn
              · rw [if_pos hc, hc.1, hc.2]; exact hv
              · rw [if_neg hc]; exact hadv' a'' q
            obtain ⟨o, ho, hR, hadvc⟩ := hF _ hcompat
            cases o with
            | nil => simp at ho
            | cons e o' =>
                simp only [List.map_cons, List.cons.injEq] at ho
                obtain ⟨he1, ho'⟩ := ho
                have he2 : e.2 = PLbl.inp a (some v) := by
                  have := hadvc [] e o' rfl a ov he1 hN
                  simpa [if_pos (And.intro rfl rfl)] using this
                refine ⟨o', ho', ?_, ?_⟩
                · have : dc ++ (e.1 :: o'.map Prod.fst) = (dc ++ [PLbl.inp a ov]) ++ o'.map Prod.fst := by
                    rw [he1]; simp
                  have h2 : dn ++ (e.2 :: o'.map Prod.snd)
                      = (dn ++ [PLbl.inp a (some v)]) ++ o'.map Prod.snd := by
                    rw [he2]; simp
                  simpa [this, h2] using hR
                · intro pre e'' post hsplit a'' ov'' hin hN''
                  have := hadvc (e :: pre) e'' post (by rw [hsplit]; rfl) a'' ov'' hin hN''
                  have hq : ¬ (a'' = a ∧ dn ++ (e :: pre).map Prod.snd = dn) := by
                    rintro ⟨-, hq2⟩
                    have := congrArg List.length hq2
                    simp at this
                  rw [if_neg hq] at this
                  simpa [he2, List.append_assoc] using this
          · simp only [CanWin2, if_neg hN]
            refine Classical.byContradiction fun hcon => ?_
            have hall : ∀ qn : PLbl Channel Value,
                ¬ CanWin2 N R env rest (dc ++ [PLbl.inp a ov]) (dn ++ [qn]) :=
              fun qn hc => hcon ⟨qn, hc⟩
            have hnf : ∀ qn : PLbl Channel Value,
                ∃ adv : Channel → List (PLbl Channel Value) → Value,
                  (∀ a' q, env a' q (adv a' q)) ∧
                  ¬ ∃ o : List (PLbl Channel Value × PLbl Channel Value),
                    o.map Prod.fst = rest ∧
                    R ((dc ++ [PLbl.inp a ov]) ++ o.map Prod.fst)
                      ((dn ++ [qn]) ++ o.map Prod.snd) ∧
                    (∀ pre e post, o = pre ++ e :: post → ∀ (a' : Channel) (ov' : Option Value),
                      e.1 = PLbl.inp a' ov' → N a' →
                      e.2 = PLbl.inp a' (some (adv a' ((dn ++ [qn]) ++ pre.map Prod.snd)))) := by
              intro qn
              have hnF : ¬ Forced2 N R env rest (dc ++ [PLbl.inp a ov]) (dn ++ [qn]) :=
                fun hf => hall qn (ih _ _ hf)
              refine Classical.byContradiction fun hc => hnF ?_
              intro adv hadv
              exact Classical.byContradiction fun hno => hc ⟨adv, hadv, hno⟩
            obtain ⟨advOf, hadvOf⟩ := Classical.axiomOfChoice hnf
            have hcompat : ∀ a'' q, env a'' q
                (advOf (q.getD dn.length (PLbl.inp a ov)) a'' q) := by
              intro a'' q; exact (hadvOf _).1 a'' q
            obtain ⟨o, ho, hR, hadvc⟩ := hF _ hcompat
            cases o with
            | nil => simp at ho
            | cons e o' =>
                simp only [List.map_cons, List.cons.injEq] at ho
                obtain ⟨he1, ho'⟩ := ho
                refine (hadvOf e.2).2 ⟨o', ho', ?_, ?_⟩
                · have h1 : dc ++ (e.1 :: o'.map Prod.fst)
                      = (dc ++ [PLbl.inp a ov]) ++ o'.map Prod.fst := by rw [he1]; simp
                  have h2 : dn ++ (e.2 :: o'.map Prod.snd)
                      = (dn ++ [e.2]) ++ o'.map Prod.snd := by simp
                  simp only [List.map_cons] at hR
                  rw [h1, h2] at hR
                  exact hR
                · intro pre e'' post hsplit a'' ov'' hin hN''
                  have hh := hadvc (e :: pre) e'' post (by rw [hsplit]; rfl) a'' ov'' hin hN''
                  have hkey : (dn ++ (e :: pre).map Prod.snd).getD dn.length (PLbl.inp a ov)
                      = e.2 := by
                    simpa using getD_append_cons dn e.2 (pre.map Prod.snd) (PLbl.inp a ov)
                  rw [hkey] at hh
                  simpa [List.append_assoc] using hh
      | out a ov =>
          simp only [CanWin2]
          refine Classical.byContradiction fun hcon => ?_
          have hall : ∀ qn : PLbl Channel Value,
              ¬ CanWin2 N R env rest (dc ++ [PLbl.out a ov]) (dn ++ [qn]) :=
            fun qn hc => hcon ⟨qn, hc⟩
          have hnf : ∀ qn : PLbl Channel Value,
              ∃ adv : Channel → List (PLbl Channel Value) → Value,
                (∀ a' q, env a' q (adv a' q)) ∧
                ¬ ∃ o : List (PLbl Channel Value × PLbl Channel Value),
                  o.map Prod.fst = rest ∧
                  R ((dc ++ [PLbl.out a ov]) ++ o.map Prod.fst)
                    ((dn ++ [qn]) ++ o.map Prod.snd) ∧
                  (∀ pre e post, o = pre ++ e :: post → ∀ (a' : Channel) (ov' : Option Value),
                    e.1 = PLbl.inp a' ov' → N a' →
                    e.2 = PLbl.inp a' (some (adv a' ((dn ++ [qn]) ++ pre.map Prod.snd)))) := by
            intro qn
            have hnF : ¬ Forced2 N R env rest (dc ++ [PLbl.out a ov]) (dn ++ [qn]) :=
              fun hf => hall qn (ih _ _ hf)
            refine Classical.byContradiction fun hc => hnF ?_
            intro adv hadv
            exact Classical.byContradiction fun hno => hc ⟨adv, hadv, hno⟩
          obtain ⟨advOf, hadvOf⟩ := Classical.axiomOfChoice hnf
          have hcompat : ∀ a'' q, env a'' q
              (advOf (q.getD dn.length (PLbl.out a ov)) a'' q) := by
            intro a'' q; exact (hadvOf _).1 a'' q
          obtain ⟨o, ho, hR, hadvc⟩ := hF _ hcompat
          cases o with
          | nil => simp at ho
          | cons e o' =>
              simp only [List.map_cons, List.cons.injEq] at ho
              obtain ⟨he1, ho'⟩ := ho
              refine (hadvOf e.2).2 ⟨o', ho', ?_, ?_⟩
              · have h1 : dc ++ (e.1 :: o'.map Prod.fst)
                    = (dc ++ [PLbl.out a ov]) ++ o'.map Prod.fst := by rw [he1]; simp
                have h2 : dn ++ (e.2 :: o'.map Prod.snd)
                    = (dn ++ [e.2]) ++ o'.map Prod.snd := by simp
                simp only [List.map_cons] at hR
                rw [h1, h2] at hR
                exact hR
              · intro pre e'' post hsplit a'' ov'' hin hN''
                have hh := hadvc (e :: pre) e'' post (by rw [hsplit]; rfl) a'' ov'' hin hN''
                have hkey : (dn ++ (e :: pre).map Prod.snd).getD dn.length (PLbl.out a ov)
                    = e.2 := by
                  simpa using getD_append_cons dn e.2 (pre.map Prod.snd) (PLbl.out a ov)
                rw [hkey] at hh
                simpa [List.append_assoc] using hh

/-! ### The game is won: from noninterference to `Forced2`

    The adversary is a function of the `n`-view; since the channels it controls
    carry the level `n`, that function *is* a legal strategy.  This is the step
    that needed `Omniscient` in `Game.lean`. -/

/-- The strategy the component faces: `w` on the channels the coalition sees, the
    adversary's `π_n`-measurable choice on `N`, and anything elsewhere. -/
noncomputable def advStratL (S : Sec Level Channel) (C n : Level) (N : Channel → Prop)
    (hNn : ∀ a : Channel, N a → S.le n (S.valL a))
    (w : S.Strategy Value) (adv : Channel → List (PLbl Channel Value) → Value) :
    S.Strategy Value where
  ω := fun a t =>
    if S.le (S.valL a) C then w.ω a t
    else if N a then (fun v => v = adv a (S.proj n t))
    else (fun _ => True)
  resp_val := by
    intro a t₁ t₂ h
    by_cases hC : S.le (S.valL a) C
    · simp only [if_pos hC]; exact w.resp_val a t₁ t₂ h
    · simp only [if_neg hC]
      by_cases hN : N a
      · simp only [if_pos hN]
        have : S.proj n t₁ = S.proj n t₂ := teq_mono (hNn a hN) h
        rw [this]
      · simp only [if_neg hN]
  resp_pres := by
    intro a t₁ t₂ h
    by_cases hC : S.le (S.valL a) C
    · simp only [if_pos hC]; exact w.resp_pres a t₁ t₂ h
    · simp only [if_neg hC]
      by_cases hN : N a
      · simp only [if_pos hN]
        exact ⟨fun hx => absurd rfl (hx _), fun hx => absurd rfl (hx _)⟩
      · simp only [if_neg hN]
        exact dotEq.refl _

/-- The adversary's strategy is total when the component's is: it answers with `w`
    on the visible channels, a single value on `N`, and anything elsewhere. -/
theorem advStratL_total {C n : Level} {N : Channel → Prop}
    (hNn : ∀ a : Channel, N a → S.le n (S.valL a))
    {w : S.Strategy Value} (htot : w.total)
    (adv : Channel → List (PLbl Channel Value) → Value) :
    (advStratL S C n N hNn w adv).total := by
  intro a t
  by_cases hC : S.le (S.valL a) C
  · exact ⟨(htot a t).choose, by
      simp only [advStratL, if_pos hC]; exact (htot a t).choose_spec⟩
  · by_cases hN : N a
    · refine ⟨adv a (S.proj n t), ?_⟩
      simp only [advStratL, if_neg hC, if_pos hN]
    · refine ⟨adv a (S.proj n t), ?_⟩
      simp only [advStratL, if_neg hC, if_neg hN]

theorem seq_advStratL {C n : Level} {N : Channel → Prop}
    (hNn : ∀ a : Channel, N a → S.le n (S.valL a))
    {w : S.Strategy Value} (htot : w.total)
    (adv : Channel → List (PLbl Channel Value) → Value) :
    S.seq C w (advStratL S C n N hNn w adv) := by
  intro a t
  refine ⟨fun hC => ?_, fun _ => ?_⟩
  · simp only [advStratL, if_pos hC]
  · by_cases hC : S.le (S.valL a) C
    · simp only [advStratL, if_pos hC]; exact dotEq.refl _
    · by_cases hN : N a
      · simp only [advStratL, if_neg hC, if_pos hN]
        exact dotEq_of_total (htot a t) ⟨adv a (S.proj n t), rfl⟩
      · simp only [advStratL, if_neg hC, if_neg hN]
        exact dotEq_of_total (htot a t) ⟨adv a (S.proj n t), trivial⟩

theorem projL_C_inp {C : Level} {x : Lbl Channel Value} {a : Channel} {ov : Option Value}
    (h : S.projL C x = PLbl.inp a ov) : ∃ v, x = Lbl.inp a v := by
  cases x with
  | inp b v =>
      by_cases hb : S.le (S.valL b) C <;>
        simp only [projL, hb, if_pos, if_neg, if_false, PLbl.inp.injEq] at h <;>
        exact ⟨v, by rw [h.1]⟩
  | out b v =>
      by_cases hb : S.le (S.valL b) C <;>
        simp only [projL, hb, if_pos, if_neg, if_false] at h <;>
        exact absurd h (by simp)

theorem projL_n_inp_full {n : Level} {a : Channel} {v : Value}
    (hv : S.le (S.valL a) n) :
    S.projL n (Lbl.inp a v) = PLbl.inp a (some v) := by
  simp only [projL]; rw [if_pos hv]

/-- **The component wins the game**, given its noninterference.  The adversary
    built by determinacy is `π_n`-measurable, hence legal -- which is exactly what
    the flatness of a layer provides. -/
theorem forced2_of_INI {St : Type} {step : St → Act Channel Value → St → Prop} {s : St}
    {C n : Level} {N : Channel → Prop} {w : S.Strategy Value}
    (hpubC : S.PubAt C) (hpubN : S.PubAt n) (htot : w.total)
    (hNn : ∀ a : Channel, N a → S.le n (S.valL a))
    (hNn' : ∀ a : Channel, N a → S.le (S.valL a) n)
    (hNC : ∀ a : Channel, N a → ¬ S.le (S.valL a) C)
    (hINI : S.StratTNI step s)
    {b : List (Lbl Channel Value)} (hb : S.produces step w s b) :
    Forced2 N (RedPair S step s C n) (fun _ _ _ => True) (S.proj C b) [] [] := by
  intro adv _
  obtain ⟨t, hprod, hteq⟩ := hINI C w (advStratL S C n N hNn w adv) htot
    (advStratL_total hNn htot adv) (seq_advStratL hNn htot adv) b hb
  obtain ⟨⟨s', hreach⟩, hcons⟩ := hprod
  have hfst : (t.map (fun x => (S.projL C x, S.projL n x))).map Prod.fst = S.proj C t := by
    rw [List.map_map, proj_eq_map_at hpubC]; rfl
  have hsnd : (t.map (fun x => (S.projL C x, S.projL n x))).map Prod.snd = S.proj n t := by
    rw [List.map_map, proj_eq_map_at hpubN]; rfl
  refine ⟨t.map (fun x => (S.projL C x, S.projL n x)), ?_, ?_, ?_⟩
  · rw [hfst]; exact hteq.symm
  · rw [hfst, hsnd]
    exact ⟨t, s', hreach, by simp, by simp⟩
  · intro pre e post hsplit a ov he1 hN
    obtain ⟨u, x, r, hdec, hu, hx⟩ :=
      map_eq_append_cons (fun x => (S.projL C x, S.projL n x)) t pre e post hsplit
    have he1' : S.projL C x = PLbl.inp a ov := by rw [← hx] at he1; exact he1
    obtain ⟨v, rfl⟩ := projL_C_inp he1'
    have hval : (advStratL S C n N hNn w adv).ω a u v := hcons u a v r hdec
    have hveq : v = adv a (S.proj n u) := by
      simp only [advStratL, if_neg (hNC a hN), if_pos hN] at hval
      exact hval
    have hpre : pre.map Prod.snd = S.proj n u := by
      rw [← hu, List.map_map, proj_eq_map_at hpubN]; rfl
    rw [← hx, projL_n_inp_full (hNn' a hN), hpre, List.nil_append, hveq]

/-- **Lemma (★) without `Omniscient`.**  A noninterfering component can *force*
    its `C`-view against every adversary on the channels a layer exposes.  The
    hypotheses are exactly what a layer provides: those channels carry the level
    `n` (`hNn`, `hNn'`) and are invisible to the coalition (`hNC`). -/
theorem canWin2_of_INI {St : Type} {step : St → Act Channel Value → St → Prop} {s : St}
    {C n : Level} {N : Channel → Prop} {w : S.Strategy Value} (dflt : Value)
    (hpubC : S.PubAt C) (hpubN : S.PubAt n) (htot : w.total)
    (hNn : ∀ a : Channel, N a → S.le n (S.valL a))
    (hNn' : ∀ a : Channel, N a → S.le (S.valL a) n)
    (hNC : ∀ a : Channel, N a → ¬ S.le (S.valL a) C)
    (hINI : S.StratTNI step s)
    {b : List (Lbl Channel Value)} (hb : S.produces step w s b) :
    CanWin2 N (RedPair S step s C n) (fun _ _ _ => True) (S.proj C b) [] [] :=
  forced2_canWin2 (fun _ _ => ⟨dflt, trivial⟩) _ _ _
    (forced2_of_INI hpubC hpubN htot hNn hNn' hNC hINI hb)

/-! ### The policy

    A winning position yields a canonical play: at each step take a move the
    position provides, resolving the component's choices by `Classical.epsilon`.
    It is a function of the position -- the `n`-view -- hence `π_n`-measurable and
    causal, which is what a policy must be. -/

/-- The `n`-label the component commits to at a position. -/
noncomputable def pick2 {Channel Value : Type} (N : Channel → Prop)
    (R : List (PLbl Channel Value) → List (PLbl Channel Value) → Prop)
    (env : Channel → List (PLbl Channel Value) → Value → Prop)
    (l : PLbl Channel Value) (rest dc dn : List (PLbl Channel Value)) :
    PLbl Channel Value :=
  @Classical.epsilon _ ⟨l⟩ (fun qn : PLbl Channel Value =>
    CanWin2 N R env rest (dc ++ [l]) (dn ++ [qn]))

theorem pick2_spec {Channel Value : Type} {N : Channel → Prop}
    {R : List (PLbl Channel Value) → List (PLbl Channel Value) → Prop}
    {env : Channel → List (PLbl Channel Value) → Value → Prop}
    {l : PLbl Channel Value} {rest dc dn : List (PLbl Channel Value)}
    (hex : ∃ qn : PLbl Channel Value, CanWin2 N R env rest (dc ++ [l]) (dn ++ [qn])) :
    CanWin2 N R env rest (dc ++ [l]) (dn ++ [pick2 N R env l rest dc dn]) := by
  unfold pick2
  exact Classical.epsilon_spec hex

/-- The canonical play: the `n`-view the policy produces. -/
noncomputable def play2 {Channel Value : Type} (N : Channel → Prop)
    (R : List (PLbl Channel Value) → List (PLbl Channel Value) → Prop)
    (env : Channel → List (PLbl Channel Value) → Value → Prop)
    (adv : Channel → List (PLbl Channel Value) → Value) :
    List (PLbl Channel Value) → List (PLbl Channel Value) →
      List (PLbl Channel Value) → List (PLbl Channel Value)
  | [], _, _ => []
  | (PLbl.inp a ov) :: rest, dc, dn =>
      if N a then
        PLbl.inp a (some (adv a dn)) ::
          play2 N R env adv rest (dc ++ [PLbl.inp a ov])
            (dn ++ [PLbl.inp a (some (adv a dn))])
      else
        pick2 N R env (PLbl.inp a ov) rest dc dn ::
          play2 N R env adv rest (dc ++ [PLbl.inp a ov])
            (dn ++ [pick2 N R env (PLbl.inp a ov) rest dc dn])
  | (PLbl.out a ov) :: rest, dc, dn =>
      pick2 N R env (PLbl.out a ov) rest dc dn ::
        play2 N R env adv rest (dc ++ [PLbl.out a ov])
          (dn ++ [pick2 N R env (PLbl.out a ov) rest dc dn])

/-- **The policy realises the target.**  Against any environment-compatible
    adversary, the canonical play is a reduced run whose `C`-view is the target. -/
theorem play2_spec {Channel Value : Type} {N : Channel → Prop}
    {R : List (PLbl Channel Value) → List (PLbl Channel Value) → Prop}
    {env : Channel → List (PLbl Channel Value) → Value → Prop}
    {adv : Channel → List (PLbl Channel Value) → Value}
    (hadv : ∀ a q, env a q (adv a q)) :
    ∀ (tgt dc dn : List (PLbl Channel Value)), CanWin2 N R env tgt dc dn →
      R (dc ++ tgt) (dn ++ play2 N R env adv tgt dc dn) ∧
      (play2 N R env adv tgt dc dn).length = tgt.length := by
  intro tgt
  induction tgt with
  | nil =>
      intro dc dn h
      refine ⟨?_, rfl⟩
      simp only [play2, List.append_nil]
      exact h
  | cons l rest ih =>
      intro dc dn hwin
      cases l with
      | inp a ov =>
          by_cases hN : N a
          · simp only [CanWin2, if_pos hN] at hwin
            obtain ⟨h1, h2⟩ := ih _ _ (hwin (adv a dn) (hadv a dn))
            refine ⟨?_, ?_⟩
            · simp only [play2, if_pos hN]
              rw [List.append_assoc, List.append_assoc] at h1
              exact h1
            · simp only [play2, if_pos hN, List.length_cons, h2]
          · simp only [CanWin2, if_neg hN] at hwin
            obtain ⟨h1, h2⟩ := ih _ _ (pick2_spec hwin)
            refine ⟨?_, ?_⟩
            · simp only [play2, if_neg hN]
              rw [List.append_assoc, List.append_assoc] at h1
              exact h1
            · simp only [play2, if_neg hN, List.length_cons, h2]
      | out a ov =>
          simp only [CanWin2] at hwin
          obtain ⟨h1, h2⟩ := ih _ _ (pick2_spec hwin)
          refine ⟨?_, ?_⟩
          · simp only [play2]
            rw [List.append_assoc, List.append_assoc] at h1
            exact h1
          · simp only [play2, List.length_cons, h2]

/-- **The policy follows the adversary.**  Every entry of the canonical play on
    an adversarial channel carries the value the adversary chose at that position.
    Together with `play2_spec` this is the full contract of a policy: causal,
    `π_n`-measurable, and faithful to the environment. -/
theorem play2_adv {Channel Value : Type} {N : Channel → Prop}
    {R : List (PLbl Channel Value) → List (PLbl Channel Value) → Prop}
    {env : Channel → List (PLbl Channel Value) → Value → Prop}
    {adv : Channel → List (PLbl Channel Value) → Value} :
    ∀ (tgt dc dn : List (PLbl Channel Value))
      (pre : List (PLbl Channel Value)) (e : PLbl Channel Value)
      (post : List (PLbl Channel Value)),
      play2 N R env adv tgt dc dn = pre ++ e :: post →
      ∀ (a : Channel) (ov : Option Value),
        tgt.getD pre.length (PLbl.out a none) = PLbl.inp a ov → N a →
        e = PLbl.inp a (some (adv a (dn ++ pre))) := by
  intro tgt
  induction tgt with
  | nil => intro dc dn pre e post hsplit; simp [play2] at hsplit
  | cons l rest ih =>
      intro dc dn pre e post hsplit a ov hget hN
      cases pre with
      | nil =>
          -- the head of the play
          simp only [List.length_nil, List.getD_cons_zero] at hget
          subst hget
          simp only [play2, if_pos hN, List.nil_append, List.cons.injEq] at hsplit
          rw [← hsplit.1, List.append_nil]
      | cons x pre =>
          -- a later entry: peel one step
          cases l with
          | inp b ov' =>
              by_cases hNb : N b
              · simp only [play2, if_pos hNb, List.cons_append, List.cons.injEq] at hsplit
                have := ih _ _ pre e post hsplit.2 a ov (by simpa using hget) hN
                rw [← hsplit.1]
                simpa [List.append_assoc] using this
              · simp only [play2, if_neg hNb, List.cons_append, List.cons.injEq] at hsplit
                have := ih _ _ pre e post hsplit.2 a ov (by simpa using hget) hN
                rw [← hsplit.1]
                simpa [List.append_assoc] using this
          | out b ov' =>
              simp only [play2, List.cons_append, List.cons.injEq] at hsplit
              have := ih _ _ pre e post hsplit.2 a ov (by simpa using hget) hN
              rw [← hsplit.1]
              simpa [List.append_assoc] using this

/-! ### The joint play

    The two policies are run together along the interleaving pattern: at each step
    the component whose turn it is commits to its next `n`-label, and on an exposed
    channel the value comes from the oracle applied to the **merged** `n`-view.
    The recursion maintains both winning positions, so at the end each component
    has realised its own target. -/

/-- The `n`-label a component commits to at a position. -/
noncomputable def moveOf {Channel Value : Type} (N : Channel → Prop)
    (R : List (PLbl Channel Value) → List (PLbl Channel Value) → Prop)
    (oracle : Channel → List (PLbl Channel Value) → Value)
    (l : PLbl Channel Value) (rest dc dn dm : List (PLbl Channel Value)) :
    PLbl Channel Value :=
  match l with
  | PLbl.inp a _ =>
      if N a then PLbl.inp a (some (oracle a dm))
      else pick2 N R (fun _ _ _ => True) l rest dc dn
  | PLbl.out _ _ => pick2 N R (fun _ _ _ => True) l rest dc dn

/-- One step of the joint play preserves the winning position. -/
theorem moveOf_win {Channel Value : Type} {N : Channel → Prop}
    {R : List (PLbl Channel Value) → List (PLbl Channel Value) → Prop}
    {oracle : Channel → List (PLbl Channel Value) → Value}
    {l : PLbl Channel Value} {rest dc dn dm : List (PLbl Channel Value)}
    (hwin : CanWin2 N R (fun _ _ _ => True) (l :: rest) dc dn) :
    CanWin2 N R (fun _ _ _ => True) rest (dc ++ [l])
      (dn ++ [moveOf N R oracle l rest dc dn dm]) := by
  cases l with
  | inp a ov =>
      by_cases hN : N a
      · simp only [CanWin2, if_pos hN] at hwin
        simp only [moveOf, if_pos hN]
        exact hwin (oracle a dm) trivial
      · simp only [CanWin2, if_neg hN] at hwin
        simp only [moveOf, if_neg hN]
        exact pick2_spec hwin
  | out a ov =>
      simp only [CanWin2] at hwin
      simp only [moveOf]
      exact pick2_spec hwin

/-- The joint play: the two `n`-views the policies produce. -/
noncomputable def joint2 {Channel Value : Type} (N : Channel → Prop)
    (RA RB : List (PLbl Channel Value) → List (PLbl Channel Value) → Prop)
    (oracle : Channel → List (PLbl Channel Value) → Value) :
    List Bool →
    List (PLbl Channel Value) → List (PLbl Channel Value) → List (PLbl Channel Value) →
    List (PLbl Channel Value) → List (PLbl Channel Value) → List (PLbl Channel Value) →
    List (PLbl Channel Value) →
    List (PLbl Channel Value) × List (PLbl Channel Value)
  | [], _, _, _, _, _, _, _ => ([], [])
  | true :: p, l :: ta, dca, dna, tb, dcb, dnb, dm =>
      (moveOf N RA oracle l ta dca dna dm ::
        (joint2 N RA RB oracle p ta (dca ++ [l])
          (dna ++ [moveOf N RA oracle l ta dca dna dm]) tb dcb dnb
          (dm ++ [moveOf N RA oracle l ta dca dna dm])).1,
       (joint2 N RA RB oracle p ta (dca ++ [l])
          (dna ++ [moveOf N RA oracle l ta dca dna dm]) tb dcb dnb
          (dm ++ [moveOf N RA oracle l ta dca dna dm])).2)
  | true :: _, [], _, _, _, _, _, _ => ([], [])
  | false :: p, ta, dca, dna, l :: tb, dcb, dnb, dm =>
      ((joint2 N RA RB oracle p ta dca dna tb (dcb ++ [l])
          (dnb ++ [moveOf N RB oracle l tb dcb dnb dm])
          (dm ++ [moveOf N RB oracle l tb dcb dnb dm])).1,
       moveOf N RB oracle l tb dcb dnb dm ::
        (joint2 N RA RB oracle p ta dca dna tb (dcb ++ [l])
          (dnb ++ [moveOf N RB oracle l tb dcb dnb dm])
          (dm ++ [moveOf N RB oracle l tb dcb dnb dm])).2)
  | false :: _, _, _, _, [], _, _, _ => ([], [])

/-- **The joint play works for both components.**  Each realises its own target,
    the two parts interleave along the pattern, and every input on an exposed
    channel carries the value the oracle gives at the merged prefix. -/
theorem joint2_spec {Channel Value : Type} {N : Channel → Prop}
    {RA RB : List (PLbl Channel Value) → List (PLbl Channel Value) → Prop}
    {oracle : Channel → List (PLbl Channel Value) → Value} :
    ∀ (p : List Bool) (ta dca dna tb dcb dnb dm : List (PLbl Channel Value)),
      Exact p ta tb →
      CanWin2 N RA (fun _ _ _ => True) ta dca dna →
      CanWin2 N RB (fun _ _ _ => True) tb dcb dnb →
      RA (dca ++ ta) (dna ++ (joint2 N RA RB oracle p ta dca dna tb dcb dnb dm).1) ∧
      RB (dcb ++ tb) (dnb ++ (joint2 N RA RB oracle p ta dca dna tb dcb dnb dm).2) ∧
      Exact p (joint2 N RA RB oracle p ta dca dna tb dcb dnb dm).1
              (joint2 N RA RB oracle p ta dca dna tb dcb dnb dm).2 ∧
      (∀ pre e post,
        weave p (joint2 N RA RB oracle p ta dca dna tb dcb dnb dm).1
                (joint2 N RA RB oracle p ta dca dna tb dcb dnb dm).2 = pre ++ e :: post →
        ∀ (a : Channel) (ov : Option Value),
          (weave p ta tb).getD pre.length (PLbl.out a none) = PLbl.inp a ov → N a →
          e = PLbl.inp a (some (oracle a (dm ++ pre)))) := by
  intro p
  induction p with
  | nil =>
      intro ta dca dna tb dcb dnb dm hE hA hB
      obtain ⟨rfl, rfl⟩ := hE
      simp only [CanWin2] at hA hB
      refine ⟨by simpa [joint2] using hA, by simpa [joint2] using hB, ⟨rfl, rfl⟩, ?_⟩
      intro pre e post hsplit
      simp [joint2, weave] at hsplit
  | cons hd p ih =>
      intro ta dca dna tb dcb dnb dm hE hA hB
      cases hd with
      | true =>
          cases ta with
          | nil => exact absurd hE (by simp [Exact])
          | cons l ta =>
              have hE' : Exact p ta tb := hE
              have hA' := moveOf_win (oracle := oracle) (dm := dm) hA
              obtain ⟨h1, h2, h3, h4⟩ := ih ta (dca ++ [l])
                (dna ++ [moveOf N RA oracle l ta dca dna dm]) tb dcb dnb
                (dm ++ [moveOf N RA oracle l ta dca dna dm]) hE' hA' hB
              refine ⟨?_, ?_, ?_, ?_⟩
              · simp only [joint2]
                rw [List.append_assoc, List.append_assoc] at h1
                exact h1
              · simp only [joint2]; exact h2
              · simp only [joint2]; exact h3
              · intro pre e post hsplit a ov hget hN
                simp only [joint2, weave] at hsplit
                cases pre with
                | nil =>
                    simp only [List.nil_append, List.cons.injEq] at hsplit
                    simp only [List.length_nil, List.getD_cons_zero, weave] at hget
                    rw [← hsplit.1, hget]
                    simp only [moveOf, if_pos hN, List.append_nil]
                | cons x pre =>
                    simp only [List.cons_append, List.cons.injEq] at hsplit
                    have hget' : (weave p ta tb).getD pre.length (PLbl.out a none)
                        = PLbl.inp a ov := by simpa [weave] using hget
                    have := h4 pre e post hsplit.2 a ov hget' hN
                    rw [← hsplit.1]
                    simpa [List.append_assoc] using this
      | false =>
          cases tb with
          | nil => exact absurd hE (by simp [Exact])
          | cons l tb =>
              have hE' : Exact p ta tb := hE
              have hB' := moveOf_win (oracle := oracle) (dm := dm) hB
              obtain ⟨h1, h2, h3, h4⟩ := ih ta dca dna tb (dcb ++ [l])
                (dnb ++ [moveOf N RB oracle l tb dcb dnb dm])
                (dm ++ [moveOf N RB oracle l tb dcb dnb dm]) hE' hA hB'
              refine ⟨?_, ?_, ?_, ?_⟩
              · simp only [joint2]; exact h1
              · simp only [joint2]
                rw [List.append_assoc, List.append_assoc] at h2
                exact h2
              · simp only [joint2]; exact h3
              · intro pre e post hsplit a ov hget hN
                simp only [joint2, weave] at hsplit
                cases pre with
                | nil =>
                    simp only [List.nil_append, List.cons.injEq] at hsplit
                    simp only [List.length_nil, List.getD_cons_zero, weave] at hget
                    rw [← hsplit.1, hget]
                    simp only [moveOf, if_pos hN, List.append_nil]
                | cons x pre =>
                    simp only [List.cons_append, List.cons.injEq] at hsplit
                    have hget' : (weave p ta tb).getD pre.length (PLbl.out a none)
                        = PLbl.inp a ov := by simpa [weave] using hget
                    have := h4 pre e post hsplit.2 a ov hget' hN
                    rw [← hsplit.1]
                    simpa [List.append_assoc] using this

/-! ### The oracle

    On a channel a layer exposes, the environment's answer depends only on the
    `n`-view, so it can be read off a view rather than a trace. -/

/-- The value `w` offers on `a` at any trace with the given `n`-view. -/
noncomputable def oracleV (S : Sec Level Channel) (n : Level) (w : S.Strategy Value)
    (dflt : Value) (a : Channel) (dn : List (PLbl Channel Value)) : Value :=
  @Classical.epsilon _ ⟨dflt⟩ (fun v => ∀ t, S.proj n t = dn → w.ω a t v)

theorem oracleV_spec {n : Level} {w : S.Strategy Value} (dflt : Value)
    (htot : w.total) {a : Channel} (hNn' : S.le (S.valL a) n)
    {dn : List (PLbl Channel Value)} {t₀ : List (Lbl Channel Value)}
    (h₀ : S.proj n t₀ = dn) :
    ∀ t, S.proj n t = dn → w.ω a t (oracleV S n w dflt a dn) := by
  have hex : ∃ v, ∀ t, S.proj n t = dn → w.ω a t v := by
    obtain ⟨v, hv⟩ := htot a t₀
    refine ⟨v, fun t ht => ?_⟩
    have hteq : S.teq (S.valL a) t t₀ := teq_mono hNn' (by unfold Sec.teq; rw [ht, h₀])
    rw [w.resp_val a t t₀ hteq]
    exact hv
  unfold oracleV
  exact Classical.epsilon_spec hex

/-! ### Assembling the layer step -/

theorem projL_inp_hidden' {ℓ : Level} {a : Channel} {v : Value}
    (hv : ¬ S.le (S.valL a) ℓ) : S.projL ℓ (Lbl.inp a v) = PLbl.inp a none := by
  simp only [projL]; rw [if_neg hv]

theorem projL_D_inp {D : Level} {x : Lbl Channel Value} {a : Channel} {v : Value}
    (hvis : S.le (S.valL a) D) (h : S.projL D x = PLbl.inp a (some v)) :
    x = Lbl.inp a v := by
  obtain ⟨v', rfl⟩ := projL_C_inp h
  rw [projL_n_inp_full (n := D) hvis] at h
  injection h with _ hv
  injection hv with hv
  rw [hv]

/-- Helper: `getD` at the position of a decomposition. -/
theorem getD_split {α : Type} (u : List α) (x : α) (r : List α) (k : Nat) (d : α)
    (hk : k = u.length) : (u ++ x :: r).getD k d = x := by
  subst hk; exact getD_append_cons u x r d

/-- **The two-sided layer step.**  Both components may read from the channels the
    layer exposes: each has a causal policy by `canWin2_of_INI`, and `joint2`
    plays the two together against the environment. -/
theorem layerStep_of_game {S : Sec Level Channel} (dflt : Value)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {w : S.coalition.Strategy Value} (htotw : w.total)
    {m n : Level} {C : Coalition Level}
    (hpubC : S.coalition.PubAt C) (hpubN : S.coalition.PubAt (sing n))
    (hCle : S.coalition.le (Cplus S m) C)
    (hNIA : S.coalition.StratTNI stepA sA) (hNIB : S.coalition.StratTNI stepB sB)
    (hflat : ∀ a : Channel, NewlyVisible S C n a → S.le n (S.valL a))
    {τ : List (PLbl Channel Value)}
    (h : LayerCons S stepA stepB sA sB w m C τ) :
    LayerCons S stepA stepB sA sB w m (addLevel C n) τ := by
  classical
  have hpub : S.coalition.PubAt (addLevel C n) := pubAt_mono hpubC (le_addLevel C n)
  obtain ⟨p, oA, oB, hE, ⟨tA, qA, vA, htA, hrA, hcA, hoA⟩,
    ⟨tB, qB, vB, htB, hrB, hcB, hoB⟩, hcons, hdown⟩ := h
  -- the exposed channels
  have hNn : ∀ a : Channel, NewlyVisible S C n a →
      S.coalition.le (sing n) (S.coalition.valL a) := by
    intro a ha c hc
    exact ⟨S.valL a, rfl, by rw [show c = n from hc]; exact hflat a ha⟩
  have hNn'0 : ∀ a : Channel, NewlyVisible S C n a → S.le (S.valL a) n := by
    intro a ha
    obtain ⟨d, hd, hle⟩ := ha.1 (S.valL a) rfl
    rcases hd with hd | rfl
    · exact absurd (fun c hc => ⟨d, hd, by rw [show c = S.valL a from hc]; exact hle⟩) ha.2
    · exact hle
  have hNn' : ∀ a : Channel, NewlyVisible S C n a →
      S.coalition.le (S.coalition.valL a) (sing n) := by
    intro a ha c hc
    exact ⟨n, rfl, by rw [show c = S.valL a from hc]; exact hNn'0 a ha⟩
  have hNC : ∀ a : Channel, NewlyVisible S C n a →
      ¬ S.coalition.le (S.coalition.valL a) C := fun a ha => ha.2
  -- both components win their game
  have hwinA := canWin2_of_INI (S := S.coalition) (N := NewlyVisible S C n) dflt hpubC hpubN htA
    hNn hNn' hNC hNIA ⟨⟨qA, hrA⟩, hcA⟩
  have hwinB := canWin2_of_INI (S := S.coalition) (N := NewlyVisible S C n) dflt hpubC hpubN htB
    hNn hNn' hNC hNIB ⟨⟨qB, hrB⟩, hcB⟩
  rw [hoA] at hwinA
  rw [hoB] at hwinB
  -- play them together
  obtain ⟨hRA, hRB, hEx, hNcond⟩ := joint2_spec (N := NewlyVisible S C n)
    (RA := RedPair S.coalition stepA sA C (sing n))
    (RB := RedPair S.coalition stepB sB C (sing n))
    (oracle := oracleV S.coalition (sing n) w dflt) p oA [] [] oB [] [] [] hE hwinA hwinB
  simp only [List.nil_append] at hRA hRB
  obtain ⟨tA', qA', hrA', hcA'', hnA'⟩ :
      ∃ (t : List (Lbl Channel Value)) (s' : StA), Reach stepA sA t s' ∧
        S.coalition.proj C t = oA ∧ S.coalition.proj (sing n) t = _ := hRA
  obtain ⟨tB', qB', hrB', hcB'', hnB'⟩ :
      ∃ (t : List (Lbl Channel Value)) (s' : StB), Reach stepB sB t s' ∧
        S.coalition.proj C t = oB ∧ S.coalition.proj (sing n) t = _ := hRB
  -- common facts about the merged trace
  have hDC : S.coalition.le C (addLevel C n) := le_addLevel C n
  have hDn : S.coalition.le (sing n) (addLevel C n) := fun c hc =>
    ⟨n, Or.inr rfl, by rw [show c = n from hc]; exact S.le_refl n⟩
  have hCplusD : S.coalition.le (Cplus S m) (addLevel C n) := S.coalition.le_trans hCle hDC
  have hlen : ∀ (ℓ : Coalition Level), S.coalition.PubAt ℓ →
      ∀ t : List (Lbl Channel Value), (S.coalition.proj ℓ t).length = t.length := by
    intro ℓ hp t; rw [proj_eq_map_at hp, List.length_map]
  have hwD : weave p (S.coalition.proj (addLevel C n) tA')
      (S.coalition.proj (addLevel C n) tB')
      = S.coalition.proj (addLevel C n) (weave p tA' tB') := (proj_weave_at hpub p tA' tB').symm
  have hwC : S.coalition.proj C (weave p tA' tB') = weave p oA oB := by
    rw [proj_weave_at hpubC, hcA'', hcB'']
  have hwn : S.coalition.proj (sing n) (weave p tA' tB')
      = weave p (joint2 (NewlyVisible S C n) (RedPair S.coalition stepA sA C (sing n))
          (RedPair S.coalition stepB sB C (sing n))
          (oracleV S.coalition (sing n) w dflt) p oA [] [] oB [] [] []).1
        (joint2 (NewlyVisible S C n) (RedPair S.coalition stepA sA C (sing n))
          (RedPair S.coalition stepB sB C (sing n))
          (oracleV S.coalition (sing n) w dflt) p oA [] [] oB [] [] []).2 := by
    rw [proj_weave_at hpubN, hnA', hnB']
  refine ⟨p, S.coalition.proj (addLevel C n) tA', S.coalition.proj (addLevel C n) tB', ?_,
    ⟨tA', qA', _, replayStrat_total dflt tA', hrA', consistent_replayStrat dflt tA', rfl⟩,
    ⟨tB', qB', _, replayStrat_total dflt tB', hrB', consistent_replayStrat dflt tB', rfl⟩,
    ?_, ?_⟩
  · refine Exact.retype p oA oB _ _ hE ?_ ?_
    · rw [← hcA'', hlen C hpubC tA', hlen (addLevel C n) hpub tA']
    · rw [← hcB'', hlen C hpubC tB', hlen (addLevel C n) hpub tB']
  · rw [hwD]
    intro o₁ a v o₂ hsplit hvis t ht
    obtain ⟨u, x, rr, hdec, hu, hx⟩ := proj_split hpub hsplit
    have hxa : x = Lbl.inp a v := projL_D_inp hvis hx
    subst hxa
    by_cases hvC : S.coalition.le (S.coalition.valL a) C
    · refine hcons (S.coalition.proj C u) a v (S.coalition.proj C rr) ?_ hvC t ?_
      · rw [← hwC, hdec, proj_append, proj_cons_some (projLbl_eq_projL_at hpubC _),
          projL_n_inp_full hvC]
      · rw [← down_proj hDC t, ht, ← hu, down_proj hDC u]
    · have hN : NewlyVisible S C n a := ⟨hvis, hvC⟩
      have hprojn : weave p (joint2 (NewlyVisible S C n)
            (RedPair S.coalition stepA sA C (sing n))
            (RedPair S.coalition stepB sB C (sing n))
            (oracleV S.coalition (sing n) w dflt) p oA [] [] oB [] [] []).1
          (joint2 (NewlyVisible S C n) (RedPair S.coalition stepA sA C (sing n))
            (RedPair S.coalition stepB sB C (sing n))
            (oracleV S.coalition (sing n) w dflt) p oA [] [] oB [] [] []).2
          = S.coalition.proj (sing n) u ++ PLbl.inp a (some v)
              :: S.coalition.proj (sing n) rr := by
        rw [← hwn, hdec, proj_append, proj_cons_some (projLbl_eq_projL_at hpubN _),
          projL_n_inp_full (hNn' a hN)]
      have hgetC : (weave p oA oB).getD (S.coalition.proj (sing n) u).length
          (PLbl.out a none) = PLbl.inp a none := by
        rw [← hwC, hdec, proj_append, proj_cons_some (projLbl_eq_projL_at hpubC _),
          projL_inp_hidden' hvC]
        exact getD_split _ _ _ _ _ (by rw [hlen _ hpubN, hlen _ hpubC])
      have hkey := hNcond (S.coalition.proj (sing n) u) (PLbl.inp a (some v))
        (S.coalition.proj (sing n) rr) hprojn a none hgetC hN
      have hv : v = oracleV S.coalition (sing n) w dflt a (S.coalition.proj (sing n) u) := by
        simp only [PLbl.inp.injEq, Option.some.injEq] at hkey
        exact hkey.2
      subst hv
      refine oracleV_spec dflt htotw (hNn' a hN) (t₀ := u) rfl t ?_
      rw [← down_proj hDn t, ht, ← hu, down_proj hDn u]
  · rw [hwD, down_proj hCplusD, ← down_proj hCle, hwC]
    exact hdown

/-- Presence-visibility along the peeling: at each level it exposes.  Note this is
    *not* the global "presence is public": it constrains only the levels the
    peeling actually touches. -/
def PeelPub (S : Sec Level Channel) : List Level → Prop
  | [] => True
  | n :: ns => S.coalition.PubAt (sing n) ∧ PeelPub S ns

theorem peelPub_of_pub {S : Sec Level Channel} (hpubS : PublicPresence S) :
    ∀ ns : List Level, PeelPub S ns
  | [] => trivial
  | n :: ns => ⟨pubAt_coalition hpubS ⟨n, rfl⟩, peelPub_of_pub hpubS ns⟩

/-- Flatness of the peeling: each layer exposes channels of its own level.  Only
    the pairs actually occurring along `ns` are constrained. -/
def PeelFlat (S : Sec Level Channel) (m : Level) : List Level → Prop
  | [] => True
  | n :: ns => (∀ a : Channel, NewlyVisible S (layerC S m ns) n a → S.le n (S.valL a)) ∧
      PeelFlat S m ns

/-- The peeling, with the two-sided layer step supplied by the game. -/
theorem layerCons_peel2 {S : Sec Level Channel} (dflt : Value)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {w : S.coalition.Strategy Value} (htotw : w.total) {m : Level}
    (hNIA : S.coalition.StratTNI stepA sA) (hNIB : S.coalition.StratTNI stepB sB)
    (hpubP : S.coalition.PubAt (Cplus S m)) {τ : List (PLbl Channel Value)}
    (h₀ : LayerCons S stepA stepB sA sB w m (Cplus S m) τ) :
    ∀ ns : List Level, PeelFlat S m ns → PeelPub S ns →
      LayerCons S stepA stepB sA sB w m (layerC S m ns) τ := by
  intro ns
  induction ns with
  | nil => intro _ _; exact h₀
  | cons n ns ih =>
      intro hflat hpp
      exact layerStep_of_game dflt htotw (pubAt_mono hpubP (layerC_le S m ns)) hpp.1
        (layerC_le S m ns) hNIA hNIB hflat.1 (ih hflat.2 hpp.2)

/-- **Compositionality of coalition noninterference at `C⁺`, with no assumption on
    the channel labelling.**  The hypotheses are the standing ones of Theorem 20 --
    presence public, strategies total -- together with the peeling data: a list of
    levels exhausting the channels, each layer of which exposes channels of its own
    level.  Spreadness of `γ` is *not* assumed. -/
theorem coalition_compositional_layered {S : Sec Level Channel}
    (hpubS : PublicPresence S) (dflt : Value)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    {m : Level} {w₁ w₂ : S.coalition.Strategy Value}
    (htot₁ : w₁.total) (htot₂ : w₂.total)
    (hNIA : S.coalition.StratTNI stepA sA) (hNIB : S.coalition.StratTNI stepB sB)
    (hne : ∃ c, Cplus S m c) (ns : List Level)
    (hfull : ∀ a : Channel, S.coalition.le (sing (S.valL a)) (layerC S m ns))
    (hflat : PeelFlat S m ns)
    (hseq : S.coalition.seq (Cplus S m) w₁ w₂)
    {t₁ : List (Lbl Channel Value)}
    (h₁ : S.coalition.produces (parStep stepA stepB) w₁ (sA, sB) t₁) :
    ∃ t₂, S.coalition.produces (parStep stepA stepB) w₂ (sA, sB) t₂ ∧
      S.coalition.teq (Cplus S m) t₁ t₂ := by
  have hpubP : S.coalition.PubAt (Cplus S m) := pubAt_coalition hpubS hne
  obtain ⟨t₂, hprod, hproj⟩ := layerFinal_holds
    (pubAt_mono hpubP (layerC_le S m ns)) _ hfull
    (layerCons_peel2 dflt htot₂ hNIA hNIB hpubP
      (layerCons_base hpubP dflt hseq h₁) ns hflat (peelPub_of_pub hpubS ns))
  exact ⟨t₂, hprod, hproj.symm⟩

/-- The empty coalition observes nothing, not even presence. -/
theorem proj_empty_coalition {S : Sec Level Channel} {C : Coalition Level}
    (hC : ¬ ∃ d, C d) (t : List (Lbl Channel Value)) :
    S.coalition.proj C t = [] := by
  induction t with
  | nil => rfl
  | cons l t ih =>
      refine Eq.trans (Sec.proj_cons_none ?_ t) ih
      rw [Sec.projLbl_eq_none_iff]
      intro h
      exact hC (by obtain ⟨d, hd, -⟩ := h (S.presL (l.chan)) rfl; exact ⟨d, hd⟩)

/-! ### From `C⁺` to an arbitrary coalition

    The invisible set of a coalition is up-closed, so the difference between two
    strategies may be peeled one channel at a time, each step using the coalition
    `C⁺(γ(δ))` -- the largest one that still hides `δ`. -/

/-- The peeling data for a perturbation at `m`: a list of levels exhausting the
    channels, fresh below the layers under it, each exposing channels of its own
    level.  This is a property of the security context, not an assumption on `γ`:
    a linear extension of the levels carrying channels provides it. -/
def Peelable (S : Sec Level Channel) (m : Level) : Prop :=
  ∃ ns : List Level,
    (∀ a : Channel, S.coalition.le (sing (S.valL a)) (layerC S m ns)) ∧ PeelFlat S m ns

/-- **The hybrid.**  Transport a composed run along a list of channels on which the
    two strategies may differ. -/
theorem compositional_of_list {S : Sec Level Channel}
    (hpubS : PublicPresence S) (dflt : Value)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    (hNIA : S.coalition.StratTNI stepA sA) (hNIB : S.coalition.StratTNI stepB sB)
    (hpeel : ∀ m : Level, Peelable S m) {C : Coalition Level} (hCne : ∃ c, C c) :
    ∀ (ds : List Channel) (w₁ w₂ : S.coalition.Strategy Value),
      w₁.total → w₂.total →
      (∀ a : Channel, a ∉ ds → ∀ t, w₁.ω a t = w₂.ω a t) →
      (∀ a : Channel, a ∈ ds → ¬ S.coalition.le (S.coalition.valL a) C) →
      ∀ t₁, S.coalition.produces (parStep stepA stepB) w₁ (sA, sB) t₁ →
        ∃ t₂, S.coalition.produces (parStep stepA stepB) w₂ (sA, sB) t₂ ∧
          S.coalition.teq C t₁ t₂ := by
  intro ds
  induction ds with
  | nil =>
      intro w₁ w₂ _ _ hagree _ t₁ h₁
      exact ⟨t₁, ⟨h₁.1, consistent_congr (fun a u => hagree a (by simp) u) h₁.2⟩, rfl⟩
  | cons δ ds ih =>
      intro w₁ w₂ htot₁ htot₂ hagree hinv t₁ h₁
      -- the intermediate strategy: `w₂` on `δ`, `w₁` elsewhere
      have htot' : (mixStrat (fun a => a = δ) w₁ w₂).total := by
        intro a t
        by_cases hp : a = δ
        · rw [mixStrat_pos (P := fun x => x = δ) hp]; exact htot₂ a t
        · rw [mixStrat_neg (P := fun x => x = δ) hp]; exact htot₁ a t
      have hδinv : ¬ S.coalition.le (S.coalition.valL δ) C := hinv δ (by simp)
      have hCle : S.coalition.le C (Cplus S (S.valL δ)) :=
        le_Cplus (fun ⟨c, hc, hle⟩ => hδinv (fun x hx => ⟨c, hc, by
          rw [show x = S.valL δ from hx]; exact hle⟩))
      have hδhid : ¬ S.coalition.le (S.coalition.valL δ) (Cplus S (S.valL δ)) := by
        intro hh
        obtain ⟨d, hd, hle⟩ := hh (S.valL δ) rfl
        exact hd hle
      have hseq : S.coalition.seq (Cplus S (S.valL δ)) w₁ (mixStrat (fun a => a = δ) w₁ w₂) := by
        intro a t
        refine ⟨fun hvis => ?_, fun _ => ?_⟩
        · have hne : ¬ (a = δ) := by
            intro he; subst he; exact hδhid hvis
          exact (mixStrat_neg (P := fun x => x = δ) hne t).symm
        · by_cases hp : a = δ
          · rw [mixStrat_pos (P := fun x => x = δ) hp]; exact dotEq_of_total (htot₁ a t) (htot₂ a t)
          · exact dotEq.of_eq (mixStrat_neg (P := fun x => x = δ) hp t).symm
      obtain ⟨ns, hfull, hflat⟩ := hpeel (S.valL δ)
      have hne : ∃ c, Cplus S (S.valL δ) c := by
        obtain ⟨c, hc⟩ := hCne
        obtain ⟨d, hd, -⟩ := hCle c hc
        exact ⟨d, hd⟩
      obtain ⟨t', h', hteq'⟩ := coalition_compositional_layered hpubS dflt htot₁ htot'
        hNIA hNIB hne ns hfull hflat hseq h₁
      obtain ⟨t₂, h₂, hteq₂⟩ := ih (mixStrat (fun a => a = δ) w₁ w₂) w₂ htot' htot₂
        (fun a ha u => by
          by_cases hp : a = δ
          · rw [mixStrat_pos (P := fun x => x = δ) hp]
          · rw [mixStrat_neg (P := fun x => x = δ) hp]
            exact hagree a (by simp [hp, ha]) u)
        (fun a ha => hinv a (by simp [ha])) t' h'
      exact ⟨t₂, h₂, (teq_mono hCle hteq').trans hteq₂⟩

/-- **Coalition `Strat_T`-noninterference composes, over an arbitrary lattice.**
    This is the total case, matching §3.3.  No assumption on the channel
    labelling: `γ` need not be spread.  Presence is public, as in §3.3. -/
theorem coalition_compositional_total {S : Sec Level Channel}
    (hpubS : PublicPresence S) (dflt : Value)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    (cs : List Channel) (hcs : ∀ a : Channel, a ∈ cs)
    (hpeel : ∀ m : Level, Peelable S m)
    (hNIA : S.coalition.StratTNI stepA sA) (hNIB : S.coalition.StratTNI stepB sB) :
    S.coalition.StratTNI (parStep stepA stepB) (sA, sB) := by
  intro C w₁ w₂ htot₁ htot₂ hseq t₁ h₁
  by_cases hCne : ∃ c, C c
  case neg =>
    -- the empty coalition observes nothing at all
    refine ⟨[], ⟨⟨(sA, sB), Reach.nil⟩, by intro u a v r heq; simp at heq⟩, ?_⟩
    unfold Sec.teq
    rw [proj_empty_coalition hCne, proj_empty_coalition hCne]
  refine compositional_of_list hpubS dflt hNIA hNIB hpeel hCne
    (cs.filter (fun a => decide (¬ S.coalition.le (S.coalition.valL a) C)))
    w₁ w₂ htot₁ htot₂ ?_ ?_ t₁ h₁
  · intro a ha u
    have hvis : S.coalition.le (S.coalition.valL a) C := by
      by_cases hv : S.coalition.le (S.coalition.valL a) C
      · exact hv
      · exact absurd (List.mem_filter.mpr ⟨hcs a, by simp only [decide_eq_true_eq]; exact hv⟩) ha
    exact (hseq a u).1 hvis
  · intro a ha
    have h2 := (List.mem_filter.mp ha).2
    simpa using h2

/-! ### The non-total case

    Section 3.1 works with `Strat`, all strategies, which may block.  That case
    follows from the total one.  Totalise both strategies -- offering a default
    value where they offer none -- apply the total theorem, and observe that the
    run it returns never uses a default: whether a strategy blocks on a channel
    depends only on the *shape* of the trace (presence visible at `C`), `≐`-equivalent
    strategies block on the same shapes, and the run has the same shape as the one
    we started from, at whose inputs the original strategy did offer a value. -/

theorem projL_out_ne_inp {ℓ : Level} {b a : Channel} {x v : Value} :
    S.projL ℓ (Lbl.out b x) ≠ S.projL ℓ (Lbl.inp a v) := by
  by_cases h1 : S.le (S.valL b) ℓ <;> by_cases h2 : S.le (S.valL a) ℓ <;>
    simp [projL, h1, h2]

/-- Totalising a strategy: offer `dflt` where it offers nothing. -/
noncomputable def totalize (S : Sec Level Channel) (dflt : Value)
    (w : S.Strategy Value) : S.Strategy Value where
  ω := fun a t v => w.ω a t v ∨ ((∀ v', ¬ w.ω a t v') ∧ v = dflt)
  resp_val := by
    intro a t₁ t₂ h
    rw [w.resp_val a t₁ t₂ h]
  resp_pres := by
    intro a t₁ t₂ _
    have key : ∀ t : List (Lbl Channel Value),
        ¬ (∀ v : Value, ¬ (w.ω a t v ∨ ((∀ v', ¬ w.ω a t v') ∧ v = dflt))) := by
      intro t hemp
      by_cases hex : ∃ v, w.ω a t v
      · obtain ⟨v, hv⟩ := hex; exact hemp v (Or.inl hv)
      · exact hemp dflt (Or.inr ⟨fun v hv => hex ⟨v, hv⟩, rfl⟩)
    exact ⟨fun h => absurd h (key t₁), fun h => absurd h (key t₂)⟩

theorem totalize_total (dflt : Value) (w : S.Strategy Value) :
    (totalize S dflt w).total := by
  intro a t
  by_cases hex : ∃ v, w.ω a t v
  · obtain ⟨v, hv⟩ := hex; exact ⟨v, Or.inl hv⟩
  · exact ⟨dflt, Or.inr ⟨fun v hv => hex ⟨v, hv⟩, rfl⟩⟩

theorem consistent_totalize {dflt : Value} {w : S.Strategy Value}
    {t : List (Lbl Channel Value)} (h : S.consistent w t) :
    S.consistent (totalize S dflt w) t :=
  fun t₁ a v t₂ heq => Or.inl (h t₁ a v t₂ heq)

theorem produces_totalize {St : Type} {step : St → Act Channel Value → St → Prop}
    {s : St} {dflt : Value} {w : S.Strategy Value} {t : List (Lbl Channel Value)}
    (h : S.produces step w s t) : S.produces step (totalize S dflt w) s t :=
  ⟨h.1, consistent_totalize h.2⟩

theorem seq_totalize {ℓ : Level} (dflt : Value) (hpres : ∀ a : Channel, S.le (S.presL a) ℓ)
    {w₁ w₂ : S.Strategy Value} (h : S.seq ℓ w₁ w₂) :
    S.seq ℓ (totalize S dflt w₁) (totalize S dflt w₂) := by
  intro a t
  refine ⟨fun hvis => ?_, fun _ => ?_⟩
  · show (fun v => w₁.ω a t v ∨ _) = (fun v => w₂.ω a t v ∨ _)
    rw [(h a t).1 hvis]
  · exact dotEq_of_total (totalize_total dflt w₁ a t) (totalize_total dflt w₂ a t)

/-- **The run returned by the total theorem is a run of the original strategy.**
    A blocked input would force the same input to be blocked on the trace we
    started from, where it was not. -/
theorem consistent_of_totalize {C : Coalition Level}
    (hpub : S.coalition.PubAt C) {dflt : Value}
    {w₁ w₂ : S.coalition.Strategy Value} (hseq : S.coalition.seq C w₁ w₂)
    {t₁ t₂ : List (Lbl Channel Value)}
    (hc₁ : S.coalition.consistent w₁ t₁) (hteq : S.coalition.teq C t₁ t₂)
    (hc₂ : S.coalition.consistent (totalize S.coalition dflt w₂) t₂) :
    S.coalition.consistent w₂ t₂ := by
  intro u a v r heq
  rcases hc₂ u a v r heq with hv | ⟨hempty, -⟩
  · exact hv
  exfalso
  -- locate the corresponding input in `t₁`
  have hsplit : S.coalition.proj C t₁
      = S.coalition.proj C u ++ S.coalition.projL C (Lbl.inp a v) :: S.coalition.proj C r := by
    rw [hteq, heq, proj_append, proj_cons_some (projLbl_eq_projL_at hpub _)]
  obtain ⟨u₁, l₁, r₁, hdec, hu₁, hl₁⟩ := proj_split hpub hsplit
  have hchan : ∃ v₁, l₁ = Lbl.inp a v₁ := by
    cases l₁ with
    | inp b x =>
        by_cases hb : S.coalition.le (S.coalition.valL b) C
        · rw [projL_inp_vis hb] at hl₁
          by_cases ha : S.coalition.le (S.coalition.valL a) C
          · rw [projL_inp_vis ha] at hl₁
            injection hl₁ with hb' hx
            exact ⟨x, by rw [hb']⟩
          · rw [projL_inp_hidden' ha] at hl₁
            injection hl₁ with hb' hx
            exact absurd hx (by simp)
        · rw [projL_inp_hidden' hb] at hl₁
          by_cases ha : S.coalition.le (S.coalition.valL a) C
          · rw [projL_inp_vis ha] at hl₁
            injection hl₁ with hb' hx
            exact absurd hx.symm (by simp)
          · rw [projL_inp_hidden' ha] at hl₁
            injection hl₁ with hb' hx
            exact ⟨x, by rw [hb']⟩
    | out b x => exact absurd hl₁ projL_out_ne_inp
  obtain ⟨v₁, rfl⟩ := hchan
  -- the original strategy was not blocked there
  have hne₁ : w₁.ω a u₁ v₁ := hc₁ u₁ a v₁ r₁ hdec
  have hteqp : S.coalition.teq (S.coalition.presL a) u u₁ :=
    teq_mono (hpub a) (by unfold Sec.teq; rw [hu₁])
  have hdot : dotEq (w₁.ω a u) (w₁.ω a u₁) := w₁.resp_pres a u u₁ hteqp
  have hne : ¬ (w₁.ω a u).isEmpty := by
    intro hemp
    exact (hdot.mp hemp) v₁ hne₁
  exact hne ((hseq a u).2 (hpub a) |>.mpr hempty)

/-- **Coalition `Strat`-noninterference composes, over an arbitrary lattice.**
    The non-total case, matching §3.1: the strategies range over all of `Strat`,
    and may block. -/
theorem coalition_compositional_strat {S : Sec Level Channel}
    (hpubS : PublicPresence S) (dflt : Value)
    {StA StB : Type} {stepA : StA → Act Channel Value → StA → Prop}
    {stepB : StB → Act Channel Value → StB → Prop} {sA : StA} {sB : StB}
    (cs : List Channel) (hcs : ∀ a : Channel, a ∈ cs)
    (hpeel : ∀ m : Level, Peelable S m)
    (hNIA : S.coalition.StratNI stepA sA) (hNIB : S.coalition.StratNI stepB sB) :
    S.coalition.StratNI (parStep stepA stepB) (sA, sB) := by
  intro C w₁ w₂ _ _ hseq t₁ h₁
  by_cases hCne : ∃ c, C c
  case neg =>
    refine ⟨[], ⟨⟨(sA, sB), Reach.nil⟩, by intro u a v r heq; simp at heq⟩, ?_⟩
    unfold Sec.teq
    rw [proj_empty_coalition hCne, proj_empty_coalition hCne]
  have hpubC : S.coalition.PubAt C := pubAt_coalition hpubS hCne
  obtain ⟨t₂, h₂, hteq⟩ := coalition_compositional_total hpubS dflt cs hcs hpeel
    (INI_mono (fun _ _ => trivial) hNIA) (INI_mono (fun _ _ => trivial) hNIB)
    C (totalize S.coalition dflt w₁) (totalize S.coalition dflt w₂)
    (totalize_total dflt w₁) (totalize_total dflt w₂)
    (seq_totalize dflt hpubC hseq) t₁ (produces_totalize h₁)
  exact ⟨t₂, ⟨h₂.1, consistent_of_totalize hpubC hseq h₁.2 hteq h₂.2⟩, hteq⟩

/-! ### On the presence hypothesis

    The total theorem asks for presence-visibility only where the peeling looks:
    at `C⁺(m)` and at each level it exposes (`Peelable`, `PeelPub`).  That is
    strictly weaker than `PublicPresence S`, which demands `presL a ⊑ ℓ` for
    *every* level of `Λ`, including levels no channel is assigned to.

    It cannot be dropped altogether, and not merely for want of effort.  With
    presence secret at the observing coalition three things fail at once.

    * `π_C` is no longer a `map`: labels vanish from the observation, so the
      observation stops pinning the *shape* of the trace.  Everything positional
      goes with it -- `proj_split`, `proj_weave_at`, `Exact.retype`, and the
      pairing of the `C`-view with the `n`-view that the game's positions rely on.
    * `seq` then constrains *nothing* on such a channel: `presL a ⊑ valL a`, so
      `valL a ⊑ C` implies `presL a ⊑ C`; when presence is invisible so is the
      value, and neither clause of `seq` applies.  The two strategies may differ
      completely there -- one blocking, the other not -- which is exactly what
      `consistent_of_totalize` rules out in the non-total case.
    * Most seriously, the game loses its measure.  Its determinacy
      (`forced2_canWin2`) is an induction on the target, and the target bounds the
      play only because every label is visible.  With presence secret a component
      may interleave unboundedly many invisible labels, so the game is no longer of
      bounded depth and the induction has nothing to recurse on.

    Recovering the theorem there would need a game of unbounded depth -- so a
    determinacy argument of a different kind -- positions carrying the two views as
    independent lists rather than aligned pairs, and something to replace the
    pinning of the shape.  Whether the statement itself survives, we do not know. -/

end Sec

end InteractiveNI
