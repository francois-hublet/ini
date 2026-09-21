/-
  **Interleavings without public presence.**

  The old proof transfers the interleaving pattern between a trace and its
  projection by counting labels, which needs every label to survive every
  projection.  Here the transfer is done by two lemmas that hold for an arbitrary
  projection: an interleaving of two traces projects to an interleaving of their
  projections (`Interleave.filterMap`), and -- the direction that matters -- an
  interleaving of the *projections* is induced by some interleaving of the traces
  (`Interleave.lift`).  The labels the level does not see are simply scheduled
  greedily; they constrain nothing.
-/
import InteractiveNI.LayerGameW

namespace InteractiveNI

open Classical
attribute [local instance] Classical.propDecidable

/-! ### Interleavings and projections -/

theorem Interleave.filterMap {α β : Type} (f : α → Option β) {u v w : List α}
    (h : Interleave u v w) :
    Interleave (u.filterMap f) (v.filterMap f) (w.filterMap f) := by
  induction h with
  | nil => exact Interleave.nil
  | @left a u v w _ ih =>
      rcases hx : f a with _ | b
      · simpa [List.filterMap_cons_none hx] using ih
      · simp only [List.filterMap_cons_some hx]; exact Interleave.left ih
  | @right a u v w _ ih =>
      rcases hx : f a with _ | b
      · simpa [List.filterMap_cons_none hx] using ih
      · simp only [List.filterMap_cons_some hx]; exact Interleave.right ih

theorem Interleave.append_left {α : Type} (blk : List α) {u v w : List α}
    (h : Interleave u v w) : Interleave (blk ++ u) v (blk ++ w) := by
  induction blk with
  | nil => simpa using h
  | cons x blk ih => exact Interleave.left ih

theorem Interleave.append_right {α : Type} (blk : List α) {u v w : List α}
    (h : Interleave u v w) : Interleave u (blk ++ v) (blk ++ w) := by
  induction blk with
  | nil => simpa using h
  | cons x blk ih => exact Interleave.right ih

theorem Interleave.nil_right {α : Type} : ∀ u : List α, Interleave u [] u
  | [] => Interleave.nil
  | _ :: u => Interleave.left (Interleave.nil_right u)

theorem Interleave.nil_left {α : Type} : ∀ v : List α, Interleave [] v v
  | [] => Interleave.nil
  | _ :: v => Interleave.right (Interleave.nil_left v)

theorem Interleave.eq_of_nil_left {α : Type} : ∀ {v w : List α}, Interleave [] v w → w = v := by
  intro v
  induction v with
  | nil => intro w h; cases h with | nil => rfl
  | cons y v ih => intro w h; cases h with | right h' => exact congrArg _ (ih h')

theorem Interleave.eq_of_nil_right {α : Type} : ∀ {u w : List α}, Interleave u [] w → w = u := by
  intro u
  induction u with
  | nil => intro w h; cases h with | nil => rfl
  | cons x u ih => intro w h; cases h with | left h' => exact congrArg _ (ih h')

/-- **Interleavings lift through a projection.**  If the projections of two traces
    interleave to `dm`, then the traces themselves interleave to some trace whose
    projection is `dm`: schedule each invisible label with the side that owns it. -/
theorem Interleave.lift {α β : Type} (f : α → Option β) :
    ∀ (u v : List α) (dm : List β),
      Interleave (u.filterMap f) (v.filterMap f) dm →
      ∃ t, Interleave u v t ∧ t.filterMap f = dm := by
  intro u
  induction u with
  | nil =>
      intro v dm h
      simp only [List.filterMap_nil] at h
      exact ⟨v, Interleave.nil_left v, (Interleave.eq_of_nil_left h).symm⟩
  | cons x u ihu =>
      intro v
      induction v with
      | nil =>
          intro dm h
          exact ⟨x :: u, Interleave.nil_right _,
            (Interleave.eq_of_nil_right h).symm ▸ rfl⟩
      | cons y v ihv =>
          intro dm h
          rcases hx : f x with _ | b
          · rw [List.filterMap_cons_none hx] at h
            obtain ⟨t, ht1, ht2⟩ := ihu (y :: v) dm h
            exact ⟨x :: t, Interleave.left ht1, by
              rw [List.filterMap_cons_none hx]; exact ht2⟩
          · rcases hy : f y with _ | c
            · rw [List.filterMap_cons_none hy] at h
              obtain ⟨t, ht1, ht2⟩ := ihv dm h
              exact ⟨y :: t, Interleave.right ht1, by
                rw [List.filterMap_cons_none hy]; exact ht2⟩
            · rw [List.filterMap_cons_some hx, List.filterMap_cons_some hy] at h
              cases h with
              | @left _ _ _ w h' =>
                  have h'' : Interleave (u.filterMap f) ((y :: v).filterMap f) w := by
                    rw [List.filterMap_cons_some hy]; exact h'
                  obtain ⟨t, ht1, ht2⟩ := ihu (y :: v) w h''
                  exact ⟨x :: t, Interleave.left ht1, by
                    rw [List.filterMap_cons_some hx, ht2]⟩
              | @right _ _ _ w h' =>
                  have h'' : Interleave ((x :: u).filterMap f) (v.filterMap f) w := by
                    rw [List.filterMap_cons_some hx]; exact h'
                  obtain ⟨t, ht1, ht2⟩ := ihv w h''
                  exact ⟨y :: t, Interleave.right ht1, by
                    rw [List.filterMap_cons_some hy, ht2]⟩

/-! ### Running a winning strategy

    A winning strategy is a well-founded tree, so a play can be read off it by
    recursion.  The value supplied at a read is the oracle's, taken at the
    **merged** view -- the strategy wins against every value, so it does not care
    where the value came from. -/

namespace Sec

variable {Level Channel Value : Type}

/-- The values a block of play commits to on the exposed channels are the
    oracle's, each at the merged view that precedes it. -/
def AdvBlk (N : Channel → Prop) (oracle : Channel → List (PLbl Channel Value) → Value)
    (dm blk : List (PLbl Channel Value)) : Prop :=
  ∀ pre e post, blk = pre ++ e :: post → ∀ (a : Channel) (ov : Option Value),
    e = PLbl.inp a ov → N a → e = PLbl.inp a (some (oracle a (dm ++ pre)))

theorem advBlk_nil {N : Channel → Prop} {oracle : Channel → List (PLbl Channel Value) → Value}
    (dm : List (PLbl Channel Value)) : AdvBlk N oracle dm [] := by
  intro pre e post h; exact absurd h.symm (by cases pre <;> simp)

theorem advBlk_cons {N : Channel → Prop}
    {oracle : Channel → List (PLbl Channel Value) → Value}
    {dm : List (PLbl Channel Value)} {e : PLbl Channel Value}
    {blk : List (PLbl Channel Value)}
    (he : ∀ (a : Channel) (ov : Option Value), e = PLbl.inp a ov → N a →
      e = PLbl.inp a (some (oracle a dm)))
    (h : AdvBlk N oracle (dm ++ [e]) blk) : AdvBlk N oracle dm (e :: blk) := by
  intro pre e' post hsplit a ov he' hN
  cases pre with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at hsplit
      rw [← hsplit.1] at he' ⊢
      simpa using he a ov he' hN
  | cons z pre =>
      simp only [List.cons_append, List.cons.injEq] at hsplit
      obtain ⟨hz, hsp⟩ := hsplit
      subst hz
      have := h pre e' post hsp a ov he' hN
      simpa [List.append_assoc] using this

theorem advBlk_append {N : Channel → Prop}
    {oracle : Channel → List (PLbl Channel Value) → Value} :
    ∀ (b₁ : List (PLbl Channel Value)) (dm b₂ : List (PLbl Channel Value)),
      AdvBlk N oracle dm b₁ →
      AdvBlk N oracle (dm ++ b₁) b₂ → AdvBlk N oracle dm (b₁ ++ b₂) := by
  intro b₁
  induction b₁ with
  | nil => intro dm b₂ _ h2; simpa using h2
  | cons e b₁ ih =>
      intro dm b₂ h1 h2
      refine advBlk_cons (fun a ov he hN => ?_) (ih (dm ++ [e]) b₂ ?_ ?_)
      · simpa using h1 [] e b₁ rfl a ov he hN
      · intro pre e' post hsplit a ov he' hN
        have := h1 (e :: pre) e' post (by rw [hsplit]; rfl) a ov he' hN
        simpa [List.append_assoc] using this
      · simpa [List.append_assoc] using h2

/-- Reading a play off a winning strategy. -/
theorem winPlay {N : Channel → Prop} {R : List (PLbl Channel Value) → Prop}
    (oracle : Channel → List (PLbl Channel Value) → Value) :
    ∀ {dn : List (PLbl Channel Value)}
      (_ws : WinStrat N R (fun _ _ _ => True) dn) (dm : List (PLbl Channel Value)),
      ∃ blk, R (dn ++ blk) ∧ AdvBlk N oracle dm blk := by
  intro dn ws
  induction ws with
  | done h => exact fun dm => ⟨[], by simpa using h, advBlk_nil dm⟩
  | @move dn q hq _ ih =>
      intro dm
      obtain ⟨blk, h1, h2⟩ := ih (dm ++ [q])
      refine ⟨q :: blk, by simpa [List.append_assoc] using h1, advBlk_cons ?_ h2⟩
      intro a ov he hN; exact absurd ⟨a, ov, he, hN⟩ hq
  | @read dn a hN _ ih =>
      intro dm
      obtain ⟨blk, h1, h2⟩ := ih (oracle a dm) trivial (dm ++ [PLbl.inp a (some (oracle a dm))])
      refine ⟨PLbl.inp a (some (oracle a dm)) :: blk,
        by simpa [List.append_assoc] using h1, advBlk_cons ?_ h2⟩
      intro a' ov he _
      injection he with ha _; rw [← ha]

theorem ne_self_append_cons {α : Type} (l : List α) (x : α) (r : List α) :
    l ≠ l ++ x :: r := by
  intro h
  have := congrArg List.length h
  simp only [List.length_append, List.length_cons] at this
  omega

/-! ### Running a winning strategy against a schedule

    `key` marks the labels the coalition can already see, by channel.  A layer is
    only usable if the coalition's labels all survive the projection the game
    plays at -- that is the `PresMono` hypothesis below -- and then the play
    itself tells the scheduler when a side has reached its next visible label. -/

/-- Run a side to the end of its play, emitting no label the coalition sees. -/
theorem runEnd {K : Type} {N : Channel → Prop} {R : List (PLbl Channel Value) → Prop}
    (oracle : Channel → List (PLbl Channel Value) → Value)
    (key : PLbl Channel Value → Option K) :
    ∀ {dn : List (PLbl Channel Value)}
      (_ws : WinStrat N R (fun _ _ _ => True) dn) (dm : List (PLbl Channel Value))
      (cA : List K),
      (∀ d, R d → d.filterMap key = cA) → dn.filterMap key = cA →
      ∃ blk, R (dn ++ blk) ∧ blk.filterMap key = [] ∧ AdvBlk N oracle dm blk := by
  intro dn ws
  induction ws with
  | done h => exact fun dm cA _ _ => ⟨[], by simpa using h, rfl, advBlk_nil dm⟩
  | @move dn q hq w ih =>
      intro dm cA hR hdn
      have hq0 : key q = none := by
        rcases hk : key q with _ | k
        · rfl
        · obtain ⟨blk, hb, -⟩ := winPlay oracle w dm
          have := hR _ hb
          rw [List.filterMap_append, List.filterMap_append, hdn,
            List.filterMap_cons_some hk] at this
          exact absurd this (by simpa using ne_self_append_cons cA k (blk.filterMap key))
      obtain ⟨blk, h1, h2, h3⟩ := ih (dm ++ [q]) cA hR
        (by rw [List.filterMap_append, hdn, List.filterMap_cons_none hq0]; simp)
      refine ⟨q :: blk, by simpa [List.append_assoc] using h1,
        by rw [List.filterMap_cons_none hq0]; exact h2, advBlk_cons ?_ h3⟩
      intro a ov he hN; exact absurd ⟨a, ov, he, hN⟩ hq
  | @read dn a hN f ih =>
      intro dm cA hR hdn
      have hq0 : key (PLbl.inp a (some (oracle a dm))) = none := by
        rcases hk : key (PLbl.inp a (some (oracle a dm))) with _ | k
        · rfl
        · obtain ⟨blk, hb, -⟩ := winPlay oracle (f (oracle a dm) trivial) dm
          have := hR _ hb
          rw [List.filterMap_append, List.filterMap_append, hdn,
            List.filterMap_cons_some hk] at this
          exact absurd this (by simpa using ne_self_append_cons cA k (blk.filterMap key))
      obtain ⟨blk, h1, h2, h3⟩ := ih (oracle a dm) trivial
        (dm ++ [PLbl.inp a (some (oracle a dm))]) cA hR
        (by rw [List.filterMap_append, hdn, List.filterMap_cons_none hq0]; simp)
      refine ⟨PLbl.inp a (some (oracle a dm)) :: blk, by simpa [List.append_assoc] using h1,
        by rw [List.filterMap_cons_none hq0]; exact h2, advBlk_cons ?_ h3⟩
      intro a' ov he' _
      injection he' with ha _; rw [← ha]

/-- Run a side until it emits the next label the coalition sees.  It must emit
    exactly the scheduled one: whatever it emits, the play it can still finish
    has the prescribed view. -/
theorem runVis {K : Type} {N : Channel → Prop} {R : List (PLbl Channel Value) → Prop}
    (oracle : Channel → List (PLbl Channel Value) → Value)
    (key : PLbl Channel Value → Option K) :
    ∀ {dn : List (PLbl Channel Value)}
      (_ws : WinStrat N R (fun _ _ _ => True) dn) (dm : List (PLbl Channel Value))
      (cA : List K) (k : K) (rest : List K),
      (∀ d, R d → d.filterMap key = cA ++ k :: rest) → dn.filterMap key = cA →
      ∃ blk, blk.filterMap key = [k] ∧ AdvBlk N oracle dm blk ∧
        Nonempty (WinStrat N R (fun _ _ _ => True) (dn ++ blk)) := by
  intro dn ws
  induction ws with
  | @done dn h =>
      intro dm cA k rest hR hdn
      exact absurd (hdn.symm.trans (hR _ h)) (ne_self_append_cons cA k rest)
  | @move dn q hq w ih =>
      intro dm cA k rest hR hdn
      have hadv : ∀ (a : Channel) (ov : Option Value), q = PLbl.inp a ov → N a →
          q = PLbl.inp a (some (oracle a dm)) := fun a ov he hN => absurd ⟨a, ov, he, hN⟩ hq
      rcases hk : key q with _ | k'
      · obtain ⟨blk, h1, h2, h3⟩ := ih (dm ++ [q]) cA k rest hR
          (by rw [List.filterMap_append, hdn, List.filterMap_cons_none hk]; simp)
        exact ⟨q :: blk, by rw [List.filterMap_cons_none hk]; exact h1,
          advBlk_cons hadv h2, by simpa [List.append_assoc] using h3⟩
      · have hkk : k' = k := by
          obtain ⟨blk, hb, -⟩ := winPlay oracle w (dm ++ [q])
          have hval := hR _ hb
          rw [List.filterMap_append, List.filterMap_append, hdn,
            List.filterMap_cons_some hk] at hval
          have hc : k' = k ∧ blk.filterMap key = rest := by
            simpa [List.append_assoc] using hval
          exact hc.1
        exact ⟨[q], by rw [List.filterMap_cons_some hk, hkk]; rfl,
          advBlk_cons hadv (advBlk_nil _), ⟨w⟩⟩
  | @read dn a hN f ih =>
      intro dm cA k rest hR hdn
      have hadv : ∀ (a' : Channel) (ov : Option Value),
          PLbl.inp a (some (oracle a dm)) = PLbl.inp a' ov → N a' →
          PLbl.inp a (some (oracle a dm)) = PLbl.inp a' (some (oracle a' dm)) := by
        intro a' ov he' _; injection he' with ha _; rw [← ha]
      rcases hk : key (PLbl.inp a (some (oracle a dm))) with _ | k'
      · obtain ⟨blk, h1, h2, h3⟩ := ih (oracle a dm) trivial
          (dm ++ [PLbl.inp a (some (oracle a dm))]) cA k rest hR
          (by rw [List.filterMap_append, hdn, List.filterMap_cons_none hk]; simp)
        exact ⟨PLbl.inp a (some (oracle a dm)) :: blk,
          by rw [List.filterMap_cons_none hk]; exact h1,
          advBlk_cons hadv h2, by simpa [List.append_assoc] using h3⟩
      · have hkk : k' = k := by
          obtain ⟨blk, hb, -⟩ := winPlay oracle (f (oracle a dm) trivial)
            (dm ++ [PLbl.inp a (some (oracle a dm))])
          have hval := hR _ hb
          rw [List.filterMap_append, List.filterMap_append, hdn,
            List.filterMap_cons_some hk] at hval
          have hc : k' = k ∧ blk.filterMap key = rest := by
            simpa [List.append_assoc] using hval
          exact hc.1
        exact ⟨[PLbl.inp a (some (oracle a dm))],
          by rw [List.filterMap_cons_some hk, hkk]; rfl,
          advBlk_cons hadv (advBlk_nil _), ⟨f (oracle a dm) trivial⟩⟩

end Sec

/-! ### Tagged merges

    An interleaving carrying, at each entry, the side it came from.  This is what
    replaces the pattern-plus-length bookkeeping of `Exact.retype`: a tagged merge
    can be pushed through a projection (`push`) by a plain `filterMap`, so the
    merge of the projections is *computed* from the merge of the traces instead of
    being re-derived by counting. -/

namespace Tag

variable {α β : Type}

/-- The entries contributed by one side. -/
def plays (b : Bool) : List (Bool × α) → List α
  | [] => []
  | (c, q) :: x => if c = b then q :: plays b x else plays b x

/-- The pattern of a tagged merge. -/
def sides (x : List (Bool × α)) : List Bool := x.map Prod.fst

/-- The merged list itself. -/
def merged (x : List (Bool × α)) : List α := x.map Prod.snd

/-- Pushing a tagged merge through a projection. -/
def push (h : α → Option β) (x : List (Bool × α)) : List (Bool × β) :=
  x.filterMap (fun e => (h e.2).map (fun q => (e.1, q)))

/-- The tagged merge along a pattern. -/
def tag : List Bool → List α → List α → List (Bool × α)
  | [], _, _ => []
  | true :: p, x :: u, v => (true, x) :: tag p u v
  | false :: p, u, y :: v => (false, y) :: tag p u v
  | true :: _, [], _ => []
  | false :: _, _, [] => []

@[simp] theorem plays_nil (b : Bool) : plays (α := α) b [] = [] := rfl

@[simp] theorem plays_cons_self (b : Bool) (q : α) (x : List (Bool × α)) :
    plays b ((b, q) :: x) = q :: plays b x := by
  simp only [plays, if_pos]

theorem plays_cons_other {b c : Bool} (h : c ≠ b) (q : α) (x : List (Bool × α)) :
    plays b ((c, q) :: x) = plays b x := by
  simp only [plays, if_neg h]

theorem plays_append (b : Bool) (x y : List (Bool × α)) :
    plays b (x ++ y) = plays b x ++ plays b y := by
  induction x with
  | nil => rfl
  | cons e x ih =>
      obtain ⟨c, q⟩ := e
      by_cases hc : c = b
      · subst hc; simp only [List.cons_append, plays_cons_self, ih]
      · simp only [List.cons_append, plays_cons_other hc, ih]

@[simp] theorem push_nil (h : α → Option β) : push h [] = [] := rfl

theorem push_cons_none {h : α → Option β} {q : α} (hq : h q = none) (b : Bool)
    (x : List (Bool × α)) : push h ((b, q) :: x) = push h x := by
  simp only [push, List.filterMap_cons, hq, Option.map_none]

theorem push_cons_some {h : α → Option β} {q : α} {r : β} (hq : h q = some r) (b : Bool)
    (x : List (Bool × α)) : push h ((b, q) :: x) = (b, r) :: push h x := by
  simp only [push, List.filterMap_cons, hq, Option.map_some]

theorem push_append (h : α → Option β) (x y : List (Bool × α)) :
    push h (x ++ y) = push h x ++ push h y := by
  simp only [push, List.filterMap_append]

theorem plays_push (h : α → Option β) (b : Bool) (x : List (Bool × α)) :
    plays b (push h x) = (plays b x).filterMap h := by
  induction x with
  | nil => rfl
  | cons e x ih =>
      obtain ⟨c, q⟩ := e
      rcases hq : h q with _ | r
      · rw [push_cons_none hq, ih]
        by_cases hc : c = b
        · subst hc; rw [plays_cons_self, List.filterMap_cons_none hq]
        · rw [plays_cons_other hc]
      · rw [push_cons_some hq]
        by_cases hc : c = b
        · subst hc; rw [plays_cons_self, plays_cons_self, List.filterMap_cons_some hq, ih]
        · rw [plays_cons_other hc, plays_cons_other hc, ih]

theorem merged_push (h : α → Option β) (x : List (Bool × α)) :
    merged (push h x) = (merged x).filterMap h := by
  induction x with
  | nil => rfl
  | cons e x ih =>
      obtain ⟨c, q⟩ := e
      rcases hq : h q with _ | r
      · rw [push_cons_none hq, ih]
        simp only [merged, List.map_cons, List.filterMap_cons_none hq]
      · rw [push_cons_some hq, merged, List.map_cons, merged, List.map_cons,
          List.filterMap_cons_some hq]
        exact congrArg _ ih

/-- A tagged merge is an interleaving of the two sides. -/
theorem interleave_plays (x : List (Bool × α)) :
    Interleave (plays true x) (plays false x) (merged x) := by
  induction x with
  | nil => exact Interleave.nil
  | cons e x ih =>
      obtain ⟨c, q⟩ := e
      cases c with
      | true =>
          simpa [plays_cons_self, plays_cons_other (by simp : true ≠ false), merged]
            using Interleave.left ih
      | false =>
          simpa [plays_cons_self, plays_cons_other (by simp : false ≠ true), merged]
            using Interleave.right ih

/-- A tagged merge is determined by its pattern and its two sides. -/
theorem eq_of_sides : ∀ (x y : List (Bool × α)), sides x = sides y →
    plays true x = plays true y → plays false x = plays false y → x = y := by
  intro x
  induction x with
  | nil => intro y hs _ _; cases y with
    | nil => rfl
    | cons e y => exact absurd hs (by simp [sides])
  | cons e x ih =>
      intro y hs h1 h2
      cases y with
      | nil => exact absurd hs (by simp [sides])
      | cons f y =>
          obtain ⟨c, q⟩ := e
          obtain ⟨d, r⟩ := f
          have hcd : c = d := by
            simpa [sides] using congrArg List.head? (congrArg id hs)
          subst hcd
          have hs' : sides x = sides y := by
            simp only [sides, List.map_cons, List.cons.injEq] at hs; exact hs.2
          cases c with
          | true =>
              rw [plays_cons_self, plays_cons_self] at h1
              rw [plays_cons_other (by simp), plays_cons_other (by simp)] at h2
              injection h1 with hq h1
              rw [hq, ih y hs' h1 h2]
          | false =>
              rw [plays_cons_self, plays_cons_self] at h2
              rw [plays_cons_other (by simp), plays_cons_other (by simp)] at h1
              injection h2 with hq h2
              rw [hq, ih y hs' h1 h2]

theorem sides_tag : ∀ (p : List Bool) (u v : List α), Exact p u v → sides (tag p u v) = p := by
  intro p
  induction p with
  | nil => intro u v _; rfl
  | cons b p ih =>
      intro u v hE
      cases b with
      | true =>
          cases u with
          | nil => exact absurd hE (by simp [Exact])
          | cons x u => exact congrArg _ (ih u v hE)
      | false =>
          cases v with
          | nil => exact absurd hE (by simp [Exact])
          | cons y v => exact congrArg _ (ih u v hE)

theorem plays_tag : ∀ (p : List Bool) (u v : List α), Exact p u v →
    plays true (tag p u v) = u ∧ plays false (tag p u v) = v := by
  intro p
  induction p with
  | nil => intro u v hE; exact ⟨by rw [hE.1]; rfl, by rw [hE.2]; rfl⟩
  | cons b p ih =>
      intro u v hE
      cases b with
      | true =>
          cases u with
          | nil => exact absurd hE (by simp [Exact])
          | cons x u =>
              obtain ⟨h1, h2⟩ := ih u v hE
              exact ⟨by rw [tag, plays_cons_self, h1],
                     by rw [tag, plays_cons_other (by simp), h2]⟩
      | false =>
          cases v with
          | nil => exact absurd hE (by simp [Exact])
          | cons y v =>
              obtain ⟨h1, h2⟩ := ih u v hE
              exact ⟨by rw [tag, plays_cons_other (by simp), h1],
                     by rw [tag, plays_cons_self, h2]⟩

theorem merged_tag : ∀ (p : List Bool) (u v : List α), merged (tag p u v) = weave p u v := by
  intro p
  induction p with
  | nil => intro u v; rfl
  | cons b p ih =>
      intro u v
      cases b with
      | true =>
          cases u with
          | nil => rfl
          | cons x u => exact congrArg _ (ih u v)
      | false =>
          cases v with
          | nil => rfl
          | cons y v => exact congrArg _ (ih u v)

/-! ### Lifting a tagged merge through a projection -/

def allTag (b : Bool) (u : List α) : List (Bool × α) := u.map (fun q => (b, q))

theorem plays_allTag_self (b : Bool) (u : List α) : plays b (allTag b u) = u := by
  induction u with
  | nil => rfl
  | cons x u ih =>
      simp only [allTag, List.map_cons, plays_cons_self]
      exact congrArg _ ih

theorem plays_allTag_other {b c : Bool} (hbc : c ≠ b) (u : List α) :
    plays b (allTag c u) = [] := by
  induction u with
  | nil => rfl
  | cons x u ih =>
      simp only [allTag, List.map_cons, plays_cons_other hbc]
      exact ih

theorem push_allTag (h : α → Option β) (b : Bool) (u : List α) :
    push h (allTag b u) = allTag b (u.filterMap h) := by
  induction u with
  | nil => rfl
  | cons x u ih =>
      rcases hx : h x with _ | r
      · simp only [allTag, List.map_cons] at *
        rw [push_cons_none hx, ih, List.filterMap_cons_none hx]
      · simp only [allTag, List.map_cons] at *
        rw [push_cons_some hx, ih, List.filterMap_cons_some hx, List.map_cons]

theorem eq_allTag : ∀ {b : Bool} (x : List (Bool × α)), plays (!b) x = [] →
    x = allTag b (plays b x) := by
  intro b x
  induction x with
  | nil => intro _; rfl
  | cons e x ih =>
      obtain ⟨c, q⟩ := e
      intro hx
      by_cases hc : c = b
      · subst hc
        rw [plays_cons_other (by cases c <;> simp)] at hx
        rw [plays_cons_self]
        simp only [allTag, List.map_cons]
        exact congrArg _ (ih hx)
      · have hcb : c = !b := by cases b <;> cases c <;> simp_all
        rw [hcb, plays_cons_self] at hx
        exact absurd hx (by simp)

/-- **A tagged merge of the projections lifts to a tagged merge of the traces.**
    This is what replaces `Exact.retype`: no counting, and no assumption that a
    projection keeps every label. -/
theorem lift_tagged (h : α → Option β) :
    ∀ (tA tB : List α) (dmT : List (Bool × β)),
      plays true dmT = tA.filterMap h → plays false dmT = tB.filterMap h →
      ∃ tT : List (Bool × α),
        plays true tT = tA ∧ plays false tT = tB ∧ push h tT = dmT := by
  intro tA
  induction tA with
  | nil =>
      intro tB dmT h1 h2
      refine ⟨allTag false tB, plays_allTag_other (by simp) tB, plays_allTag_self false tB, ?_⟩
      rw [push_allTag, ← h2]
      exact (eq_allTag (b := false) dmT (by simpa using h1)).symm
  | cons x tA ihA =>
      intro tB
      induction tB with
      | nil =>
          intro dmT h1 h2
          refine ⟨allTag true (x :: tA), plays_allTag_self true _,
            plays_allTag_other (by simp) _, ?_⟩
          rw [push_allTag, ← h1]
          exact (eq_allTag (b := true) dmT (by simpa using h2)).symm
      | cons y tB ihB =>
          intro dmT h1 h2
          rcases hx : h x with _ | r
          · rw [List.filterMap_cons_none hx] at h1
            obtain ⟨tT, k1, k2, k3⟩ := ihA (y :: tB) dmT h1 h2
            exact ⟨(true, x) :: tT, by rw [plays_cons_self, k1],
              by rw [plays_cons_other (by simp), k2], by rw [push_cons_none hx, k3]⟩
          · rcases hy : h y with _ | r'
            · rw [List.filterMap_cons_none hy] at h2
              obtain ⟨tT, k1, k2, k3⟩ := ihB dmT h1 h2
              exact ⟨(false, y) :: tT, by rw [plays_cons_other (by simp), k1],
                by rw [plays_cons_self, k2], by rw [push_cons_none hy, k3]⟩
            · rw [List.filterMap_cons_some hx] at h1
              rw [List.filterMap_cons_some hy] at h2
              cases dmT with
              | nil => exact absurd h1 (by simp)
              | cons e dmT =>
                  obtain ⟨c, q⟩ := e
                  cases c with
                  | true =>
                      rw [plays_cons_self] at h1
                      rw [plays_cons_other (by simp)] at h2
                      injection h1 with hq h1
                      obtain ⟨tT, k1, k2, k3⟩ := ihA (y :: tB) dmT h1
                        (by rw [h2, List.filterMap_cons_some hy])
                      exact ⟨(true, x) :: tT, by rw [plays_cons_self, k1],
                        by rw [plays_cons_other (by simp), k2],
                        by rw [push_cons_some hx, k3, hq]⟩
                  | false =>
                      rw [plays_cons_self] at h2
                      rw [plays_cons_other (by simp)] at h1
                      injection h2 with hq h2
                      obtain ⟨tT, k1, k2, k3⟩ := ihB dmT
                        (by rw [h1, List.filterMap_cons_some hx]) h2
                      exact ⟨(false, y) :: tT, by rw [plays_cons_other (by simp), k1],
                        by rw [plays_cons_self, k2],
                        by rw [push_cons_some hy, k3, hq]⟩

theorem merged_allTag (b : Bool) (u : List α) : merged (allTag b u) = u := by
  induction u with
  | nil => rfl
  | cons x u ih => simp only [allTag, List.map_cons, merged] at *; exact congrArg _ ih

theorem merged_append (x y : List (Bool × α)) :
    merged (x ++ y) = merged x ++ merged y := by
  simp only [merged, List.map_append]

/-- Relabelling a tagged merge, keeping every entry. -/
def mapTag (f : α → β) (x : List (Bool × α)) : List (Bool × β) :=
  x.map (fun e => (e.1, f e.2))

theorem sides_mapTag (f : α → β) (x : List (Bool × α)) : sides (mapTag f x) = sides x := by
  simp only [sides, mapTag, List.map_map]; rfl

theorem plays_mapTag (f : α → β) (b : Bool) (x : List (Bool × α)) :
    plays b (mapTag f x) = (plays b x).map f := by
  induction x with
  | nil => rfl
  | cons e x ih =>
      obtain ⟨c, q⟩ := e
      by_cases hc : c = b
      · subst hc
        simp only [mapTag, List.map_cons, plays_cons_self, List.map_cons]
        exact congrArg _ ih
      · simp only [mapTag, List.map_cons, plays_cons_other hc]
        exact ih

theorem push_push {γ : Type} (h : α → Option β) (g : β → Option γ) (x : List (Bool × α)) :
    push g (push h x) = push (fun q => (h q).bind g) x := by
  induction x with
  | nil => rfl
  | cons e x ih =>
      obtain ⟨c, q⟩ := e
      rcases hq : h q with _ | r
      · rw [push_cons_none hq, ih, push_cons_none (by rw [hq]; rfl)]
      · rcases hr : g r with _ | z
        · rw [push_cons_some hq, push_cons_none hr, ih,
            push_cons_none (by rw [hq]; exact hr)]
        · rw [push_cons_some hq, push_cons_some hr, ih,
            push_cons_some (by rw [hq]; exact hr)]

theorem exact_sides : ∀ x : List (Bool × α), Exact (sides x) (plays true x) (plays false x) := by
  intro x
  induction x with
  | nil => exact ⟨rfl, rfl⟩
  | cons e x ih =>
      obtain ⟨c, q⟩ := e
      cases c with
      | true =>
          rw [sides, List.map_cons, plays_cons_self, plays_cons_other (by simp)]
          exact ih
      | false =>
          rw [sides, List.map_cons, plays_cons_self, plays_cons_other (by simp)]
          exact ih

theorem weave_sides : ∀ x : List (Bool × α),
    weave (sides x) (plays true x) (plays false x) = merged x := by
  intro x
  induction x with
  | nil => rfl
  | cons e x ih =>
      obtain ⟨c, q⟩ := e
      cases c with
      | true =>
          rw [sides, List.map_cons, plays_cons_self, plays_cons_other (by simp), weave]
          exact congrArg _ ih
      | false =>
          rw [sides, List.map_cons, plays_cons_self, plays_cons_other (by simp), weave]
          exact congrArg _ ih

theorem push_congr_on {h g : α → Option β} :
    ∀ x : List (Bool × α), (∀ e ∈ x, h e.2 = g e.2) → push h x = push g x := by
  intro x
  induction x with
  | nil => intro _; rfl
  | cons e x ih =>
      intro hx
      obtain ⟨c, q⟩ := e
      have hq : h q = g q := hx (c, q) (by simp)
      rcases hh : h q with _ | r
      · rw [push_cons_none hh, push_cons_none (by rw [← hq]; exact hh),
          ih (fun e he => hx e (by simp [he]))]
      · rw [push_cons_some hh, push_cons_some (by rw [← hq]; exact hh),
          ih (fun e he => hx e (by simp [he]))]

theorem mem_plays : ∀ (x : List (Bool × α)) {e : Bool × α}, e ∈ x → e.2 ∈ plays e.1 x := by
  intro x
  induction x with
  | nil => intro e he; exact absurd he (by simp)
  | cons f x ih =>
      intro e he
      obtain ⟨c, q⟩ := f
      rcases List.mem_cons.mp he with rfl | he'
      · rw [plays_cons_self]; simp
      · by_cases hc : c = e.1
        · rw [hc, plays_cons_self]; exact List.mem_cons.mpr (Or.inr (ih he'))
        · rw [plays_cons_other hc]; exact ih he'

end Tag

/-! ### The joint play

    The two winning strategies are played together, scheduled by the coalition's
    own view: when the pattern says `A`, side `A` runs until it emits the label
    the coalition expects next, and then it is `B`'s turn.  A side cannot stop
    early, because the play it can still finish has to produce the whole of its
    prescribed view.  Nothing is aligned by counting: the schedule is recorded as
    a tagged merge, and the coalition's view of it is obtained by a `filterMap`. -/

namespace Sec

variable {Level Channel Value : Type}

theorem jointPlay {K : Type} {N : Channel → Prop}
    {RA RB : List (PLbl Channel Value) → Prop}
    (oracle : Channel → List (PLbl Channel Value) → Value)
    (key : PLbl Channel Value → Option K) :
    ∀ (pT : List (Bool × K)) (dnA dnB dm : List (PLbl Channel Value)) (cA cB : List K),
      Nonempty (WinStrat N RA (fun _ _ _ => True) dnA) →
      Nonempty (WinStrat N RB (fun _ _ _ => True) dnB) →
      (∀ d, RA d → d.filterMap key = cA ++ Tag.plays true pT) →
      (∀ d, RB d → d.filterMap key = cB ++ Tag.plays false pT) →
      dnA.filterMap key = cA → dnB.filterMap key = cB →
      ∃ blkT : List (Bool × PLbl Channel Value),
        RA (dnA ++ Tag.plays true blkT) ∧ RB (dnB ++ Tag.plays false blkT) ∧
        Tag.push key blkT = pT ∧ AdvBlk N oracle dm (Tag.merged blkT) := by
  intro pT
  induction pT with
  | nil =>
      intro dnA dnB dm cA cB ⟨wsA⟩ ⟨wsB⟩ hRA hRB hdnA hdnB
      obtain ⟨blkA, hA1, hA2, hA3⟩ := runEnd oracle key wsA dm cA
        (by simpa using hRA) hdnA
      obtain ⟨blkB, hB1, hB2, hB3⟩ := runEnd oracle key wsB (dm ++ blkA) cB
        (by simpa using hRB) hdnB
      refine ⟨Tag.allTag true blkA ++ Tag.allTag false blkB, ?_, ?_, ?_, ?_⟩
      · rw [Tag.plays_append, Tag.plays_allTag_self, Tag.plays_allTag_other (by simp)]
        simpa using hA1
      · rw [Tag.plays_append, Tag.plays_allTag_other (by simp), Tag.plays_allTag_self]
        simpa using hB1
      · rw [Tag.push_append, Tag.push_allTag, Tag.push_allTag, hA2, hB2]; rfl
      · rw [Tag.merged_append, Tag.merged_allTag, Tag.merged_allTag]
        exact advBlk_append blkA dm blkB hA3 hB3
  | cons e pT ih =>
      obtain ⟨b, k⟩ := e
      cases b with
      | true =>
          intro dnA dnB dm cA cB ⟨wsA⟩ hwB hRA hRB hdnA hdnB
          obtain ⟨blkA, hA1, hA2, hA3⟩ := runVis oracle key wsA dm cA k
            (Tag.plays true pT) (by simpa using hRA) hdnA
          obtain ⟨blkT, k1, k2, k3, k4⟩ := ih (dnA ++ blkA) dnB (dm ++ blkA)
            (cA ++ [k]) cB hA3 hwB
            (fun d hd => by rw [hRA d hd]; simp) (by simpa [Tag.plays] using hRB)
            (by rw [List.filterMap_append, hdnA, hA1]) hdnB
          refine ⟨Tag.allTag true blkA ++ blkT, ?_, ?_, ?_, ?_⟩
          · rw [Tag.plays_append, Tag.plays_allTag_self]
            simpa [List.append_assoc] using k1
          · rw [Tag.plays_append, Tag.plays_allTag_other (by simp), List.nil_append]
            exact k2
          · rw [Tag.push_append, Tag.push_allTag, hA1, k3]; rfl
          · rw [Tag.merged_append, Tag.merged_allTag]
            exact advBlk_append blkA dm _ hA2 k4
      | false =>
          intro dnA dnB dm cA cB hwA ⟨wsB⟩ hRA hRB hdnA hdnB
          obtain ⟨blkB, hB1, hB2, hB3⟩ := runVis oracle key wsB dm cB k
            (Tag.plays false pT) (by simpa using hRB) hdnB
          obtain ⟨blkT, k1, k2, k3, k4⟩ := ih dnA (dnB ++ blkB) (dm ++ blkB)
            cA (cB ++ [k]) hwA hB3
            (by simpa [Tag.plays] using hRA) (fun d hd => by rw [hRB d hd]; simp)
            hdnA (by rw [List.filterMap_append, hdnB, hB1])
          refine ⟨Tag.allTag false blkB ++ blkT, ?_, ?_, ?_, ?_⟩
          · rw [Tag.plays_append, Tag.plays_allTag_other (by simp), List.nil_append]
            exact k1
          · rw [Tag.plays_append, Tag.plays_allTag_self]
            simpa [List.append_assoc] using k2
          · rw [Tag.push_append, Tag.push_allTag, hB1, k3]; rfl
          · rw [Tag.merged_append, Tag.merged_allTag]
            exact advBlk_append blkB dm _ hB2 k4

end Sec

end InteractiveNI
