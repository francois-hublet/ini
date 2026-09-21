/-
  **A flat peeling always exists; a presence-monotone one does not.**

  Two incomparable levels `Ob` and `Hi`, one channel at each, and the high
  channel's *presence* secret.  A flat peeling exists here, as it does
  everywhere (`peelable_of_finite`).  A presence-monotone one does not: the low
  channel is invisible at `C⁺(Ob)`, so the peeling has to add `Ob`; but `Hi` is
  already in `C⁺(Ob)`, so at that layer the coalition can already detect the high
  channel's presence, and presence-monotonicity would ask for `Hi ⊑ Ob`.

  This is what separates clause (iii) of the peeling from clauses (i) and (ii).
-/
import InteractiveNI.PeelExists
import InteractiveNI.LayerStepW

namespace InteractiveNI

namespace NoPeelMono

open Classical
attribute [local instance] Classical.propDecidable

/-- Two incomparable levels. -/
inductive L where | Ob | Hi
deriving DecidableEq

inductive Ch where | pub | sec
deriving DecidableEq

/-- The high channel's presence is secret: `ℓ₂(sec) = Hi`. -/
def Sc : Sec L Ch where
  le := fun x y => x = y
  le_refl := fun _ => rfl
  le_trans := fun h₁ h₂ => h₁.trans h₂
  presL := fun c => match c with | .pub => L.Ob | .sec => L.Hi
  valL := fun c => match c with | .pub => L.Ob | .sec => L.Hi
  pres_le_val := fun c => by cases c <;> rfl

theorem not_pub : ¬ Sec.PublicPresence Sc := by
  intro h
  exact L.noConfusion (h Ch.sec L.Ob)

/-- A flat peeling exists, as everywhere. -/
theorem peelable : ∀ m : L, Sec.Peelable Sc m :=
  Sec.peelable_of_finite [Ch.pub, Ch.sec] (fun a => by cases a <;> simp)

theorem hi_cplus : Sec.Cplus Sc L.Ob L.Hi := fun h => L.noConfusion h

theorem ob_not_cplus : ¬ Sec.Cplus Sc L.Ob L.Ob := by intro h; exact h rfl

/-- **No presence-monotone peeling exists at `Ob`.** -/
theorem not_peelableM : ¬ Sec.PeelableM Sc L.Ob [L.Ob, L.Hi] := by
  rintro ⟨ns, hfull, -, hmono⟩
  -- the low channel must be made visible, and only `Ob` can do it
  obtain ⟨d, hd, hle⟩ := hfull Ch.pub (by left) (Sc.valL Ch.pub) rfl
  have hdOb : d = L.Ob := hle.symm
  subst hdOb
  have hmem : L.Ob ∈ ns := by
    rcases Sec.layerC_inv ns L.Ob hd with h | h
    · exact absurd h ob_not_cplus
    · exact h
  -- at that layer the coalition already sees the high channel's presence
  obtain ⟨ns', hpres⟩ := Sec.peelMono_mem ns hmono L.Ob hmem
  have hvis : Sc.coalition.le (Sec.sing (Sc.presL Ch.sec)) (Sec.layerC Sc L.Ob ns') :=
    fun c hc => ⟨L.Hi, Sec.layerC_of_cplus ns' L.Hi hi_cplus,
      by rw [show c = L.Hi from hc]; rfl⟩
  exact L.noConfusion (hpres Ch.sec (by right; left) hvis)

end NoPeelMono

end InteractiveNI
