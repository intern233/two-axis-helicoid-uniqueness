import TwoAxisHelicoid.ThetaJointContinuity
import TwoAxisHelicoid.RootVerticalBranch
import Mathlib.Topology.Maps.Proper.Basic

namespace TwoAxisHelicoid
open Set
attribute [local irreducible] thetaG thetaJet thetaTerm thetaQuotient

abbrev RootHeight := Icc (rootTLower : ℝ) rootTUpper
abbrev RootAbscissa := Icc (rootALower : ℝ) rootAUpper

@[irreducible] noncomputable def rootVerticalA (t : RootHeight) : RootAbscissa :=
  let h := existsUnique_root_vertical_zero t.property.1 t.property.2
  ⟨h.choose, ⟨h.choose_spec.1.1.1.le, h.choose_spec.1.1.2.le⟩⟩

theorem rootVerticalA_spec (t : RootHeight) :
    (rootVerticalA t : ℝ) ∈ Ioo (rootALower : ℝ) rootAUpper ∧
      thetaG t (rootVerticalA t) = 0 := by
  unfold rootVerticalA
  exact (existsUnique_root_vertical_zero t.property.1 t.property.2).choose_spec.1

theorem rootVerticalA_continuous : Continuous rootVerticalA := by
  let : CompactSpace RootAbscissa := isCompact_iff_compactSpace.mp isCompact_Icc
  have hm : Continuous (fun p : RootHeight × RootAbscissa => ((p.1 : ℝ), (p.2 : ℝ))) := by
    fun_prop
  have hx : ∀ p : RootHeight × RootAbscissa, ((p.1 : ℝ), (p.2 : ℝ)) ∈ rootRectangle := by
    intro p
    exact ⟨p.1.property, p.2.property⟩
  have hc : Continuous (fun p : RootHeight × RootAbscissa => thetaG p.1 p.2) :=
    thetaG_rootRectangle_continuousOn.comp_continuous hm hx
  apply continuous_of_isClosed_graph (f := rootVerticalA)
  have he : rootVerticalA.graph = {p : RootHeight × RootAbscissa | thetaG p.1 p.2 = 0} := by
    ext p
    change (rootVerticalA p.1 = p.2) ↔ thetaG p.1 p.2 = 0
    constructor
    · intro h
      rw [← h]
      exact (rootVerticalA_spec p.1).2
    · intro h
      apply Subtype.ext
      apply (root_vertical_strictAnti p.1.property.1 p.1.property.2).injOn
        (rootVerticalA p.1).property p.2.property
      change (thetaG p.1 (rootVerticalA p.1)).re = (thetaG p.1 p.2).re
      rw [(rootVerticalA_spec p.1).2, h]
  rw [he]
  exact isClosed_eq hc continuous_const

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rootVerticalA_continuous
