import TwoAxisHelicoid.ActualPrimitiveEndEscape
import TwoAxisHelicoid.QuotientPunctureEscape
import TwoAxisHelicoid.ActualTorusImmersion
import TwoAxisHelicoid.EmbeddedTorusAxesNormalization

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology

/-- The explicit torus immersion is spatially proper. Period closure is
used to define the map on the quotient; escape is proved from its actual
Weierstrass data. Embeddedness is not an input or a conclusion. -/
theorem actualTorusImmersion_isProperMap {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    IsProperMap (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
      actualTorusImmersion ht ha hc hG hH q.1) := by
  let L := rhombicPeriodPair t ht
  let := periodTorus_compactSpace L
  let := periodTorus_t2Space L
  have hd : HasTwoAxisHelicoidCoordinateDifferential (actualGlobalImmersion t a c ht) t a c ht :=
    fun z hz => ((actual_global_conformal_harmonic_immersion ht ha hc hG hH).2.2.2 z hz).1
  apply compact_puncture_map_isProperMap
  · intro q hq
    obtain ⟨z,hz⟩ := Quotient.exists_rep q
    have hproj : periodTorusProjection L z = q := hz
    have hzn : z ∉ L.lattice := by
      intro h
      exact hq (hproj.symm.trans ((periodTorusProjection_eq_zero L z).mpr h))
    have hcont := periodTorusLift_continuousAt L (actualGlobalImmersion t a c ht)
      (actualGlobalImmersion_add_lattice ht ha hc hG hH) (hd z hzn).continuousAt
    simpa only [hproj,actualTorusImmersion] using hcont
  · exact periodTorusLift_puncture_escape L (actualGlobalImmersion_add_lattice ht ha hc hG hH)
      (actual_coordinate_primitive_end_escape ht ha hc hd)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualTorusImmersion_isProperMap
