import TwoAxisHelicoid.HarmonicTorusC1Normalization
import TwoAxisHelicoid.MeromorphicSpatialOrientation

namespace TwoAxisHelicoid
open Complex

/-- The two meromorphic double-pole orders on an actual two-axis harmonic
conformal torus immersion imply full C¹ helicoidal asymptotics. The actual
height and Gauss classification, both ambient reflection choices, all
integer branches, thinness and the global graph are joined here.
The original surface's conformal compactification and pole orders remain
separate geometric obligations. -/
theorem harmonic_meromorphic_torus_C1_helicoidal_end {t : ℝ} (ht : 0 < t)
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hhOrder : meromorphicOrderAt
      (fun z => puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2) 0 = (-2 : ℤ))
    (hgOrder : meromorphicOrderAt (fun z =>
      deriv (fun w => nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X w)) z /
        nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)) 0 = (-2 : ℤ)) :
    HasHelicoidalC1End (harmonicTorusImmersion hX) := by
  obtain ⟨a,c,m,R,ha,hc,_htu,_haB,hR,hY,hh,hg⟩ :=
    harmonic_meromorphic_oriented_integer_data ht hX hhOrder hgOrder
  have hEnd := harmonic_integer_data_hasHelicoidalC1End ht ha hc m hY hh hg
  rw [harmonicTorusImmersion_space_map hX R hY] at hEnd
  exact HasHelicoidalC1End.of_isometry R hR hEnd

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_meromorphic_torus_C1_helicoidal_end
