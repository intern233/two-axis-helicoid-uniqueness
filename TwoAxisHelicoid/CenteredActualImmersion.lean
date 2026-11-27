import TwoAxisHelicoid.ActualMeanCurvature
import TwoAxisHelicoid.ActualEuclideanManifoldImmersion
import TwoAxisHelicoid.ActualCompleteAxes

namespace TwoAxisHelicoid
open Complex Matrix Set Filter InnerProductSpace
open scoped Topology ContDiff Manifold
set_option maxHeartbeats 1000000

/-- Center the actual primitive at the intersection of its two axes. -/
noncomputable def centeredActualPrimitive (t a c : ℝ) (ht : 0 < t) : ℂ → Fin 3 → ℝ :=
  fun z => actualGlobalImmersion t a c ht z-actualGlobalImmersion t a c ht 1

noncomputable def centeredActualTorusImmersion {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    PuncturedPeriodTorus (rhombicPeriodPair t ht) → Fin 3 → ℝ :=
  fun q => actualTorusImmersion ht ha hc hG hH q.1-actualGlobalImmersion t a c ht 1

noncomputable def centeredActualEuclideanImmersion {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    PuncturedPeriodTorus (rhombicPeriodPair t ht) → EuclideanSpace ℝ (Fin 3) :=
  coordinateToEuclidean ∘ centeredActualTorusImmersion ht ha hc hG hH

theorem centeredActualPrimitive_hasFDerivAt {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    HasFDerivAt (centeredActualPrimitive t a c ht) (nullRealDerivative (coordinateData t a c ht z)) z :=
  (((actual_global_conformal_harmonic_immersion ht ha hc hG hH).2.2.2 z hz).1).sub_const _

theorem centeredActualPrimitive_mean_curvature_zero {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    coordinateMeanCurvature (centeredActualPrimitive t a c ht) z = 0 := by
  have h := actual_global_conformal_harmonic_immersion ht ha hc hG hH
  have hh : HarmonicAt (centeredActualPrimitive t a c ht) z :=
    (h.2.2.1 z hz).sub (harmonicAt_const _)
  have hd := (centeredActualPrimitive_hasFDerivAt ht ha hc hG hH hz).fderiv
  have he : fderiv ℝ (centeredActualPrimitive t a c ht) z =
      fderiv ℝ (actualGlobalImmersion t a c ht) z := hd.trans ((h.2.2.2 z hz).1).fderiv.symm
  have hg := (h.2.2.2 z hz).2.2
  apply conformal_harmonic_coordinate_mean_curvature_zero hh
    (g := nullMetric (coordinateData t a c ht z))
  · simpa only [he,dotProduct,pow_two] using hg.2.1
  · simpa only [he,dotProduct,pow_two] using hg.2.2.1
  · simpa only [he,dotProduct] using hg.2.2.2

theorem centeredActualTorusImmersion_contMDiff {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 3 → ℝ) ω (centeredActualTorusImmersion ht ha hc hG hH) :=
  (actualPuncturedTorusImmersion_contMDiff ht ha hc hG hH).sub contMDiff_const

theorem centeredActualTorusImmersion_hasMFDerivAt {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) :
    HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 3 → ℝ) (centeredActualTorusImmersion ht ha hc hG hH) q
      (nullRealDerivative (coordinateData t a c ht (chartAt ℂ q q))) := by
  have hd : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 3 → ℝ)
      (centeredActualTorusImmersion ht ha hc hG hH) q
      (nullRealDerivative (coordinateData t a c ht (chartAt ℂ q q))-(0 : ℂ →L[ℝ] (Fin 3 → ℝ))) :=
    (actualPuncturedTorusImmersion_hasMFDerivAt ht ha hc hG hH q).sub
      (hasMFDerivAt_const (actualGlobalImmersion t a c ht 1) q)
  simpa only [sub_zero] using hd

theorem centeredActualTorusImmersion_isDiffImmersionAt {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) :
    IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 3 → ℝ) (centeredActualTorusImmersion ht ha hc hG hH) q := by
  apply IsDiffImmersionAt.of_injective_of_finiteDimensional
  rw [(centeredActualTorusImmersion_hasMFDerivAt ht ha hc hG hH q).mfderiv]
  have hz := puncturedPeriodTorus_chart_not_lattice (rhombicPeriodPair t ht) q
  exact nullRealDerivative_injective (coordinateData_null ht ha hz) (coordinateData_ne_zero ht ha hc hz)

theorem centeredActualTorusImmersion_isProperMap {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) : IsProperMap (centeredActualTorusImmersion ht ha hc hG hH) := by
  exact (Homeomorph.addRight (-actualGlobalImmersion t a c ht 1)).isProperMap.comp
    (actualTorusImmersion_isProperMap ht ha hc hG hH)

theorem centeredActualTorusImmersion_contains_axes {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    (∀ r : ℝ, ∃ q, centeredActualTorusImmersion ht ha hc hG hH q = ![r,0,0]) ∧
    (∀ r : ℝ, ∃ q, centeredActualTorusImmersion ht ha hc hG hH q = ![0,0,r]) := by
  have hd : HasTwoAxisHelicoidCoordinateDifferential (actualGlobalImmersion t a c ht) t a c ht :=
    fun z hz => ((actual_global_conformal_harmonic_immersion ht ha hc hG hH).2.2.2 z hz).1
  have h := actual_primitive_contains_complete_axes ht ha hc hd
  constructor
  · intro r
    obtain ⟨z,hz,he⟩ := h.1 r
    exact ⟨⟨periodTorusProjection (rhombicPeriodPair t ht) z,
      fun h => hz ((periodTorusProjection_eq_zero _ _).mp h)⟩,he⟩
  · intro r
    obtain ⟨z,hz,he⟩ := h.2 r
    exact ⟨⟨periodTorusProjection (rhombicPeriodPair t ht) z,
      fun h => hz ((periodTorusProjection_eq_zero _ _).mp h)⟩,he⟩

theorem centeredActualEuclideanImmersion_contMDiff {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ω
      (centeredActualEuclideanImmersion ht ha hc hG hH) :=
  coordinateToEuclidean.contMDiff.comp (centeredActualTorusImmersion_contMDiff ht ha hc hG hH)

theorem centeredActualEuclideanImmersion_hasMFDerivAt {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) :
    HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      (centeredActualEuclideanImmersion ht ha hc hG hH) q
      (coordinateToEuclidean.comp (nullRealDerivative (coordinateData t a c ht (chartAt ℂ q q)))) :=
  coordinateToEuclidean.hasFDerivAt.hasMFDerivAt.comp q
    (centeredActualTorusImmersion_hasMFDerivAt ht ha hc hG hH q)

theorem centeredActualEuclideanImmersion_mvfderiv_injective {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) :
    Function.Injective (mvfderiv 𝓘(ℝ, ℂ) (centeredActualEuclideanImmersion ht ha hc hG hH) q) := by
  have hm : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      (centeredActualEuclideanImmersion ht ha hc hG hH) q) := by
    rw [(centeredActualEuclideanImmersion_hasMFDerivAt ht ha hc hG hH q).mfderiv]
    have hz := puncturedPeriodTorus_chart_not_lattice (rhombicPeriodPair t ht) q
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective.comp
      (nullRealDerivative_injective (coordinateData_null ht ha hz) (coordinateData_ne_zero ht ha hc hz))
  exact (NormedSpace.fromTangentSpace _).injective.comp hm

theorem centeredActualEuclideanImmersion_isProperMap {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) : IsProperMap (centeredActualEuclideanImmersion ht ha hc hG hH) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isProperMap.comp
    (centeredActualTorusImmersion_isProperMap ht ha hc hG hH)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.centeredActualPrimitive_mean_curvature_zero
#print axioms TwoAxisHelicoid.centeredActualTorusImmersion_contains_axes
#print axioms TwoAxisHelicoid.centeredActualEuclideanImmersion_mvfderiv_injective
