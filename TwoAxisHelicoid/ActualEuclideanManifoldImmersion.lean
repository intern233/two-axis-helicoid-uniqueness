import TwoAxisHelicoid.ActualTorusManifoldDifferential
import TwoAxisHelicoid.ActualTorusProperness
import TwoAxisHelicoid.NullEuclideanMetric
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold
set_option maxHeartbeats 1000000

noncomputable def actualEuclideanPuncturedTorusImmersion {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    PuncturedPeriodTorus (rhombicPeriodPair t ht) → EuclideanSpace ℝ (Fin 3) :=
  fun q => coordinateToEuclidean (actualTorusImmersion ht ha hc hG hH q.1)

theorem actualEuclideanPuncturedTorusImmersion_contMDiff {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ω
      (actualEuclideanPuncturedTorusImmersion ht ha hc hG hH) :=
  coordinateToEuclidean.contMDiff.comp (actualPuncturedTorusImmersion_contMDiff ht ha hc hG hH)

theorem actualEuclideanPuncturedTorusImmersion_hasMFDerivAt {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0)
    (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) :
    HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      (actualEuclideanPuncturedTorusImmersion ht ha hc hG hH) q
      (coordinateToEuclidean.comp (nullRealDerivative (coordinateData t a c ht (chartAt ℂ q q)))) := by
  exact coordinateToEuclidean.hasFDerivAt.hasMFDerivAt.comp q
    (actualPuncturedTorusImmersion_hasMFDerivAt ht ha hc hG hH q)

theorem actualEuclideanPuncturedTorusImmersion_mvfderiv_injective {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0)
    (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) :
    Function.Injective (mvfderiv 𝓘(ℝ, ℂ)
      (actualEuclideanPuncturedTorusImmersion ht ha hc hG hH) q) := by
  have hm : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      (actualEuclideanPuncturedTorusImmersion ht ha hc hG hH) q) := by
    rw [(actualEuclideanPuncturedTorusImmersion_hasMFDerivAt ht ha hc hG hH q).mfderiv]
    have hz := puncturedPeriodTorus_chart_not_lattice (rhombicPeriodPair t ht) q
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective.comp
      (nullRealDerivative_injective (coordinateData_null ht ha hz) (coordinateData_ne_zero ht ha hc hz))
  exact (NormedSpace.fromTangentSpace _).injective.comp hm

theorem actualEuclideanPuncturedTorusImmersion_isProperMap {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    IsProperMap (actualEuclideanPuncturedTorusImmersion ht ha hc hG hH) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isProperMap.comp
    (actualTorusImmersion_isProperMap ht ha hc hG hH)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualEuclideanPuncturedTorusImmersion_mvfderiv_injective
#print axioms TwoAxisHelicoid.actualEuclideanPuncturedTorusImmersion_isProperMap
