import TwoAxisHelicoid.RhombicGlobalPrimitiveRegularity
import TwoAxisHelicoid.OriginalHeightPeriod
import TwoAxisHelicoid.HolomorphicNullImmersion

namespace TwoAxisHelicoid
open Complex Set Filter InnerProductSpace
open scoped Topology
set_option maxHeartbeats 1200000
attribute [local irreducible] coordinateData

/-- The actual global real primitive of the three manuscript coordinate
forms, constructed using only the two primitive closing integrals. -/
noncomputable def actualGlobalImmersion (t a c : ℝ) (ht : 0 < t) (z : ℂ) : Fin 3 → ℝ :=
  fun j => rhombicGlobalRealPrimitive t (fun w => coordinateData t a c ht w j) z

theorem actualGlobalImmersion_scalar_conditions {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) (j : Fin 3) :
    (∀ z ∉ (rhombicPeriodPair t ht).lattice, AnalyticAt ℂ (fun w => coordinateData t a c ht w j) z) ∧
    (∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice →
      coordinateData t a c ht (z+ω) j = coordinateData t a c ht z j) ∧
    (rhombicDownPeriod t (fun w => coordinateData t a c ht w j)).re = 0 ∧
    (rhombicUpPeriod t (fun w => coordinateData t a c ht w j)).re = 0 := by
  have hperiod := (original_all_generators_close_iff ht
    (show a ∈ Ioo (0 : ℝ) 2 from ⟨ha.1,by linarith [ha.2]⟩) hc).mpr ⟨hG,hH⟩
  refine ⟨?_,?_,(hperiod j).1,(hperiod j).2⟩
  · intro z hz
    exact ((ContinuousLinearMap.proj j : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt _).comp
      (coordinateData_analyticAt ht hz)
  · intro z ω hω
    exact congrFun (coordinateData_add_lattice ht z (⟨ω,hω⟩ : (rhombicPeriodPair t ht).lattice)) j

theorem actualGlobalImmersion_add_lattice {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) (z ω : ℂ)
    (hω : ω ∈ (rhombicPeriodPair t ht).lattice) :
    actualGlobalImmersion t a c ht (z+ω) = actualGlobalImmersion t a c ht z := by
  funext j
  obtain ⟨hf,hp,hd,hu⟩ := actualGlobalImmersion_scalar_conditions ht ha hc hG hH j
  exact rhombicGlobalRealPrimitive_add_lattice ht hf hp hd hu z ω hω

theorem actualGlobalImmersion_local_holomorphic {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    ∃ F : ℂ → Fin 3 → ℂ, AnalyticAt ℂ F z ∧ HasDerivAt F (coordinateData t a c ht z) z ∧
      actualGlobalImmersion t a c ht =ᶠ[𝓝 z] fun w => coordinateRealPart (F w) := by
  have hj (j : Fin 3) : ∃ G : ℂ → ℂ, AnalyticAt ℂ G z ∧
      HasDerivAt G (coordinateData t a c ht z j) z ∧
      (fun w => actualGlobalImmersion t a c ht w j) =ᶠ[𝓝 z] fun w => (G w).re := by
    obtain ⟨hf,hp,hd,hu⟩ := actualGlobalImmersion_scalar_conditions ht ha hc hG hH j
    exact rhombicGlobalRealPrimitive_local_holomorphic ht hf hp hd hu hz
  choose G hGa hGD hEq using hj
  refine ⟨fun w j => G j w,AnalyticAt.pi hGa,hasDerivAt_pi.mpr hGD,?_⟩
  filter_upwards [Filter.eventually_all.mpr hEq] with w hw
  funext j
  exact hw j

/-- Global periodicity and the local Weierstrass equations are established
for one actual map on the entire lattice complement, including the finite
Gauss zeros and poles. This does not assert embeddedness. -/
theorem actual_global_conformal_harmonic_immersion {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    (∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice →
      actualGlobalImmersion t a c ht (z+ω) = actualGlobalImmersion t a c ht z) ∧
    AnalyticOnNhd ℝ (actualGlobalImmersion t a c ht) (rhombicPeriodPair t ht).latticeᶜ ∧
    HarmonicOnNhd (actualGlobalImmersion t a c ht) (rhombicPeriodPair t ht).latticeᶜ ∧
    ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      HasFDerivAt (actualGlobalImmersion t a c ht) (nullRealDerivative (coordinateData t a c ht z)) z ∧
      Function.Injective (fderiv ℝ (actualGlobalImmersion t a c ht) z) ∧
      0 < nullMetric (coordinateData t a c ht z) ∧
      (∑ j, (fderiv ℝ (actualGlobalImmersion t a c ht) z 1 j)^2) = nullMetric (coordinateData t a c ht z) ∧
      (∑ j, (fderiv ℝ (actualGlobalImmersion t a c ht) z I j)^2) = nullMetric (coordinateData t a c ht z) ∧
      (∑ j, fderiv ℝ (actualGlobalImmersion t a c ht) z 1 j*
        fderiv ℝ (actualGlobalImmersion t a c ht) z I j) = 0 := by
  have hloc (z : ℂ) (hz : z ∉ (rhombicPeriodPair t ht).lattice) :=
    actualGlobalImmersion_local_holomorphic ht ha hc hG hH hz
  refine ⟨actualGlobalImmersion_add_lattice ht ha hc hG hH,?_,?_,?_⟩
  · intro z hz
    obtain ⟨F,hFa,_,he⟩ := hloc z hz
    exact ((coordinateRealPart.analyticAt (F z)).comp (hFa.restrictScalars (𝕜 := ℝ))).congr he.symm
  · intro z hz
    obtain ⟨F,hFa,_,he⟩ := hloc z hz
    exact (harmonicAt_congr_nhds he).mpr (hFa.harmonicAt.comp_CLM coordinateRealPart)
  · intro z hz
    obtain ⟨F,_,hFd,he⟩ := hloc z hz
    have hD := (realPart_primitive_hasFDerivAt hFd).congr_of_eventuallyEq he
    refine ⟨hD,?_,?_⟩
    · rw [hD.fderiv]
      exact nullRealDerivative_injective (coordinateData_null ht ha hz) (coordinateData_ne_zero ht ha hc hz)
    · simp only [hD.fderiv]
      exact nullRealDerivative_conformal (coordinateData_null ht ha hz) (coordinateData_ne_zero ht ha hc hz)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_global_conformal_harmonic_immersion
