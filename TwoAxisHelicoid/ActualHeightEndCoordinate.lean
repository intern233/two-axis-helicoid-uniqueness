import TwoAxisHelicoid.ActualHeightInverse
import TwoAxisHelicoid.ActualGaussHeightCorrection
import TwoAxisHelicoid.HeightCoordinateChange
import TwoAxisHelicoid.HeightEndProper

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology

theorem puncture_eventually_avoids_height_zeros {t a : ℝ} (ht : 0 < t) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ (rhombicPeriodPair t ht).lattice ∧
      z-a ∉ (rhombicPeriodPair t ht).lattice ∧ z+a ∉ (rhombicPeriodPair t ht).lattice := by
  have hm := latticePoleSet_punctured_avoids (rhombicPeriodPair t ht) (finite_singleton (a : ℂ)) 0
  have hp := latticePoleSet_punctured_avoids (rhombicPeriodPair t ht) (finite_singleton (-(a : ℂ))) 0
  filter_upwards [rhombic_puncture_eventually_off_lattice ht,hm,hp] with z hz hm hp
  refine ⟨hz,?_,?_⟩
  · simpa [latticePoleSet] using hm
  · simpa [latticePoleSet] using hp

/-- The explicit coordinate differential determines an actual height chart
and a decaying helicoidal Gauss correction for its spatial primitive. -/
theorem actual_primitive_analytic_height_end_coordinate {X : ℂ → Fin 3 → ℝ} {t a c : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht) :
    ∃ (K f : ℂ → ℂ) (b R₀ : ℝ),
      Tendsto K (cobounded ℂ) (𝓝[≠] 0) ∧ AnalyticAt ℂ f 0 ∧ f 0 = 0 ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), K (actualComplexHeight t a c ht z) = z) ∧
      ∀ ξ : ℂ, R₀ < ‖ξ‖ →
        actualComplexHeight t a c ht (K ξ) = ξ ∧
        HasFDerivAt (fun ξ => verticalRotation I (X (K ξ)))
          (nullRealDerivative (weierstrassTriple (exp (I*((2*(a-1)/c : ℝ) : ℂ)*ξ+infinityCorrection f ξ)) 1)) ξ ∧
        verticalRotation I (X (K ξ)) 2 = ξ.re+b := by
  obtain ⟨k,hka,hk0,hK,hKR,hKL,hKa⟩ := actual_complex_height_inverse (a := a) ht hc
  let K : ℂ → ℂ := fun ξ => k ξ⁻¹
  obtain ⟨φ,hφ,hφ0,hgf⟩ := actual_gauss_height_holomorphic_correction ht ha hc 1
  let f : ℂ → ℂ := fun w => φ (k w)
  let F := infinityCorrection f
  have hf : AnalyticAt ℂ f 0 :=
    (show AnalyticAt ℂ φ (k 0) by simpa only [hk0] using hφ).comp hka
  have hf0 : f 0 = 0 := by simp only [f,hk0,hφ0]
  obtain ⟨b,hheight⟩ := actual_complex_height_real_primitive ht hX
  have he : ∀ᶠ ξ : ℂ in cobounded ℂ,
      actualComplexHeight t a c ht (K ξ) = ξ ∧ AnalyticAt ℂ K ξ ∧
      K ξ ∉ (rhombicPeriodPair t ht).lattice ∧
      K ξ-a ∉ (rhombicPeriodPair t ht).lattice ∧ K ξ+a ∉ (rhombicPeriodPair t ht).lattice ∧
      I*thetaGauss t a 1 (K ξ) = exp (I*((2*(a-1)/c : ℝ) : ℂ)*ξ+F ξ) := by
    filter_upwards [hKR,hKa,hK.eventually (puncture_eventually_avoids_height_zeros (a := a) ht),
      hK.eventually (hgf.filter_mono nhdsWithin_le_nhds)] with ξ hξ hξa hξn hg
    refine ⟨hξ,hξa,hξn.1,hξn.2.1,hξn.2.2,?_⟩
    simpa only [Int.cast_one,hξ,F,f,K,infinityCorrection] using hg
  obtain ⟨R₀,_,hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp he
  refine ⟨K,f,b,R₀,hK,hf,hf0,hKL,?_⟩
  intro ξ hξ
  obtain ⟨hH,hKa,hKn,hKm,hKp,hg⟩ := hR hξ.le
  refine ⟨hH,?_,?_⟩
  · have hEq : (fun ξ => actualComplexHeight t a c ht (K ξ)) =ᶠ[𝓝 ξ] (fun ξ => ξ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hξ] with w hw
      exact (hR hw.le).1
    have hXd : HasFDerivAt X
        (nullRealDerivative (weierstrassTriple (thetaGauss t a 1 (K ξ)) (coordinateData t a c ht (K ξ) 2)))
        (K ξ) := by
      have hd := hX (K ξ) hKn
      rw [coordinateData_eq_original ht ha hKn hKm hKp] at hd
      exact hd
    have hd := weierstrass_height_coordinate_quarter_turn hXd
      (actualComplexHeight_hasDerivAt ht hKn) hKa.differentiableAt.hasDerivAt hEq
    rwa [hg] at hd
  · simp [verticalRotation_apply,hheight (K ξ) hKn,hH]

theorem actual_primitive_height_end_coordinate {X : ℂ → Fin 3 → ℝ} {t a c : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht) :
    ∃ (K F : ℂ → ℂ) (b R₀ : ℝ),
      Tendsto K (cobounded ℂ) (𝓝[≠] 0) ∧ Tendsto F (cobounded ℂ) (𝓝 0) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), K (actualComplexHeight t a c ht z) = z) ∧
      ∀ ξ : ℂ, R₀ < ‖ξ‖ →
        actualComplexHeight t a c ht (K ξ) = ξ ∧
        HasFDerivAt (fun ξ => verticalRotation I (X (K ξ)))
          (nullRealDerivative (weierstrassTriple (exp (I*((2*(a-1)/c : ℝ) : ℂ)*ξ+F ξ)) 1)) ξ ∧
        verticalRotation I (X (K ξ)) 2 = ξ.re+b := by
  obtain ⟨K,f,b,R₀,hK,hf,hf0,hKL,hcoord⟩ := actual_primitive_analytic_height_end_coordinate ht ha hc hX
  exact ⟨K,infinityCorrection f,b,R₀,hK,infinityCorrection_tendsto_zero hf hf0,hKL,hcoord⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_primitive_height_end_coordinate
