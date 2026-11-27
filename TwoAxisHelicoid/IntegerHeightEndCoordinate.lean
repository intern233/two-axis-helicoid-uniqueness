import TwoAxisHelicoid.ActualHeightEndCoordinate
import TwoAxisHelicoid.HeightEndVerticalCoordinate
import TwoAxisHelicoid.NullCoordinateRecognition

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology
set_option maxHeartbeats 1000000

/-- The analytic height-coordinate normal form for every integer Gauss
branch. No choice of the basic branch is made. Only the actual coordinate
differential away from its finite height zeros is used. -/
theorem integer_primitive_analytic_height_end_coordinate
    {X : ℂ → Fin 3 → ℝ} {t a c : ℝ} (m : ℤ)
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (hX : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      HasFDerivAt X (nullRealDerivative
        (weierstrassTriple (thetaGauss t a m z) (coordinateData t a c ht z 2))) z) :
    ∃ (K f : ℂ → ℂ) (b R : ℝ),
      Tendsto K (cobounded ℂ) (𝓝[≠] 0) ∧ AnalyticAt ℂ f 0 ∧ f 0 = 0 ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), K (actualComplexHeight t a c ht z) = z) ∧
      ∀ ξ : ℂ, R < ‖ξ‖ →
        actualComplexHeight t a c ht (K ξ) = ξ ∧
        HasFDerivAt (fun ξ => verticalRotation I (X (K ξ)))
          (nullRealDerivative (weierstrassTriple
            (exp (I*((2*(a-m)/c : ℝ) : ℂ)*ξ+infinityCorrection f ξ)) 1)) ξ ∧
        verticalRotation I (X (K ξ)) 2 = ξ.re+b := by
  obtain ⟨k,hka,hk0,hK,hKR,hKL,hKa⟩ := actual_complex_height_inverse (a := a) ht hc
  let K : ℂ → ℂ := fun ξ => k ξ⁻¹
  obtain ⟨φ,hφ,hφ0,hgf⟩ := actual_gauss_height_holomorphic_correction ht ha hc m
  let f : ℂ → ℂ := fun w => φ (k w)
  have hf : AnalyticAt ℂ f 0 :=
    (show AnalyticAt ℂ φ (k 0) by simpa only [hk0] using hφ).comp hka
  have hf0 : f 0 = 0 := by simp only [f,hk0,hφ0]
  have he : ∀ᶠ ξ : ℂ in cobounded ℂ,
      actualComplexHeight t a c ht (K ξ) = ξ ∧ AnalyticAt ℂ K ξ ∧
      K ξ ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a ∧
      I*thetaGauss t a m (K ξ) =
        exp (I*((2*(a-m)/c : ℝ) : ℂ)*ξ+infinityCorrection f ξ) := by
    filter_upwards [hKR,hKa,hK.eventually (puncture_eventually_avoids_height_zeros (a := a) ht),
      hK.eventually (hgf.filter_mono nhdsWithin_le_nhds)] with ξ hξ hξa hξn hg
    refine ⟨hξ,hξa,(not_mem_gaussLogPoleSet _ _ _).mpr hξn,?_⟩
    simpa only [hξ,f,K,infinityCorrection] using hg
  obtain ⟨B,_hB,hB⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp he
  let R := max B 0+1
  have hR0 : 0 ≤ R := by dsimp [R]; linarith [le_max_right B 0]
  have hRB : B < R := by dsimp [R]; linarith [le_max_left B 0]
  have hD ξ (hξ : R < ‖ξ‖) : HasFDerivAt (fun ξ => verticalRotation I (X (K ξ)))
      (nullRealDerivative (weierstrassTriple
        (exp (I*((2*(a-m)/c : ℝ) : ℂ)*ξ+infinityCorrection f ξ)) 1)) ξ := by
    obtain ⟨hH,hKξ,hKn,hg⟩ := hB (hRB.trans hξ).le
    have hEq : (fun ξ => actualComplexHeight t a c ht (K ξ)) =ᶠ[𝓝 ξ] (fun ξ => ξ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hξ] with w hw
      exact (hB (hRB.trans hw).le).1
    have hd := weierstrass_height_coordinate_quarter_turn (hX _ hKn)
      (actualComplexHeight_hasDerivAt ht ((not_mem_gaussLogPoleSet _ _ _).mp hKn).1)
      hKξ.differentiableAt.hasDerivAt hEq
    rwa [hg] at hd
  obtain ⟨b,hb⟩ := height_end_third_coordinate hR0 hD
  exact ⟨K,f,b,R,hK,hf,hf0,hKL,fun ξ hξ =>
    ⟨(hB (hRB.trans hξ).le).1,hD ξ hξ,hb ξ hξ⟩⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.integer_primitive_analytic_height_end_coordinate
