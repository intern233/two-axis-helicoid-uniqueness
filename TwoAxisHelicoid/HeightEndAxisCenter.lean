import TwoAxisHelicoid.HeightEndAxis

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology ComplexConjugate

theorem actualComplexHeight_neg {t a c : ℝ} (ht : 0 < t) (z : ℂ) :
    actualComplexHeight t a c ht (-z) = -actualComplexHeight t a c ht z := by
  unfold actualComplexHeight
  rw [thetaZeta_neg]
  ring

theorem actualComplexHeight_ofReal_re {t a c : ℝ} (ht : 0 < t) (x : ℝ) :
    (actualComplexHeight t a c ht (x : ℂ)).re = 0 := by
  have hh := actualComplexHeight_reflection (a := a) (c := c) ht (x : ℂ)
  rw [Complex.conj_ofReal,actualComplexHeight_neg ht] at hh
  have hr := congrArg Complex.re hh
  simp only [Complex.neg_re,Complex.conj_re] at hr
  linarith

theorem actual_complex_height_centered_primitive {X : ℂ → Fin 3 → ℝ} {t a c : ℝ}
    (ht : 0 < t) (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    {z : ℂ} (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    X z 2-X 1 2 = (actualComplexHeight t a c ht z).re := by
  obtain ⟨b,hb⟩ := actual_complex_height_real_primitive ht hX
  have h1 := hb 1 (real_not_mem_rhombic_lattice_of_pos ht (by norm_num : (0 : ℝ) < 1) (by norm_num))
  rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by rfl,actualComplexHeight_ofReal_re ht,zero_add] at h1
  simp only [Complex.ofReal_one] at h1
  rw [hb z hz,h1]
  ring

/-- Centering the actual periodic primitive at its two-axis intersection
gives an actual analytic height end with zero horizontal axis values at
both real infinities. -/
theorem actual_periodic_primitive_centered_axis_end {X : ℂ → Fin 3 → ℝ} {t a c : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (hp : ∀ z ω : ℂ, ω ∈ (rhombicPeriodPair t ht).lattice → X (z+ω) = X z) :
    ∃ (K f : ℂ → ℂ) (R : ℝ),
      Tendsto K (cobounded ℂ) (𝓝[≠] 0) ∧ AnalyticAt ℂ f 0 ∧ f 0 = 0 ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), K (actualComplexHeight t a c ht z) = z) ∧
      (∀ ξ : ℂ, R < ‖ξ‖ →
        actualComplexHeight t a c ht (K ξ) = ξ ∧
        HasFDerivAt (fun ξ => verticalRotation I (X (K ξ))-verticalRotation I (X 1))
          (nullRealDerivative (weierstrassTriple (exp (I*((2*(a-1)/c : ℝ) : ℂ)*ξ+infinityCorrection f ξ)) 1)) ξ ∧
        (verticalRotation I (X (K ξ))-verticalRotation I (X 1)) 2 = ξ.re) ∧
      ∃ A : ℝ, ∀ x : ℝ, A < |x| →
        (verticalRotation I (X (K (x : ℂ)))-verticalRotation I (X 1)) 0 = 0 ∧
        (verticalRotation I (X (K (x : ℂ)))-verticalRotation I (X 1)) 1 = 0 := by
  obtain ⟨K,f,_b,R₀,hK,hf,hf0,hKL,hcoord⟩ := actual_primitive_analytic_height_end_coordinate ht ha hc hX
  have hlarge : ∀ᶠ ξ : ℂ in cobounded ℂ, R₀ < ‖ξ‖ :=
    tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R₀)
  have hKR : ∀ᶠ ξ : ℂ in cobounded ℂ, actualComplexHeight t a c ht (K ξ) = ξ :=
    hlarge.mono (fun ξ hξ => (hcoord ξ hξ).1)
  have he : ∀ᶠ ξ : ℂ in cobounded ℂ,
      R₀ < ‖ξ‖ ∧ K ξ ∉ (rhombicPeriodPair t ht).lattice :=
    hlarge.and (hK.eventually (rhombic_puncture_eventually_off_lattice ht))
  obtain ⟨R,_hR,hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp he
  obtain ⟨A,_hA,hA⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp
    (actual_height_inverse_same_vertical_axis ht hX hp hK hKL hKR)
  refine ⟨K,f,R,hK,hf,hf0,hKL,?_,A,?_⟩
  · intro ξ hξ
    have hh := hR hξ.le
    refine ⟨(hcoord ξ hh.1).1,((hcoord ξ hh.1).2.1).sub_const _,?_⟩
    change X (K ξ) 2-X 1 2 = ξ.re
    rw [actual_complex_height_centered_primitive ht hX hh.2,(hcoord ξ hh.1).1]
  · intro x hx
    have hn : A ≤ ‖(x : ℂ)‖ := by simpa only [Complex.norm_real,Real.norm_eq_abs] using hx.le
    have hh := hA hn (by simp : (x : ℂ).im = 0)
    simp [verticalRotation_apply,hh.1,hh.2]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_periodic_primitive_centered_axis_end
