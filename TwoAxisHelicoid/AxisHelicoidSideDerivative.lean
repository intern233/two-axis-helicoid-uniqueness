import TwoAxisHelicoid.AxisHelicoidCalibration

namespace TwoAxisHelicoid
open Set Complex
attribute [local irreducible] thetaGauss

/-- Across the actual vertical axis, the derivative of a signed defining
function for the comparison helicoid is the sine of the continuously
lifted relative phase times the height differential's imaginary part. -/
theorem harmonic_integer_axis_side_derivative {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = coordinateData t a c ht z 2)
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) (2*t)) :
    let g₀ := thetaGauss t a m (I*t)
    let α := 2*(a-m)/c
    let b := X (I*t) 2
    HasDerivAt (fun x : ℝ => axisHelicoidSide g₀ α b (X ((x : ℂ)+I*y)))
      ((coordinateData t a c ht (I*y) 2).im * Real.sin (integerAxisPhase t a m y)) 0 := by
  let z := I*(y : ℂ)
  let q := thetaGauss t a m z
  let h := coordinateData t a c ht z 2
  let g₀ := thetaGauss t a m (I*t)
  let α : ℝ := 2*(a-m)/c
  let b := X (I*t) 2
  let γ := fun x : ℝ => (x : ℂ)+z
  let V := fun x : ℝ => g₀*Complex.exp (I*(α*(X (γ x) 2-b) : ℝ))
  let δ := integerAxisPhase t a m y
  have hreg := integerAxis_regular_points ht ha hy
  have hD := harmonic_integer_gauss_data_has_coordinate_differential ht ha hc m hX hh hg _
    ((not_mem_gaussLogPoleSet _ _ _).mpr hreg)
  have hγ0 : γ 0 = z := by simp [γ]
  have hγ : HasDerivAt γ 1 0 := by
    have hγ' : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 0 := by
      simpa using! (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ)))
    exact hγ'.add_const z
  change HasFDerivAt X (nullRealDerivative (weierstrassTriple q h)) z at hD
  have hcoord (j : Fin 3) : HasDerivAt (fun x => X (γ x) j)
      (nullRealDerivative (weierstrassTriple q h) 1 j) 0 := by
    have hd := ((ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp (γ 0)
      (hγ0.symm ▸ hD)).comp_hasDerivAt 0 hγ
    exact hd
  have hV : DifferentiableAt ℝ V 0 := by
    have hv := (hcoord 2).differentiableAt
    have hcpx := Complex.ofRealCLM.differentiableAt.comp 0 ((hv.sub_const b).const_mul α)
    change DifferentiableAt ℝ (fun x => g₀ * Complex.exp (I*Complex.ofRealCLM (α*(X (γ x) 2-b)))) 0
    exact (hcpx.const_mul I).cexp.const_mul g₀
  have hvre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hV.hasDerivAt
  have hvim := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hV.hasDerivAt
  have hside := (hvre.mul (hcoord 0)).add (hvim.mul (hcoord 1))
  have haxis := hX.vertical_axis_zero hreg.1 (by simp [Complex.mul_re])
  have hq : normSq q = 1 := thetaGauss_axis_normSq ht ha m hy
  have hqi : q⁻¹ = starRingEnd ℂ q := by simp [Complex.inv_def,hq]
  have hd0 : nullRealDerivative (weierstrassTriple q h) 1 0 = h.im*q.im := by
    simp [weierstrassTriple,hqi,Complex.mul_re]
    ring
  have hd1 : nullRealDerivative (weierstrassTriple q h) 1 1 = -h.im*q.re := by
    simp [weierstrassTriple,hqi,Complex.mul_re,Complex.mul_im]
    ring
  have hphase : q = V 0 * Complex.exp ((δ : ℂ)*I) := by
    have he := thetaGauss_integerAxisPhase_identity ht ha hG hc m hy
    dsimp only at he
    rw [harmonic_integer_axis_height_difference ht hX hh hy,mul_add,Complex.exp_add,← mul_assoc] at he
    convert he using 2 <;> simp only [V,hγ0,g₀,α,b,z,δ,Complex.ofReal_sub,Complex.ofReal_mul,
      Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_intCast]
    ring
  have hVunit : normSq (V 0) = 1 := by
    rw [show V 0 = g₀*Complex.exp ((α*(X (γ 0) 2-b) : ℝ)*I) by dsimp [V]; ring_nf,
      Complex.normSq_mul,show normSq g₀ = 1 from thetaGauss_axis_normSq ht ha m ⟨ht,by linarith⟩,
      normSq_eq_norm_sq,Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hcross : (V 0).re*q.im-(V 0).im*q.re = Real.sin δ := by
    rw [hphase,Complex.mul_im (V 0) _,Complex.mul_re (V 0) _,Complex.exp_ofReal_mul_I_im,Complex.exp_ofReal_mul_I_re]
    change (V 0).re*(V 0).re+(V 0).im*(V 0).im = 1 at hVunit
    linear_combination (Real.sin δ)*hVunit
  change HasDerivAt (fun x => (V x).re*X (γ x) 0 + (V x).im*X (γ x) 1) (h.im*Real.sin δ) 0
  convert hside using 1
  · rfl
  change h.im*Real.sin δ = _*X (γ 0) 0+(V 0).re*nullRealDerivative (weierstrassTriple q h) 1 0+
    (_*X (γ 0) 1+(V 0).im*nullRealDerivative (weierstrassTriple q h) 1 1)
  rw [hγ0,haxis.1,haxis.2,hd0,hd1,← hcross]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_integer_axis_side_derivative
