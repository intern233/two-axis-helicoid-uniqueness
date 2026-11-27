import TwoAxisHelicoid.HalfHelicoidDirichletStability
import TwoAxisHelicoid.AnalyticCompactAreaVariation

namespace TwoAxisHelicoid
open Complex Set MeasureTheory Filter Topology
open scoped Topology ContDiff

/-- Unit-pitch helicoid in the physical height coordinate Re z. The two
half helicoids are the positive and negative Im z sides of its axis. -/
noncomputable def verticalHeightHelicoid (z : ℂ) : Fin 3 → ℝ :=
  ![(I*Complex.cos z).re,(I*Complex.sin z).re,z.re]

theorem verticalHeightHelicoid_coordinates (z : ℂ) : verticalHeightHelicoid z=
    ![Real.sinh z.im*Real.sin z.re,-Real.sinh z.im*Real.cos z.re,z.re] := by
  ext j
  fin_cases j
  · change (I*Complex.cos z).re=_
    rw [Complex.cos_eq]
    simp [Complex.mul_re,Complex.mul_im,← Complex.ofReal_cosh,← Complex.ofReal_sinh,
      ← Complex.ofReal_cos,← Complex.ofReal_sin,mul_comm]
  · change (I*Complex.sin z).re=_
    rw [Complex.sin_eq]
    simp [Complex.mul_re,Complex.mul_im,← Complex.ofReal_cosh,← Complex.ofReal_sinh,
      ← Complex.ofReal_cos,← Complex.ofReal_sin,mul_comm]
  · rfl

theorem verticalHeightHelicoid_weierstrass (z : ℂ) :
    HasFDerivAt verticalHeightHelicoid (nullRealDerivative (weierstrassTriple (exp (I*z)) 1)) z := by
  let F := fun w : ℂ => (![I*Complex.cos w,I*Complex.sin w,w] : Fin 3 → ℂ)
  let p := (![I*(-Complex.sin z),I*Complex.cos z,1] : Fin 3 → ℂ)
  have dF : HasDerivAt F p z := by
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases j
    · exact (Complex.hasDerivAt_cos z).const_mul I
    · exact (Complex.hasDerivAt_sin z).const_mul I
    · exact hasDerivAt_id' z
  have pos : exp (I*z)=Complex.cos z+Complex.sin z*I := by rw [mul_comm I z,Complex.cos_add_sin_I]
  have neg : (exp (I*z))⁻¹=Complex.cos z-Complex.sin z*I := by
    rw [← Complex.exp_neg,Complex.cos_sub_sin_I,neg_mul,mul_comm I z]
  have form : weierstrassTriple (exp (I*z)) 1=p := by
    ext j
    fin_cases j
    · change ((exp (I*z))⁻¹-exp (I*z))/2*1=I*(-Complex.sin z)
      rw [neg,pos];ring
    · change I*((exp (I*z))⁻¹+exp (I*z))/2*1=I*Complex.cos z
      rw [neg,pos];ring
    · rfl
  have re : verticalHeightHelicoid=fun w => coordinateRealPart (F w) := by
    funext w j
    fin_cases j <;> rfl
  rw [form,re]
  exact realPart_primitive_hasFDerivAt dF

/-- The second derivative here is that of the area of the actually
varied spatial helicoid. A bounded Dirichlet subdomain has a uniform
positive lower bound relative to its physical area measure. -/
theorem physical_half_helicoid_dirichlet_gap {R T : ℝ} (rp : 0<R) (tp : 0<T)
    {v : ℝ × ℝ → ℝ} (smooth : ContDiff ℝ ∞ v) (supp : tsupport v⊆Ioo (-R) R ×ˢ Ioo (0:ℝ) T) :
    let K := Icc (-R) R ×ˢ Icc (0:ℝ) T
    ((1/(R+1))^2/(Real.cosh T)^2)*(∫ p : ℝ × ℝ, (Real.cosh p.2)^2*v p^2)≤
      deriv (deriv (fun s => ∫ p in K, coordinateVariationDensity verticalHeightHelicoid (fun z => I*z) v s p)) 0 := by
  let W := fun z : ℂ => I*z
  let K := Icc (-R) R ×ˢ Icc (0:ℝ) T
  have ck : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have inK : tsupport v⊆K := fun p hp => ⟨⟨(supp hp).1.1.le,(supp hp).1.2.le⟩,⟨(supp hp).2.1.le,(supp hp).2.2.le⟩⟩
  have area := compact_actual_area_second_variation_of_analytic_data (W:=W) ck inK smooth
    (fun p _ => verticalHeightHelicoid_weierstrass (planeComplex p))
    (fun p _ => analyticAt_const.mul analyticAt_id)
  have potential : gaussNormalDirichletDensity W=fun p => 2*(Real.cosh p.2)⁻¹^2 := by
    funext p
    have d : HasDerivAt W I (planeComplex p) := by simpa only [mul_one] using (hasDerivAt_id' (planeComplex p)).const_mul I
    rw [gaussNormalDirichletDensity_formula d]
    simp [W,planeComplex,Complex.mul_re,Complex.mul_im,Real.cosh_neg,div_eq_mul_inv,inv_pow]
  change _≤deriv (deriv (fun s => ∫ p in K, coordinateVariationDensity verticalHeightHelicoid W v s p)) 0
  rw [area.deriv,potential]
  exact half_helicoid_compact_test_gap rp tp smooth supp

/-- Every nonzero smooth compactly supported variation in the open
half helicoid increases its area to second order. The previous uniform
constant is independent of the test on each fixed bounded subdomain. -/
theorem physical_half_helicoid_compact_variation_positive {v : ℝ × ℝ → ℝ}
    (smooth : ContDiff ℝ ∞ v) (compact : HasCompactSupport v) (nonzero : v≠0)
    (half : ∀ p∈tsupport v, 0<p.2) :
    ∃ R T : ℝ, 0<R ∧ 0<T ∧ tsupport v⊆Ioo (-R) R ×ˢ Ioo (0:ℝ) T ∧
      0<deriv (deriv (fun s => ∫ p in Icc (-R) R ×ˢ Icc (0:ℝ) T,
        coordinateVariationDensity verticalHeightHelicoid (fun z => I*z) v s p)) 0 := by
  obtain ⟨B,bp,large⟩ := compact.isCompact.isBounded.exists_pos_norm_le
  have pos : 0<B+1 := by linarith
  have inc : tsupport v⊆Ioo (-(B+1)) (B+1) ×ˢ Ioo (0:ℝ) (B+1) := by
    intro p hp
    have x := (norm_fst_le p).trans (large p hp)
    have y := (norm_snd_le p).trans (large p hp)
    rw [Real.norm_eq_abs,abs_le] at x y
    exact ⟨⟨by linarith [x.1],by linarith [x.2]⟩,half p hp,by linarith [y.2]⟩
  have gap := physical_half_helicoid_dirichlet_gap pos pos smooth inc
  have val : ∃ p, v p≠0 := by
    by_contra! no
    exact nonzero (funext no)
  obtain ⟨p,hp⟩ := val
  let m := fun q : ℝ × ℝ => (Real.cosh q.2)^2*v q^2
  have cm : Continuous m := ((Real.continuous_cosh.comp continuous_snd).pow 2).mul (smooth.continuous.pow 2)
  have support : HasCompactSupport m := (compact.comp_left (g:=fun u : ℝ => u^2) (by norm_num)).mul_left
  have integralPos : 0<∫ q, m q := integral_pos_of_integrable_nonneg_nonzero cm
    (cm.integrable_of_hasCompactSupport support) (fun q => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_ne_zero (pow_ne_zero 2 (Real.cosh_pos _).ne') (pow_ne_zero 2 hp))
  exact ⟨_,_,pos,pos,inc,(mul_pos (by positivity) integralPos).trans_le gap⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.verticalHeightHelicoid_coordinates
#print axioms TwoAxisHelicoid.verticalHeightHelicoid_weierstrass
#print axioms TwoAxisHelicoid.physical_half_helicoid_dirichlet_gap
#print axioms TwoAxisHelicoid.physical_half_helicoid_compact_variation_positive
