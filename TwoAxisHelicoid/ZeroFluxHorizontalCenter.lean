import TwoAxisHelicoid.ExteriorConormalPrimitives
import TwoAxisHelicoid.OscillatoryExteriorPrimitive
import TwoAxisHelicoid.HeightEndVerticalCoordinate

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology ComplexConjugate

private theorem coordinate_primitive_constant {R : ℝ} (hR : 0 ≤ R)
    {X : ℂ → Fin 3 → ℝ} {p : ℂ → Fin 3 → ℂ} {W : ℂ → ℂ} (j : Fin 3)
    (hX : ∀ z, R < ‖z‖ → HasFDerivAt X (nullRealDerivative (p z)) z)
    (hW : ∀ z, R < ‖z‖ → HasDerivAt W (p z j) z) :
    ∃ b : ℝ, ∀ z : ℂ, R < ‖z‖ → X z j = (W z).re+b := by
  let L := (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ)
  have dx z hz := L.hasFDerivAt.comp z (hX z hz)
  have dw z hz := reCLM.hasFDerivAt.comp z ((hW z hz).hasFDerivAt.restrictScalars ℝ)
  apply (isOpen_lt continuous_const continuous_norm).exists_eq_add_of_fderiv_eq
    (complex_norm_exterior_isPreconnected hR)
    (fun z hz => (dx z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (dw z hz).differentiableAt.differentiableWithinAt)
  intro z hz
  rw [(dx z hz).fderiv,(dw z hz).fderiv]
  ext v
  change (v*p z j).re = (v • p z j).re
  rfl

private theorem exp_i_deriv (z : ℂ) : HasDerivAt (fun w : ℂ => exp (I*w)) (exp (I*z)*I) z := by
  simpa only [mul_one,Function.comp_def,id_eq] using (hasDerivAt_exp (I*z)).comp z ((hasDerivAt_id z).const_mul I)

theorem exponential_height_triple_null (w : ℂ) : ComplexNull (weierstrassTriple (exp w) 1) := by
  change (((exp w)⁻¹-exp w)/2*1)^2+(I*((exp w)⁻¹+exp w)/2*1)^2+(1:ℂ)^2 = 0
  linear_combination (((exp w)⁻¹+exp w)^2/4)*I_sq - (inv_mul_cancel₀ (exp_ne_zero w))

/-- A vanishing peripheral spatial flux forces a single common horizontal
center for both real tails of a height-normalized helicoidal end. -/
theorem zero_flux_height_end_horizontal_center {R r : ℝ} (hR : 0 < R) (hr : R < r)
    {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ} (hf : Tendsto F (cobounded ℂ) (𝓝 0))
    (hhol : ∀ z : ℂ, R < ‖z‖ → DifferentiableAt ℂ F z)
    (hd : ∀ z : ℂ, R < ‖z‖ → HasFDerivAt X (nullRealDerivative
      (weierstrassTriple (exp (I*z+F z)) 1)) z)
    (hflux : ∀ j, (exteriorFluxCircle hR hr).spatialConormalFlux X j = 0) :
    ∃ b₀ b₁ : ℝ, Tendsto (fun x : ℝ => X (x : ℂ) 0) (cobounded ℝ) (𝓝 b₀) ∧
      Tendsto (fun x : ℝ => X (x : ℂ) 1) (cobounded ℝ) (𝓝 b₁) := by
  let g := fun z : ℂ => exp (I*z+F z)
  let p := fun z : ℂ => weierstrassTriple (g z) 1
  have gh (z : ℂ) (hz : R < ‖z‖) : DifferentiableAt ℂ g z := differentiableAt_exp.comp z
    ((differentiableAt_id.const_mul I).add (hhol z hz))
  have ph (z : ℂ) (hz : R < ‖z‖) (j : Fin 3) : DifferentiableAt ℂ (fun w => p w j) z := by
    have h := gh z hz
    have hg : g z ≠ 0 := exp_ne_zero _
    fin_cases j <;> dsimp [p,weierstrassTriple] <;> fun_prop
  obtain ⟨P,hP⟩ := exterior_primitive_of_zero_spatial_flux hR hr X p hd
    (fun z _ => exponential_height_triple_null (I*z+F z)) ph hflux
  let A := fun z : ℂ => -(P 0 z)-I*P 1 z+I*exp (I*z)
  let C := fun z : ℂ => P 0 (-z)-I*P 1 (-z)-I*exp (I*z)
  have da (z : ℂ) (hz : R < ‖z‖) :
      HasDerivAt A (exp (I*z)*(exp (F z)-1)) z := by
    convert (((hP 0 z hz).neg.sub ((hP 1 z hz).const_mul I)).add ((exp_i_deriv z).const_mul I)) using 1
    simp only [p,g,weierstrassTriple,Matrix.cons_val_zero,Matrix.cons_val_one,mul_one,exp_add]
    linear_combination (norm := ring_nf) ((exp (I*z)*exp (F z)+(exp (I*z)*exp (F z))⁻¹)/2 - exp (I*z)) * I_sq
  have dc (z : ℂ) (hz : R < ‖z‖) :
      HasDerivAt C (exp (I*z)*(1-exp (-F (-z)))) z := by
    have hn : R < ‖-z‖ := by simpa only [norm_neg] using hz
    have negz : HasDerivAt (fun w : ℂ => -w) (-1) z := (hasDerivAt_id z).neg
    have d := ((((hP 0 (-z) hn).comp (h := fun w : ℂ => -w) z negz).sub
      (((hP 1 (-z) hn).comp (h := fun w : ℂ => -w) z negz).const_mul I)).sub ((exp_i_deriv z).const_mul I))
    apply d.congr_deriv
    change p (-z) 0*(-1)-I*(p (-z) 1*(-1))-I*(exp (I*z)*I) = exp (I*z)*(1-exp (-F (-z)))
    simp only [p,g,weierstrassTriple,Matrix.cons_val_zero,Matrix.cons_val_one,mul_one,exp_add,mul_neg,
      exp_neg,mul_inv_rev,inv_inv]
    ring_nf; simp [I_sq]; ring
  have blim : Tendsto (fun z : ℂ => exp (F z)-1) (cobounded ℂ) (𝓝 0) := by
    simpa using ((continuous_exp.tendsto 0).comp hf).sub_const 1
  have nlim : Tendsto (fun z : ℂ => 1-exp (-F (-z))) (cobounded ℂ) (𝓝 0) := by
    have h : Tendsto (fun z : ℂ => -F (-z)) (cobounded ℂ) (𝓝 0) := by
      simpa only [neg_zero,Function.comp_def] using (hf.comp tendsto_neg_cobounded).neg
    simpa using (tendsto_const_nhds (x := (1 : ℂ))).sub ((continuous_exp.tendsto 0).comp h)
  obtain ⟨u,hu⟩ := exterior_oscillatory_primitive_common_limit R da blim
  obtain ⟨v,hv⟩ := exterior_oscillatory_primitive_common_limit R dc nlim
  have hv' := hv.comp (show Tendsto (fun x : ℝ => -x) (cobounded ℝ) (cobounded ℝ) from tendsto_neg_cobounded)
  obtain ⟨b,hb⟩ := coordinate_primitive_constant hR.le 0 hd (hP 0)
  obtain ⟨c,hc⟩ := coordinate_primitive_constant hR.le 1 hd (hP 1)
  have eq (x : ℝ) : conj (C (-(x:ℂ)))-A (x:ℂ) = 2*((P 0 x).re+(P 1 x).re*I) := by
    simp only [A,C,neg_neg,map_sub,map_mul,conj_I,← exp_conj,conj_ofReal,map_neg]
    apply Complex.ext <;> simp [Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im] <;> ring
  have lim : Tendsto (fun x : ℝ => conj (C (-(x:ℂ)))-A x) (cobounded ℝ) (𝓝 (conj v-u)) := by
    simpa only [Function.comp_def,ofReal_neg] using ((continuous_conj.tendsto v).comp hv').sub hu
  have large : ∀ᶠ x : ℝ in cobounded ℝ, R < ‖(x:ℂ)‖ := by
    simpa only [norm_real] using tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)
  refine ⟨(conj v-u).re/2+b,(conj v-u).im/2+c,?_,?_⟩
  · apply ((((continuous_re.tendsto _).comp lim).div_const 2).add_const b).congr'
    filter_upwards [large] with x hx
    rw [Function.comp_apply,eq,hb _ hx]
    simp [Complex.mul_re,Complex.add_re]
  · apply ((((continuous_im.tendsto _).comp lim).div_const 2).add_const c).congr'
    filter_upwards [large] with x hx
    rw [Function.comp_apply,eq,hc _ hx]
    simp [Complex.mul_im,Complex.add_im]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.zero_flux_height_end_horizontal_center
