import TwoAxisHelicoid.AlignedEndDoublePoles

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology
set_option maxHeartbeats 1400000

theorem analytic_double_pole_with_remainder {f k : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hk : AnalyticAt ℂ k 0) (he : f =ᶠ[𝓝[≠] (0:ℂ)] fun w => c/w^2+k w) :
    MeromorphicAt f 0 ∧ meromorphicOrderAt f 0 = -2 := by
  let g := fun w : ℂ => c+w^2*k w
  have hg : AnalyticAt ℂ g 0 := analyticAt_const.add ((analyticAt_id.pow 2).mul hk)
  have h0 : g 0 ≠ 0 := by simpa [g] using hc
  have hm : MeromorphicAt (fun w : ℂ => c/w^2+k w) 0 :=
    ((MeromorphicAt.const c 0).div (analyticAt_id.pow 2).meromorphicAt).add hk.meromorphicAt
  have hf := hm.congr he.symm
  refine ⟨hf,(meromorphicOrderAt_eq_int_iff (n := (-2:ℤ)) hf).mpr ⟨g,hg,h0,?_⟩⟩
  filter_upwards [he,self_mem_nhdsWithin] with w hw hn
  change w ≠ 0 at hn
  rw [hw]
  simp only [g,sub_zero,zpow_neg,smul_eq_mul]
  field_simp

theorem scalarComplexCoefficient_of_real_part {f : ℂ → ℂ} {z c : ℂ} (h : HasDerivAt f c z) (b : ℝ) :
    scalarComplexCoefficient (fun w => b+(f w).re) z = c := by
  have hf := (reCLM.hasFDerivAt.comp z (h.hasFDerivAt.restrictScalars ℝ)).const_add b
  change HasFDerivAt (fun w => b+(f w).re) _ z at hf
  unfold scalarComplexCoefficient
  rw [hf.fderiv]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]

/-- In the inverse coordinate centered at the compactifying point,
the BBC end normal form gives actual orders of both differentials.
The leading coefficient of the Gauss logarithmic derivative is
nonzero because the pitch coefficient is nonzero. -/
theorem height_gauss_normal_form_actual_double_poles (X : ℂ → Fin 3 → ℝ) (b α : ℝ) (hα : α ≠ 0)
    (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0)
    (hh : (fun w => X w 2) =ᶠ[𝓝[≠] (0:ℂ)] fun w => b+w⁻¹.re)
    (hg : immersionGaussMap X =ᶠ[𝓝[≠] (0:ℂ)] fun w => Complex.exp (I*(α:ℂ)/w+F w)) :
    MeromorphicAt (fun w => immersionComplexCoefficient X w 2) 0 ∧
      meromorphicOrderAt (fun w => immersionComplexCoefficient X w 2) 0 = -2 ∧
      MeromorphicAt (immersionGaussLogDerivative X) 0 ∧
      meromorphicOrderAt (immersionGaussLogDerivative X) 0 = -2 := by
  have hd : (fun w => immersionComplexCoefficient X w 2) =ᶠ[𝓝[≠] (0:ℂ)]
      fun w => (-1:ℂ)/w^2+(fun _ : ℂ => (0:ℂ)) w := by
    filter_upwards [punctured_germ_eventually_local hh,self_mem_nhdsWithin] with w hw hn
    change w ≠ 0 at hn
    change scalarComplexCoefficient (fun z => X z 2) w = _
    have he : scalarComplexCoefficient (fun z => X z 2) w = scalarComplexCoefficient (fun z : ℂ => b+z⁻¹.re) w := by
      unfold scalarComplexCoefficient
      rw [hw.fderiv_eq]
    rw [he]
    have hi : HasDerivAt (fun z : ℂ => z⁻¹) ((-1:ℂ)/w^2) w := by
      simpa only [neg_div,one_div] using! hasDerivAt_inv hn
    simpa only [add_zero] using scalarComplexCoefficient_of_real_part hi b
  have hΩ : immersionGaussLogDerivative X =ᶠ[𝓝[≠] (0:ℂ)] fun w => (-(I*(α:ℂ)))/w^2+deriv F w := by
    filter_upwards [punctured_germ_eventually_local hg,hF.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hw hFw hn
    change w ≠ 0 at hn
    have hi : HasDerivAt (fun z : ℂ => I*(α:ℂ)/z) ((-(I*(α:ℂ)))/w^2) w := by
      simpa only [zero_mul,mul_one,zero_sub,id_eq,Pi.div_def] using!
        (hasDerivAt_const w (I*(α:ℂ))).div (hasDerivAt_id w) hn
    unfold immersionGaussLogDerivative
    have hc := (hi.add hFw.differentiableAt.hasDerivAt).cexp.deriv
    dsimp only [Pi.add_def] at hc
    rw [hw.deriv_eq,hw.self_of_nhds,hc]
    field_simp [Complex.exp_ne_zero]
  have ha : -(I*(α:ℂ)) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hα))
  have h₁ := analytic_double_pole_with_remainder (neg_ne_zero.mpr (one_ne_zero : (1:ℂ) ≠ 0)) analyticAt_const hd
  have h₂ := analytic_double_pole_with_remainder ha hF.deriv hΩ
  exact ⟨h₁.1,h₁.2,h₂⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.height_gauss_normal_form_actual_double_poles
