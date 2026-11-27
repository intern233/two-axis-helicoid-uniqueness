import TwoAxisHelicoid.GrowingPrimitiveComparison

namespace TwoAxisHelicoid
open Set Filter Metric Complex
open scoped Topology

/-- Complex analogue of asymptotic integration on a ray where a
nonzero exponential dominates. The comparison function may rotate; the
real derivative comparison is made only with its positive modulus. -/
theorem complex_primitive_ratio_on_growing_ray {Z U D A : ℝ → ℂ} {V : ℝ → ℝ} {b μ : ℂ}
    (positive : 0<μ.re) (escape : Tendsto (fun t => ‖U t‖) atTop atTop)
    (regular : ∀ᶠ t in atTop, HasDerivAt Z (D t) t ∧ HasDerivAt U (A t*U t) t ∧
      HasDerivAt (fun x => ‖U x‖) (V t*‖U t‖) t)
    (coeff : Tendsto A atTop (𝓝 μ)) (radial : Tendsto V atTop (𝓝 μ.re))
    (speed : Tendsto (fun t => D t/U t) atTop (𝓝 b)) :
    Tendsto (fun t => Z t/U t) atTop (𝓝 (b/μ)) := by
  let k := b/μ
  let S := fun t => Z t-k*U t
  let v := fun t => D t-k*(A t*U t)
  have non : μ≠0 := fun e => (by simpa only [e,Complex.zero_re] using positive : (0:ℝ)<0).false
  have regular' : ∀ᶠ t in atTop, HasDerivAt S (v t) t ∧
      HasDerivAt (fun t => ‖U t‖) (V t*‖U t‖) t ∧ 0<V t*‖U t‖ := by
    filter_upwards [regular,radial.eventually (lt_mem_nhds positive),escape.eventually_gt_atTop 0] with t h ht hp
    exact ⟨h.1.sub (h.2.1.const_mul k),h.2.2,mul_pos ht hp⟩
  have zero : b-k*μ=0 := by dsimp [k]; rw [div_mul_cancel₀ _ non,sub_self]
  have residual : Tendsto (fun t => v t/U t) atTop (𝓝 0) := by
    rw [← zero]
    apply (speed.sub (coeff.const_mul k)).congr'
    filter_upwards [escape.eventually_gt_atTop 0] with t ht
    dsimp only [v]
    field_simp [norm_pos_iff.mp ht]
  have realResidual : Tendsto (fun t => ‖v t‖/(V t*‖U t‖)) atTop (𝓝 0) := by
    have h := residual.norm.div radial positive.ne'
    change Tendsto (fun t => ‖v t/U t‖/V t) atTop (𝓝 (‖(0:ℂ)‖/μ.re)) at h
    simpa only [norm_zero,zero_div,norm_div,div_div,mul_comm] using h
  have bound := growing_primitive_negligible escape regular' realResidual
  rw [← tendsto_sub_nhds_zero_iff]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply bound.congr'
  filter_upwards [escape.eventually_gt_atTop 0] with t ht
  rw [← norm_div]
  congr 1
  dsimp [S,k]
  field_simp [norm_pos_iff.mp ht]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.complex_primitive_ratio_on_growing_ray
