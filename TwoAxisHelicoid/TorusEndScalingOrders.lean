import TwoAxisHelicoid.HolomorphicImmersionCoordinateChange
import TwoAxisHelicoid.HarmonicNullLift

namespace TwoAxisHelicoid
open Complex Filter Set InnerProductSpace
open scoped Topology

theorem punctured_lattice_regular_near_zero (L : PeriodPair) :
    ∀ᶠ z in 𝓝[≠] (0:ℂ), z ∉ L.lattice := by
  filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
    self_mem_nhdsWithin] with z hz hn
  exact fun h => hz ⟨h,hn⟩

/-- Changing the marking by a nonzero complex scale preserves both actual
Weierstrass orders. Their values at the omitted lattice points are immaterial.
Holomorphicity of the Gauss map on a whole punctured neighborhood follows
here from the height pole and the null equation. -/
theorem marked_torus_scaled_end_orders (L M : PeriodPair) (X : ℂ → Fin 3 → ℝ)
    (s : ℂ) (hs : s ≠ 0)
    (hh : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X w j) z) ∧ ConformalCoordinateDerivatives X z)
    (hheight : meromorphicOrderAt (fun w => immersionComplexCoefficient X w 2) 0 = (-2 : ℤ))
    (hgauss : meromorphicOrderAt (immersionGaussLogDerivative X) 0 = (-2 : ℤ)) :
    let Y := fun w => X (s*w)
    meromorphicOrderAt (fun w => puncturedImmersionCoefficient M Y w 2) 0 = (-2 : ℤ) ∧
    meromorphicOrderAt (fun w => deriv (fun v => nullGauss (puncturedImmersionCoefficient M Y v)) w /
      nullGauss (puncturedImmersionCoefficient M Y w)) 0 = (-2 : ℤ) := by
  let u := fun w : ℂ => s*w
  let Y := X ∘ u
  have h₁ := meromorphicAt_of_meromorphicOrderAt_ne_zero (f := fun w => immersionComplexCoefficient X w 2)
    (by rw [hheight]; norm_num)
  have h₂ := meromorphicAt_of_meromorphicOrderAt_ne_zero (f := immersionGaussLogDerivative X)
    (by rw [hgauss]; norm_num)
  have hn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero h₁).mp (by rw [hheight]; norm_num)
  have hreg : ∀ᶠ w in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ X w ∧ DifferentiableAt ℂ (immersionGaussMap X) w := by
    filter_upwards [hn,punctured_lattice_regular_near_zero L] with w hw hL
    obtain ⟨ha,hc⟩ := hh w hL
    exact ⟨(analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (ha j))).differentiableAt,
      (immersionGaussMap_differentiableAt_of_coefficients (fun j => scalarComplexCoefficient_analyticAt (ha j))
        (immersionComplexCoefficient_null hc) hw).1⟩
  have hu0 : u 0 = 0 := mul_zero _
  have hdu : deriv u 0 ≠ 0 := by rw [(hasDerivAt_const_mul (x := (0:ℂ)) s).deriv]; exact hs
  have horder := actual_end_double_poles_change_coordinate (X := X) (Y := Y) (u := u) (z := 0)
    (analyticAt_const.mul analyticAt_id) hdu EventuallyEq.rfl (hu0.symm ▸ hreg) (hu0.symm ▸ h₁) (hu0.symm ▸ h₂)
  rw [hu0,hheight,hgauss] at horder
  have he : (fun w => puncturedImmersionCoefficient M Y w 2) =ᶠ[𝓝[≠] (0:ℂ)]
      (fun w => immersionComplexCoefficient Y w 2) :=
    (punctured_lattice_regular_near_zero M).mono fun w hw => congrFun (puncturedImmersionCoefficient_eq hw) 2
  have hg : (fun w => nullGauss (puncturedImmersionCoefficient M Y w)) =ᶠ[𝓝[≠] (0:ℂ)] immersionGaussMap Y :=
    (punctured_lattice_regular_near_zero M).mono fun w hw => congrArg nullGauss (puncturedImmersionCoefficient_eq hw)
  have hg' : (fun w => deriv (fun v => nullGauss (puncturedImmersionCoefficient M Y v)) w /
      nullGauss (puncturedImmersionCoefficient M Y w)) =ᶠ[𝓝[≠] (0:ℂ)] immersionGaussLogDerivative Y := by
    filter_upwards [punctured_germ_eventually_local hg] with w hw
    exact congrArg₂ (· / ·) hw.deriv_eq hw.self_of_nhds
  exact ⟨(meromorphicOrderAt_congr he).trans horder.2.1,(meromorphicOrderAt_congr hg').trans horder.2.2.2⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.marked_torus_scaled_end_orders
