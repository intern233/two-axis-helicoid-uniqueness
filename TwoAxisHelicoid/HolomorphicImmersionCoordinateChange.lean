import TwoAxisHelicoid.AlignedEndDoublePoles
import Mathlib.Analysis.Calculus.Deriv.Inverse

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology

/-- Change of local complex parameter for the three actual coordinate one-forms. -/
theorem immersionComplexCoefficient_comp_holomorphic
    {X : ℂ → Fin 3 → ℝ} {u : ℂ → ℂ} {z d : ℂ}
    (hX : DifferentiableAt ℝ X (u z)) (hu : HasDerivAt u d z) (j : Fin 3) :
    immersionComplexCoefficient (X ∘ u) z j = d * immersionComplexCoefficient X (u z) j := by
  have hY := hX.comp z (hu.differentiableAt.restrictScalars ℝ)
  have hs := (immersionComplexCoefficient_hasFDerivAt hX).comp z (hu.hasFDerivAt.restrictScalars ℝ)
  have he := (immersionComplexCoefficient_hasFDerivAt hY).unique hs
  apply realCoefficientDerivative_injective
  ext v
  have hh := congrArg (fun D : ℂ →L[ℝ] (Fin 3 → ℝ) => D v j) he
  change (v*immersionComplexCoefficient (X ∘ u) z j).re = ((v*d)*immersionComplexCoefficient X (u z) j).re at hh
  change (v*immersionComplexCoefficient (X ∘ u) z j).re = (v*(d*immersionComplexCoefficient X (u z) j)).re
  rwa [← mul_assoc]

theorem immersionGaussMap_comp_holomorphic {X : ℂ → Fin 3 → ℝ} {u : ℂ → ℂ} {z d : ℂ}
    (hX : DifferentiableAt ℝ X (u z)) (hu : HasDerivAt u d z) (hn : d ≠ 0) :
    immersionGaussMap (X ∘ u) z = immersionGaussMap X (u z) := by
  change immersionComplexCoefficient (X ∘ u) z 2 /
      (immersionComplexCoefficient (X ∘ u) z 0-I*immersionComplexCoefficient (X ∘ u) z 1) = _
  simp only [immersionComplexCoefficient_comp_holomorphic hX hu]
  rw [mul_left_comm I d,← mul_sub]
  exact mul_div_mul_left _ _ hn

/-- The order of a meromorphic one-form does not change under a regular
holomorphic change of parameter, including its Jacobian. -/
theorem meromorphic_oneForm_order_change {f u v : ℂ → ℂ} {z : ℂ}
    (hu : AnalyticAt ℂ u z) (hn : deriv u z ≠ 0) (hf : MeromorphicAt f (u z))
    (he : v =ᶠ[𝓝[≠] z] fun w => deriv u w*f (u w)) :
    MeromorphicAt v z ∧ meromorphicOrderAt v z = meromorphicOrderAt f (u z) := by
  have hmer := hu.deriv.meromorphicAt.mul (hf.comp_analyticAt hu)
  have hunit : meromorphicOrderAt (deriv u) z = 0 := by
    simp [hu.deriv.meromorphicOrderAt_eq,hu.deriv.analyticOrderAt_eq_zero.mpr hn]
  exact ⟨hmer.congr he.symm,by
    rw [meromorphicOrderAt_congr he]
    change meromorphicOrderAt (deriv u * (f ∘ u)) z = _
    rw [meromorphicOrderAt_mul hu.deriv.meromorphicAt (hf.comp_analyticAt hu),
      hunit,zero_add,meromorphicOrderAt_comp_of_deriv_ne_zero hu hn]⟩

/-- The two end orders computed in an exterior-end coordinate survive
passage to any other holomorphic coordinate on the compactification. -/
theorem actual_end_double_poles_change_coordinate {X : ℂ → Fin 3 → ℝ} {Y : ℂ → Fin 3 → ℝ}
    {u : ℂ → ℂ} {z : ℂ} (hu : AnalyticAt ℂ u z) (hn : deriv u z ≠ 0)
    (hY : Y =ᶠ[𝓝[≠] z] X ∘ u)
    (hX : ∀ᶠ y in 𝓝[≠] u z, DifferentiableAt ℝ X y ∧ DifferentiableAt ℂ (immersionGaussMap X) y)
    (hh : MeromorphicAt (fun w => immersionComplexCoefficient X w 2) (u z))
    (hg : MeromorphicAt (immersionGaussLogDerivative X) (u z)) :
    MeromorphicAt (fun w => immersionComplexCoefficient Y w 2) z ∧
      meromorphicOrderAt (fun w => immersionComplexCoefficient Y w 2) z =
        meromorphicOrderAt (fun w => immersionComplexCoefficient X w 2) (u z) ∧
      MeromorphicAt (immersionGaussLogDerivative Y) z ∧
      meromorphicOrderAt (immersionGaussLogDerivative Y) z =
        meromorphicOrderAt (immersionGaussLogDerivative X) (u z) := by
  have hX' := hu.differentiableAt.hasDerivAt.tendsto_nhdsNE hn |>.eventually hX
  have hu' : ∀ᶠ y in 𝓝[≠] z, AnalyticAt ℂ u y := hu.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  have hn' : ∀ᶠ y in 𝓝[≠] z, deriv u y ≠ 0 :=
    ((hu.deriv.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hn).filter_mono nhdsWithin_le_nhds
  have hc : ∀ᶠ w in 𝓝[≠] z, immersionComplexCoefficient Y w = immersionComplexCoefficient (X ∘ u) w := by
    filter_upwards [punctured_germ_eventually_local hY] with w hw
    funext j
    have he : (fun v => Y v j) =ᶠ[𝓝 w] (fun v => (X ∘ u) v j) := hw.fun_comp (fun a => a j)
    unfold immersionComplexCoefficient scalarComplexCoefficient
    rw [he.fderiv_eq]
  have h₁ := meromorphic_oneForm_order_change (f := fun w => immersionComplexCoefficient X w 2)
    (v := fun w => immersionComplexCoefficient Y w 2) hu hn hh (by
      filter_upwards [hc,hX',hu'] with w hw hx hau
      rw [hw,immersionComplexCoefficient_comp_holomorphic hx.1 hau.differentiableAt.hasDerivAt])
  have ge : immersionGaussMap Y =ᶠ[𝓝[≠] z] (immersionGaussMap X) ∘ u := by
    filter_upwards [hc,hX',hu',hn'] with w hw hx hau hnu
    change nullGauss (immersionComplexCoefficient Y w) = _
    rw [hw]
    exact immersionGaussMap_comp_holomorphic hx.1 hau.differentiableAt.hasDerivAt hnu
  have h₂ := meromorphic_oneForm_order_change (v := immersionGaussLogDerivative Y) hu hn hg (by
    filter_upwards [punctured_germ_eventually_local ge,hX',hu'] with w hw hx hau
    unfold immersionGaussLogDerivative
    rw [hw.deriv_eq,hw.self_of_nhds,deriv_comp w hx.2 hau.differentiableAt]
    change _ / immersionGaussMap X (u w) = _
    ring)
  exact ⟨h₁.1,h₁.2,h₂⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_end_double_poles_change_coordinate
