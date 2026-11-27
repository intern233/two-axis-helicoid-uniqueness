import TwoAxisHelicoid.ActualAreaVariationIndex

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology

/-- Any constant term of the analytic Gauss correction can be absorbed
into the choice of origin for the genuine height parameter. -/
theorem recentered_analytic_helicoid_area_index {X : ℂ → Fin 3 → ℝ} {α : ℝ}
    (hα : α ≠ 0) (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0)
    (hX : ∀ᶠ z in cobounded ℂ, HasFDerivAt X (nullRealDerivative
      (weierstrassTriple (exp (I*(α:ℂ)*z+F z⁻¹)) 1)) z) :
    ∃ (c : ℂ) (f : ℂ → ℂ), AnalyticAt ℂ f 0 ∧ f 0 = 0 ∧
      (∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → HasFDerivAt (fun w => X (w+c)) (nullRealDerivative
        (weierstrassTriple (exp (I*(α:ℂ)*z+infinityCorrection f z)) 1)) z) ∧
      HasInfiniteCompactActualAreaIndexAtInfinity (fun z => X (z+c))
        (fun z => I*(α:ℂ)*z+infinityCorrection f z) := by
  let k := I*(α:ℂ)
  have hk : k ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hα)
  let c := -(F 0)/k
  let u := fun w : ℂ => w/(1+c*w)
  let f := fun w : ℂ => F (u w)-F 0
  have hu0 : u 0 = 0 := by simp [u]
  have hu : AnalyticAt ℂ u 0 := analyticAt_id.div (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
    (by simp)
  have hf : AnalyticAt ℂ f 0 := ((hu0.symm ▸ hF).comp hu).sub analyticAt_const
  have hf0 : f 0 = 0 := by simp [f,hu0]
  obtain ⟨B,_,hB⟩ := hasBasis_cobounded_norm.eventually_iff.mp hX
  let R := max B 1+‖c‖+1
  have hd' (z : ℂ) (hbound : R ≤ ‖z‖) : HasFDerivAt (fun w => X (w+c))
      (nullRealDerivative (weierstrassTriple (exp (k*z+infinityCorrection f z)) 1)) z := by
    change max B 1+‖c‖+1 ≤ ‖z‖ at hbound
    have hn : ‖z‖ ≤ ‖z+c‖+‖c‖ := by simpa using norm_sub_le (z+c) c
    have hz : z ≠ 0 := by intro h; rw [h,norm_zero] at hbound; linarith [le_max_right B 1,norm_nonneg c]
    have he : u z⁻¹ = (z+c)⁻¹ := by
      have hd : 1+c*z⁻¹ = (z+c)/z := by field_simp
      unfold u
      rw [hd,div_div_eq_mul_div,inv_mul_cancel₀ hz,one_div]
    have hs : k*z+infinityCorrection f z = k*(z+c)+F (z+c)⁻¹ := by
      change k*z+(F (u z⁻¹)-F 0) = _
      rw [he,mul_add,show k*c = -(F 0) from by dsimp [c]; field_simp]
      ring
    have hd := hB (show z+c ∈ {w : ℂ | B ≤ ‖w‖} from by change B ≤ ‖z+c‖; linarith [le_max_left B 1])
    change HasFDerivAt (fun w => X (w+c)) (nullRealDerivative (weierstrassTriple (exp (k*z+infinityCorrection f z)) 1)) z
    rw [hs]
    exact (hasFDerivAt_comp_add_right c).2 hd
  exact ⟨c,f,hf,hf0,⟨R,hd'⟩,analytic_helicoid_actual_area_infinite_index hα hf hf0
    (B := R) (fun p hp => hd' _ (hp.trans (norm_le_planeComplex_norm p)))⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.recentered_analytic_helicoid_area_index
