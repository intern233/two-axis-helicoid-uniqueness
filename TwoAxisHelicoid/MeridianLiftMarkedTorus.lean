import TwoAxisHelicoid.TorusActualLifts
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace TwoAxisHelicoid
open Complex Set Topology

/-- A meridian parametrized as a circle with a continuous angular
coordinate on the entire marked torus has an injective real lift with
nonzero lattice displacement. No smoothness of the marking is used. -/
theorem meridian_has_essential_marked_lift (L : PeriodPair) (β : C(Circle,PeriodTorus L)) (θ : C(PeriodTorus L,Circle))
    (hr : ∀ u, θ (β u) = u) :
    ∃ (ξ : C(ℝ,ℂ)) (ω : ℂ), ω ≠ 0 ∧ ω ∈ L.lattice ∧
      (∀ t, periodTorusProjection L (ξ t) = β (Circle.exp (2*Real.pi*t))) ∧
      (∀ t, ξ (t+1) = ξ t+ω) ∧ Function.Injective ξ := by
  let k := 2*Real.pi
  have hk : k ≠ 0 := by dsimp [k]; positivity
  let c : C(ℝ,Circle) := ⟨fun t => Circle.exp (k*t),Circle.exp.continuous.comp (continuous_const.mul continuous_id)⟩
  have hc0 : c 0 = 1 := by change Circle.exp (k*0) = 1; simp
  have hc1 (t : ℝ) : c (t+1) = c t := by
    change Circle.exp (k*(t+1)) = Circle.exp (k*t)
    rw [mul_add,mul_one]; exact Circle.periodic_exp _
  let π : C(ℂ,PeriodTorus L) := ⟨periodTorusProjection L,QuotientAddGroup.continuous_mk⟩
  obtain ⟨z,hz⟩ := (Quotient.mk_surjective : Function.Surjective π) (β (c 0))
  have hπ := periodTorusProjection_isCoveringMap L
  obtain ⟨ξ,⟨_,hξ⟩,_⟩ := hπ.existsUnique_continuousMap_lifts (β.comp c) 0 z hz
  have hproj (t : ℝ) : π (ξ t) = β (c t) := congrFun hξ t
  let ω := ξ 1-ξ 0
  have hωL : ω ∈ L.lattice := (periodTorusProjection_eq_iff L (ξ 0) (ξ 1)).mp <| by
    change π (ξ 0) = π (ξ 1)
    rw [hproj,hproj,← hc1 0,zero_add]
  have hper : ∀ t, ξ (t+1) = ξ t+ω := by
    apply congrFun
    apply hπ.eq_of_comp_eq (ξ.continuous.comp (continuous_id.add continuous_const)) (ξ.continuous.add continuous_const) _ 0
    · change ξ (0+1) = ξ 0+(ξ 1-ξ 0)
      rw [zero_add]; abel
    · funext t
      change π (ξ (t+1)) = periodTorusProjection L (ξ t+ω)
      rw [periodTorusProjection_add_lattice L _ _ hωL]
      exact (hproj _).trans ((congrArg β (hc1 t)).trans (hproj t).symm)
  have hθ0 : Circle.exp 0 = (θ.comp π) (ξ 0) := by
    change Circle.exp 0 = θ (π (ξ 0))
    rw [hproj,hr,hc0,Circle.exp_zero]
  have he := Circle.isCoveringMap_exp
  obtain ⟨φ,⟨hφ0,hφ⟩,_⟩ := he.existsUnique_continuousMap_lifts (θ.comp π) (ξ 0) 0 hθ0
  have hid : φ ∘ ξ = fun t : ℝ => k*t := by
    apply he.eq_of_comp_eq (φ.continuous.comp ξ.continuous) (continuous_const.mul continuous_id) _ 0
    · change φ (ξ 0) = k*(0:ℝ)
      rw [mul_zero]
      exact hφ0
    · funext t
      change Circle.exp (φ (ξ t)) = c t
      exact (congrFun hφ (ξ t)).trans (by change θ (π (ξ t)) = c t; rw [hproj,hr])
  have hxi : Function.Injective ξ := by
    intro a b hab
    have he : k*a = k*b := (congrFun hid a).symm.trans ((congrArg φ hab).trans (congrFun hid b))
    exact mul_left_cancel₀ hk he
  have hω : ω ≠ 0 := by
    intro hzero
    have hh := hper 0
    rw [zero_add,hzero,add_zero] at hh
    exact one_ne_zero (hxi hh)
  exact ⟨ξ,ω,hω,hωL,hproj,hper,hxi⟩

/-- Every meridian circle of a genuine boundary-torus homeomorphism
satisfies the lifting criterion, without supplying a marked homotopy. -/
theorem marked_boundary_torus_meridian_lift (L : PeriodPair) (H : Circle × Circle ≃ₜ PeriodTorus L) (a : Circle) :
    ∃ (ξ : C(ℝ,ℂ)) (ω : ℂ), ω ≠ 0 ∧ ω ∈ L.lattice ∧
      (∀ t, periodTorusProjection L (ξ t) = H (a,Circle.exp (2*Real.pi*t))) ∧
      (∀ t, ξ (t+1) = ξ t+ω) ∧ Function.Injective ξ :=
  meridian_has_essential_marked_lift L ⟨fun u => H (a,u),H.continuous.comp (continuous_const.prodMk continuous_id)⟩
    ⟨fun x => (H.symm x).2,continuous_snd.comp H.symm.continuous⟩
    (fun u => congrArg Prod.snd (H.symm_apply_apply (a,u)))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_boundary_torus_meridian_lift
