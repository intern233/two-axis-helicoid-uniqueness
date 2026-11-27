import TwoAxisHelicoid.PeriodicSmoothFlow
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

namespace TwoAxisHelicoid
open Set Metric
open scoped Topology NNReal ContDiff Manifold

/-- A bounded C¹ plane field has a complete autonomous flow.
The common unit time of local existence is obtained from bounded speed
and Picard--Lindelöf on a compact ball around the initial position. -/
theorem bounded_plane_field_global_flow {V : ℂ → ℂ} (sm : ContDiff ℝ 1 V)
    {B : ℝ≥0} (bound : ∀ z, ‖V z‖≤B) :
    ∃ Φ : ℝ → ℂ → ℂ, (∀ z, Φ 0 z=z) ∧ (∀ a b z, Φ (a+b) z=Φ a (Φ b z)) ∧
      (∀ z t, HasDerivAt (fun s => Φ s z) (V (Φ t z)) t) ∧
      ∀ (γ : ℝ → ℂ), (∀ t, HasDerivAt γ (V (γ t)) t) → ∀ t, Φ t (γ 0)=γ t := by
  let W : (x : ℂ) → TangentSpace 𝓘(ℝ,ℂ) x := V
  have sw : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).tangent) 1 (fun x => (⟨x,W x⟩ : TangentBundle 𝓘(ℝ,ℂ) ℂ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr sm
  have localSol (x : ℂ) : ∃ γ : ℝ → ℂ, γ 0=x ∧ IsMIntegralCurveOn γ W (Ioo (-1:ℝ) 1) := by
    obtain ⟨K,lip⟩ := sm.contDiffOn.exists_lipschitzOnWith one_ne_zero
      (convex_closedBall x (B:ℝ)) (isCompact_closedBall x (B:ℝ))
    have hp : IsPicardLindelof (fun _ : ℝ => V) (tmin:=-1) (tmax:=1)
        ⟨0,by norm_num⟩ x B 0 B K := by
      apply IsPicardLindelof.of_time_independent (fun z _ => bound z) lip
      change (B:ℝ)*max ((1:ℝ)-0) (0-(-1))≤B-0
      norm_num
    obtain ⟨γ,at0,d⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    exact ⟨γ,at0,fun t ht =>
      ((d t (Ioo_subset_Icc_self ht)).mono Ioo_subset_Icc_self).hasFDerivWithinAt.hasMFDerivWithinAt⟩
  choose P start ode using exists_isMIntegralCurve_of_isMIntegralCurveOn sw zero_lt_one localSol
  refine ⟨fun t z => P z t,start,?_,?_,?_⟩
  · intro a b z
    have same := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless sw ((ode z).comp_add b) (ode (P z b))
      (t₀:=0) (by simp [start])
    exact congrFun same a
  · intro z t
    apply hasDerivAt_iff_hasFDerivAt.mpr
    exact (ode z t).hasFDerivAt
  · intro γ derivs t
    have intg : IsMIntegralCurve γ W := fun s => (derivs s).hasFDerivAt.hasMFDerivAt
    exact congrFun (isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless sw (ode (γ 0)) intg (start _)) t

/-- The complete trajectories of a periodic plane field respect the lattice
at every time; hence they induce actual trajectories on the quotient. -/
theorem periodic_plane_field_global_flow (L : PeriodPair) {V : ℂ → ℂ} (sm : ContDiff ℝ 1 V)
    (periodic : ∀ z w, w∈L.lattice → V (z+w)=V z) :
    ∃ Φ : ℝ → ℂ → ℂ, (∀ z, Φ 0 z=z) ∧ (∀ a b z, Φ (a+b) z=Φ a (Φ b z)) ∧
      (∀ z t, HasDerivAt (fun s => Φ s z) (V (Φ t z)) t) ∧
      (∀ t z w, w∈L.lattice → Φ t (z+w)=Φ t z+w) ∧
      ∀ z, V z=0 → ∀ t, Φ t z=z := by
  obtain ⟨B,_,bound,_⟩ := periodic_smooth_field_bounds L sm periodic
  obtain ⟨Φ,at0,add,diff,unique⟩ := bounded_plane_field_global_flow sm bound
  refine ⟨Φ,at0,add,diff,?_,?_⟩
  · intro t z w hw
    have eq := unique (fun a => Φ a z+w) (fun a => by rw [periodic _ _ hw]; exact (diff z a).add_const w) t
    simpa only [at0] using eq
  · intro z zero
    exact unique (fun _ => z) (fun t => by rw [zero]; exact hasDerivAt_const t z)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.periodic_plane_field_global_flow
