import TwoAxisHelicoid.SmoothFlowTransport
import TwoAxisHelicoid.PeriodTorusTopology
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue

namespace TwoAxisHelicoid
open Complex Set Metric Topology
open scoped Topology NNReal

/-- A periodic C¹ field on the whole marked plane is bounded and
globally Lipschitz, including at the lifted punctures. -/
theorem periodic_smooth_field_bounds (L : PeriodPair) {W : ℂ → ℂ} (sm : ContDiff ℝ 1 W)
    (per : ∀ z w, w∈L.lattice → W (z+w)=W z) :
    ∃ B K : ℝ≥0, (∀ z, ‖W z‖≤B) ∧ LipschitzWith K W := by
  have dp (z w : ℂ) (hw : w∈L.lattice) : fderiv ℝ W (z+w)=fderiv ℝ W z := by
    have eq : (fun u => W (u+w))=W := funext fun u => per u w hw
    exact (fderiv_comp_add_right (𝕜 := ℝ) (f := W) (x := z) w).symm.trans (congrArg (fun f => fderiv ℝ f z) eq)
  obtain ⟨B,bd⟩ := (IsZLattice.isCompact_range_of_periodic L.lattice (fun z => ‖W z‖₊)
    sm.continuous.nnnorm (fun z w hw => congrArg nnnorm (per z w hw))).bddAbove
  obtain ⟨K,kd⟩ := (IsZLattice.isCompact_range_of_periodic L.lattice (fun z => ‖fderiv ℝ W z‖₊)
    (sm.continuous_fderiv one_ne_zero).nnnorm (fun z w hw => congrArg nnnorm (dp z w hw))).bddAbove
  exact ⟨B,K,fun z => bd (mem_range_self z),lipschitzWith_of_nnnorm_fderiv_le (sm.differentiable one_ne_zero)
    (fun z => kd (mem_range_self z))⟩

private theorem unit_flow_endpoint_continuous {W : ℂ → ℂ} {K : ℝ≥0} (lip : LipschitzWith K W)
    {P : ℂ → ℝ → ℂ} (start : ∀ x, P x 0=x)
    (ode : ∀ x t, t∈Icc (0:ℝ) 1 → HasDerivAt (P x) (W (P x t)) t) :
    Continuous (fun x => P x 1) := by
  let k : ℝ≥0 := ⟨Real.exp K,(Real.exp_pos _).le⟩
  apply LipschitzWith.continuous (K := k)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have cont (p : ℂ) : ContinuousOn (P p) (Icc (0:ℝ) 1) := fun t ht => (ode p t ht).continuousAt.continuousWithinAt
  have one := dist_le_of_trajectories_ODE (v := fun _ => W) (fun _ => lip)
    (cont x) (fun t ht => (ode x t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (cont y) (fun t ht => (ode y t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (δ := dist x y) (by rw [start,start]) 1 (right_mem_Icc.mpr zero_le_one)
  change dist (P x 1) (P y 1)≤Real.exp K*dist x y
  simpa only [sub_zero,mul_one,mul_comm (dist x y)] using one

private theorem reverse_unit_trajectory {W : ℂ → ℂ} {γ : ℝ → ℂ}
    (ode : ∀ t∈Icc (0:ℝ) 1, HasDerivAt γ (W (γ t)) t) :
    ∀ s∈Icc (0:ℝ) 1, HasDerivAt (fun r => γ (1-r)) (-W (γ (1-s))) s := by
  intro s hs
  exact (ode (1-s) ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩).comp_const_sub 1 s

/-- The time-one map of a periodic smooth plane field is an actual
homeomorphism, commutes with the lattice, and equals the endpoint of
every solution. Its inverse is the flow of the negative field. -/
theorem periodic_smooth_field_homeomorph (L : PeriodPair) {W : ℂ → ℂ} (sm : ContDiff ℝ 1 W)
    (per : ∀ z w, w∈L.lattice → W (z+w)=W z) :
    ∃ F : ℂ ≃ₜ ℂ, (∀ z w, w∈L.lattice → F (z+w)=F z+w) ∧
      (∀ p, W p=0 → F p=p) ∧
      (∀ γ : ℝ → ℂ, (∀ t∈Icc (0:ℝ) 1, HasDerivAt γ (W (γ t)) t) → F (γ 0)=γ 1) ∧
      ∀ γ : ℝ → ℂ, (∀ t∈Icc (0:ℝ) 1, HasDerivAt γ (-W (γ t)) t) → F.symm (γ 0)=γ 1 := by
  let N := fun z => -W z
  have sn : ContDiff ℝ 1 N := sm.neg
  obtain ⟨B,K,b,lip⟩ := periodic_smooth_field_bounds L sm per
  obtain ⟨D,J,d,ln⟩ := periodic_smooth_field_bounds L sn (fun z w hw => congrArg Neg.neg (per z w hw))
  choose P p0 dP using fun x => bounded_smooth_vector_field_unit_solution sm B.coe_nonneg b x
  choose Q q0 dQ using fun x => bounded_smooth_vector_field_unit_solution sn D.coe_nonneg d x
  have zero : (0:ℝ)∈Icc 0 1 := left_mem_Icc.mpr zero_le_one
  have one : (1:ℝ)∈Icc 0 1 := right_mem_Icc.mpr zero_le_one
  have ep (γ : ℝ → ℂ) (de : ∀ t∈Icc (0:ℝ) 1, HasDerivAt γ (W (γ t)) t) : P (γ 0) 1=γ 1 :=
    smooth_field_unit_trajectory_unique sm (dP _) de zero (p0 _) one
  have eq (γ : ℝ → ℂ) (de : ∀ t∈Icc (0:ℝ) 1, HasDerivAt γ (N (γ t)) t) : Q (γ 0) 1=γ 1 :=
    smooth_field_unit_trajectory_unique sn (dQ _) de zero (q0 _) one
  let F : ℂ ≃ₜ ℂ :=
    { toFun := fun z => P z 1
      invFun := fun z => Q z 1
      left_inv := fun z => by
        have e := eq (fun s => P z (1-s)) (reverse_unit_trajectory (dP z))
        simpa only [sub_zero,sub_self,p0] using e
      right_inv := fun z => by
        have e := ep (fun s => Q z (1-s)) (fun s hs => by simpa only [N,neg_neg] using reverse_unit_trajectory (dQ z) s hs)
        simpa only [sub_zero,sub_self,q0] using e
      continuous_toFun := unit_flow_endpoint_continuous lip p0 dP
      continuous_invFun := unit_flow_endpoint_continuous ln q0 dQ }
  refine ⟨F,?_,?_,ep,eq⟩
  · intro z w hw
    have e := ep (fun s => P z s+w) (fun s hs => by rw [per _ w hw]; exact (dP z s hs).add_const w)
    change P (z+w) 1=P z 1+w
    simpa only [p0] using e
  · intro z hz
    exact ep (fun _ => z) (fun s _ => by rw [hz]; exact hasDerivAt_const _ _)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.periodic_smooth_field_homeomorph
