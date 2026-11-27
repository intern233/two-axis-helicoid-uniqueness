import TwoAxisHelicoid.BoundedSmoothODE
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Complex.Basic

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped Topology ContDiff NNReal

/-- Integrate a uniformly bounded field of real-linear maps on the
plane along straight target segments. The endpoints depend continuously
on their direction; the entire trajectories satisfy the speed bound. -/
theorem bounded_plane_radial_lifts {A : ℂ → ℂ →L[ℝ] ℂ} (smooth : ContDiff ℝ 1 A)
    {M : ℝ} (mp : 0≤M) (bound : ∀ z, ‖A z‖≤M) (a : ℂ) {r : ℝ} (rp : 0<r) :
    ∃ γ : ℂ → ℝ → ℂ, (∀ v, γ v 0=a) ∧
      (∀ v t, t∈Icc (0:ℝ) 1 → HasDerivAt (γ v) (A (γ v t) v) t) ∧
      (∀ v t, t∈Icc (0:ℝ) 1 → dist (γ v t) a≤M*‖v‖*t) ∧
      ContinuousOn (fun v => γ v 1) (ball 0 r) := by
  have ex (v : ℂ) : ∃ g : ℝ → ℂ, g 0=a ∧ ∀ t∈Icc (0:ℝ) 1, HasDerivAt g (A (g t) v) t :=
    bounded_smooth_vector_field_unit_solution (smooth.clm_apply contDiff_const) (mul_nonneg mp (norm_nonneg v))
      (fun x => ((A x).le_opNorm v).trans (mul_le_mul_of_nonneg_right (bound x) (norm_nonneg v))) a
  choose γ at0 ode using ex
  have speed (v : ℂ) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : dist (γ v t) a≤M*‖v‖*t := by
    have b (s : ℝ) (_ : s∈Ico (0:ℝ) 1) : ‖A (γ v s) v‖≤M*‖v‖ :=
      ((A _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (bound _) (norm_nonneg v))
    simpa only [at0,← dist_eq_norm,sub_zero] using norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs => (ode v s hs).hasDerivWithinAt) b t ht
  let P := fun v t => (γ v t,v)
  let W := fun z : ℂ × ℂ => (A z.1 z.2,(0:ℂ))
  have sw : ContDiff ℝ 1 W := ((smooth.comp contDiff_fst).clm_apply contDiff_snd).prodMk contDiff_const
  let C := closedBall (a,(0:ℂ)) (M*r+r)
  obtain ⟨K,lip⟩ := sw.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall (a,(0:ℂ)) (M*r+r)) (isCompact_closedBall _ _)
  have track (v : ℂ) (hv : v∈ball (0:ℂ) r) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : P v t∈C := by
    have small : ‖v‖<r := by simpa only [mem_ball,dist_zero_right] using hv
    change max (dist (γ v t) a) (dist v 0)≤M*r+r
    rw [dist_zero_right]
    apply max_le
    · calc _ ≤ M*‖v‖*t := speed _ _ ht
           _ ≤ M*r*1 := mul_le_mul (mul_le_mul_of_nonneg_left small.le mp) ht.2 ht.1 (mul_nonneg mp rp.le)
           _ ≤ _ := by rw [mul_one]; linarith
    · linarith [mul_nonneg mp rp.le]
  have dd (v : ℂ) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt (P v) (W (P v t)) t :=
    (ode v t ht).prodMk (hasDerivAt_const t v)
  have continuous (v : ℂ) : ContinuousOn (P v) (Icc (0:ℝ) 1) := fun t ht => (dd v t ht).continuousAt.continuousWithinAt
  refine ⟨γ,at0,ode,speed,?_⟩
  let k : ℝ≥0 := ⟨Real.exp K,(Real.exp_pos _).le⟩
  apply LipschitzOnWith.continuousOn (K:=k)
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  have same := dist_le_of_trajectories_ODE_of_mem (v:=fun _ => W) (s:=fun _ => C) (fun _ _ => lip)
    (continuous v) (fun t ht => (dd v t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => track v hv t (Ico_subset_Icc_self ht))
    (continuous w) (fun t ht => (dd w t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => track w hw t (Ico_subset_Icc_self ht))
    (δ:=dist v w) (by simp [P,Prod.dist_eq,at0]) 1 (right_mem_Icc.mpr zero_le_one)
  have fst : dist (γ v 1) (γ w 1)≤dist (P v 1) (P w 1) := le_max_left _ _
  change dist (γ v 1) (γ w 1)≤Real.exp (K:ℝ)*dist v w
  exact fst.trans (by simpa only [sub_zero,mul_one,mul_comm (dist v w)] using same)

/-- A uniform bound for the inverse differential on a physical patch
yields a genuine inverse branch over a target disk. The cutoff field A
agrees with that inverse on the patch. No second derivative bound enters
the radius estimate. -/
theorem radial_inverse_branch_on_disk {F : ℂ → ℂ} {a : ℂ} {R M r : ℝ}
    (mp : 0≤M) (rp : 0<r) (room : M*r<R) {A : ℂ → ℂ →L[ℝ] ℂ}
    (smooth : ContDiff ℝ 1 A) (bound : ∀ z, ‖A z‖≤M)
    (derivative : ∀ z∈ball a R, ∃ e : ℂ ≃L[ℝ] ℂ, HasFDerivAt F (e : ℂ →L[ℝ] ℂ) z ∧
      (e.symm : ℂ →L[ℝ] ℂ)=A z) :
    ∃ s : ℂ → ℂ, s (F a)=a ∧ ∀ w∈ball (F a) r,
      s w∈ball a R ∧ F (s w)=w ∧ HasFDerivAt s (A (s w)) w := by
  obtain ⟨γ,start,ode,speed,continuous⟩ := bounded_plane_radial_lifts smooth mp bound a rp
  have within {v : ℂ} (hv : ‖v‖<r) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : γ v t∈ball a R := by
    calc dist (γ v t) a≤M*‖v‖*t := speed _ _ ht
         _ ≤ M*r*1 := mul_le_mul (mul_le_mul_of_nonneg_left hv.le mp) ht.2 ht.1 (mul_nonneg mp rp.le)
         _ < R := by simpa only [mul_one] using room
  have endpoint {v : ℂ} (hv : ‖v‖<r) : F (γ v 1)=v+F a := by
    let h := fun t : ℝ => F (γ v t)-t • v
    have dz (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt h 0 t := by
      obtain ⟨e,d,inv⟩ := derivative _ (within hv ht)
      have chain := d.comp_hasDerivAt t (ode v t ht)
      rw [← inv] at chain
      have tangent : (e : ℂ →L[ℝ] ℂ) ((e.symm : ℂ →L[ℝ] ℂ) v)=v := e.apply_symm_apply _
      rw [tangent] at chain
      change HasDerivAt (fun s : ℝ => F (γ v s)-s • v) 0 t
      simpa only [Function.comp_def,Pi.sub_def,sub_self,one_smul] using chain.sub ((hasDerivAt_id' t).smul_const v)
    have zero := norm_image_sub_le_of_norm_deriv_le_segment' (fun t ht => (dz t ht).hasDerivWithinAt)
      (C:=0) (fun _ _ => by simp) 1 (right_mem_Icc.mpr zero_le_one)
    simp only [zero_mul,norm_le_zero_iff,sub_eq_zero,h,start,one_smul,zero_smul,sub_zero] at zero
    exact sub_eq_iff_eq_add'.mp zero
  let s := fun w => γ (w-F a) 1
  have small {w : ℂ} (hw : w∈ball (F a) r) : ‖w-F a‖<r := by simpa only [mem_ball,dist_eq_norm] using hw
  have right {w : ℂ} (hw : w∈ball (F a) r) : F (s w)=w := (endpoint (small hw)).trans (sub_add_cancel _ _)
  have center := speed 0 1 (right_mem_Icc.mpr zero_le_one)
  have atCenter : γ 0 1=a := dist_le_zero.mp (by simpa only [norm_zero,mul_zero,zero_mul] using center)
  refine ⟨s,by simpa only [s,sub_self] using atCenter,?_⟩
  intro w hw
  have here : s w∈ball a R := within (small hw) (right_mem_Icc.mpr zero_le_one)
  obtain ⟨e,d,inv⟩ := derivative (s w) here
  have ballV : w-F a∈ball (0:ℂ) r := by simpa only [mem_ball,dist_zero_right] using small hw
  have shift : ContinuousAt (fun y : ℂ => y-F a) w := continuousAt_id.sub continuousAt_const
  have cs : ContinuousAt s w := (continuous.continuousAt (isOpen_ball.mem_nhds ballV)).comp (f:=fun y : ℂ => y-F a) shift
  exact ⟨here,right hw,inv ▸ HasFDerivAt.of_local_left_inverse cs d
    (Filter.mem_of_superset (isOpen_ball.mem_nhds hw) (fun _ i => right i))⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.bounded_plane_radial_lifts
#print axioms TwoAxisHelicoid.radial_inverse_branch_on_disk
