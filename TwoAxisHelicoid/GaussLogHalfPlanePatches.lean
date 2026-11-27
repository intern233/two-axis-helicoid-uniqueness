import TwoAxisHelicoid.HelicoidEndPotential
import TwoAxisHelicoid.CoordinateAreaHessian
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.MeanValue

namespace TwoAxisHelicoid
open Complex Set Metric

private theorem half_plane_affine_error {W : ℂ → ℂ} {B ε : ℝ}
    (df : ∀ z : ℂ, B<z.re → DifferentiableAt ℂ W z)
    (bound : ∀ z : ℂ, B<z.re → ‖deriv W z-I‖≤ε)
    {c z : ℂ} (hc : B<c.re) (hz : B<z.re) : ‖W z-W c-I*(z-c)‖≤ε*‖z-c‖ := by
  let f := fun u => W u-I*u
  let S := {u : ℂ | B<u.re}
  have d (u) (hu : u ∈ S) : HasDerivAt f (deriv W u-I) u := by
    simpa only [mul_one,Pi.sub_def,id_eq,f] using! (df u hu).hasDerivAt.sub ((hasDerivAt_id u).const_mul I)
  have e := (convex_halfSpace_re_gt B).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (d u hu).hasDerivWithinAt) (fun u hu => bound u hu) hc hz
  calc
    _ = ‖f z-f c‖ := by dsimp [f]; congr 1; ring
    _ ≤ _ := e

/-- When the logarithmic Gauss derivative is close to i in a right
half-plane, every vertical line there meets the unit Gauss locus.
This also allows a logarithmic drift of the center of the end. -/
theorem gauss_log_has_unit_center_on_vertical {W : ℂ → ℂ} {B x : ℝ}
    (df : ∀ z : ℂ, B<z.re → DifferentiableAt ℂ W z)
    (bound : ∀ z : ℂ, B<z.re → ‖deriv W z-I‖≤1/2) (hx : B<x) :
    ∃ c : ℂ, c.re=x ∧ (W c).re=0 := by
  let line := fun y : ℝ => (x:ℂ)+(y:ℂ)*I
  let h := fun y : ℝ => (W (line y)).re
  have rx (y) : (line y).re=x := by simp [line]
  have cl : Continuous line := by dsimp [line]; fun_prop
  have ch : Continuous h := continuous_iff_continuousAt.mpr fun y =>
    continuous_re.continuousAt.comp ((df _ ((rx y).symm ▸ hx)).continuousAt.comp cl.continuousAt)
  have estimate (y : ℝ) : |h y-(W x).re+y|≤(1/2)*|y| := by
    have e := half_plane_affine_error df bound (c := (x:ℂ)) (z := line y) hx ((rx y).symm ▸ hx)
    have hr := (abs_re_le_norm _).trans e
    simpa [line,h,Complex.I_mul_re,add_assoc,sub_eq_add_neg] using hr
  let R := 2*(|(W x).re|+1)
  have hr : 0<R := by dsimp [R]; positivity
  have low : h R≤0 := by
    have he := (abs_le.mp (estimate R)).2
    rw [abs_of_pos hr] at he
    dsimp [R] at he ⊢
    linarith [le_abs_self (W x).re]
  have high : 0≤h (-R) := by
    have he := (abs_le.mp (estimate (-R))).1
    rw [abs_neg,abs_of_pos hr] at he
    dsimp [R] at he ⊢
    linarith [neg_abs_le (W x).re]
  obtain ⟨y,_,hy⟩ := intermediate_value_Icc' (show -R≤R by linarith) ch.continuousOn (show (0:ℝ)∈Icc (h R) (h (-R)) from ⟨low,high⟩)
  exact ⟨line y,rx y,hy⟩

/-- A double-pole logarithmic derivative, once written in a reciprocal
coordinate so that its limit is i, supplies almost helicoidal Gauss
potentials on arbitrarily far translates of every fixed compact patch. -/
theorem gauss_log_half_plane_potential_on_compact {W : ℂ → ℂ}
    (asym : ∀ δ : ℝ, 0<δ → ∃ B : ℝ, ∀ z : ℂ, B<z.re →
      AnalyticAt ℂ W z ∧ ‖deriv W z-I‖≤δ)
    {K : Set (ℝ × ℝ)} (compact : IsCompact K) {ε : ℝ} (he : 0<ε) (R : ℝ) :
    ∃ c : ℂ, (W c).re=0 ∧ ∀ p∈K, R<(planeComplex p+c).re ∧ AnalyticAt ℂ W (planeComplex p+c) ∧
      |gaussNormalDirichletDensity (fun z => W (z+c)) p-2*helicoidGroundState p.2^2|≤ε := by
  obtain ⟨δ,hd,uniform⟩ := continuous_compact_uniform_small_parameter (endPotentialKernel_continuous 1)
    (compact.image continuous_snd) he
  obtain ⟨M,hm,range⟩ := (compact.image planeComplex_continuous).isBounded.exists_pos_norm_le
  let η := min (1/2:ℝ) (δ/(M+1))
  have hp : 0<η := lt_min (by norm_num) (div_pos hd (by linarith))
  obtain ⟨B,hB⟩ := asym η hp
  let T := max R B+M+1
  have ht : B<T := by dsimp [T]; linarith [le_max_right R B]
  obtain ⟨c,rc,zero⟩ := gauss_log_has_unit_center_on_vertical (fun z hz => (hB z hz).1.differentiableAt)
    (fun z hz => (hB z hz).2.trans (min_le_left _ _)) ht
  refine ⟨c,zero,fun p hmem => ?_⟩
  let z := planeComplex p+c
  have norm : ‖planeComplex p‖≤M := range _ (mem_image_of_mem _ hmem)
  have left : max R B<z.re := by
    change max R B<(planeComplex p+c).re
    rw [add_re,rc]
    dsimp [T]
    linarith [(abs_le.mp ((abs_re_le_norm _).trans norm)).1]
  have safe : B<z.re := (le_max_right _ _).trans_lt left
  obtain ⟨an,bd⟩ := hB z safe
  have error := half_plane_affine_error (fun w hw => (hB w hw).1.differentiableAt) (fun w hw => (hB w hw).2)
    (rc.symm ▸ ht) safe
  let F := W z-W c-I*planeComplex p
  have level : ‖F‖≤δ := by
    have est : ‖F‖≤η*‖planeComplex p‖ := by simpa only [z,add_sub_cancel_right,F] using error
    exact est.trans ((mul_le_mul (min_le_right _ _) (by linarith : ‖planeComplex p‖≤M+1) (norm_nonneg _) (div_pos hd (by linarith)).le).trans
      (le_of_eq (div_mul_cancel₀ δ (by linarith : M+1≠0))))
  have bd' : ‖deriv W z-I‖≤δ := bd.trans ((min_le_right _ _).trans (div_le_self hd.le (by linarith)))
  have e := uniform p.2 ⟨p,hmem,rfl⟩ (F,deriv W z-I) (norm_prod_le_iff.mpr ⟨level,bd'⟩)
  have der : HasDerivAt (fun w => W (w+c)) (deriv W z) (planeComplex p) := by
    simpa only [Function.comp_def,id_eq,mul_one] using! an.differentiableAt.hasDerivAt.comp (planeComplex p) ((hasDerivAt_id _).add_const c)
  have fr : -p.2+F.re=(W z).re := by simp [F,zero,planeComplex_im]
  refine ⟨(le_max_left _ _).trans_lt left,an,?_⟩
  rw [endPotentialKernel_zero] at e
  rw [gaussNormalDirichletDensity_formula der]
  simpa [Real.dist_eq,endPotentialKernel,helicoidGroundState,fr,z,div_eq_mul_inv] using e

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.gauss_log_has_unit_center_on_vertical
#print axioms TwoAxisHelicoid.gauss_log_half_plane_potential_on_compact
