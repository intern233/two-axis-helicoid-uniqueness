import TwoAxisHelicoid.HelicoidDistanceDifferential
import TwoAxisHelicoid.ThinGraphTaylor
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace TwoAxisHelicoid
open Real Set

theorem finite_real_dot_bound {ι : Type*} [Fintype ι] {u v : ι → ℝ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : (∑ i, (u i)^2) ≤ A^2) (hv : (∑ i, (v i)^2) ≤ B^2) :
    |∑ i, u i*v i| ≤ A*B := by
  have hC := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) u v
  have hprod := mul_le_mul hu hv (Finset.sum_nonneg (fun i _ => sq_nonneg (v i))) (sq_nonneg A)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hA hB)).mp
  simpa only [sq_abs,mul_pow] using hC.trans hprod

noncomputable def helicoidDistanceVelocity (x v : ℝ → HelicoidTubeCoordinates) (t : ℝ) : ℝ :=
  ∑ i, helicoidNormalField (x t) i*tubeCartesian (v t) i

noncomputable def helicoidDistanceAcceleration (x v a : ℝ → HelicoidTubeCoordinates) (t : ℝ) : ℝ :=
  ∑ i, (((fderiv ℝ helicoidNormalField (x t)) (v t)) i*tubeCartesian (v t) i+
    helicoidNormalField (x t) i*tubeCartesian (a t) i)

theorem helicoidDistanceVelocity_hasDerivAt {x v a : ℝ → HelicoidTubeCoordinates} {t : ℝ}
    (hx : HasDerivAt x (v t) t) (hv : HasDerivAt v (a t) t)
    (hy : x t ∈ helicoidTubeEquiv.target) :
    HasDerivAt (helicoidDistanceVelocity x v) (helicoidDistanceAcceleration x v a t) t := by
  have hn := ((helicoidNormalField_contDiffAt hy).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hx
  have hvel := tubeCartesian_hasDerivAt hv
  unfold helicoidDistanceVelocity helicoidDistanceAcceleration
  apply HasDerivAt.fun_sum
  intro i _
  exact (hasDerivAt_pi.mp hn i).mul (hasDerivAt_pi.mp hvel i)

theorem helicoidDistanceAcceleration_bound {x v a : ℝ → HelicoidTubeCoordinates} {t A : ℝ}
    (hy : x t ∈ helicoidTubeEquiv.target) (hs : |helicoidSignedDistance (x t)| ≤ 1/2)
    (hA : 0 ≤ A) (hv : (∑ i, (tubeCartesian (v t) i)^2) ≤ 1)
    (ha : (∑ i, (tubeCartesian (a t) i)^2) ≤ A^2) :
    |helicoidDistanceAcceleration x v a t| ≤ 2+A := by
  have hn : (∑ i, (((fderiv ℝ helicoidNormalField (x t)) (v t)) i)^2) ≤ 2^2 := by
    have h := helicoidSignedDistance_hessian_bound (v := v t) hy hs
    nlinarith
  have hN : (∑ i, (helicoidNormalField (x t) i)^2) ≤ (1 : ℝ)^2 := by
    change (∑ i, (standardHelicoidNormal (helicoidTubeEquiv.symm (x t)).1.2
      (helicoidTubeEquiv.symm (x t)).2 i)^2) ≤ 1^2
    rw [(standardHelicoid_unit_normal _ _).1]
    norm_num
  have h1 := finite_real_dot_bound (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (0 : ℝ) ≤ 1) hn (by simpa using hv)
  have h2 := finite_real_dot_bound (by norm_num : (0 : ℝ) ≤ 1) hA hN ha
  unfold helicoidDistanceAcceleration
  rw [Finset.sum_add_distrib]
  exact (abs_add_le _ _).trans (by simpa using add_le_add h1 h2)

/-- The thin-tube derivative estimate for an actual Euclidean curve of
speed at most one and acceleration at most `A`. Unit-speed surface geodesics
with a second fundamental form bound satisfy precisely these curve bounds. -/
theorem helicoid_distance_thin_curve_bound {x v a : ℝ → HelicoidTubeCoordinates}
    {l ε A : ℝ} (hl : 0 < l) (hε : ε ≤ 1/2) (hA : 0 ≤ A)
    (hx : ∀ t ∈ Icc 0 l, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ Icc 0 l, HasDerivAt v (a t) t)
    (hy : ∀ t ∈ Icc 0 l, x t ∈ helicoidTubeEquiv.target)
    (hsmall : ∀ t ∈ Icc 0 l, |helicoidSignedDistance (x t)| ≤ ε)
    (hspeed : ∀ t ∈ Icc 0 l, (∑ i, (tubeCartesian (v t) i)^2) ≤ 1)
    (haccel : ∀ t ∈ Icc 0 l, (∑ i, (tubeCartesian (a t) i)^2) ≤ A^2) :
    |helicoidDistanceVelocity x v 0| ≤ 2*ε/l+(2+A)*l/2 := by
  apply thin_graph_derivative_bound hl
    (f := fun t => helicoidSignedDistance (x t))
    (f₁ := helicoidDistanceVelocity x v) (f₂ := helicoidDistanceAcceleration x v a)
  · intro t ht
    exact helicoidSignedDistance_curve_hasDerivAt (hx t ht) (hy t ht)
  · intro t ht
    exact helicoidDistanceVelocity_hasDerivAt (hx t ht) (hv t ht) (hy t ht)
  · exact hsmall
  · intro t ht
    exact helicoidDistanceAcceleration_bound (hy t ht) ((hsmall t ht).trans hε) hA
      (hspeed t ht) (haccel t ht)

theorem helicoid_distance_thin_curve_sqrt_bound {x v a : ℝ → HelicoidTubeCoordinates}
    {ε A : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1/2) (hA : 0 ≤ A)
    (hx : ∀ t ∈ Icc 0 (sqrt ε), HasDerivAt x (v t) t)
    (hv : ∀ t ∈ Icc 0 (sqrt ε), HasDerivAt v (a t) t)
    (hy : ∀ t ∈ Icc 0 (sqrt ε), x t ∈ helicoidTubeEquiv.target)
    (hsmall : ∀ t ∈ Icc 0 (sqrt ε), |helicoidSignedDistance (x t)| ≤ ε)
    (hspeed : ∀ t ∈ Icc 0 (sqrt ε), (∑ i, (tubeCartesian (v t) i)^2) ≤ 1)
    (haccel : ∀ t ∈ Icc 0 (sqrt ε), (∑ i, (tubeCartesian (a t) i)^2) ≤ A^2) :
    |helicoidDistanceVelocity x v 0| ≤ (3+A/2)*sqrt ε := by
  have h := thin_graph_sqrt_bound hε0
    (f := fun t => helicoidSignedDistance (x t))
    (f₁ := helicoidDistanceVelocity x v) (f₂ := helicoidDistanceAcceleration x v a)
    (fun t ht => helicoidSignedDistance_curve_hasDerivAt (hx t ht) (hy t ht))
    (fun t ht => helicoidDistanceVelocity_hasDerivAt (hx t ht) (hv t ht) (hy t ht))
    hsmall (fun t ht => helicoidDistanceAcceleration_bound (hy t ht) ((hsmall t ht).trans hε) hA
      (hspeed t ht) (haccel t ht))
  convert h using 1
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoid_distance_thin_curve_bound
#print axioms TwoAxisHelicoid.helicoid_distance_thin_curve_sqrt_bound
