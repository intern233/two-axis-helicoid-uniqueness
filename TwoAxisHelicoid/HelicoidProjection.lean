import TwoAxisHelicoid.HelicoidDistanceDifferential
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace TwoAxisHelicoid
open Real Set Filter
open scoped Topology ContDiff

noncomputable def helicoidBaseCoordinates (y : HelicoidTubeCoordinates) : ℝ × ℝ :=
  ((helicoidTubeEquiv.symm y).1.2,(helicoidTubeEquiv.symm y).2)

theorem helicoidBaseCoordinates_contDiffAt {y : HelicoidTubeCoordinates}
    (hy : y ∈ helicoidTubeEquiv.target) :
    ContDiffAt ℝ (∞ : WithTop ℕ∞) helicoidBaseCoordinates y :=
  (helicoidTubeEquiv_inverse_contDiffAt hy).fst.snd.prodMk
    (helicoidTubeEquiv_inverse_contDiffAt hy).snd

/-- The kernel of the derivative of the actual tube projection consists
of normal vectors. The statement uses the previously constructed inverse
of the global normal-tube map. -/
theorem helicoidBaseCoordinates_kernel_normal {y v : HelicoidTubeCoordinates}
    (hy : y ∈ helicoidTubeEquiv.target)
    (hv : (fderiv ℝ helicoidBaseCoordinates y) v = 0) :
    ∃ c : ℝ, tubeCartesian v = c • helicoidNormalField y := by
  have hx : HasDerivAt (fun t : ℝ => y+t • v) v 0 := by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hym : y+(0 : ℝ) • v ∈ helicoidTubeEquiv.target := by simpa using hy
  obtain ⟨hi,he⟩ := helicoid_inverse_curve_differential hx hym
  have h₁ : HasDerivAt (fun t : ℝ => helicoidBaseCoordinates (y+t • v))
      ((((fderiv ℝ helicoidTubeEquiv.symm (y+(0 : ℝ) • v)) v).1.2),
        ((fderiv ℝ helicoidTubeEquiv.symm (y+(0 : ℝ) • v)) v).2) 0 :=
    HasDerivAt.prodMk hi.fst.snd hi.snd
  have h₂ := ((helicoidBaseCoordinates_contDiffAt hym).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hx
  have hpair : (((fderiv ℝ helicoidTubeEquiv.symm y) v).1.2,
      ((fderiv ℝ helicoidTubeEquiv.symm y) v).2) = (0 : ℝ × ℝ) := by
    have h := h₁.unique h₂
    simpa only [zero_smul,add_zero,hv] using h
  have hr : ((fderiv ℝ helicoidTubeEquiv.symm y) v).1.2 = 0 := congrArg Prod.fst hpair
  have hθ : ((fderiv ℝ helicoidTubeEquiv.symm y) v).2 = 0 := congrArg Prod.snd hpair
  refine ⟨((fderiv ℝ helicoidTubeEquiv.symm y) v).1.1,?_⟩
  simp only [zero_smul,add_zero] at he
  rw [hr,hθ] at he
  ext i
  change tubeCartesian v i = _ * helicoidNormalField y i
  simpa only [zero_mul,zero_add,helicoidNormalField] using congrFun he.symm i

theorem helicoidNormalField_unit (y : HelicoidTubeCoordinates) :
    (∑ i, (helicoidNormalField y i)^2) = 1 :=
  (standardHelicoid_unit_normal _ _).1

theorem tubeCartesian_eq_zero_iff {v : HelicoidTubeCoordinates} :
    tubeCartesian v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    apply Prod.ext
    · exact Prod.ext h0 h1
    · exact h2
  · rintro rfl
    ext i
    fin_cases i <;> rfl

/-- A strict normal-component bound on the tangent plane gives injectivity
of the derivative of the real normal projection on the surface. -/
theorem helicoid_projection_derivative_injective {y : HelicoidTubeCoordinates}
    (hy : y ∈ helicoidTubeEquiv.target)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : E →L[ℝ] HelicoidTubeCoordinates} (hD : Function.Injective D)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ < 1)
    (hangle : ∀ u : E,
      (∑ i, helicoidNormalField y i*tubeCartesian (D u) i)^2 ≤
        κ^2*(∑ i, (tubeCartesian (D u) i)^2)) :
    Function.Injective ((fderiv ℝ helicoidBaseCoordinates y).comp D) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  obtain ⟨c,hc⟩ := helicoidBaseCoordinates_kernel_normal (v := D u) hy (by exact hu)
  have hnorm : (∑ i, (tubeCartesian (D u) i)^2) = c^2 := by
    rw [hc]
    simp only [Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum,helicoidNormalField_unit,mul_one]
  have hdot : (∑ i, helicoidNormalField y i*tubeCartesian (D u) i) = c := by
    rw [hc]
    simp only [Pi.smul_apply,smul_eq_mul]
    have he (i : Fin 3) : helicoidNormalField y i*(c*helicoidNormalField y i) =
        c*(helicoidNormalField y i)^2 := by ring
    simp_rw [he]
    rw [← Finset.mul_sum,helicoidNormalField_unit,mul_one]
  have hc0 : c = 0 := by
    have h := hangle u
    rw [hdot,hnorm] at h
    have hk : κ^2 < 1 := by nlinarith
    by_contra hcn
    have hpos := mul_pos (sub_pos.mpr hk) (sq_pos_of_ne_zero hcn)
    nlinarith
  have hDu : D u = 0 := tubeCartesian_eq_zero_iff.mp (by simpa [hc0] using hc)
  apply hD
  simpa using hDu

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoid_projection_derivative_injective
