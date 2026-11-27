import TwoAxisHelicoid.HelicoidAsymptoticAxis
import TwoAxisHelicoid.MinimalChartComplexData
import Mathlib.Analysis.Meromorphic.Order

namespace TwoAxisHelicoid
open Complex Matrix Filter Set
open scoped Topology
set_option maxHeartbeats 1300000

/-- An orthogonal ambient map preserving the vertical line changes the
height only by a fixed sign. The sign follows from its action on the
unit vertical vector. -/
theorem aligned_orthogonal_height (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
    (hL : ∀ u v, L u ⬝ᵥ L v = u ⬝ᵥ v)
    (haxis : L ![0,0,1] 0 = 0 ∧ L ![0,0,1] 1 = 0) :
    ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ ∀ p, L p 2 = e*p 2 := by
  let k : Fin 3 → ℝ := ![0,0,1]
  let e := L k 2
  have h₀ : L k 0 = 0 := haxis.1
  have h₁ : L k 1 = 0 := haxis.2
  have he : e*e = 1 := by
    have hh := hL k k
    simp [dotProduct,Fin.sum_univ_succ,h₀,h₁,show k 0 = 0 from rfl,show k 1 = 0 from rfl,
      show k 2 = 1 from rfl] at hh
    exact hh
  refine ⟨e,?_ ,?_⟩
  · have hr : (e-1)*(e+1) = 0 := by nlinarith only [he]
    exact (mul_eq_zero.mp hr).imp sub_eq_zero.mp eq_neg_of_add_eq_zero_left
  · intro p
    have hh := hL p k
    simp [dotProduct,Fin.sum_univ_succ,h₀,h₁,show k 0 = 0 from rfl,show k 1 = 0 from rfl,
      show k 2 = 1 from rfl] at hh
    change L p 2*e = p 2 at hh
    linear_combination e*hh-(L p 2)*he

theorem scalarComplexCoefficient_affine {F : ℂ → ℝ} {z : ℂ} (hF : DifferentiableAt ℝ F z)
    (c e : ℝ) : scalarComplexCoefficient (fun w => c+e*F w) z = (e : ℂ)*scalarComplexCoefficient F z := by
  have hd : HasFDerivAt (fun w => c+e*F w) (e • fderiv ℝ F z) z :=
    (hF.hasFDerivAt.const_smul e).const_add c
  unfold scalarComplexCoefficient
  rw [hd.fderiv]
  simp only [_root_.smul_apply,smul_eq_mul,Complex.ofReal_mul]
  ring

/-- In any complex parameter, the actual height differential computed
in the given coordinates and in the coordinates of the rotated BBC
helicoid differ by one globally fixed sign. -/
theorem asymptotic_helicoid_actual_height_coefficient {S : Set (Fin 3 → ℝ)}
    (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (hL : ∀ u v, L u ⬝ᵥ L v = u ⬝ᵥ v)
    (P : Fin 3 → ℝ) (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (h₁ : ApproachesSetAtInfinity ((fun p => P+L p) '' range (axisRuledHelicoid I β 0)) S)
    (h₂ : ApproachesSetAtInfinity S (range (axisRuledHelicoid I α 0))) :
    ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ ∀ (X : ℂ → Fin 3 → ℝ) (z : ℂ),
      DifferentiableAt ℝ X z →
      immersionComplexCoefficient (fun w => P+L (X w)) z 2 = (e : ℂ)*immersionComplexCoefficient X z 2 := by
  obtain ⟨e,he,hp⟩ := aligned_orthogonal_height L hL
    (helicoid_axis_alignment_through_surface L hL P α β hα hβ h₁ h₂)
  refine ⟨e,he,?_⟩
  intro X z hX
  change scalarComplexCoefficient (fun w => P 2 + L (X w) 2) z = _
  simp only [hp]
  exact scalarComplexCoefficient_affine
    ((ContinuousLinearMap.proj (2 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ).differentiableAt.comp z hX) _ _

/-- Constant nonzero changes of height differential preserve its exact
meromorphic pole order, including when the value at the puncture is
defined differently. -/
theorem meromorphicOrderAt_of_punctured_constant_multiple {f g : ℂ → ℂ} {z a : ℂ}
    (ha : a ≠ 0) (hf : MeromorphicAt f z) (h : g =ᶠ[𝓝[≠] z] fun w => a*f w) :
    MeromorphicAt g z ∧ meromorphicOrderAt g z = meromorphicOrderAt f z := by
  have ha' : MeromorphicAt (fun _ : ℂ => a) z := MeromorphicAt.const a z
  have hg : MeromorphicAt (fun w => a*f w) z := ha'.mul hf
  refine ⟨hg.congr h.symm,?_⟩
  rw [meromorphicOrderAt_congr h]
  change meromorphicOrderAt ((fun _ : ℂ => a)*f) z = _
  rw [meromorphicOrderAt_mul ha' hf,meromorphicOrderAt_const]
  simp [ha]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.asymptotic_helicoid_actual_height_coefficient
