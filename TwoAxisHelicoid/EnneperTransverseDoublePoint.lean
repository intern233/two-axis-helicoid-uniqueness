import TwoAxisHelicoid.TransverseDoublePointPersistence
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ComplexConjugate ContDiff

/-- The horizontal coordinates of Enneper's immersion as one complex
number, and its height. This normalization comes from g(w)=w, dh=2w dw. -/
noncomputable def enneperPosition (z : ℂ) : ℂ × ℝ :=
  (conj z - z^3 / 3, (z^2).re)

theorem enneperPosition_fderiv_apply (z u : ℂ) :
    fderiv ℝ enneperPosition z u = (conj u-z^2*u, (2*z*u).re) := by
  have h₃ : HasDerivAt (fun w : ℂ => w^3/3) (z^2) z := by
    convert (hasDerivAt_pow 3 z).div_const (3:ℂ) using 1
    ring
  have h₂ : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by
    convert hasDerivAt_pow 2 z using 1
    ring
  have h := (conjCLE.hasFDerivAt.sub (h₃.hasFDerivAt.restrictScalars ℝ)).prodMk
    (reCLM.hasFDerivAt.comp z (h₂.hasFDerivAt.restrictScalars ℝ))
  change HasFDerivAt enneperPosition _ z at h
  rw [h.fderiv]
  change (conj u - u*z^2, (u*(2*z)).re) = _
  rw [mul_comm u (z^2),mul_comm u (2*z)]

/-- At the distinct parameters ±√3 the images agree. The difference of
the two tangent maps is onto all of three-space, verified by an explicit
right inverse. -/
theorem enneper_transverse_crossing :
    let r := Real.sqrt 3
    (r:ℂ) ≠ -(r:ℂ) ∧ enneperPosition r = enneperPosition (-r) ∧
    ∀ y : ℂ × ℝ, ∃ u v : ℂ,
      fderiv ℝ enneperPosition (r:ℂ) u - fderiv ℝ enneperPosition (-(r:ℂ)) v = y := by
  intro r
  have hr : 0 < r := Real.sqrt_pos.2 (by norm_num)
  have hs : r^2 = 3 := Real.sq_sqrt (by norm_num)
  have hz : (r:ℂ)^2 = 3 := by exact_mod_cast hs
  refine ⟨fun h => (ne_of_gt hr) (by have e := congrArg Complex.re h; simp at e; linarith),?_,?_⟩
  · apply Prod.ext
    · change conj (r:ℂ) - (r:ℂ)^3/3 = conj (-(r:ℂ)) - (-(r:ℂ))^3/3
      have cube : (r:ℂ)^3 = 3*r := by rw [pow_succ,hz]
      simp only [map_neg,conj_ofReal,Odd.neg_pow (by decide : Odd 3),cube]
      ring
    · simp [enneperPosition]
  · rintro ⟨c,k⟩
    let u : ℂ := ⟨k/(4*r)-c.re/4,-c.im/4⟩
    let v : ℂ := ⟨k/(4*r)+c.re/4,0⟩
    refine ⟨u,v,?_⟩
    rw [enneperPosition_fderiv_apply,enneperPosition_fderiv_apply,neg_sq,hz]
    apply Prod.ext
    · apply Complex.ext <;> simp [u,v,sub_re,sub_im,mul_re,mul_im] <;> ring
    · simp [u,v,mul_re,mul_im]
      field_simp [hr.ne']
      ring

/-- The transverse Enneper crossing forces self-intersection of every
nearby member on the same two neighborhoods. -/
theorem family_with_enneper_limit_has_double_points (F : ℝ × ℂ → ℂ × ℝ)
    (h₀ : ∀ z, F (0,z) = enneperPosition z)
    (hF : ∀ z, ContDiffAt ℝ 1 F (0,z))
    {U W : Set ℂ} (hU : U ∈ 𝓝 (Real.sqrt 3 : ℂ)) (hW : W ∈ 𝓝 (-(Real.sqrt 3 : ℂ))) :
    ∀ᶠ t : ℝ in 𝓝 0, ∃ u ∈ U, ∃ v ∈ W, u ≠ v ∧ F (t,u) = F (t,v) := by
  obtain ⟨hne,he,hs⟩ := enneper_transverse_crossing
  apply transverse_double_point_persists F 0 hne _ (hF _) (hF _) _ hU hW
  · rw [h₀,h₀,he]
  · simpa only [funext h₀] using hs

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.family_with_enneper_limit_has_double_points
