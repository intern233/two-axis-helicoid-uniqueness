import TwoAxisHelicoid.WholePlaneWeakCorrector
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace TwoAxisHelicoid
open InnerProductSpace Set
open scoped ContDiff RealInnerProductSpace

/-- Smooth coefficients and loads in operator norm give smooth dependence of
the *actual weak solution* in the energy norm on a fixed closed test space. -/
theorem smooth_coercive_variational_solution {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : Submodule ℝ E) (closed : IsClosed (S:Set E)) (T : P → E →L[ℝ] E) (b : P → E)
    (sT : ContDiff ℝ ∞ T) (sb : ContDiff ℝ ∞ b)
    (ell : ∀ t, ∃ c : ℝ, 0<c ∧ ∀ v, c*‖v‖^2≤⟪T t v,v⟫_ℝ)
    (u : P → S) (sol : ∀ t (v : S), ⟪T t (u t).val-b t,v.val⟫_ℝ=0) : ContDiff ℝ ∞ u := by
  let : CompleteSpace S := closed.completeSpace_coe
  let proj := S.orthogonalProjectionOnto
  let Q := fun t => proj.comp ((T t).comp S.subtypeL)
  have sq : ContDiff ℝ ∞ Q := contDiff_const.clm_comp (sT.clm_comp contDiff_const)
  have pairing (t : P) (x y : S) : ⟪Q t x,y⟫_ℝ=⟪T t x.val,y.val⟫_ℝ :=
    S.inner_orthogonalProjectionOnto_eq_of_mem_right _ _
  have invert (t : P) : (Q t).IsInvertible := by
    obtain ⟨c,hc,low⟩ := ell t
    obtain ⟨B,hB⟩ := exists_restricted_flux_inverse S closed (T t) hc low
    refine ⟨B,?_⟩
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℝ
    intro y
    exact (hB x y).trans (pairing t x y).symm
  have invsmooth : ContDiff ℝ ∞ (fun t => (Q t).inverse) :=
    contDiff_iff_contDiffAt.mpr fun t => (invert t).contDiffAt_map_inverse.comp t sq.contDiffAt
  have ident (t : P) : Q t (u t)=proj (b t) := by
    apply ext_inner_right ℝ
    intro y
    have eq := sol t y
    rw [inner_sub_left] at eq
    exact (pairing _ _ _).trans ((sub_eq_zero.mp eq).trans (S.inner_orthogonalProjectionOnto_eq_of_mem_right _ _).symm)
  have repr : u=(fun t => (Q t).inverse (proj (b t))) := by
    funext t
    rw [←ident]
    obtain ⟨B,hB⟩ := invert t
    rw [←hB,ContinuousLinearMap.inverse_equiv]
    exact (B.symm_apply_apply _).symm
  rw [repr]
  exact invsmooth.clm_apply (proj.contDiff.comp sb)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_coercive_variational_solution
