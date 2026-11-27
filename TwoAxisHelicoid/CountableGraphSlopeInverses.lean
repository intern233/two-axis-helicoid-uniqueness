import TwoAxisHelicoid.PlaneSectionCriticalSlopes
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Compactness.Lindelof

namespace TwoAxisHelicoid
open Set Complex Filter Topology InnerProductSpace
open scoped Topology ContDiff

/-- Near a point of nonzero Hessian determinant, solve the graph
contact equation for the horizontal position as a function of slope.
Both neighborhoods and the inverse are obtained from the actual graph. -/
theorem graph_slope_local_inverse {f : ℂ → ℝ} {x : ℂ} (sm : ContDiffAt ℝ 3 f x)
    (nondeg : (fderiv ℝ (gradient f) x).det≠0) :
    ∃ (U V : Set ℂ) (p : ℂ → ℂ),
      IsOpen U ∧ x∈U ∧ IsOpen V ∧
        (∀ y∈U, gradient f y∈V ∧ p (gradient f y)=y) ∧
        ∀ s∈V, ContDiffAt ℝ 1 p s ∧ ContDiffAt ℝ 1 f (p s) ∧ gradient f (p s)=s := by
  let N := gradient f
  have sn : ContDiffAt ℝ 1 N x :=
    (toDual ℝ ℂ).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x
      (sm.fderiv_right (m:=1) (by norm_num))
  let D := fderiv ℝ N x
  let E := (D.toLinearMap.equivOfDetNeZero nondeg).toContinuousLinearEquiv
  have de : HasFDerivAt N E.toContinuousLinearMap x := (sn.differentiableAt one_ne_zero).hasFDerivAt
  let e := sn.toOpenPartialHomeomorph N de one_ne_zero
  have ex : x∈e.source := sn.mem_toOpenPartialHomeomorph_source de one_ne_zero
  have back : ContDiffAt ℝ 1 e.symm (e x) := sn.to_localInverse de one_ne_zero
  have fx : ContDiffAt ℝ 1 f (e.symm (e x)) := (e.left_inv ex).symm ▸ sm.of_le (by norm_num)
  have good : ∀ᶠ s in 𝓝 (e x), s∈e.target ∧ ContDiffAt ℝ 1 e.symm s ∧ ContDiffAt ℝ 1 f (e.symm s) := by
    filter_upwards [e.open_target.mem_nhds (e.map_source ex),back.eventually (by norm_num),
      (e.continuousAt_symm (e.map_source ex)).eventually (fx.eventually (by norm_num))] with y hy h1 h2
    exact ⟨hy,h1,h2⟩
  obtain ⟨V,sub,op,inside⟩ := mem_nhds_iff.mp good
  refine ⟨e.source∩e ⁻¹' V,V,e.symm,e.isOpen_inter_preimage op,⟨ex,inside⟩,op,
    fun y hy => ⟨hy.2,e.left_inv hy.1⟩,fun s hs => ⟨(sub hs).2.1,(sub hs).2.2,e.right_inv (sub hs).1⟩⟩

/-- A countable family of regular inverse branches covers every
nondegenerate contact on a graph patch. No finiteness or compactness
of the patch or of the set of nondegenerate points is assumed. -/
theorem countable_graph_slope_inverses {D : Set ℂ} {f : ℂ → ℝ}
    (smooth : ∀ x∈D, ContDiffAt ℝ 3 f x) :
    ∃ (C : Set {x : ℂ // x∈D ∧ (fderiv ℝ (gradient f) x).det≠0}),
      C.Countable ∧ ∃ (V : C → Set ℂ) (p : C → ℂ → ℂ),
        (∀ j s, s∈V j → ContDiffAt ℝ 1 (p j) s ∧ ContDiffAt ℝ 1 f (p j s) ∧ gradient f (p j s)=s) ∧
        (∀ x∈D, (fderiv ℝ (gradient f) x).det≠0 →
          ∃ j, gradient f x∈V j ∧ p j (gradient f x)=x) := by
  classical
  let S := {x : ℂ | x∈D ∧ (fderiv ℝ (gradient f) x).det≠0}
  choose U V p op xu _ hit inv using fun x : S => graph_slope_local_inverse (smooth _ x.2.1) x.2.2
  obtain ⟨C,ct,cover⟩ := TopologicalSpace.countable_cover_nhds (fun x : S =>
    ((op x).preimage continuous_subtype_val).mem_nhds (show x∈(Subtype.val : S → ℂ) ⁻¹' U x from xu x))
  refine ⟨C,ct,fun i => V i.1,fun i => p i.1,fun i => inv i.1,?_⟩
  intro x hx nondeg
  obtain ⟨j,jC,inU⟩ := mem_iUnion₂.mp
    (show (⟨x,hx,nondeg⟩:S)∈⋃ q∈C, (Subtype.val : S → ℂ) ⁻¹' U q from cover.symm ▸ mem_univ _)
  exact ⟨⟨j,jC⟩,hit j x inU⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.countable_graph_slope_inverses
