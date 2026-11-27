import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace TwoAxisHelicoid
open Set Complex MeasureTheory Filter Topology InnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff

/-- For countably many smooth embedded graph patches, almost every
slope gives only nondegenerate critical points of the corresponding
linear height. The exceptional set is measured in the actual plane
of slopes, so one direction works on every patch. -/
theorem ae_nondegenerate_graph_height_slopes {ι : Type*} [Countable ι]
    (U : ι → Set ℂ) (f : ι → ℂ → ℝ)
    (smooth : ∀ i x, x∈U i → ContDiffAt ℝ 2 (f i) x) :
    ∀ᵐ s : ℂ, ∀ i x, x∈U i → gradient (f i) x=s →
      (fderiv ℝ (gradient (f i)) x).det≠0 := by
  let N := fun i => gradient (f i)
  let B := fun i => {x : ℂ | x∈U i ∧ (fderiv ℝ (N i) x).det=0}
  have df (i : ι) (x : ℂ) (hx : x∈U i) : DifferentiableAt ℝ (N i) x := by
    have h := ((smooth i x hx).fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero
    exact (toDual ℝ ℂ).symm.toContinuousLinearEquiv.differentiableAt.comp x h
  have null (i : ι) : volume (N i '' B i)=0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (fun x hx => (df i x hx.1).hasFDerivAt.hasFDerivWithinAt) (fun _ hx => hx.2)
  have all : volume (⋃ i, N i '' B i)=0 := measure_iUnion_null null
  filter_upwards [show ∀ᵐ s : ℂ, s∉⋃ i, N i '' B i from (ae_iff.mpr (by simpa only [not_not,ofPred_mem_eq] using all))] with s hs
  intro i x hx eq degenerate
  exact hs (mem_iUnion.mpr ⟨i,x,⟨hx,degenerate⟩,eq⟩)

/-- The derivative of the critical height with respect to plane
slope is minus the horizontal position. Critical points are allowed
to move in the graph as the slope varies. -/
theorem critical_graph_height_derivative {f : ℂ → ℝ} {p : ℂ → ℂ} {s : ℂ}
    (df : DifferentiableAt ℝ f (p s)) (dp : DifferentiableAt ℝ p s)
    (critical : gradient f (p s)=s) (v : ℂ) :
    fderiv ℝ (fun t => f (p t)-⟪t,p t⟫_ℝ) s v= -⟪v,p s⟫_ℝ := by
  have left := df.comp s dp
  have right := differentiableAt_id.inner ℝ dp
  change (fderiv ℝ ((f ∘ p)-(fun t => ⟪id t,p t⟫_ℝ)) s) v=_
  rw [fderiv_sub left right,sub_apply,fderiv_comp s df dp,
    ContinuousLinearMap.comp_apply,fderiv_inner_apply ℝ differentiableAt_id dp,
    fderiv_id,ContinuousLinearMap.id_apply,← inner_gradient_left,critical,id_eq]
  ring

/-- Two distinct contact points of smooth graphs cannot give the
same critical height throughout an open neighborhood of the slope.
Equality of the moving support heights gives equality of the planar
positions by differentiation, then equality of their third coordinates. -/
theorem distinct_critical_supports_separate {f g : ℂ → ℝ} {p q : ℂ → ℂ} {s : ℂ}
    (df : DifferentiableAt ℝ f (p s)) (dg : DifferentiableAt ℝ g (q s))
    (dp : DifferentiableAt ℝ p s) (dq : DifferentiableAt ℝ q s)
    (fp : gradient f (p s)=s) (gq : gradient g (q s)=s)
    (distinct : (p s,f (p s))≠(q s,g (q s))) :
    ∃ᶠ t in 𝓝 s, f (p t)-⟪t,p t⟫_ℝ≠g (q t)-⟪t,q t⟫_ℝ := by
  by_contra fail
  have same : (fun t => f (p t)-⟪t,p t⟫_ℝ) =ᶠ[𝓝 s] fun t => g (q t)-⟪t,q t⟫_ℝ := by
    change ∀ᶠ t in 𝓝 s, f (p t)-⟪t,p t⟫_ℝ=g (q t)-⟪t,q t⟫_ℝ
    simpa only [not_frequently,not_not] using fail
  have eq := same.fderiv_eq (𝕜:=ℝ)
  have dot (v : ℂ) : ⟪v,p s⟫_ℝ=⟪v,q s⟫_ℝ := by
    have h := DFunLike.congr_fun eq v
    rw [critical_graph_height_derivative df dp fp,critical_graph_height_derivative dg dq gq] at h
    exact neg_injective h
  have xy : p s=q s := by
    exact ext_inner_left ℝ dot
  apply distinct
  have heights := same.self_of_nhds
  change f (p s)-⟪s,p s⟫_ℝ=g (q s)-⟪s,q s⟫_ℝ at heights
  rw [xy] at heights ⊢
  exact Prod.ext rfl (sub_left_inj.mp heights)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ae_nondegenerate_graph_height_slopes
#print axioms TwoAxisHelicoid.critical_graph_height_derivative
#print axioms TwoAxisHelicoid.distinct_critical_supports_separate
