import TwoAxisHelicoid.ExteriorPlaneBase
import TwoAxisHelicoid.HelicoidGraphDerivative
import TwoAxisHelicoid.HelicoidGraphSmoothness
import TwoAxisHelicoid.OneEndedGraphExterior
import TwoAxisHelicoid.OpenSubsetCoordinate

namespace TwoAxisHelicoid
open Set Filter Bornology Topology
open scoped Topology ContDiff

/-- The single-valued normal graph in Section 2 with literal C¹ regularity.
The graph is represented by its actual spatial points on the compact
complement. The derivative norm is the induced helicoid norm used in the paper. -/
def HasManuscriptC1HelicoidGraph {M : Type*} [TopologicalSpace M] (Y : M → HelicoidTubeCoordinates) : Prop :=
  ∃ (S : Set M), IsCompact Sᶜ ∧ ∃ R : ℝ, 0<R ∧ ∃ E : S ≃ₜ exteriorPlaneBase R,
    ∃ u : exteriorPlaneBase R → ℝ,
      ContDiffOn ℝ 1 (extendOpenScalar u) (exteriorPlaneBase R) ∧
      (∀ b, |u b|≤1/2 ∧ Y (E.symm b).1=helicoidTubeMap ((u b,b.1.1),b.1.2)) ∧
      Tendsto (fun b : exteriorPlaneBase R => |u b|+helicoidGraphGradientNorm (extendOpenScalar u) b.1)
        (comap (Subtype.val : exteriorPlaneBase R → ℝ × ℝ) (cobounded (ℝ × ℝ))) (𝓝 0)

/-- A single normal graph on the complements of compact sets in the surface
and in the parameter plane of the helicoid. Its derivative is measured in
the induced metric on the helicoid. -/
def HasCompactComplementC1Graph {M : Type*} [TopologicalSpace M]
    (Y : M → HelicoidTubeCoordinates) : Prop :=
  ∃ (S : Set M) (B : Set (ℝ × ℝ)), IsCompact Sᶜ ∧ IsCompact Bᶜ ∧
    ∃ (E : S ≃ₜ B) (u : B → ℝ),
      ContDiffOn ℝ 1 (extendOpenScalar u) B ∧
      (∀ p : B, Y (E.symm p).1 = helicoidTubeMap ((u p,p.1.1),p.1.2)) ∧
      Tendsto (fun p : B => |u p| + helicoidGraphGradientNorm (extendOpenScalar u) p.1)
        (comap (Subtype.val : B → ℝ × ℝ) (cobounded (ℝ × ℝ))) (𝓝 0)

theorem HasManuscriptC1HelicoidGraph.off_compact {M : Type*} [TopologicalSpace M]
    {Y : M → HelicoidTubeCoordinates} (graph : HasManuscriptC1HelicoidGraph Y) :
    HasCompactComplementC1Graph Y := by
  obtain ⟨S,core,R,_,E,u,reg,shape,decay⟩ := graph
  exact ⟨S,exteriorPlaneBase R,core,exteriorPlaneBase_complement_isCompact R,E,u,reg,
    fun p => (shape p).2,decay⟩

/-- On a one-ended surface the annular restriction of the graph still
contains the complement of a compact set. The helicoid normal above
`(0, θ)` is horizontal, so its actual height is exactly `θ` for every
value of the graph function. -/
theorem HasCompactComplementC1Graph.round_exterior {M : Type*} [TopologicalSpace M]
    [T2Space M] {Y : M → HelicoidTubeCoordinates} (graph : HasCompactComplementC1Graph Y)
    (cont : Continuous Y) (tails : ∀ K : Set M, IsCompact K →
      ∃ U : Set M, IsPreconnected U ∧ IsCompact Uᶜ ∧ Disjoint U K) :
    HasManuscriptC1HelicoidGraph Y := by
  classical
  obtain ⟨S,B,core,baseCore,E,u,reg,shape,decay⟩ := graph
  obtain ⟨r,bound⟩ := baseCore.isBounded.exists_norm_le
  have outside : exteriorPlaneBase r ⊆ B := by
    intro p hp
    by_contra absent
    exact (hp : r < ‖p‖).not_ge (bound p absent)
  have ray (A : ℝ) : ∃ θ : ℝ, ((0,θ) : ℝ × ℝ) ∈ B ∧ A < θ ∧ A < ‖((0,θ) : ℝ × ℝ)‖ := by
    let θ := max A r + 1
    have aθ : A < θ := by dsimp [θ]; linarith [le_max_left A r]
    have rθ : r < θ := by dsimp [θ]; linarith [le_max_right A r]
    have axisNorm : θ ≤ ‖((0,θ) : ℝ × ℝ)‖ := by
      rw [Prod.norm_mk, Real.norm_eq_abs θ]
      exact (le_abs_self θ).trans (le_max_right _ _)
    exact ⟨θ,outside (rθ.trans_le axisNorm),aθ,aθ.trans_le axisNorm⟩
  have openS : IsOpen S := by simpa only [compl_compl] using core.isClosed.isOpen_compl
  have openB : IsOpen B := by simpa only [compl_compl] using baseCore.isClosed.isOpen_compl
  obtain ⟨θ,hθ,_,_⟩ := ray 0
  obtain ⟨e,source,target,coord⟩ :=
    open_coordinate_of_subsets openS openB ⟨E.symm ⟨(0,θ),hθ⟩⟩ E
  have forward (p : B) : e (E.symm p).1 = p.1 := by
    simpa only [E.apply_symm_apply] using coord (E.symm p)
  have inverse (p : B) : e.symm p.1 = (E.symm p).1 :=
    (congrArg e.symm (forward p).symm).trans (e.left_inv (source.symm ▸ (E.symm p).2))
  have escapes (A : ℝ) : ∃ x ∈ e.source, A < (Y x).2 ∧ A < ‖e x‖ := by
    obtain ⟨v,hv,tall,far⟩ := ray A
    let p : B := ⟨(0,v),hv⟩
    refine ⟨(E.symm p).1,source.symm ▸ (E.symm p).2,?_,?_⟩
    · rw [shape p]
      simpa only [p,helicoidTubeMap,helicoidNormalMap,helicoidAngle,mul_zero,zero_div,add_zero] using tall
    · rw [forward p]
      exact far
  obtain ⟨L,_,small⟩ := ((hasBasis_cobounded_norm.comap
    (Subtype.val : B → ℝ × ℝ)).eventually_iff).mp
      (decay.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2)))
  let R := max 0 (max r L) + 1
  have Rpos : 0 < R := by dsimp [R]; linarith [le_max_left (0:ℝ) (max r L)]
  have rR : r < R := by
    dsimp [R]
    linarith [le_max_left r L,le_max_right (0:ℝ) (max r L)]
  have LR : L < R := by
    dsimp [R]
    linarith [le_max_right r L,le_max_right (0:ℝ) (max r L)]
  let T := exteriorPlaneBase R
  have inside : T ⊆ B := fun _ hp => outside (rR.trans hp)
  have targetR : T ⊆ e.target := target.symm ▸ inside
  let D := e.source ∩ e ⁻¹' T
  have openD : IsOpen D := e.continuousOn.isOpen_inter_preimage e.open_source (exteriorPlaneBase_isOpen R)
  have levels (t : ℝ) : IsCompact {p : ℝ × ℝ | ‖p‖ = t} := by
    simpa only [Metric.sphere,dist_zero_right] using (isCompact_sphere (0 : ℝ × ℝ) t)
  have eventuallyD : D ∈ cocompact M := one_ended_chart_exterior_mem_cocompact tails e
    (fun p : ℝ × ℝ => ‖p‖) continuous_norm levels
    (target.symm ▸ outside) (source.symm ▸ core) (fun x => (Y x).2) cont.snd escapes R
  obtain ⟨K,compactK,inK⟩ := mem_cocompact'.mp eventuallyD
  have compactD : IsCompact Dᶜ := compactK.of_isClosed_subset openD.isClosed_compl inK
  obtain ⟨F,invF⟩ := exists_restricted_exterior_homeomorph e targetR
  let j : T → B := fun p => ⟨p.1,inside p.2⟩
  let v : T → ℝ := u ∘ j
  have same (p : ℝ × ℝ) (hp : p ∈ T) :
      extendOpenScalar v =ᶠ[𝓝 p] extendOpenScalar u := by
    filter_upwards [(exteriorPlaneBase_isOpen R).mem_nhds hp] with q hq
    simp only [extendOpenScalar,dite_eq_left (show q ∈ T from hq),dite_eq_left (inside hq),v,j,Function.comp_apply]
  have restricted : ContDiffOn ℝ 1 (extendOpenScalar u) T := reg.mono inside
  refine ⟨D,compactD,R,Rpos,F,v,?_,?_,?_⟩
  · intro p hp
    exact (restricted p hp).congr_of_eventuallyEq
      ((same p hp).filter_mono nhdsWithin_le_nhds) (same p hp).self_of_nhds
  · intro p
    have far : L ≤ ‖(j p).1‖ := (LR.trans (p.2 : R < ‖p.1‖)).le
    have smallAt := small (show j p ∈ (Subtype.val : B → ℝ × ℝ) ⁻¹' {q | L ≤ ‖q‖} from far)
    refine ⟨(le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans smallAt.le,?_⟩
    rw [invF p,inverse (j p)]
    exact shape (j p)
  · have inclusion : Tendsto j (comap (Subtype.val : T → ℝ × ℝ) (cobounded (ℝ × ℝ)))
        (comap (Subtype.val : B → ℝ × ℝ) (cobounded (ℝ × ℝ))) :=
      tendsto_comap_iff.mpr (show Tendsto (Subtype.val : T → ℝ × ℝ)
        (comap Subtype.val (cobounded (ℝ × ℝ))) (cobounded (ℝ × ℝ)) from tendsto_comap)
    apply (decay.comp inclusion).congr
    intro p
    simp only [Function.comp_apply,v,j,helicoidGraphGradientNorm,(same p.1 p.2).fderiv_eq]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HasManuscriptC1HelicoidGraph.off_compact
#print axioms TwoAxisHelicoid.HasCompactComplementC1Graph.round_exterior
