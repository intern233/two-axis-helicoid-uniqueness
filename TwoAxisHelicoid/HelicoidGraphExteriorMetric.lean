import TwoAxisHelicoid.HelicoidConformalExteriorParameter
import TwoAxisHelicoid.CertifiedC1HelicoidEnd

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Metric
open scoped Topology

/-- The graph and its quantitative metric hypotheses hold beyond a
single spatial radius on the surface occurring in the definition of
a C¹ helicoidal end. The radius also excludes the compact interior. -/
theorem HasHelicoidC1End.exterior_conformal_graph {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (endGraph : HasHelicoidC1End X) (cont : Continuous X) :
    ∃ u : ℝ × ℝ → ℝ, ∃ B : ℝ, ∀ y∈range X, B<‖y‖ →
      ∃ z : ℂ, 2<‖z‖ ∧ DifferentiableAt ℝ u (helicoidConformalBase z) ∧
        |u (helicoidConformalBase z)|≤1/2 ∧ helicoidGraphGradientNorm u (helicoidConformalBase z)≤1/2 ∧
        y=helicoidGraphMap u (helicoidConformalBase z) := by
  obtain ⟨C,_,R,_,core,E,_,u,smooth,graph,decay⟩ := endGraph
  let U := extendOpenScalar u
  let S := helicoidProjectedEnd X C (exteriorPlaneBase R)
  obtain ⟨T,_,hT⟩ := ((hasBasis_cobounded_norm.comap
    (Subtype.val : exteriorPlaneBase R → ℝ × ℝ)).eventually_iff).mp
      (decay.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)))
  obtain ⟨K,hK⟩ := ((isCompact_closedBall (0:ℂ) 2).image
    helicoidConformalBaseHomeomorph.continuous).isBounded.exists_norm_le
  let A := max T (K+1)
  let sectionMap := fun q : ℝ × (ℝ × ℝ) => helicoidTubeMap ((q.1,q.2.1),q.2.2)
  have sectionCont : Continuous sectionMap := helicoidTubeMap_contDiff.continuous.comp (by fun_prop)
  obtain ⟨B,hB⟩ := (((isCompact_Icc (a := (-1:ℝ)) (b := 1)).prod
    (isCompact_closedBall (0:ℝ × ℝ) A)).image sectionCont).isBounded.exists_norm_le
  obtain ⟨D,hD⟩ := (core.image cont).isBounded.exists_norm_le
  refine ⟨U,max D B,?_⟩
  rintro _ ⟨x,rfl⟩ hx
  have tail : x∈S := by
    by_contra h
    exact (not_lt_of_ge (hD (X x) ⟨x,h,rfl⟩)) ((le_max_left D B).trans_lt hx)
  let p := E ⟨x,tail⟩
  have val : U p.1=u p := by simp only [U,extendOpenScalar,dite_eq_left p.2]
  have eq : X x=sectionMap (u p,p.1) := by simpa only [p,E.symm_apply_apply] using (graph p).2
  have sb := (graph p).1
  have far : A<‖p.1‖ := by
    by_contra h
    have hb := hB (sectionMap (u p,p.1)) ⟨(u p,p.1),⟨abs_le.mp (sb.trans (by norm_num)),
      (by simpa only [mem_closedBall,dist_zero_right] using le_of_not_gt h)⟩,rfl⟩
    exact (not_lt_of_ge (eq ▸ hb)) ((le_max_right D B).trans_lt hx)
  let z := helicoidConformalBaseHomeomorph.symm p.1
  have q : helicoidConformalBase z=p.1 := helicoidConformalBaseHomeomorph.apply_symm_apply p.1
  have normZ : 2<‖z‖ := by
    by_contra h
    have b := hK (helicoidConformalBaseHomeomorph z) ⟨z,(by simpa using le_of_not_gt h),rfl⟩
    change ‖helicoidConformalBase z‖≤K at b
    rw [q] at b
    linarith [le_max_right T (K+1)]
  refine ⟨z,normZ,?_⟩
  rw [q]
  have hq : T≤‖p.1‖ := (le_max_left T (K+1)).trans far.le
  have small := hT (show p∈(Subtype.val : exteriorPlaneBase R → ℝ × ℝ) ⁻¹' {q | T≤‖q‖} from hq)
  refine ⟨(smooth.contDiffAt ((exteriorPlaneBase_isOpen R).mem_nhds p.2)).differentiableAt (by simp),
    val ▸ sb,le_of_lt ((le_add_of_nonneg_left (abs_nonneg (u p))).trans_lt small),?_⟩
  change X x=sectionMap (U p.1,p.1)
  rwa [val]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidC1End.exterior_conformal_graph
