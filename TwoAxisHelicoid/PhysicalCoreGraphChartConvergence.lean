import TwoAxisHelicoid.MarkedPhysicalCoreGraph
import TwoAxisHelicoid.SpatialNormalGraphDerivativeLimit

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- C¹ convergence on every fixed regular chart of the limiting
surface. One sequence of open graph markings covers the whole core,
so the maps and their derivatives agree on overlaps. -/
theorem physical_core_graphs_C1_in_parameter {B : Type*} [TopologicalSpace B]
    {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] {X N : B → SurfaceEuclideanSpace}
    {Y m : ∀ k, M k → SurfaceEuclideanSpace} {r : ℝ}
    (G : ∀ k, PhysicalCoreGraph (fun q : B × ℝ => X q.1+q.2 • N q.1) (Y k) r)
    (moving : ∀ k y, ∃ a : OpenPartialHomeomorph (M k) ℂ, y∈a.source ∧
      ContDiffAt ℝ 1 (Y k ∘ a.symm) (a y) ∧ Function.Injective (fderiv ℝ (Y k ∘ a.symm) (a y)) ∧
      ∀ v, ⟪fderiv ℝ (Y k ∘ a.symm) (a y) v,m k y⟫=0)
    (unit : ∀ k y, ‖m k y‖=1) (near : ∀ k b, coreNormalDistance (m k ((G k).point b)) (N b)<1)
    (limit : ∀ ε : ℝ, 0<ε → ∀ᶠ k in atTop, ∀ b, |(G k).height b|<ε ∧ coreNormalDistance (m k ((G k).point b)) (N b)<ε)
    {U : Set ℂ} (op : IsOpen U) (a : ℂ → B) (ca : ContinuousOn a U)
    (sx : ∀ z∈U, ContDiffAt ℝ 1 (X ∘ a) z) (sn : ∀ z∈U, ContDiffAt ℝ 1 (N ∘ a) z)
    (ref : ∀ z∈U, ‖N (a z)‖=1 ∧ ∀ v, ⟪fderiv ℝ (X ∘ a) z v,N (a z)⟫=0) :
    let u := fun k => (G k).height ∘ a
    let Z := fun k => Y k ∘ (G k).point ∘ a
    (∀ k z, z∈U → ContDiffAt ℝ 1 (u k) z ∧ ContDiffAt ℝ 1 (Z k) z) ∧
      TendstoLocallyUniformlyOn (fun k => fderiv ℝ (u k)) (fun _ => 0) atTop U ∧
      TendstoLocallyUniformlyOn (fun k => fderiv ℝ (Z k)) (fderiv ℝ (X ∘ a)) atTop U := by
  intro u Z
  let f := fun k => (G k).point ∘ a
  let field := fun k z => m k (f k z)
  apply continuous_spatial_normal_graphs_converge_C1 op (X ∘ a) (N ∘ a) Y f u field sx sn ref
    (fun k => (G k).open_point.continuous.comp_continuousOn ca)
    (fun k => (G k).continuous_height.comp_continuousOn ca) (fun k z _ => (G k).position (a z))
    (fun k z _ => moving k (f k z)) (fun k z _ => unit k (f k z)) (fun k z _ => near k (a z))
  · apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε ep
    filter_upwards [limit ε ep] with k good z _
    simpa only [u,Function.comp_apply,Real.dist_eq,zero_sub,abs_neg,sub_zero] using (good (a z)).1
  · apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε ep
    filter_upwards [limit ε ep] with k good z _
    have non : 0≤coreNormalDistance (m k ((G k).point (a z))) (N (a z)) := le_min (norm_nonneg _) (norm_nonneg _)
    simpa only [field,f,Function.comp_apply,Real.dist_eq,zero_sub,sub_zero,abs_neg,abs_of_nonneg non] using (good (a z)).2

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_core_graphs_C1_in_parameter
