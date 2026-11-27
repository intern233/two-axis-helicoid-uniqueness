import TwoAxisHelicoid.RegularBallComponentBoundary
import TwoAxisHelicoid.RegularOneSidedCuttingBalls
import TwoAxisHelicoid.OriginalExteriorBallDomains

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped Topology ContDiff Manifold RealInnerProductSpace

/-- At a regular sphere every boundary point of a connected component
of its open ball has a coordinate taking the component, its closure,
and its frontier to an open half-plane, a closed half-plane and a line. -/
theorem original_regular_sphere_component_charts (s : OriginalSmoothHelicoid)
    (R : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ)) (c : SurfaceEuclideanSpace) {r : ℝ} (rp : 0<r) :
    let Y := R ∘ s.position
    let X := coordinateToEuclidean ∘ Y
    (∀ q : s.carrier, dist (X q) c=r → ∃ p : s.carrier, q∈(chartAt ℂ p).source ∧
      ∃ v : ℂ, ⟪coordinateToEuclidean (fderiv ℝ (Y ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) q) v),c-X q⟫≠0) →
    ∀ p q : s.carrier, let V := connectedComponentIn (X ⁻¹' ball c r) p
      q∈frontier V → ∃ e : OpenPartialHomeomorph s.carrier (ℝ × ℝ), q∈e.source ∧ (e q).1=0 ∧
        e.IsImage V (Iio 0 ×ˢ univ) ∧ e.IsImage (closure V) (Iic 0 ×ˢ univ) ∧
          e.IsImage (frontier V) ({0} ×ˢ univ) := by
  intro Y X transverse p q V boundary
  let _ : LocallyConnectedSpace s.carrier := ChartedSpace.locallyConnectedSpace ℂ _
  have cx : Continuous X := coordinateToEuclidean.continuous.comp (R.continuous.comp s.closedEmbedding.continuous)
  have level := component_frontier_lies_on_level (cx.dist continuous_const) boundary
  obtain ⟨a,qa,v,hit⟩ := transverse q level
  let e := chartAt ℂ a
  let z := e q
  let Z := s.position ∘ e.symm
  let F := coordinateToEuclidean ∘ R ∘ Z
  have st := (smooth_surface_regular_manifold_chart s.smooth s.immersion a z (e.map_source qa)).1
  have sy : ContDiffAt ℝ ∞ (R ∘ Z) z := R.contDiff.contDiffAt.comp z st
  have sf : ContDiffAt ℝ ∞ F z := coordinateToEuclidean.contDiff.contDiffAt.comp z sy
  have df := (coordinateToEuclidean.hasFDerivAt.comp z (sy.differentiableAt (by simp)).hasFDerivAt).fderiv
  have fy : F z=X q := congrArg X (e.left_inv qa)
  have angle : ⟪fderiv ℝ F z v,c-F z⟫≠0 := by
    rw [fy,show fderiv ℝ F z=_ from df]
    exact hit
  obtain ⟨b,zb,center,_,_,side⟩ := transverse_sphere_has_half_plane_chart rp sf (fy.symm ▸ level) ⟨v,angle⟩
  let h := e.trans b
  have hq : q∈h.source := ⟨qa,zb⟩
  have sub (y : s.carrier) (hy : y∈h.source) : y∈X ⁻¹' ball c r ↔ (h y).1<0 := by
    change X y∈ball c r ↔ (b (e y)).1<0
    have eq : F (e y)=X y := congrArg X (e.left_inv hy.1)
    simpa only [eq] using (side (e y)).1
  obtain ⟨d,dq,eq,openCut,closedCut,line⟩ := component_regular_half_plane (frontier_subset_closure boundary) h hq sub
  exact ⟨d,dq,by rw [eq]; exact center,openCut,closedCut,line⟩

/-- For the weak positional class and one single scale, the far test
balls are one-sided, have a transverse boundary, and cut out planar
patches with connected spherical complement. All patch boundary
coordinates refer to those same balls and components. -/
theorem positional_one_sided_regular_planar_components (s : OriginalPositionallyAsymptoticHelicoid) {ε : ℝ} (ep : 0<ε) :
    let X := coordinateToEuclidean ∘ centeredHelicoidNormalization s.axes.pitch_ne ∘ s.position
    ∃ (r B : ℝ) (j : ℂ → OnePoint s.carrier), 0<r ∧ IsOpenEmbedding j ∧ j 0=OnePoint.infty ∧
      ∀ p : s.carrier, B≤‖X p‖ → ∃ c n : SurfaceEuclideanSpace,
        ‖n‖=1 ∧ dist (X p) c<min ε 1*r ∧ (∀ y∈range X∩closedBall c (2*r), 0<⟪y-c,n⟫) ∧
        let V := connectedComponentIn (X ⁻¹' ball c (2*r)) p
        (∃ W : Set ℂ, IsOpen W ∧ IsConnected W ∧ IsCompact (closure W) ∧
          IsPreconnected ((OnePoint.some : ℂ → OnePoint ℂ) '' W)ᶜ ∧ j '' W=(OnePoint.some : s.carrier → OnePoint s.carrier) '' V) ∧
        ∀ q∈frontier V, ∃ e : OpenPartialHomeomorph s.carrier (ℝ × ℝ), q∈e.source ∧ (e q).1=0 ∧
          e.IsImage V (Iio 0 ×ˢ univ) ∧ e.IsImage (closure V) (Iic 0 ×ˢ univ) ∧ e.IsImage (frontier V) ({0} ×ˢ univ) := by
  intro X
  let R := centeredHelicoidNormalization s.axes.pitch_ne
  obtain ⟨r,B,rp,balls⟩ := original_exterior_regular_one_sided_balls s ep
  obtain ⟨j,T,emb,zero,patches⟩ := original_far_ball_components_are_planar s.toOriginalSmoothHelicoid R (2*r)
  refine ⟨r,max B (T+r),j,rp,emb,zero,?_⟩
  intro p far
  obtain ⟨c,n,unit,near,above,sphere⟩ := balls (X p) (mem_range_self p) ((le_max_left _ _).trans far)
  have close : dist (X p) c<r := near.trans_le (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_right ε 1) rp.le)
  have big : T≤‖c‖ := by
    have edge := norm_sub_norm_le (X p) c
    rw [← dist_eq_norm] at edge
    linarith [(le_max_right B (T+r)).trans far]
  exact ⟨c,n,unit,near,above,patches c big p (show dist (X p) c<2*r by linarith),
    fun q h => original_regular_sphere_component_charts s.toOriginalSmoothHelicoid R c (by positivity) sphere p q h⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_regular_sphere_component_charts
#print axioms TwoAxisHelicoid.positional_one_sided_regular_planar_components
