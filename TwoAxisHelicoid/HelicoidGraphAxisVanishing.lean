import TwoAxisHelicoid.CertifiedC1HelicoidEnd
import TwoAxisHelicoid.HelicoidRadialGraphDecay

namespace TwoAxisHelicoid
open Real Set Filter Bornology
open scoped ContDiff Topology

/-- An actual exterior graph containing the spatial axis has zero
normal displacement on that axis outside a finite height interval.
The graph height is recovered using injectivity of the normal tube. -/
theorem exterior_helicoid_graph_zero_on_far_axis {M : Type*} [TopologicalSpace M]
    {Y : M → HelicoidTubeCoordinates} (cy : Continuous Y)
    (axis : ∀ θ : ℝ, ((0,0),θ) ∈ range Y) {K : Set M} (compact : IsCompact Kᶜ)
    {R : ℝ} (E : K ≃ₜ exteriorPlaneBase R) {u : exteriorPlaneBase R → ℝ}
    (graph : ∀ p, |u p|≤1/2 ∧ Y (E.symm p).1=helicoidTubeMap ((u p,p.1.1),p.1.2)) :
    ∀ᶠ θ in cobounded ℝ, extendOpenScalar u (0,θ)=0 := by
  obtain ⟨B,bound⟩ := (compact.image cy).isBounded.exists_norm_le
  apply Filter.hasBasis_cobounded_norm.eventually_iff.mpr
  refine ⟨B+1,trivial,?_⟩
  intro θ hθ
  change B+1≤‖θ‖ at hθ
  obtain ⟨x,ex⟩ := axis θ
  have inK : x ∈ K := by
    by_contra hx
    have d := bound _ (show ((0,0),θ) ∈ Y '' Kᶜ from ⟨x,hx,ex⟩)
    have hd : ‖θ‖≤‖(((0,0),θ) : HelicoidTubeCoordinates)‖ := le_max_right _ _
    linarith
  let p := E ⟨x,inK⟩
  have eq : helicoidTubeMap ((u p,p.1.1),p.1.2)=((0,0),θ) := by
    rw [← (graph p).2,show (E.symm p).1=x by simp [p],ex]
  have hel : helicoidNormalMap p.1.1 p.1.2 (u p)=helicoidNormalMap 0 θ 0 := by
    have e := congrArg (fun q : HelicoidTubeCoordinates => (q.1.1,q.1.2,q.2)) eq
    change helicoidNormalMap p.1.1 p.1.2 (u p)=(0,0,θ) at e
    simpa [helicoidNormalMap,helicoidAngle] using e
  obtain ⟨hr,hh,hu⟩ := helicoidNormalMap_injective ((graph p).1.trans_lt (by norm_num)) (by norm_num) hel
  have ep : p.1=(0,θ) := Prod.ext hr hh
  have inB : (0,θ) ∈ exteriorPlaneBase R := ep ▸ p.2
  have same : (⟨(0,θ),inB⟩ : exteriorPlaneBase R)=p := Subtype.ext ep.symm
  simpa only [extendOpenScalar,dite_eq_left inB,same] using (show u p=0 from hu)

/-- The decay hypotheses in the geometric C¹ end definition imply
uniform decay of the far-axis transverse quotient for its own graph
height extended to the parameter plane. -/
theorem exterior_helicoid_graph_relative_radial_decay {M : Type*} [TopologicalSpace M]
    {Y : M → HelicoidTubeCoordinates} (cy : Continuous Y) (axis : ∀ θ : ℝ, ((0,0),θ) ∈ range Y)
    {K : Set M} (compact : IsCompact Kᶜ) {R : ℝ} (E : K ≃ₜ exteriorPlaneBase R) {u : exteriorPlaneBase R → ℝ}
    (smooth : ContDiffOn ℝ (∞ : WithTop ℕ∞) (extendOpenScalar u) (exteriorPlaneBase R))
    (graph : ∀ p, |u p|≤1/2 ∧ Y (E.symm p).1=helicoidTubeMap ((u p,p.1.1),p.1.2))
    (limit : Tendsto (fun p : exteriorPlaneBase R => |u p|+helicoidGraphGradientNorm (extendOpenScalar u) p.1)
      (comap Subtype.val (cobounded (ℝ × ℝ))) (𝓝 0)) :
    (Tendsto (fun q => |extendOpenScalar u q|+helicoidGraphGradientNorm (extendOpenScalar u) q)
      (cobounded (ℝ × ℝ)) (𝓝 0)) ∧
    ∀ ε : ℝ, 0<ε → ∀ᶠ q in cobounded (ℝ × ℝ), |extendOpenScalar u q|≤ε*|q.1| := by
  have far : ∀ᶠ q in cobounded (ℝ × ℝ), q ∈ exteriorPlaneBase R :=
    Filter.hasBasis_cobounded_norm.eventually_iff.mpr ⟨R+1,trivial,fun q h => by
      change R+1≤‖q‖ at h
      change R<‖q‖
      linarith⟩
  have d := far.mono fun q hq => (smooth.contDiffAt ((exteriorPlaneBase_isOpen R).mem_nhds hq)).differentiableAt (by simp)
  have total : Tendsto (fun q => |extendOpenScalar u q|+helicoidGraphGradientNorm (extendOpenScalar u) q)
      (cobounded (ℝ × ℝ)) (𝓝 0) := by
    intro s hs
    have within := Filter.eventually_comap.mp (limit hs)
    change ∀ᶠ q in cobounded (ℝ × ℝ), |extendOpenScalar u q|+helicoidGraphGradientNorm (extendOpenScalar u) q ∈ s
    filter_upwards [far,within] with q hq h
    simpa only [extendOpenScalar,dite_eq_left hq] using h (⟨q,hq⟩ : exteriorPlaneBase R) rfl
  exact ⟨total,fun _ hε => helicoid_graph_height_small_relative_to_radius d total
    (exterior_helicoid_graph_zero_on_far_axis cy axis compact E graph) hε⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exterior_helicoid_graph_relative_radial_decay
