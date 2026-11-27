import TwoAxisHelicoid.RegularOriginalSurfaceNormals

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- A continuous choice of either sign of a nonvanishing continuous
field agrees locally with one of the two signs. -/
theorem continuous_sign_choice_germ {E F : Type*} [TopologicalSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n m : E → F} {x : E} (cn : ContinuousAt n x) (cm : ContinuousAt m x) (nz : m x≠0)
    (choice : ∀ᶠ y in 𝓝 x, n y=m y ∨ n y= -m y) : n=ᶠ[𝓝 x] m ∨ n=ᶠ[𝓝 x] fun y => -m y := by
  have ne : m x≠ -m x := by
    intro eq
    have zero : (2:ℝ) • m x=0 := by rw [two_smul]; exact add_eq_zero_iff_eq_neg.mpr eq
    exact nz ((smul_eq_zero.mp zero).resolve_left (by norm_num))
  rcases choice.self_of_nhds with pos|neg
  · left
    have apart : n x≠ -m x := pos ▸ ne
    filter_upwards [choice,(cn.sub cm.neg).eventually_ne (sub_ne_zero.mpr apart)] with y h ht
    exact h.resolve_right (sub_ne_zero.mp ht)
  · right
    have apart : n x≠m x := neg ▸ ne.symm
    filter_upwards [choice,(cn.sub cm).eventually_ne (sub_ne_zero.mpr apart)] with y h ht
    exact h.resolve_left (sub_ne_zero.mp ht)

/-- An actual continuous unit normal on the original immersion is C¹
in every smooth regular parametrization. Its direction annihilates
the ordinary Euclidean derivative in that parametrization. -/
theorem original_unit_normal_in_arbitrary_regular_chart (s : OriginalSmoothHelicoid)
    {N : s.carrier → SurfaceEuclideanSpace} (cn : Continuous N) (unit : ∀ b, ‖N b‖=1)
    (normals : s.unorientedNormals=unorientedSurfaceNormals s.euclideanPosition N)
    (a : OpenPartialHomeomorph s.carrier ℂ) (reg : RegularImmersionChart s.position a) {z : ℂ} (az : z∈a.target) :
    ContDiffAt ℝ 1 (s.euclideanPosition ∘ a.symm) z ∧ ContDiffAt ℝ 1 (N ∘ a.symm) z ∧
    Function.Injective (fderiv ℝ (s.euclideanPosition ∘ a.symm) z) ∧
    ∀ v, ⟪fderiv ℝ (s.euclideanPosition ∘ a.symm) z v,N (a.symm z)⟫=0 := by
  let Y := s.position ∘ a.symm
  let m := euclideanUnitChartNormal Y
  have old := smooth_surface_regular_manifold_chart s.smooth s.immersion
  have plane (w : ℂ) (aw : w∈a.target) : chartEuclideanTangent s.position a w=
      chartEuclideanTangent s.position (chartAt ℂ (a.symm w)) ((chartAt ℂ (a.symm w)) (a.symm w)) := by
    simpa only [a.right_inv aw] using chartEuclideanTangent_eq reg (old _) (a.map_target aw) (mem_chart_source ℂ _)
  have derivEq (w : ℂ) (aw : w∈a.target) : fderiv ℝ (s.euclideanPosition ∘ a.symm) w=
      coordinateToEuclidean.comp (fderiv ℝ Y w) :=
    (coordinateToEuclidean.hasFDerivAt.comp w ((reg w aw).1.differentiableAt (by simp)).hasFDerivAt).fderiv
  have inj (w : ℂ) (aw : w∈a.target) : Function.Injective (fderiv ℝ (s.euclideanPosition ∘ a.symm) w) := by
    rw [derivEq w aw]
    exact surfaceCartesianEquiv.symm.injective.comp (reg w aw).2
  have tangent (w : ℂ) (aw : w∈a.target) (v : ℂ) : fderiv ℝ (s.euclideanPosition ∘ a.symm) w v∈chartEuclideanTangent s.position a w := by
    rw [derivEq w aw]
    exact ⟨v,rfl⟩
  have perp (w : ℂ) (aw : w∈a.target) (v : ℂ) : ⟪fderiv ℝ (s.euclideanPosition ∘ a.symm) w v,N (a.symm w)⟫=0 := by
    let b := a.symm w
    have member : (s.euclideanPosition b,N b)∈s.unorientedNormals := normals ▸ (show
      (s.euclideanPosition b,N b)∈unorientedSurfaceNormals s.euclideanPosition N from ⟨b,rfl,Or.inl rfl⟩)
    obtain ⟨p,pos,_,orth⟩ := member
    have eq : p=b := (surfaceCartesianEquiv.symm.injective.comp s.closedEmbedding.injective) pos
    subst p
    exact orth _ ((plane w aw) ▸ tangent w aw v)
  have choice : ∀ᶠ w in 𝓝 z, (N ∘ a.symm) w=m w ∨ (N ∘ a.symm) w= -m w := by
    filter_upwards [a.open_target.mem_nhds az] with w aw
    exact regular_plane_unit_normal_choices (inj w aw) (euclideanUnitChartNormal_unit (reg w aw).2)
      (unit _) (fun v => (chartEuclideanTangent_iff_unitNormal (reg w aw).2 _).mp (tangent w aw v)) (perp w aw)
  have sm : ContDiffAt ℝ 1 m z := euclideanUnitChartNormal_contDiffAt ((reg z az).1.of_le (by norm_num)) (reg z az).2
  have nz : m z≠0 := by
    intro eq
    have n : ‖m z‖=1 := euclideanUnitChartNormal_unit (reg z az).2
    simp [eq] at n
  refine ⟨coordinateToEuclidean.contDiff.contDiffAt.comp z ((reg z az).1.of_le (by norm_num)),?_,inj z az,perp z az⟩
  rcases continuous_sign_choice_germ (cn.continuousAt.comp (a.symm.continuousAt az)) sm.continuousAt nz choice with a|b
  · exact sm.congr_of_eventuallyEq a
  · exact sm.neg.congr_of_eventuallyEq b

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_unit_normal_in_arbitrary_regular_chart
