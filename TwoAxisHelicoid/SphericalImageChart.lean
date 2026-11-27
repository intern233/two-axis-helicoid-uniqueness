import TwoAxisHelicoid.NorthSphereChart

namespace TwoAxisHelicoid
open Real Set Topology
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

/-- An embedded image which actually agrees with a sphere near the
added point has a regular smooth chart there. No regularity of an old
compactification chart at that point is assumed. -/
theorem exists_regular_chart_of_spherical_image
    {M : Type*} [TopologicalSpace M] {F : M → HelicoidTubeCoordinates}
    (hF : IsEmbedding F) {p : M} {H : ℝ} (hH : 0 < H)
    (hp : F p = planeCapNorth H) {W₀ : Set HelicoidTubeCoordinates}
    (hW₀ : IsOpen W₀) (hpW : planeCapNorth H ∈ W₀)
    (himage : range F ∩ W₀ = planeCapSphere H ∩ W₀) :
    ∃ e : OpenPartialHomeomorph M (ℝ × ℝ),
      RegularImmersionChart F e ∧ p ∈ e.source ∧ e p = 0 := by
  let : Nonempty M := ⟨p⟩
  let W : Set HelicoidTubeCoordinates := W₀ ∩ {y | 0 < y.1.2}
  let U : Set M := F ⁻¹' W
  let V : Set (ℝ × ℝ) := northSphereParam H ⁻¹' W
  have hW : IsOpen W := hW₀.inter (isOpen_lt continuous_const (by fun_prop))
  have hU : IsOpen U := hW.preimage hF.continuous
  have hV : IsOpen V := hW.preimage (northSphereParam_contDiff H).continuous
  have hFU (x : M) (hx : x ∈ U) : F x ∈ planeCapSphere H := by
    have hh : F x ∈ range F ∩ W₀ := ⟨mem_range_self x,hx.1⟩
    rw [himage] at hh
    exact hh.1
  have hleft (x : M) (hx : x ∈ U) :
      northSphereParam H (northSphereProjection (F x)) = F x :=
    northSphereParam_projection (hFU x hx) hx.2
  have hcP : ContinuousOn (northSphereProjection ∘ F) U := by
    intro x hx
    exact ((northSphereProjection_contDiffAt hx.2.ne').continuousAt.comp
      hF.continuous.continuousAt).continuousWithinAt
  have hP : MapsTo (northSphereProjection ∘ F) U V := by
    intro x hx
    change northSphereParam H (northSphereProjection (F x)) ∈ W
    rw [hleft x hx]
    exact hx
  have hG (y : ℝ × ℝ) (hy : y ∈ V) : ∃ x ∈ U, F x = northSphereParam H y := by
    have hh : northSphereParam H y ∈ planeCapSphere H ∩ W₀ :=
      ⟨northSphereParam_mem_sphere H y,hy.1⟩
    rw [← himage] at hh
    obtain ⟨x,hx⟩ := hh.1
    refine ⟨x,?_,hx⟩
    change F x ∈ W
    rw [hx]
    exact hy
  obtain ⟨e,heU,heV,heP,heG⟩ := exists_embedded_parametrization_chart hF
    northSphereProjection (northSphereParam H) U V hU hV hcP
    (northSphereParam_contDiff H).continuous.continuousOn hP hleft
    (fun y _ => northSphereProjection_param hH y) hG
  have he : RegularImmersionChart F e := regularImmersionChart_of_parametrization e
    (fun y hy => heG y (heV ▸ hy))
    (fun _ _ => (northSphereParam_contDiff H).contDiffAt)
    (fun y _ => northSphereParam_fderiv_injective hH y)
  refine ⟨e,he,?_,?_⟩
  · rw [heU]
    change F p ∈ W
    rw [hp]
    exact ⟨hpW,hH⟩
  · rw [heP]
    simp [hp,northSphereProjection,planeCapNorth]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exists_regular_chart_of_spherical_image
