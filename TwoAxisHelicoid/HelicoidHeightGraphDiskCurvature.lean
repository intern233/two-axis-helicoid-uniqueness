import TwoAxisHelicoid.ConformalHelicoidGaussFrame
import TwoAxisHelicoid.QuantitativeMinimalDiskCurvature

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped Topology ContDiff

theorem helicoidHeightSurface_contDiffAt {u : ℝ × ℝ → ℝ} {z : ℂ}
    (su : ContDiffAt ℝ ∞ u (helicoidConformalBase z)) : ContDiffAt ℝ ∞ (helicoidHeightSurface u) z := by
  have sb : ContDiff ℝ ∞ helicoidConformalBase := Real.contDiff_sinh.comp reCLM.contDiff |>.prodMk imCLM.contDiff
  have sg : ContDiffAt ℝ ∞ (helicoidGraphMap u) (helicoidConformalBase z) :=
    helicoidTubeMap_contDiff.contDiffAt.comp _ ((su.prodMk contDiffAt_fst).prodMk contDiffAt_snd)
  exact tubeCartesianLinear.contDiff.contDiffAt.comp z (sg.comp z sb.contDiffAt)

theorem helicoidHeightSurface_injective_derivative {u : ℝ × ℝ → ℝ} {z : ℂ}
    (du : DifferentiableAt ℝ u (helicoidConformalBase z)) (half : |u (helicoidConformalBase z)|≤1/2) :
    Function.Injective (fderiv ℝ (helicoidHeightSurface u) z) := by
  intro v w eq
  have lower := physical_height_graph_speed_lower du half (v-w)
  rw [map_sub,eq,sub_self,map_zero,norm_zero,mul_zero] at lower
  exact sub_eq_zero.mp (norm_le_zero_iff.mp lower)

/-- A smooth minimal normal graph with amplitude at most one half on
a fixed physical parameter disk has an absolute Weingarten bound at
its center. The estimate assumes no control of the first derivative
of the graph. The ambient frame is chosen from the base helicoid. -/
theorem helicoid_height_graph_disk_curvature {u : ℝ × ℝ → ℝ} {a : ℂ}
    (smooth : ∀ z∈ball a (1/2), ContDiffAt ℝ ∞ u (helicoidConformalBase z))
    (height : ∀ z∈ball a (1/2), |u (helicoidConformalBase z)|≤1/2)
    (minimal : ∀ z∈ball a (1/2), coordinateMeanCurvature (helicoidHeightSurface u) z=0) (v : ℂ) :
    ‖fderiv ℝ (euclideanUnitChartNormal (helicoidHeightSurface u)) a v‖≤
      12288*‖coordinateToEuclidean (fderiv ℝ (helicoidHeightSurface u) a v)‖ := by
  let X := helicoidHeightSurface u
  have du (z : ℂ) (hz : z∈ball a (1/2)) := (smooth z hz).differentiableAt (by simp)
  obtain ⟨T,ortho,cross,pole⟩ := physical_height_graph_disk_frame (by norm_num : (1:ℝ)/2≤15/16) du height
  have reg (z : ℂ) (hz : z∈ball a (1/2)) : ContDiffAt ℝ ∞ (T ∘ X) z ∧
      Function.Injective (fderiv ℝ (T ∘ X) z) ∧ coordinateMeanCurvature (T ∘ X) z=0 := by
    refine ⟨T.contDiff.contDiffAt.comp z (helicoidHeightSurface_contDiffAt (smooth z hz)),?_,?_⟩
    · rw [T.comp_fderiv]
      exact T.injective.comp (helicoidHeightSurface_injective_derivative (du z hz) (height z hz))
    · simpa only [zero_add,Function.comp_def] using coordinate_minimal_orthogonal_affine T ortho 0 (minimal z hz)
  have speed (z : ℂ) (hz : z∈ball a (1/2)) (w : ℂ) : ‖w‖≤2*‖coordinateToEuclidean (fderiv ℝ (T ∘ X) z w)‖ := by
    rw [T.comp_fderiv]
    change _≤2*‖coordinateToEuclidean (T (fderiv ℝ X z w))‖
    rw [euclidean_speed_of_orthogonal_frame ortho]
    exact physical_height_graph_speed_lower (du z hz) (height z hz) w
  have h := regular_minimal_disk_bounded_normal_derivative (r:=(1:ℝ)/256) (by norm_num) (by norm_num : (0:ℝ)≤2)
    (by norm_num) (by norm_num) reg pole speed v
  obtain ⟨normal,tangent⟩ := oriented_spatial_frame_derivative_lengths ortho cross X a v
  rw [normal,tangent] at h
  norm_num at h
  exact h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoid_height_graph_disk_curvature
