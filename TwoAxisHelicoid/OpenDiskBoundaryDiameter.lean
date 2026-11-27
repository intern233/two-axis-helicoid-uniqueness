import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

namespace TwoAxisHelicoid
open Complex Metric Set Filter
open scoped Topology

private theorem exists_farther_in_ball (p q : ℂ) {δ : ℝ} (hδ : 0<δ) :
    ∃ w∈ball p δ, dist p q<dist w q := by
  by_cases eq : p=q
  · subst q
    refine ⟨p+(δ/2:ℝ),?_,?_⟩
    · simpa [mem_ball,dist_eq_norm,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (half_pos hδ),abs_of_pos hδ] using half_lt_self hδ
    · simp [dist_eq_norm,Complex.norm_real,Real.norm_eq_abs,hδ.ne']
  have pos : 0<‖p-q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr eq)
  let s := δ/(2*‖p-q‖)
  have hs : 0<s := div_pos hδ (by positivity)
  have mul : s*‖p-q‖=δ/2 := by dsimp [s]; field_simp
  let w := p+s • (p-q)
  have delta : w-q=(1+s) • (p-q) := by simp [w,add_smul]; abel
  refine ⟨w,?_,?_⟩
  · rw [mem_ball,dist_eq_norm,show w-p=s • (p-q) by dsimp [w]; abel,
      norm_smul,Real.norm_eq_abs,abs_of_pos hs,mul]
    exact half_lt_self hδ
  · rw [dist_eq_norm,dist_eq_norm,delta,norm_smul,Real.norm_eq_abs,abs_of_pos (by linarith : 0<1+s)]
    nlinarith [mul_pos hs pos]

/-- A planar coordinate is open, so the farthest image point of a
closed disk from any prescribed point is attained on its circle. -/
theorem open_disk_boundary_farthest (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ} {r : ℝ}
    (hr : 0<r) (domain : closedBall a r⊆e.source) (q : ℂ) :
    ∃ x∈sphere a r, ∀ z∈closedBall a r, dist (e z) q≤dist (e x) q := by
  have cont : ContinuousOn (fun z => dist (e z) q) (closedBall a r) :=
    fun z hz => (e.continuousAt (domain hz)).tendsto.dist tendsto_const_nhds |>.mono_left nhdsWithin_le_nhds
  obtain ⟨x,hx,bound⟩ := (isCompact_closedBall a r).exists_isMaxOn
    ⟨a,mem_closedBall_self hr.le⟩ cont
  refine ⟨x,?_,bound⟩
  rw [mem_sphere]
  apply le_antisymm hx
  by_contra! interior
  have nh := e.image_mem_nhds (domain hx) (isOpen_ball.mem_nhds (show x∈ball a r from interior))
  obtain ⟨δ,hδ,sub⟩ := Metric.mem_nhds_iff.mp nh
  obtain ⟨w,hw,large⟩ := exists_farther_in_ball (e x) q hδ
  obtain ⟨z,hz,eq⟩ := sub hw
  exact large.not_ge (eq ▸ bound (ball_subset_closedBall hz))

/-- A uniform distance bound for pairs on a circle controls every
pair in the image of the closed disk. -/
theorem open_disk_diameter_le_boundary (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ} {r D : ℝ}
    (hr : 0<r) (domain : closedBall a r⊆e.source)
    (bd : ∀ x∈sphere a r, ∀ y∈sphere a r, dist (e x) (e y)≤D)
    {z w : ℂ} (hz : z∈closedBall a r) (hw : w∈closedBall a r) : dist (e z) (e w)≤D := by
  obtain ⟨x,hx,h⟩ := open_disk_boundary_farthest e hr domain (e w)
  obtain ⟨y,hy,k⟩ := open_disk_boundary_farthest e hr domain (e x)
  calc
    dist (e z) (e w) ≤ dist (e x) (e w) := h z hz
    _ = dist (e w) (e x) := dist_comm _ _
    _ ≤ dist (e y) (e x) := k w hw
    _ ≤ D := bd y hy x hx

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.open_disk_diameter_le_boundary
