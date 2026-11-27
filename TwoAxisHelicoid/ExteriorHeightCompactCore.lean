import TwoAxisHelicoid.ExteriorHeightEscape

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology

/-- The exterior coordinate itself supplies points of arbitrarily large
height. This uses only the equality with the real part of the coordinate
on the actual surface. -/
theorem exterior_height_unbounded {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) {R : ℝ} (ht : e.target = {ζ : ℂ | R < ‖ζ‖}) (h : M → ℝ)
    (b : ℝ) (hh : ∀ x ∈ e.source, h x = b+(e x).re) (A : ℝ) : ∃ x, A < h x := by
  let B := max (max R (A-b)) 0 + 1
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right (max R (A-b)) 0]
  have hbig : max R (A-b) < B := by dsimp [B]; linarith [le_max_left (max R (A-b)) 0]
  have hz : (B:ℂ) ∈ e.target := by
    rw [ht]
    change R < ‖(B:ℂ)‖
    rw [Complex.norm_real,Real.norm_of_nonneg hB.le]
    exact (le_max_left _ _).trans_lt hbig
  refine ⟨e.symm (B:ℂ),?_⟩
  rw [hh _ (e.map_target hz),e.right_inv hz,ofReal_re]
  linarith [(le_max_right R (A-b)).trans_lt hbig]

theorem true_exterior_height_coordinate_escapes {M : Type*} [TopologicalSpace M]
    (hEnd : HasConnectedCompactTails M) (e : OpenPartialHomeomorph M ℂ) {R : ℝ}
    (ht : e.target = {ζ : ℂ | R < ‖ζ‖}) (hc : IsCompact e.sourceᶜ)
    (h : M → ℝ) (hcont : Continuous h) (b : ℝ) (hh : ∀ x ∈ e.source, h x = b+(e x).re) :
    Tendsto (fun x => ‖e x‖) (cocompact M) atTop :=
  exterior_coordinate_escapes_of_height hEnd e ht hc h hcont b hh (exterior_height_unbounded e ht h b hh)

theorem noncompact_of_exterior_height {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) {R : ℝ} (ht : e.target = {ζ : ℂ | R < ‖ζ‖})
    (h : M → ℝ) (hcont : Continuous h) (b : ℝ) (hh : ∀ x ∈ e.source, h x = b+(e x).re) :
    NoncompactSpace M := by
  constructor
  intro hK
  obtain ⟨B,hB⟩ := hK.bddAbove_image hcont.continuousOn
  obtain ⟨x,hx⟩ := exterior_height_unbounded e ht h b hh B
  exact hx.not_ge (hB (mem_image_of_mem h (mem_univ x)))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.true_exterior_height_coordinate_escapes
