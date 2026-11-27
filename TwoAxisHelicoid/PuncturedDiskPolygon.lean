import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Basic

namespace TwoAxisHelicoid
open Set Metric
open scoped Topology
set_option maxHeartbeats 800000

theorem complex_ball_diff_finite_isPreconnected (c : ℂ) {r : ℝ} (hr : 0 < r)
    {P : Set ℂ} (hP : P.Finite) : IsPreconnected (ball c r \ P) := by
  let e := OpenPartialHomeomorph.univBall c r
  have heS : e.source = univ := OpenPartialHomeomorph.univBall_source c r
  have heT : e.target = ball c r := OpenPartialHomeomorph.univBall_target c hr
  have hi : Function.Injective e := by
    intro x y h
    exact e.injOn (by rw [heS]; trivial) (by rw [heS]; trivial) h
  have hQ : (e ⁻¹' P).Countable := (Set.Finite.preimage hi.injOn hP).countable
  have hc := hQ.isConnected_compl_of_one_lt_rank
    (by rw [← Module.finrank_eq_rank,Complex.finrank_real_complex]; norm_num : 1 < Module.rank ℝ ℂ)
  have he : e '' (e ⁻¹' P)ᶜ = ball c r \ P := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨heT ▸ e.map_source (heS ▸ mem_univ w),hw⟩
    · intro hz
      have hzt : z ∈ e.target := heT.symm ▸ hz.1
      refine ⟨e.symm z,?_,e.right_inv hzt⟩
      simpa only [mem_compl_iff,mem_preimage,e.right_inv hzt] using hz.2
  rw [← he]
  exact hc.isPreconnected.image e (OpenPartialHomeomorph.continuous_univBall c r).continuousOn

/-- A finite polygon in an open subset of the complex plane. -/
inductive PlanePolygon (Ω : Set ℂ) : ℂ → ℂ → Type
  | refl (z : ℂ) (hz : z ∈ Ω) : PlanePolygon Ω z z
  | step (x y : ℂ) (h : ∀ s : ℝ, s ∈ Icc 0 1 →
      AffineMap.lineMap (k := ℝ) x y s ∈ Ω) : PlanePolygon Ω x y
  | trans {x y z : ℂ} : PlanePolygon Ω x y → PlanePolygon Ω y z → PlanePolygon Ω x z

theorem planePolygon_exists {Ω : Set ℂ} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    {x y : ℂ} (hx : x ∈ Ω) (hy : y ∈ Ω) : Nonempty (PlanePolygon Ω x y) := by
  let R : Set ℂ := {z | z ∈ Ω ∧ Nonempty (PlanePolygon Ω x z)}
  let S : Set ℂ := {z | z ∈ Ω ∧ ¬ Nonempty (PlanePolygon Ω x z)}
  have hopenR : IsOpen R := by
    apply Metric.isOpen_iff.mpr
    rintro z ⟨hz,⟨c⟩⟩
    obtain ⟨δ,hδ,hB⟩ := Metric.isOpen_iff.mp hΩ z hz
    refine ⟨δ,hδ,?_⟩
    intro w hw
    refine ⟨hB hw,⟨PlanePolygon.trans c (PlanePolygon.step z w ?_)⟩⟩
    intro s hs
    exact hB ((convex_ball z δ).lineMap_mem (mem_ball_self hδ) hw hs)
  have hopenS : IsOpen S := by
    apply Metric.isOpen_iff.mpr
    rintro z ⟨hz,hn⟩
    obtain ⟨δ,hδ,hB⟩ := Metric.isOpen_iff.mp hΩ z hz
    refine ⟨δ,hδ,?_⟩
    intro w hw
    refine ⟨hB hw,?_⟩
    rintro ⟨c⟩
    apply hn
    refine ⟨PlanePolygon.trans c (PlanePolygon.step w z ?_)⟩
    intro s hs
    exact hB ((convex_ball z δ).lineMap_mem hw (mem_ball_self hδ) hs)
  have hdis : Disjoint R S := by
    rw [disjoint_left]
    intro z hz hs
    exact hs.2 hz.2
  have hcov : Ω ⊆ R ∪ S := by
    intro z hz
    by_cases h : Nonempty (PlanePolygon Ω x z)
    · exact Or.inl ⟨hz,h⟩
    · exact Or.inr ⟨hz,h⟩
  rcases hconn.subset_or_subset hopenR hopenS hdis hcov with hR | hS
  · exact (hR hy).2
  · exact False.elim ((hS hx).2 ⟨PlanePolygon.refl x hx⟩)

theorem punctured_disk_polygon_exists (c : ℂ) {r : ℝ} (hr : 0 < r)
    {P : Set ℂ} (hP : P.Finite) {x y : ℂ}
    (hx : x ∈ ball c r \ P) (hy : y ∈ ball c r \ P) :
    Nonempty (PlanePolygon (ball c r \ P) x y) :=
  planePolygon_exists (isOpen_ball.sdiff hP.isClosed)
    (complex_ball_diff_finite_isPreconnected c hr hP) hx hy

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.punctured_disk_polygon_exists
