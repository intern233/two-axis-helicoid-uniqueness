import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Clopen

namespace TwoAxisHelicoid
open Set Filter Metric
open scoped Topology ENNReal

/-- The finite-distance classes in an extended metric space are clopen;
hence a connected manifold's induced length distance is everywhere finite. -/
theorem edist_ne_top_of_preconnected {M : Type*} [EMetricSpace M] [PreconnectedSpace M]
    (x y : M) : edist x y ≠ ⊤ := by
  let S : Set M := {z | edist x z < ⊤}
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    apply mem_of_superset (eball_mem_nhds z (by norm_num : (0 : ℝ≥0∞) < 1))
    intro w hw
    exact (edist_triangle x z w).trans_lt (ENNReal.add_lt_top.mpr
      ⟨hz,by simpa only [edist_comm z w] using hw.trans (by norm_num : (1 : ℝ≥0∞) < ⊤)⟩)
  have hcompl : IsOpen Sᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    apply mem_of_superset (eball_mem_nhds z (by norm_num : (0 : ℝ≥0∞) < 1))
    intro w hw hmem
    exact hz ((edist_triangle x w z).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hmem,hw.trans (by norm_num : (1 : ℝ≥0∞) < ⊤)⟩))
  have hall : S = univ := (show IsClopen S from ⟨isOpen_compl_iff.mp hcompl,hopen⟩).eq_univ
    ⟨x,by simp [S]⟩
  have hy : y ∈ S := by rw [hall]; trivial
  exact ne_top_of_lt hy

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.edist_ne_top_of_preconnected
