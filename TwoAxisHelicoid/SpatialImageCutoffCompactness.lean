import TwoAxisHelicoid.NonperiodicCompactnessCutoffs
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Sequences

namespace TwoAxisHelicoid
open Set Filter Topology Metric
open scoped Topology

/-- Convergence of distances to the actual closed surfaces suffices to
identify their spatial limit on all neighborhoods. -/
theorem local_spatial_image_limit_of_distances {E : Type*} [MetricSpace E] (S : ℕ → Set E) (L : Set E)
    (hs : ∀ n, (S n).Nonempty) (hl : L.Nonempty) (hc : IsClosed L)
    (conv : ∀ x, Tendsto (fun n => infDist x (S n)) atTop (𝓝 (infDist x L))) : LocalSpatialImageLimit S L := by
  constructor
  · intro x hx U hu
    obtain ⟨r,hr,hU⟩ := Metric.mem_nhds_iff.mp hu
    have small : ∀ᶠ n in atTop, infDist x (S n) < r := (conv x).eventually_lt_const (by rwa [infDist_zero_of_mem hx])
    filter_upwards [small] with n hn
    obtain ⟨y,hy,hxy⟩ := (infDist_lt_iff (hs n)).mp hn
    exact ⟨y,hy,hU (show dist y x < r from (dist_comm x y) ▸ hxy)⟩
  · intro x hx
    let d := infDist x L
    have hd : 0 < d := (hc.notMem_iff_infDist_pos hl).mp hx
    have away : ∀ᶠ n in atTop, d/2 < infDist x (S n) := (conv x).eventually_const_lt (show d/2 < d by linarith)
    refine ⟨ball x (d/2),ball_mem_nhds x (by linarith),?_⟩
    filter_upwards [away] with n hn
    apply Set.disjoint_left.mpr
    intro y hy hb
    have hxy : dist x y < d/2 := (dist_comm y x) ▸ (show dist y x < d/2 from hb)
    exact ((hn.trans_le (infDist_le_dist_of_mem hy)).not_gt hxy)

/-- Convert compactness of every cutoff in a first-countable space of
smooth surfaces into the image-subsequence statement in the cutoff proof.
The geometry enters only through the convergence of distance to the image. -/
theorem compact_screw_cutoffs_of_compact_families {M : Type*} [TopologicalSpace M] [FirstCountableTopology M]
    (X : M → Set (Fin 3 → ℝ)) (hn : ∀ m, (X m).Nonempty) (hclosed : ∀ m, IsClosed (X m))
    (compact : ∀ η : ℝ, Real.pi/2 < η → IsCompact {m : M | HasNoScrewBelow η (X m)})
    (spatial : ∀ (s : ℕ → M) (m : M), Tendsto s atTop (𝓝 m) → ∀ x,
      Tendsto (fun n => infDist x (X (s n))) atTop (𝓝 (infDist x (X m)))) : CompactScrewCutoffs (range X) := by
  intro η hη S hS
  choose a ha using fun n => (hS n).1
  have hmem (n : ℕ) : a n ∈ {m : M | HasNoScrewBelow η (X m)} := by
    change HasNoScrewBelow η (X (a n))
    rw [ha n]
    exact (hS n).2
  obtain ⟨m,hm,φ,hφ,hlim⟩ := (compact η hη).isSeqCompact hmem
  refine ⟨φ,X m,hφ,mem_range_self m,?_,hm⟩
  have images : (fun n => X ((a ∘ φ) n)) = S ∘ φ := funext fun n => ha (φ n)
  rw [← images]
  exact local_spatial_image_limit_of_distances _ _ (fun n => hn _) (hn _) (hclosed _) (spatial _ m hlim)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_screw_cutoffs_of_compact_families
