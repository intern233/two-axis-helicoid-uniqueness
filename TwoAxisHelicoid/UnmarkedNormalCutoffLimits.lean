import TwoAxisHelicoid.SpatialImageCutoffCompactness
import TwoAxisHelicoid.RegularOriginalSurfaceNormals
import Mathlib.Topology.Bases

namespace TwoAxisHelicoid
open Set Filter Metric Topology TopologicalSpace
open scoped Topology

abbrev PhysicalPositionNormal := SurfaceEuclideanSpace × SurfaceEuclideanSpace

/-- Coordinates for a closed point--normal set in the topology of
local closed-set convergence. Distances on a single countable dense
subset recover distances at every point. -/
noncomputable def denseDistanceProfile {E : Type*} [MetricSpace E] [SeparableSpace E] [Nonempty E]
    (S : Set E) : ℕ → ℝ := fun j => infDist (denseSeq E j) S

theorem dense_distances_determine_local_limit {E : Type*} [MetricSpace E] [SeparableSpace E] [Nonempty E]
    {S : ℕ → Set E} {L : Set E} (sn : ∀ n, (S n).Nonempty) (ln : L.Nonempty) (cl : IsClosed L)
    (limit : Tendsto (fun n => denseDistanceProfile (S n)) atTop (𝓝 (denseDistanceProfile L))) :
    LocalSpatialImageLimit S L := by
  apply local_spatial_image_limit_of_distances S L sn ln cl
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  obtain ⟨j,hj⟩ := (denseRange_denseSeq (α := E)).exists_dist_lt x (show 0<ε/3 by positivity)
  let d := denseSeq E j
  have test := (tendsto_pi_nhds.mp limit) j
  filter_upwards [(Metric.tendsto_nhds.mp test) (ε/3) (by positivity)] with n small
  have near (K : Set E) : dist (infDist x K) (infDist d K)≤dist x d := by
    simpa using (lipschitz_infDist_pt K).dist_le_mul x d
  have left := dist_triangle (infDist x (S n)) (infDist d (S n)) (infDist x L)
  have right := dist_triangle (infDist d (S n)) (infDist d L) (infDist x L)
  change dist (infDist d (S n)) (infDist d L)<ε/3 at small
  have enddist := near L
  rw [dist_comm (infDist x L)] at enddist
  linarith [near (S n)]

def physicalNormalPositions (U : Set PhysicalPositionNormal) : Set (Fin 3 → ℝ) :=
  (fun q : PhysicalPositionNormal => WithLp.ofLp q.1) '' U

theorem OriginalSmoothHelicoid.normal_positions (s : OriginalSmoothHelicoid) :
    physicalNormalPositions s.unorientedNormals=range s.position := by
  obtain ⟨N,_,_,ns,_⟩ := original_smooth_regular_normal_geometry s
  ext v
  rw [ns]
  constructor
  · rintro ⟨q,⟨b,p,_⟩,rfl⟩
    exact ⟨b,congrArg WithLp.ofLp p⟩
  · rintro ⟨b,rfl⟩
    exact ⟨(s.euclideanPosition b,N b),⟨b,rfl,Or.inl rfl⟩,rfl⟩

/-- If every lower cutoff of the screw period is compact in the
unmarked point--normal topology, a sequence with no positive screw
period has a limit with exactly that property. Both the position and
the tangent plane at all the points are retained in the subsequence. -/
theorem compact_normal_cutoffs_preserve_nonperiodicity (family : Set (Set PhysicalPositionNormal))
    (regular : ∀ U∈family, IsClosed U ∧ U.Nonempty)
    (compact : ∀ η : ℝ, Real.pi/2<η → IsCompact
      (denseDistanceProfile '' {U | U∈family ∧ HasNoScrewBelow η (physicalNormalPositions U)}))
    (S : ℕ → Set PhysicalPositionNormal) (member : ∀ n, S n∈family)
    (nonperiod : ∀ n h, 0<h → unitHelicoidScrew h '' physicalNormalPositions (S n)≠physicalNormalPositions (S n)) :
    ∃ (φ : ℕ → ℕ) (L : Set PhysicalPositionNormal), StrictMono φ ∧ L∈family ∧
      LocalSpatialImageLimit (S ∘ φ) L ∧ ∀ h : ℝ, 0<h → unitHelicoidScrew h '' physicalNormalPositions L≠physicalNormalPositions L := by
  have extract (η : ℝ) (ηpos : Real.pi/2<η) (T : ℕ → Set PhysicalPositionNormal)
      (mem : ∀ n, T n∈family) (period : ∀ n, HasNoScrewBelow η (physicalNormalPositions (T n))) :
      ∃ (ψ : ℕ → ℕ) (K : Set PhysicalPositionNormal), StrictMono ψ ∧ K∈family ∧
        LocalSpatialImageLimit (T ∘ ψ) K ∧ HasNoScrewBelow η (physicalNormalPositions K) := by
    let U := {K | K∈family ∧ HasNoScrewBelow η (physicalNormalPositions K)}
    have inU (n : ℕ) : denseDistanceProfile (T n)∈denseDistanceProfile '' U := ⟨T n,⟨mem n,period n⟩,rfl⟩
    obtain ⟨_,⟨K,hK,rfl⟩,ψ,hψ,conv⟩ := (compact η ηpos).isSeqCompact inU
    exact ⟨ψ,K,hψ,hK.1,dense_distances_determine_local_limit (fun n => (regular _ (mem (ψ n))).2)
      (regular _ hK.1).2 (regular _ hK.1).1 conv,hK.2⟩
  obtain ⟨φ,L,hφ,mem,conv,_⟩ := extract (Real.pi/2+1) (by linarith) S member (fun n h hp _ => nonperiod n h hp)
  refine ⟨φ,L,hφ,mem,conv,?_⟩
  intro h hp
  let η := max (Real.pi/2) h+1
  have ηpos : Real.pi/2<η := by dsimp [η]; linarith [le_max_left (Real.pi/2) h]
  have hη : h<η := by dsimp [η]; linarith [le_max_right (Real.pi/2) h]
  obtain ⟨ψ,K,hψ,_,cv,below⟩ := extract η ηpos (S ∘ φ) (fun n => member (φ n))
    (fun n d dp _ => nonperiod (φ n) d dp)
  rw [(conv.subsequence hψ).unique cv]
  exact below h hp hη

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.dense_distances_determine_local_limit
#print axioms TwoAxisHelicoid.compact_normal_cutoffs_preserve_nonperiodicity
