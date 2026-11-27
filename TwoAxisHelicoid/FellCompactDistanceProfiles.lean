module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith

public section
namespace TwoAxisHelicoid
open Set Filter Metric Topology

/-- The open-set hit and compact-set miss neighborhoods for a family of
closed sets, restricted to a specified set of parameters. -/
def ContinuousFellOn {J E : Type*} [TopologicalSpace J] [TopologicalSpace E]
    (S : J → Set E) (K : Set J) : Prop :=
  ∀ m∈K,
    (∀ U : Set E, IsOpen U → (U ∩ S m).Nonempty →
      ∀ᶠ i in 𝓝[K] m, (U ∩ S i).Nonempty) ∧
    (∀ C : Set E, IsCompact C → Disjoint C (S m) →
      ∀ᶠ i in 𝓝[K] m, Disjoint C (S i))

/-- In a proper metric space these neighborhoods make distance to
each fixed point continuous on the original parameter set. -/
theorem continuousOn_infDist_of_fell {J E : Type*} [TopologicalSpace J] [MetricSpace E] [ProperSpace E]
    {S : J → Set E} {K : Set J} (nonempty : ∀ m∈K, (S m).Nonempty)
    (continuousSets : ContinuousFellOn S K) (x : E) : ContinuousOn (fun m => infDist x (S m)) K := by
  intro m hm
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  let d := infDist x (S m)
  have half : 0<ε/2 := half_pos ep
  have upper : d<d+ε/2 := lt_add_of_pos_right _ half
  obtain ⟨y,hy,distY⟩ := (infDist_lt_iff (nonempty m hm)).mp upper
  have hit : (ball x (d+ε/2) ∩ S m).Nonempty := ⟨y,mem_ball'.mpr distY,hy⟩
  have exclude : Disjoint (closedBall x (d-ε/2)) (S m) :=
    disjoint_closedBall_of_lt_infDist (show d-ε/2<d by linarith)
  obtain ⟨hits,misses⟩ := continuousSets m hm
  filter_upwards [self_mem_nhdsWithin,hits _ isOpen_ball hit,misses _ (isCompact_closedBall _ _) exclude] with i hi touches avoids
  obtain ⟨z,inBall,inSet⟩ := touches
  have hiBound : infDist x (S i)<d+ε/2 := (infDist_le_dist_of_mem inSet).trans_lt (mem_ball'.mp inBall)
  have loBound : d-ε/2 ≤ infDist x (S i) := (le_infDist (nonempty i hi)).mpr (by
    intro w hw
    apply le_of_not_gt
    intro low
    exact disjoint_left.mp avoids (mem_closedBall'.mpr low.le) hw)
  rw [Real.dist_eq,abs_lt]
  change -ε < infDist x (S i)-d ∧ infDist x (S i)-d<ε
  constructor <;> linarith

/-- From a compact family one obtains a subsequence whose distances
converge at every point of a countable list to those of one member
of the same family. No countability assumption on its parameter space. -/
theorem compact_fell_distances_have_common_subsequence {J E : Type*} [TopologicalSpace J] [MetricSpace E] [ProperSpace E]
    {S : J → Set E} {K : Set J} (compact : IsCompact K) (nonempty : ∀ m∈K, (S m).Nonempty)
    (continuousSets : ContinuousFellOn S K) (x : ℕ → E) (a : ℕ → J) (inside : ∀ n, a n∈K) :
    ∃ (m : J), m∈K ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ j, Tendsto (fun n => infDist (x j) (S (a (φ n)))) atTop (𝓝 (infDist (x j) (S m))) := by
  let P (i : J) (j : ℕ) := infDist (x j) (S i)
  have continuousP : ContinuousOn P K := fun m hm => tendsto_pi_nhds.mpr
    (fun j => continuousOn_infDist_of_fell nonempty continuousSets (x j) m hm)
  have subseq := (compact.image_of_continuousOn continuousP).isSeqCompact
  obtain ⟨_,⟨m,hm,rfl⟩,φ,mono,limit⟩ := subseq (fun n => mem_image_of_mem P (inside n))
  exact ⟨m,hm,φ,mono,tendsto_pi_nhds.mp limit⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.continuousOn_infDist_of_fell
#print axioms TwoAxisHelicoid.compact_fell_distances_have_common_subsequence
