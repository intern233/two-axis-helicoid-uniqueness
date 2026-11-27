import TwoAxisHelicoid.UnmarkedNormalCutoffLimits
import TwoAxisHelicoid.SpatialSheetImageConvergence

namespace TwoAxisHelicoid
open Set Filter Metric Topology TopologicalSpace
open scoped Topology

/-- In proper metric space, local convergence of closed sets implies
convergence of distance to every fixed point. Compact exclusion is
essential for the lower bound; a nearby limiting point gives the
upper bound. -/
theorem LocalSpatialImageLimit.infDist_tendsto {E : Type*} [MetricSpace E] [ProperSpace E]
    {S : ℕ → Set E} {L : Set E} (h : LocalSpatialImageLimit S L) (sn : ∀ n, (S n).Nonempty)
    (ln : L.Nonempty) (x : E) : Tendsto (fun n => infDist x (S n)) atTop (𝓝 (infDist x L)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  let d := infDist x L
  let r := ε/3
  have rp : 0<r := by dsimp [r]; positivity
  obtain ⟨y,hy,xy⟩ := (infDist_lt_iff ln).mp (show d<d+r by linarith)
  have exclude : Disjoint (closedBall x (d-r)) L := by
    apply disjoint_left.mpr
    intro z hz zl
    have near : dist x z≤d-r := by rw [dist_comm x z]; exact mem_closedBall.mp hz
    linarith [show d≤dist x z from infDist_le_dist_of_mem zl]
  filter_upwards [h.1 y hy _ (ball_mem_nhds y rp),h.eventually_disjoint_compact (isCompact_closedBall _ _) exclude] with n hits sep
  obtain ⟨a,has,near⟩ := hits
  have upper := (infDist_le_dist_of_mem (x := x) has).trans (dist_triangle _ y _)
  have close : dist y a<r := by rw [dist_comm y a]; exact mem_ball.mp near
  have lower : d-r ≤ infDist x (S n) := (le_infDist (sn n)).mpr (by
    intro t ht
    have out : t∉closedBall x (d-r) := disjoint_left.mp sep ht
    rw [dist_comm x t]
    exact (lt_of_not_ge fun bad => out (mem_closedBall.mpr bad)).le)
  rw [Real.dist_eq,abs_lt]
  change -ε < infDist x (S n)-d ∧ infDist x (S n)-d<ε
  constructor <;> dsimp [r] at * <;> linarith

/-- Compactness for locally smooth surface convergence has a compact
image in countably many distance coordinates of its unoriented normal
bundle. It suffices for the class of surfaces to be first countable. -/
theorem compact_normal_profiles_of_local_convergence {M : Type*} [TopologicalSpace M] [FirstCountableTopology M]
    (N : M → Set PhysicalPositionNormal) (nonempty : ∀ m, (N m).Nonempty)
    (limits : ∀ (s : ℕ → M) m, Tendsto s atTop (𝓝 m) → LocalSpatialImageLimit (N ∘ s) (N m))
    (compact : ∀ η : ℝ, Real.pi/2<η → IsCompact {m : M | HasNoScrewBelow η (physicalNormalPositions (N m))}) :
    ∀ η : ℝ, Real.pi/2<η → IsCompact (denseDistanceProfile '' {U | U∈range N ∧ HasNoScrewBelow η (physicalNormalPositions U)}) := by
  have c : Continuous (denseDistanceProfile ∘ N) := by
    apply continuous_iff_seqContinuous.mpr
    intro s m sm
    apply tendsto_pi_nhds.mpr
    intro j
    exact (limits s m sm).infDist_tendsto (fun n => nonempty (s n)) (nonempty m) _
  intro η hp
  convert (compact η hp).image c using 1
  ext p
  constructor
  · rintro ⟨_,⟨⟨m,rfl⟩,hm⟩,rfl⟩
    exact ⟨m,hm,rfl⟩
  · rintro ⟨m,hm,rfl⟩
    exact ⟨N m,⟨mem_range_self m,hm⟩,rfl⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.LocalSpatialImageLimit.infDist_tendsto
#print axioms TwoAxisHelicoid.compact_normal_profiles_of_local_convergence
