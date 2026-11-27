import TwoAxisHelicoid.HelicoidHeightDecayStraightening
import TwoAxisHelicoid.HelicoidEndDomain

namespace TwoAxisHelicoid
open Set Filter Bornology Metric Topology
open scoped Topology

/-- Small height on the base of an actual proper graph gives small
height off a compact subset of the physical surface. A graph over a
bounded set of base parameters lies in a compact spatial block. -/
theorem HasHelicoidHeightEnd.arbitrarily_thin {M : Type*} [TopologicalSpace M]
    {Y : M → HelicoidTubeCoordinates} (graph : HasHelicoidHeightEnd Y) (proper : IsProperMap Y) :
    ∀ ε : ℝ, 0<ε → ∃ W : Set M, IsCompact Wᶜ ∧ ∀ x∈W, ∃ s r θ : ℝ,
      |s|<ε ∧ Y x=helicoidTubeMap ((s,r),θ) := by
  obtain ⟨S,core,R,_,E,u,_,half,formula,decay⟩ := graph
  intro ε ep
  obtain ⟨T,_,small⟩ := ((hasBasis_cobounded_norm.comap
    (Subtype.val : exteriorPlaneBase R → ℝ × ℝ)).eventually_iff).mp (decay.eventually (gt_mem_nhds ep))
  let B := closedBall (0 : ℝ × ℝ) T
  let K := Sᶜ ∪ Y ⁻¹' helicoidHeightBlock (1/2) B
  have kc : IsCompact K := core.union (proper.isCompact_preimage (helicoidHeightBlock_isCompact _ (isCompact_closedBall _ _)))
  refine ⟨Kᶜ,by simpa only [compl_compl] using kc,?_⟩
  intro x hx
  have inside : x∈S := by
    by_contra no
    exact hx (Or.inl no)
  let q : S := ⟨x,inside⟩
  let b := E q
  have large : T≤‖b.1‖ := by
    by_contra! lt
    apply hx
    right
    change Y q.1∈helicoidHeightBlock (1/2) B
    exact ⟨(u b,b.1),⟨abs_le.mp (half b),by simpa only [B,mem_closedBall,dist_zero_right] using lt.le⟩,
      (formula q).symm⟩
  refine ⟨u b,b.1.1,b.1.2,?_,formula q⟩
  exact small (show b∈(Subtype.val : exteriorPlaneBase R → ℝ × ℝ) ⁻¹' {v | T≤‖v‖} from large)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidHeightEnd.arbitrarily_thin
