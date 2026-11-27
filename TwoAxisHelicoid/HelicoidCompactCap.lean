import TwoAxisHelicoid.HelicoidCapNormalization
import TwoAxisHelicoid.PuncturedCapMap
import TwoAxisHelicoid.FlatEndCapNeighborhood
import TwoAxisHelicoid.CappedLocalImmersion

namespace TwoAxisHelicoid
open Real Set
open scoped ContDiff
set_option maxHeartbeats 1000000

noncomputable def helicoidCompactCap {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    (p : M) (D : HelicoidTubeCoordinates ≃ₜ HelicoidTubeCoordinates) (R : ℝ)
    (X : {q : M // q ≠ p} → HelicoidTubeCoordinates) : M → HelicoidTubeCoordinates :=
  D ∘ puncturedCapMap p (max 1 (4*R^2)) (4*R) (D.symm ∘ X)

/-- The actual helicoidal surface can be capped while fixing any chosen
compact parameter core pointwise. The closed embedding has the original
compactification as its parameter space. In smooth ambient coordinates
the added point has an entire round-sphere neighborhood. -/
theorem HasHelicoidC1End.exists_compact_cap_fixing_core
    {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] {p : M}
    {X : {q : M // q ≠ p} → HelicoidTubeCoordinates} (hEnd : HasHelicoidC1End X)
    (hX : IsProperMap X) (hXi : Function.Injective X)
    {C : Set {q : M // q ≠ p}} (hC : IsCompact C) :
    ∃ (D : HelicoidTubeCoordinates ≃ₜ HelicoidTubeCoordinates) (R : ℝ), 0 < R ∧
      ContDiff ℝ (∞ : WithTop ℕ∞) D ∧ ContDiff ℝ (∞ : WithTop ℕ∞) D.symm ∧
      Topology.IsClosedEmbedding (helicoidCompactCap p D R X) ∧
      (∀ q ∈ C, helicoidCompactCap p D R X q.1 = X q) ∧
      (∀ y, R^2 < ambientRadiusSq y → (y ∈ range (D.symm ∘ X) ↔ y.1.2 = 0)) ∧
      ∃ U : Set HelicoidTubeCoordinates, IsOpen U ∧ planeCapNorth (4*R) ∈ U ∧
        range (puncturedCapMap p (max 1 (4*R^2)) (4*R) (D.symm ∘ X)) ∩ U =
          planeCapSphere (4*R) ∩ U := by
  obtain ⟨D,R,hR,hD,hDi,hexact,hcore⟩ := hEnd.exists_cap_normalization hX hC
  let Y := D.symm ∘ X
  let A := max 1 (4*R^2)
  let H := 4*R
  have hY : IsProperMap Y := D.symm.isProperMap.comp hX
  have hYi : Function.Injective Y := D.symm.injective.comp hXi
  have hA1 : 1 ≤ A := le_max_left _ _
  have hAR : 4*R^2 ≤ A := le_max_right _ _
  have hflat : ∀ y ∈ range Y, R^2 < ambientRadiusSq y → y.1.2 = 0 :=
    fun y hy hr => (hexact y hr).mp hy
  have hemb : Topology.IsClosedEmbedding (puncturedCapMap p A H Y) :=
    puncturedCapMap_isClosedEmbedding hY hYi hR hA1 hAR le_rfl hflat
  refine ⟨D,R,hR,hD,hDi,D.isClosedEmbedding.comp hemb,?_,hexact,?_⟩
  · intro q hq
    change D (puncturedCapMap p A H Y q.1) = X q
    rw [puncturedCapMap_on_punctured]
    have hfix : ambientPlaneCap A H (Y q) = Y q :=
      ambientPlaneCap_fixes_ball (by nlinarith [sq_nonneg R] : R^2 ≤ A) (hcore q hq)
    rw [hfix]
    exact D.apply_symm_apply (X q)
  · obtain ⟨U,hU,hUN,hUs⟩ := cappedOnePointMap_spherical_neighborhood hR hA1 hAR
      (show 4*R ≤ H from le_rfl) hexact
    refine ⟨U,hU,hUN,?_⟩
    have hrange : range (puncturedCapMap p A H Y) = range (cappedOnePointMap A H Y) :=
      (punctureOnePointHomeomorph p).symm.surjective.range_comp _
    rw [hrange]
    exact hUs

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HasHelicoidC1End.exists_compact_cap_fixing_core
