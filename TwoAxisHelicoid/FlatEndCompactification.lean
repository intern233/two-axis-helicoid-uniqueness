import TwoAxisHelicoid.FlatEndCappingMap
import TwoAxisHelicoid.PlaneCapLimit
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

namespace TwoAxisHelicoid
open Real Set Filter Bornology
open scoped Topology
set_option maxHeartbeats 1000000

theorem proper_flat_map_cap_tendsto {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (hX : IsProperMap X) {R : ℝ}
    (hflat : ∀ y ∈ range X, R^2 < ambientRadiusSq y → y.1.2 = 0) (A H : ℝ) :
    Tendsto (ambientPlaneCap A H ∘ X) (cocompact M) (𝓝 (planeCapNorth H)) := by
  have hnorm : Tendsto (fun p => ‖X p‖) (cocompact M) atTop :=
    tendsto_norm_cocompact_atTop.comp (isProperMap_iff_tendsto_cocompact.mp hX).2
  have hQ : Tendsto (fun p => ambientRadiusSq (X p)) (cocompact M) atTop :=
    tendsto_atTop_mono (fun p => ambient_norm_sq_le_radius (X p))
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hnorm)
  have hflatE : ∀ᶠ p in cocompact M, (X p).1.2 = 0 := by
    filter_upwards [hQ.eventually_gt_atTop (R^2)] with p hp
    exact hflat (X p) (mem_range_self p) hp
  have hq : Tendsto (fun p => (X p).1.1^2+(X p).2^2) (cocompact M) atTop := by
    apply hQ.congr'
    filter_upwards [hflatE] with p hp
    simp [ambientRadiusSq,hp]
  apply (smoothPlaneCap_tendsto (p := fun z => ((X z).1.1,(X z).2)) A H hq).congr'
  filter_upwards [hflatE] with p hp
  exact (ambientPlaneCap_of_flat hp).symm

noncomputable def cappedOnePointMap {M : Type*} (A H : ℝ) (X : M → HelicoidTubeCoordinates)
    (p : OnePoint M) : HelicoidTubeCoordinates :=
  p.elim (planeCapNorth H) (ambientPlaneCap A H ∘ X)

theorem cappedOnePointMap_continuous {M : Type*} [TopologicalSpace M] [T2Space M]
    {X : M → HelicoidTubeCoordinates} (hX : IsProperMap X) {R : ℝ}
    (hflat : ∀ y ∈ range X, R^2 < ambientRadiusSq y → y.1.2 = 0) (A H : ℝ) :
    Continuous (cappedOnePointMap A H X) := by
  rw [OnePoint.continuous_iff]
  constructor
  · change Tendsto (ambientPlaneCap A H ∘ X) (coclosedCompact M) (𝓝 (planeCapNorth H))
    rw [coclosedCompact_eq_cocompact]
    exact proper_flat_map_cap_tendsto hX hflat A H
  · exact (ambientPlaneCap_contDiff A H).continuous.comp hX.continuous

theorem cappedOnePointMap_injective {M : Type*} {X : M → HelicoidTubeCoordinates}
    (hXi : Function.Injective X) {A H R : ℝ}
    (hR : 0 < R) (hA1 : 1 ≤ A) (hAR : 4*R^2 ≤ A) (hH : 4*R ≤ H)
    (hflat : ∀ y ∈ range X, R^2 < ambientRadiusSq y → y.1.2 = 0) :
    Function.Injective (cappedOnePointMap A H X) := by
  intro p q hpq
  induction p using OnePoint.rec with
  | infty =>
    induction q using OnePoint.rec with
    | infty => rfl
    | coe q =>
      exact False.elim (ambientPlaneCap_avoids_north hR hA1 hAR hH hflat (mem_range_self q) hpq.symm)
  | coe p =>
    induction q using OnePoint.rec with
    | infty =>
      exact False.elim (ambientPlaneCap_avoids_north hR hA1 hAR hH hflat (mem_range_self p) hpq)
    | coe q =>
      apply congrArg OnePoint.some
      exact hXi (ambientPlaneCap_injOn_flat_exterior hR hA1 hAR hH hflat
        (mem_range_self p) (mem_range_self q) hpq)

/-- The cap closes the actual embedded spatial surface to a compact
embedded image, with exactly the one-point compactification topology. -/
theorem cappedOnePointMap_isClosedEmbedding {M : Type*} [TopologicalSpace M] [T2Space M]
    {X : M → HelicoidTubeCoordinates} (hX : IsProperMap X) (hXi : Function.Injective X)
    {A H R : ℝ} (hR : 0 < R) (hA1 : 1 ≤ A) (hAR : 4*R^2 ≤ A) (hH : 4*R ≤ H)
    (hflat : ∀ y ∈ range X, R^2 < ambientRadiusSq y → y.1.2 = 0) :
    Topology.IsClosedEmbedding (cappedOnePointMap A H X) :=
  (cappedOnePointMap_continuous hX hflat A H).isClosedEmbedding
    (cappedOnePointMap_injective hXi hR hA1 hAR hH hflat)

noncomputable def punctureOnePointHomeomorph {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] (p : M) : OnePoint {q : M // q ≠ p} ≃ₜ M :=
  OnePoint.equivOfIsEmbeddingOfRangeEq p Subtype.val Topology.IsEmbedding.subtypeVal (by
    ext q
    simp)

/-- When the original parameter space is a punctured compact surface,
the closed cap has that very compact surface as its parameter topology. -/
theorem punctured_flat_end_has_compact_embedding
    {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] {p : M}
    {X : {q : M // q ≠ p} → HelicoidTubeCoordinates} (hX : IsProperMap X)
    (hXi : Function.Injective X) {R : ℝ} (hR : 0 < R)
    (hflat : ∀ y ∈ range X, R^2 < ambientRadiusSq y → y.1.2 = 0) :
    ∃ F : M → HelicoidTubeCoordinates, Topology.IsClosedEmbedding F ∧
      F p = planeCapNorth (4*R) ∧
      ∀ q : {q : M // q ≠ p}, ambientRadiusSq (X q) ≤ R^2 → F q.1 = X q := by
  let A := max 1 (4*R^2)
  let H := 4*R
  let e := punctureOnePointHomeomorph p
  let F := cappedOnePointMap A H X ∘ e.symm
  have hA1 : 1 ≤ A := le_max_left _ _
  have hAR : 4*R^2 ≤ A := le_max_right _ _
  have hemb : Topology.IsClosedEmbedding F :=
    (cappedOnePointMap_isClosedEmbedding hX hXi hR hA1 hAR le_rfl hflat).comp e.symm.isClosedEmbedding
  refine ⟨F,hemb,?_,?_⟩
  · have he0 : e (OnePoint.infty : OnePoint {q : M // q ≠ p}) = p := rfl
    have hback : e.symm p = OnePoint.infty := by
      simpa only [e.symm_apply_apply] using (congrArg e.symm he0).symm
    change cappedOnePointMap A H X (e.symm p) = planeCapNorth H
    rw [hback]
    rfl
  · intro q hq
    have heq : e (q : OnePoint {q : M // q ≠ p}) = q.1 := rfl
    change cappedOnePointMap A H X (e.symm q.1) = X q
    rw [← heq,e.symm_apply_apply]
    exact ambientPlaneCap_fixes_ball (by nlinarith [sq_nonneg R] : R^2 ≤ A) hq

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.cappedOnePointMap_isClosedEmbedding
#print axioms TwoAxisHelicoid.punctured_flat_end_has_compact_embedding
