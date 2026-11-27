import TwoAxisHelicoid.SpatialSheetInverseGerms
import TwoAxisHelicoid.NonperiodicCompactnessCutoffs
import TwoAxisHelicoid.SpatialPeriodicCoreLimits
import TwoAxisHelicoid.SpatialNonperiodicCoreLimits
import TwoAxisHelicoid.PhysicalAppendixBCompactness

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped ContDiff Topology

/-- The nonperiodic compact-core data in Euclidean positions and their
first derivatives. `spatial_core_charts_of_ambient_sheets` constructs its
marked charts from the spatial sheets. Normal heights and their derivative convergence are
consequences. No fixed covering degree is part of this package. -/
structure EuclideanCoreSheetLimit (W : ℕ → PitchNormalizedBasicImmersion) where
  lattice : PeriodPair
  core : TorusGeneratingCoreModel lattice
  sheets : ∀ n, SpatialCoreSheetCharts core (W n)
  position : ℂ → EuclideanSpace ℝ (Fin 3)
  normal : ℂ → EuclideanSpace ℝ (Fin 3)
  signed : EuclideanSpace ℝ (Fin 3) → ℝ
  position_chart : ∀ n (b : core.carrier) z, b.1 = periodTorusProjection lattice z → (sheets n).position b = position z
  normal_chart : ∀ n (b : core.carrier) z, b.1 = periodTorusProjection lattice z → (sheets n).normal b = normal z
  height_chart : ∀ n (q : (sheets n).patch), (sheets n).signedHeight ((W n).torusPosition q.1) = signed ((W n).torusPosition q.1)
  smooth_position : ∀ z ∈ periodTorusProjection lattice ⁻¹' core.carrier, ContDiffAt ℝ 1 position z
  smooth_normal : ∀ z ∈ periodTorusProjection lattice ⁻¹' core.carrier, ContDiffAt ℝ 1 normal z
  smooth_signed : ∀ z ∈ periodTorusProjection lattice ⁻¹' core.carrier, ContDiffAt ℝ 1 signed (position z)
  zero_signed : ∀ z ∈ periodTorusProjection lattice ⁻¹' core.carrier, signed (position z) = 0
  convergence : let U := periodTorusProjection lattice ⁻¹' core.carrier
    let p := fun n (q : (sheets n).patch) => (sheets n).base ((W n).torusPosition q.1)
    (∀ n, Function.Injective (p n)) → ∃ Z : ℕ → ℂ → EuclideanSpace ℝ (Fin 3),
      (∀ n (q : (sheets n).patch) z, (p n q).1 = periodTorusProjection lattice z → Z n z = (W n).torusPosition q.1) ∧
      (∀ n z, z ∈ U → DifferentiableAt ℝ (Z n) z) ∧ (∀ n z, z ∈ U → DifferentiableAt ℝ signed (Z n z)) ∧
      TendstoLocallyUniformlyOn Z position atTop U ∧
      TendstoLocallyUniformlyOn (fun n => fderiv ℝ (Z n)) (fderiv ℝ position) atTop U

/-- The remaining compactness input extracts finitely many local Euclidean
sheets from a sequence of embedded, axes-marked unit-pitch surfaces. A
periodic limit may have any positive vertical translation step. -/
def UnitPitchEuclideanSheetCompactness : Prop :=
  ∀ x : ℕ → positiveUnitPitchFamily, ∃ φ : ℕ → ℕ, StrictMono φ ∧
    let W := fun n => (x (φ n)).1
    (∃ (A : PeriodPair) (C : TorusGeneratingCoreModel A) (v : C.carrier → ℝ) (d : ℝ),
      0 < d ∧ BddAbove (range (fun q => |v q|)) ∧
      ∀ (k : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ n in atTop, ∃ G : SpatialCoreSheetCharts C (W n),
        ∀ q : G.patch, |(W n).torusPosition q.1 2-(v (G.base ((W n).torusPosition q.1))+(k:ℝ)*d)| < ε) ∨
    Nonempty (EuclideanCoreSheetLimit W)

/-- Derive the covering, single-sheet, height-decay and periodic-core
conclusions used by the genus and flux proof directly from spatial charts. -/
theorem physical_compactness_of_euclidean_sheets (hs : UnitPitchEuclideanSheetCompactness) :
    PhysicalUnitPitchHelicoidCompactness := by
  intro x _ _
  obtain ⟨φ,hφ,alt⟩ := hs x
  let W := fun n => (x (φ n)).1
  have hW (n : ℕ) : W n ∈ embeddedPitchFamily := (x (φ n)).2.1
  rcases alt with ⟨A,C,v,d,hd,hB,hG⟩ | ⟨D⟩
  · exact ⟨φ,hφ,Or.inl (periodic_spatial_charts_give_two_core_patches W hW C v hd hB hG)⟩
  · obtain ⟨D⟩ := D
    exact spatial_charts_give_nonperiodic_core_limit x φ hφ hW D.core D.sheets D.position D.normal D.signed
      D.position_chart D.normal_chart D.height_chart D.smooth_position D.smooth_normal D.smooth_signed D.zero_signed D.convergence

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_compactness_of_euclidean_sheets
