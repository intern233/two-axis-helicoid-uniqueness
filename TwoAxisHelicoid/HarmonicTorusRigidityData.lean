import TwoAxisHelicoid.HarmonicTorusHeightFlux
import TwoAxisHelicoid.PuncturedLatticePlane
import TwoAxisHelicoid.TorusGaussFluxRigidity
import Mathlib.Analysis.Meromorphic.Order

namespace TwoAxisHelicoid
open Complex Set Filter InnerProductSpace
open scoped Topology

/-- On the marked chart cover all coordinate forms are recovered directly
from the real derivatives of the given position map. -/
noncomputable def torusImmersionForms (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ) :
    ℂ → Fin 3 → ℂ := immersionComplexCoefficient (puncturedTorusPullback L X)

noncomputable def torusFilledPosition (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ) :
    PeriodTorus L → Fin 3 → ℝ :=
  periodTorusLift L (puncturedTorusPullback L X) (puncturedTorusPullback_periodic L X)

theorem torusFilledPosition_eq (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (q : PuncturedPeriodTorus L) : torusFilledPosition L X q.1 = X q := by
  obtain ⟨z,rfl⟩ := puncturedPlaneProjection_surjective L q
  exact (show puncturedTorusPullback L X z.1 = _ from by simp [puncturedTorusPullback,z.2])

theorem torusImmersionForms_periodic (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (z ω : ℂ) (hω : ω ∈ L.lattice) : torusImmersionForms L X (z+ω) = torusImmersionForms L X z := by
  funext j
  let f := fun w => puncturedTorusPullback L X w j
  have he : (fun w => f (w+ω)) = f :=
    funext fun u => congrFun (puncturedTorusPullback_periodic L X u ω hω) j
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := z) ω
  rw [he] at hd
  change scalarComplexCoefficient f (z+ω) = scalarComplexCoefficient f z
  unfold scalarComplexCoefficient
  rw [hd]

theorem torusImmersionForms_regular (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hh : ∀ z ∉ L.lattice, ∀ j, HarmonicAt (fun u => puncturedTorusPullback L X u j) z)
    (hc : ∀ z ∉ L.lattice, ConformalCoordinateDerivatives (puncturedTorusPullback L X) z) :
    (∀ z ∉ L.lattice, ∀ j, AnalyticAt ℂ (fun u => torusImmersionForms L X u j) z) ∧
    (∀ z ∉ L.lattice, ComplexNull (torusImmersionForms L X z)) ∧
    ∀ z ∉ L.lattice, HasFDerivAt (torusFilledPosition L X ∘ periodTorusProjection L)
      (nullRealDerivative (torusImmersionForms L X z)) z := by
  refine ⟨fun z hz j => scalarComplexCoefficient_analyticAt (hh z hz j),
    fun z hz => immersionComplexCoefficient_null (hc z hz),?_⟩
  intro z hz
  have ha : AnalyticAt ℝ (puncturedTorusPullback L X) z :=
    analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hh z hz j)
  exact immersionComplexCoefficient_hasFDerivAt ha.differentiableAt

theorem height_differential_nonzero_at_regular_point (L : PeriodPair) {f : ℂ → ℂ}
    (ho : meromorphicOrderAt f 0 = (-2 : ℤ)) : ∃ z ∉ L.lattice, f z ≠ 0 := by
  have hm := meromorphicAt_of_meromorphicOrderAt_ne_zero (f := f) (by rw [ho]; norm_num)
  have hn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hm).mp (by rw [ho]; norm_num)
  have hL : ∀ᶠ z in 𝓝[≠] (0:ℂ), z ∉ L.lattice := by
    filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),self_mem_nhdsWithin] with z hz hz0 hm
    exact hz ⟨hm,hz0⟩
  exact (hL.and hn).exists

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.torusImmersionForms_regular
