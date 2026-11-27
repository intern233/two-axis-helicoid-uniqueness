import TwoAxisHelicoid.PeriodicCoefficientComplexPrimitive
import TwoAxisHelicoid.HarmonicNullLift
import TwoAxisHelicoid.PeriodicHeightRigidity

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- Every physical coordinate of a harmonic rhombic torus immersion
has a single-valued complex primitive on the punctured covering plane
whose real part is the given spatial coordinate. There is no pole
hypothesis or choice of periods. -/
theorem TwoAxisHarmonicConformalImmersion.complex_coordinate_primitive {t : ℝ} (ht : 0<t)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (j : Fin 3) : ∃ H : ℂ → ℂ, ∀ z∉(rhombicPeriodPair t ht).lattice,
      HasDerivAt H (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z j) z ∧
      (H z).re=X z j := by
  let L := rhombicPeriodPair t ht
  let f := fun z => puncturedImmersionCoefficient L X z j
  obtain ⟨F,dF⟩ := periodic_coefficient_unrestricted_complex_primitive (f := f) ht
    (fun _ hz => puncturedImmersionCoefficient_analyticAt hX hz j)
    (fun z ω hω => congrFun (puncturedImmersionCoefficient_periodic hX z ω hω) j)
  have dRe (z : ℂ) (hz : z∉L.lattice) : HasFDerivAt (fun w => (F w).re) (realCoefficientDerivative (f z)) z :=
    Complex.reCLM.hasFDerivAt.comp z ((dF z hz).hasFDerivAt.restrictScalars ℝ)
  have dX (z : ℂ) (hz : z∉L.lattice) : HasFDerivAt (fun w => X w j) (realCoefficientDerivative (f z)) z := by
    dsimp [f]
    rw [puncturedImmersionCoefficient_eq hz]
    exact scalarComplexCoefficient_hasFDerivAt ((hX.harmonic z hz j).1.differentiableAt two_ne_zero)
  obtain ⟨b,eq⟩ := L.isClosed_lattice.isOpen_compl.exists_eq_add_of_fderiv_eq
    (marked_torus_lattice_complement_connected L).isPreconnected
    (fun z hz => (dX z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (dRe z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(dX z hz).fderiv,(dRe z hz).fderiv])
  exact ⟨fun z => F z+(b:ℂ),fun z hz => ⟨(dF z hz).add_const _,(eq hz).symm⟩⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.TwoAxisHarmonicConformalImmersion.complex_coordinate_primitive
