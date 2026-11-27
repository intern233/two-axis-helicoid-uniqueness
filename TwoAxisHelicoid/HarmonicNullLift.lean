import TwoAxisHelicoid.RealCoefficientSymmetry
import TwoAxisHelicoid.SymmetricNullDifferential
import TwoAxisHelicoid.PeriodTorusConjugation

namespace TwoAxisHelicoid
open Complex Set Filter InnerProductSpace
open scoped Topology ComplexConjugate

/-- Analytic and geometric properties of an actual map on the punctured
cover. No meromorphic coefficient, height zero, Gauss divisor or period
equation is included among these hypotheses. -/
structure TwoAxisHarmonicConformalImmersion (L : PeriodPair)
    (X : ℂ → Fin 3 → ℝ) : Prop where
  differentiable : ∀ z ∉ L.lattice, DifferentiableAt ℝ X z
  harmonic : ∀ z ∉ L.lattice, ∀ j, HarmonicAt (fun w => X w j) z
  conformal : ∀ z ∉ L.lattice, ConformalCoordinateDerivatives X z
  immersion : ∀ z ∉ L.lattice, Function.Injective (fderiv ℝ X z)
  periodic : ∀ z ∉ L.lattice, ∀ ω ∈ L.lattice, X (z+ω) = X z
  neg : ∀ z ∉ L.lattice, X (-z) = ![-X z 0,X z 1,-X z 2]
  conjugation : ∀ z ∉ L.lattice, X (conj z) = ![X z 0,-X z 1,-X z 2]

noncomputable def puncturedImmersionCoefficient (L : PeriodPair)
    (X : ℂ → Fin 3 → ℝ) (z : ℂ) : Fin 3 → ℂ :=
  by
    classical
    exact if z ∈ L.lattice then 0 else immersionComplexCoefficient X z

theorem puncturedImmersionCoefficient_eq {L : PeriodPair}
    {X : ℂ → Fin 3 → ℝ} {z : ℂ} (hz : z ∉ L.lattice) :
    puncturedImmersionCoefficient L X z = immersionComplexCoefficient X z := by
  simp [puncturedImmersionCoefficient,hz]

theorem puncturedImmersionCoefficient_analyticAt {L : PeriodPair}
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion L X)
    {z : ℂ} (hz : z ∉ L.lattice) (j : Fin 3) :
    AnalyticAt ℂ (fun w => puncturedImmersionCoefficient L X w j) z := by
  apply (scalarComplexCoefficient_analyticAt (hX.harmonic z hz j)).congr
  filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
  exact (congrFun (puncturedImmersionCoefficient_eq hw) j).symm

theorem puncturedImmersionCoefficient_hasFDerivAt {L : PeriodPair}
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion L X)
    {z : ℂ} (hz : z ∉ L.lattice) :
    HasFDerivAt X (nullRealDerivative (puncturedImmersionCoefficient L X z)) z := by
  rw [puncturedImmersionCoefficient_eq hz]
  exact immersionComplexCoefficient_hasFDerivAt (hX.differentiable z hz)

theorem puncturedImmersionCoefficient_periodic {L : PeriodPair}
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion L X)
    (z ω : ℂ) (hω : ω ∈ L.lattice) :
    puncturedImmersionCoefficient L X (z+ω) = puncturedImmersionCoefficient L X z := by
  have hmem : z+ω ∈ L.lattice ↔ z ∈ L.lattice := by
    constructor
    · intro h
      simpa using L.lattice.sub_mem h hω
    · intro h
      exact L.lattice.add_mem h hω
  by_cases hz : z ∈ L.lattice
  · simp [puncturedImmersionCoefficient,hz,hmem.mpr hz]
  · have hzw : z+ω ∉ L.lattice := fun h => hz (hmem.mp h)
    rw [puncturedImmersionCoefficient_eq hz,puncturedImmersionCoefficient_eq hzw]
    ext j
    apply real_primitive_translation_coefficient
      (scalarComplexCoefficient_hasFDerivAt ((hX.harmonic z hz j).1.differentiableAt two_ne_zero))
      (scalarComplexCoefficient_hasFDerivAt ((hX.harmonic (z+ω) hzw j).1.differentiableAt two_ne_zero))
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact congrFun (hX.periodic w hw ω hω) j

theorem puncturedImmersionCoefficient_neg {L : PeriodPair}
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion L X)
    {z : ℂ} (hz : z ∉ L.lattice) :
    puncturedImmersionCoefficient L X (-z) =
      ![puncturedImmersionCoefficient L X z 0,
        -puncturedImmersionCoefficient L X z 1,
        puncturedImmersionCoefficient L X z 2] := by
  have hn : -z ∉ L.lattice := by simpa using hz
  rw [puncturedImmersionCoefficient_eq hz,puncturedImmersionCoefficient_eq hn]
  have he (j : Fin 3) :
      scalarComplexCoefficient (fun w => X w j) (-z) =
        -((![-1,1,-1] : Fin 3 → ℝ) j : ℂ)*scalarComplexCoefficient (fun w => X w j) z := by
    apply real_primitive_negation_coefficient
      ((![-1,1,-1] : Fin 3 → ℝ) j)
      (scalarComplexCoefficient_hasFDerivAt ((hX.harmonic z hz j).1.differentiableAt two_ne_zero))
      (scalarComplexCoefficient_hasFDerivAt ((hX.harmonic (-z) hn j).1.differentiableAt two_ne_zero))
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    have h := congrFun (hX.neg w hw) j
    fin_cases j <;> simpa using h
  ext j
  have hj := he j
  fin_cases j <;> simpa [immersionComplexCoefficient] using hj

theorem puncturedImmersionCoefficient_conjugation {L : PeriodPair}
    (hL : ConjugationInvariantLattice L)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion L X)
    {z : ℂ} (hz : z ∉ L.lattice) :
    puncturedImmersionCoefficient L X (conj z) =
      ![conj (puncturedImmersionCoefficient L X z 0),
        -conj (puncturedImmersionCoefficient L X z 1),
        -conj (puncturedImmersionCoefficient L X z 2)] := by
  have hc : conj z ∉ L.lattice := by
    intro h
    exact hz (by simpa using hL (conj z) h)
  rw [puncturedImmersionCoefficient_eq hz,puncturedImmersionCoefficient_eq hc]
  have he (j : Fin 3) :
      scalarComplexCoefficient (fun w => X w j) (conj z) =
        ((![1,-1,-1] : Fin 3 → ℝ) j : ℂ)*conj (scalarComplexCoefficient (fun w => X w j) z) := by
    apply real_primitive_conjugation_coefficient
      ((![1,-1,-1] : Fin 3 → ℝ) j)
      (scalarComplexCoefficient_hasFDerivAt ((hX.harmonic z hz j).1.differentiableAt two_ne_zero))
      (scalarComplexCoefficient_hasFDerivAt ((hX.harmonic (conj z) hc j).1.differentiableAt two_ne_zero))
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    have h := congrFun (hX.conjugation w hw) j
    fin_cases j <;> simpa using h
  ext j
  have hj := he j
  fin_cases j <;> simpa [immersionComplexCoefficient] using hj

theorem TwoAxisHarmonicConformalImmersion.null_differential {L : PeriodPair}
    (hL : ConjugationInvariantLattice L)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion L X) :
    TwoAxisNullDifferential L (puncturedImmersionCoefficient L X) where
  periodic := puncturedImmersionCoefficient_periodic hX
  null := fun z hz => by
    rw [puncturedImmersionCoefficient_eq hz]
    exact immersionComplexCoefficient_null (hX.conformal z hz)
  regular := fun z hz => by
    rw [puncturedImmersionCoefficient_eq hz]
    exact immersionComplexCoefficient_regular (hX.differentiable z hz) (hX.immersion z hz)
  neg := fun _ hz => puncturedImmersionCoefficient_neg hX hz
  conjugation := fun _ hz => puncturedImmersionCoefficient_conjugation hL hX hz

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.TwoAxisHarmonicConformalImmersion.null_differential
