import TwoAxisHelicoid.NullGaussLocal
import TwoAxisHelicoid.SymmetricNullDifferential

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

theorem null_horizontal_minus_neg {L : PeriodPair} {p : ℂ → Fin 3 → ℂ}
    (hp : TwoAxisNullDifferential L p) {z : ℂ} (hz : z ∉ L.lattice) :
    nullHorizontalMinus (p (-z)) = nullHorizontalPlus (p z) := by
  rw [hp.neg z hz]
  simp [nullHorizontalMinus,nullHorizontalPlus]

theorem null_horizontal_plus_neg {L : PeriodPair} {p : ℂ → Fin 3 → ℂ}
    (hp : TwoAxisNullDifferential L p) {z : ℂ} (hz : z ∉ L.lattice) :
    nullHorizontalPlus (p (-z)) = nullHorizontalMinus (p z) := by
  rw [hp.neg z hz]
  simp [nullHorizontalMinus,nullHorizontalPlus,sub_eq_add_neg]

theorem null_gauss_periodic {L : PeriodPair} {p : ℂ → Fin 3 → ℂ}
    (hp : TwoAxisNullDifferential L p) (z ω : ℂ) (hω : ω ∈ L.lattice) :
    nullGauss (p (z+ω)) = nullGauss (p z) := by rw [hp.periodic z ω hω]

theorem null_gauss_conjugation {L : PeriodPair} {p : ℂ → Fin 3 → ℂ}
    (hp : TwoAxisNullDifferential L p) {z : ℂ} (hz : z ∉ L.lattice) :
    nullGauss (p (conj z)) = -conj (nullGauss (p z)) := by
  rw [hp.conjugation z hz]
  simp [nullGauss,nullHorizontalMinus,map_div₀,map_sub,map_mul,neg_div]

theorem null_gauss_neg_product {L : PeriodPair} {p : ℂ → Fin 3 → ℂ}
    (hp : TwoAxisNullDifferential L p) {z : ℂ} (hz : z ∉ L.lattice)
    (h2 : p z 2 ≠ 0) : nullGauss (p (-z))*nullGauss (p z) = -1 := by
  have he : nullGauss (p (-z)) = p z 2/nullHorizontalPlus (p z) := by
    unfold nullGauss
    rw [null_horizontal_minus_neg hp hz,hp.neg z hz]
    rfl
  rw [he]
  exact null_gauss_opposite_product (hp.null z hz) h2

noncomputable def flipNullY (p : Fin 3 → ℂ) : Fin 3 → ℂ := ![p 0,-p 1,p 2]

theorem flipNullY_null {p : Fin 3 → ℂ} (hp : ComplexNull p) : ComplexNull (flipNullY p) := by
  simpa [ComplexNull,flipNullY] using hp

theorem flipNullY_regular {p : Fin 3 → ℂ} (hp : p ≠ 0) : flipNullY p ≠ 0 := by
  intro he
  apply hp
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  funext j
  fin_cases j
  · simpa [flipNullY] using h0
  · simpa [flipNullY] using h1
  · simpa [flipNullY] using h2

theorem flipNullY_two_axis {L : PeriodPair} {p : ℂ → Fin 3 → ℂ}
    (hp : TwoAxisNullDifferential L p) : TwoAxisNullDifferential L (fun z => flipNullY (p z)) where
  periodic := by intro z ω hω; rw [hp.periodic z ω hω]
  null := fun z hz => flipNullY_null (hp.null z hz)
  regular := fun z hz => flipNullY_regular (hp.regular z hz)
  neg := by
    intro z hz
    rw [hp.neg z hz]
    ext j
    fin_cases j <;> simp [flipNullY]
  conjugation := by
    intro z hz
    rw [hp.conjugation z hz]
    ext j
    fin_cases j <;> simp [flipNullY]

theorem flipNullY_minus (p : Fin 3 → ℂ) :
    nullHorizontalMinus (flipNullY p) = nullHorizontalPlus p := by
  simp [flipNullY,nullHorizontalMinus,nullHorizontalPlus]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.null_gauss_conjugation
#print axioms TwoAxisHelicoid.flipNullY_two_axis
