import TwoAxisHelicoid.ActualQuarterHeightSlices
import TwoAxisHelicoid.ExplicitMarkedReflections
import TwoAxisHelicoid.HeightEndAxisCenter
import TwoAxisHelicoid.GaussPeriodicity

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- The vertical half turn doubles the quarter across its axis. It
preserves physical height and changes the real Gauss component by a
strictly positive reciprocal-square factor. -/
theorem quarter_gauss_vertical_mirror {t a : ℝ} (ht : 0<t)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → X (z+ω)=X z) {z : ℂ} (hy : z.im∈Ioo (0:ℝ) t) :
    let w : ℂ := 2-conj z
    let H := actualComplexHeight t a 1 ht
    let G := thetaGauss t a 1
    (H w).re=(H z).re ∧ ((G w).re<0 ↔ (G z).re<0) := by
  intro w H G
  let L := rhombicPeriodPair t ht
  have equal : w= -conj z+2 := by dsimp [w]; ring
  have off := rhombic_horizontal_strip_not_mem (z:=z) ht hy
  have ow : w∉L.lattice := rhombic_horizontal_strip_not_mem ht (by change w.im∈Ioo 0 t; simpa [w] using hy)
  have oc : conj z∉L.lattice := fun m => off (by simpa using rhombic_conj_mem ht m)
  have hm : z-a∉L.lattice := rhombic_horizontal_strip_not_mem ht (by change (z-a).im∈Ioo 0 t; simpa using hy)
  have hp : z+a∉L.lattice := rhombic_horizontal_strip_not_mem ht (by change (z+a).im∈Ioo 0 t; simpa using hy)
  have cm : conj z-a∉L.lattice := fun m => hm (by simpa using rhombic_conj_mem ht m)
  have cp : conj z+a∉L.lattice := fun m => hp (by simpa using rhombic_conj_mem ht m)
  have n := congrFun (explicit_centered_primitive_reflections ht d per _ oc).1 2
  have c := congrFun (explicit_centered_primitive_reflections ht d per z off).2 2
  change X (-conj z) 2-X 1 2= -(X (conj z) 2-X 1 2) at n
  change X (conj z) 2-X 1 2= -(X z 2-X 1 2) at c
  constructor
  · rw [← actual_complex_height_centered_primitive ht d ow,← actual_complex_height_centered_primitive ht d off,
      equal,per (-conj z) 2 L.ω₁_mem_lattice,n,c,neg_neg]
  · have gn : G z≠0 := thetaGauss_ne_zero ht a 1 hm hp
    have cn : conj (G z)≠0 := (map_ne_zero (starRingEnd ℂ)).mpr gn
    have product := thetaGauss_neg_product ht a 1 cm cp
    rw [thetaGauss_conj] at product
    have id : G (-conj z)=(conj (G z))⁻¹ := by
      rw [← one_div]
      apply (eq_div_iff cn).mpr
      change G (-conj z)*(-conj (G z))= -1 at product
      linear_combination -product
    rw [equal,show G (-conj z+2)=G (-conj z) from thetaGauss_period_two t a 1 _,id,inv_re,conj_re,normSq_conj]
    rw [div_lt_iff₀ (normSq_pos.mpr gn),zero_mul]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarter_gauss_vertical_mirror
