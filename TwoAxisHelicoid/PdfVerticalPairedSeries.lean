import TwoAxisHelicoid.JacobiFiniteSecond
import TwoAxisHelicoid.JacobiVerticalIdentity

namespace TwoAxisHelicoid

/-- Pair the two Jacobi fractions with a common factor before performing
interval arithmetic. The term remains accurate at the smallest PDF boxes. -/
noncomputable def pairedVerticalTerm (q E : ℝ) (j : ℕ) : ℝ :=
  let p := (-q^2)^j
  let s := p*q
  p*((E⁻¹-E)*(1-s*s)+4*s)/((1-s*E⁻¹)*(1+s*E))^2

private theorem paired_vertical_term_eq {q E : ℝ} (qp : 0<q) (hq : q<1) (ep : 0<E)
    (down : q/E<1) (up : q*E<1) (j : ℕ) :
    q*pairedVerticalTerm q E j=jacobiFraction ((-q^2)^j*(q/E))+
      jacobiFraction ((-q^2)^j*(-q*E)) := by
  let p := (-q^2)^j
  let s := p*q
  have q2 : q^2<1 := pow_lt_one₀ qp.le hq (by decide)
  have ap : |p|≤1 := by dsimp [p];rw [abs_pow,abs_neg,abs_sq];exact pow_le_one₀ (sq_nonneg q) q2.le
  have hx : |s*E⁻¹|<1 := by
    rw [show s*E⁻¹=p*(q/E) by dsimp [s];ring,abs_mul,abs_of_pos (div_pos qp ep)]
    exact ((mul_le_mul_of_nonneg_right ap (div_pos qp ep).le).trans_eq (one_mul _)).trans_lt down
  have hy : |s*E|<1 := by
    rw [show s*E=p*(q*E) by dsimp [s];ring,abs_mul,abs_of_pos (mul_pos qp ep)]
    exact ((mul_le_mul_of_nonneg_right ap (mul_pos qp ep).le).trans_eq (one_mul _)).trans_lt up
  have nl : 1-s*E⁻¹≠0 := (sub_pos.mpr (abs_lt.mp hx).2).ne'
  have nr : 1+s*E≠0 := by linarith [(abs_lt.mp hy).1]
  change q*(p*((E⁻¹-E)*(1-s*s)+4*s)/((1-s*E⁻¹)*(1+s*E))^2)=_
  rw [show (-q^2)^j*(q/E)=s*E⁻¹ by dsimp [s,p];ring,
    show (-q^2)^j*(-q*E)= -(s*E) by dsimp [s,p];ring]
  simp only [jacobiFraction,sub_neg_eq_add]
  have combine (x y A B : ℝ) (hA : A≠0) (hB : B≠0) :
      x/A^2+y/B^2=(x*B^2+y*A^2)/(A*B)^2 := by field_simp [hA,hB]
  rw [combine _ _ _ _ nl nr,← mul_div_assoc]
  congr 1
  dsimp only [s]
  field_simp [ep.ne']; ring

private theorem normalized_jacobi_tail {Q a : ℝ} (q1 : |Q|<1) (a1 : |a|<1)
    {N : ℕ} (small : |Q|^N≤1/2) :
    |jacobiGeometricSeries Q a-jacobiFiniteSecond Q a N|≤4*|Q|^N*|a|/(1-|Q|) := by
  have pow : |Q^N*a|=|Q|^N*|a| := by rw [abs_mul,abs_pow]
  have half : |Q^N*a|≤1/2 := by
    rw [pow]
    exact (mul_le_of_le_one_right (by positivity) a1.le).trans small
  have less : |Q^N*a|<1 := by linarith
  apply (jacobiGeometricSeries_finite_error (σ:=|Q|) le_rfl q1 a1 (N:=N) le_rfl less).trans
  have d := sub_pos.mpr q1
  apply (div_le_div_iff₀ (mul_pos d (sq_pos_of_pos (sub_pos.mpr less))) d).mpr
  rw [mul_assoc 4 (|Q|^N) |a|,← pow]
  have sq : 1≤4*(1-|Q^N*a|)^2 := by nlinarith [sq_nonneg (1/2-|Q^N*a|)]
  nlinarith only [mul_le_mul_of_nonneg_left sq (mul_nonneg (abs_nonneg (Q^N*a)) d.le)]

/-- Actual vertical Jacobi expression and a rationally evaluable tail.
For the PDFs 12 terms suffice with the disjoint subintervals recorded
in the certificate. No sign assumption on the evaluated function is used. -/
theorem normalized_vertical_paired_enclosure {q E : ℝ} (qp : 0<q) (hq : q<1) (ep : 0<E)
    (down : q/E<1) (up : q*E<1) {N : ℕ} (small : (q^2)^N≤1/2) :
    |jacobiRealE (-q^2) (q/E)/q-∑ j∈Finset.range N, pairedVerticalTerm q E j|≤
      4*(E⁻¹+E)*(q^2)^N/(1-q^2) := by
  let Q := -q^2
  have qnorm : |Q|=q^2 := by rw [show Q= -q^2 from rfl,abs_neg,abs_sq]
  have q1 : |Q|<1 := qnorm ▸ pow_lt_one₀ qp.le hq (by decide)
  have ar : |q/E|=q/E := abs_of_pos (div_pos qp ep)
  have ab : |-q*E|=q*E := by rw [neg_mul,abs_neg,abs_of_pos (mul_pos qp ep)]
  have r1 := ar.trans_lt down
  have b1 := ab.trans_lt up
  have tail1 := normalized_jacobi_tail (a:=q/E) q1 r1 (qnorm ▸ small)
  have tail2 := normalized_jacobi_tail (a:=-q*E) q1 b1 (qnorm ▸ small)
  have relation : jacobiFiniteSecond Q (q/E) N+jacobiFiniteSecond Q (-q*E) N=
      q*(∑ j∈Finset.range N, pairedVerticalTerm q E j) := by
    dsimp only [jacobiFiniteSecond]
    rw [← Finset.sum_add_distrib,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => (paired_vertical_term_eq qp hq ep down up j).symm)
  have err := (abs_add_le (jacobiGeometricSeries Q (q/E)-jacobiFiniteSecond Q (q/E) N)
    (jacobiGeometricSeries Q (-q*E)-jacobiFiniteSecond Q (-q*E) N)).trans (add_le_add tail1 tail2)
  rw [ar,ab,qnorm] at err
  have E2 : jacobiRealE Q (q/E)=jacobiGeometricSeries Q (q/E)+jacobiGeometricSeries Q (-q*E) := by
    rw [jacobiRealE_two_series q1 r1]
    congr 1
    dsimp only [Q]
    field_simp [qp.ne',ep.ne']
  rw [show (jacobiGeometricSeries Q (q/E)-jacobiFiniteSecond Q (q/E) N)+
      (jacobiGeometricSeries Q (-q*E)-jacobiFiniteSecond Q (-q*E) N)=
      jacobiRealE Q (q/E)-(jacobiFiniteSecond Q (q/E) N+jacobiFiniteSecond Q (-q*E) N) by rw [E2];ring,relation] at err
  change |jacobiRealE Q (q/E)/q-_|≤_
  let S := ∑ j∈Finset.range N, pairedVerticalTerm q E j
  change |jacobiRealE Q (q/E)/q-S|≤_
  rw [show jacobiRealE Q (q/E)/q-S=(jacobiRealE Q (q/E)-q*S)/q by field_simp [qp.ne'],
    abs_div,abs_of_pos qp]
  apply (div_le_iff₀ qp).mpr
  calc _ ≤ _ := err
       _ = _ := by ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.normalized_vertical_paired_enclosure

