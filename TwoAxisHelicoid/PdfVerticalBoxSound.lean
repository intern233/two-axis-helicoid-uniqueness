import TwoAxisHelicoid.PdfVerticalBoxCheck
import TwoAxisHelicoid.PdfVerticalPairedSeries
import TwoAxisHelicoid.PdfVerticalGridExp

namespace TwoAxisHelicoid.PdfVertical

open Grid

private theorem grid_one : (ofInt 1).Contains 1 := by simpa using contains_int 1
private theorem grid_two : (ofInt 2).Contains 2 := by simpa using contains_int 2
private theorem grid_four : (ofInt 4).Contains 4 := by simpa using contains_int 4

theorem pairedBoxTerm_contains {u v e p : Grid} {q E : ℝ} {j : ℕ}
    (hu : u.Contains q) (hv : v.Contains E) (he : e.Contains E⁻¹)
    (hp : p.Contains ((-q^2)^j)) :
    (pairedBoxTerm u v e p).Contains (pairedVerticalTerm q E j) := by
  let hs := contains_mul hp hu
  let hd := contains_mul (contains_sub grid_one (contains_mul hs he))
    (contains_add grid_one (contains_mul hs hv))
  let ht := contains_add (contains_mul (contains_sub he hv)
    (contains_sub grid_one (contains_mul hs hs))) (contains_mul grid_four hs)
  simpa only [pairedBoxTerm,pairedVerticalTerm,pow_two] using
    contains_div (contains_mul hp ht) (contains_mul hd hd)

theorem pairedBoxSum_contains {u v e Q : Grid} {q E : ℝ}
    (hu : u.Contains q) (hv : v.Contains E) (he : e.Contains E⁻¹)
    (hQ : Q.Contains (-q^2)) (n : ℕ) :
    (pairedBoxSum u v e Q n).1.Contains ((-q^2)^n) ∧
    (pairedBoxSum u v e Q n).2.Contains (∑ j∈Finset.range n, pairedVerticalTerm q E j) := by
  induction n with
  | zero => simpa [pairedBoxSum] using And.intro grid_one (contains_int 0)
  | succ n ih =>
    simpa only [pairedBoxSum,pow_succ,Finset.sum_range_succ] using
      And.intro (contains_mul ih.1 hQ)
        (contains_add ih.2 (pairedBoxTerm_contains hu hv he ih.1))

theorem pairedBoxWithTail_contains {u v : Grid} {q E : ℝ}
    (hu : u.Contains q) (hv : v.Contains E) (qp : 0<q) (hq : q<1) (ep : 0<E)
    (down : q/E<1) (up : q*E<1) :
    (pairedBoxWithTail u v).Contains (jacobiRealE (-q^2) (q/E)/q) := by
  let e := (ofInt 1).divPos v
  let Q := (u.mul u).neg
  let P := pairedBoxSum u v e Q 12
  let T := (((ofInt 4).mul (e.add v)).mul P.1).divPos ((ofInt 1).add Q)
  have he : e.Contains E⁻¹ := by simpa only [one_div] using contains_div grid_one hv
  have hQ : Q.Contains (-q^2) := by simpa only [pow_two] using contains_neg (contains_mul hu hu)
  obtain ⟨hp,hs⟩ := pairedBoxSum_contains hu hv he hQ 12
  change P.1.Contains ((-q^2)^12) at hp
  rw [show (-q^2)^12=(q^2)^12 by ring] at hp
  have hT : T.Contains (4*(E⁻¹+E)*(q^2)^12/(1-q^2)) := by
    simpa only [sub_eq_add_neg] using
      contains_div (contains_mul (contains_mul grid_four (contains_add he hv)) hp) (contains_add grid_one hQ)
  intro valid
  change ((P.2.ok && T.ok && P.1.ok) && decide (2*P.1.hi≤denom))=true at valid
  simp only [Bool.and_eq_true,decide_eq_true_eq] at valid
  obtain ⟨⟨⟨sok,tok⟩,pok⟩,pmax⟩ := valid
  have bound : (2:ℝ)*(P.1.hi:ℝ)≤(denom:ℝ) := by exact_mod_cast pmax
  have sm : (q^2)^12≤1/2 := by
    apply (le_of_mul_le_mul_left _ real_denom_pos)
    linarith [(hp pok).2]
  have err := abs_le.mp (normalized_vertical_paired_enclosure qp hq ep down up sm)
  have low := mul_le_mul_of_nonneg_left err.1 real_denom_pos.le
  have high := mul_le_mul_of_nonneg_left err.2 real_denom_pos.le
  obtain ⟨slo,shi⟩ := hs sok
  have thi := (hT tok).2
  change ((P.2.lo-T.hi:ℤ):ℝ)≤_ ∧ _≤((P.2.hi+T.hi:ℤ):ℝ)
  push_cast
  constructor <;> linarith only [low,high,slo,shi,thi]

/-- The columns below 3/5 report the normalized vertical function; above the
switch, the columns report the real vertical period itself. -/
noncomputable def reportedVertical (dual : Bool) (t a : ℝ) : ℝ :=
  if dual then (thetaG t a).re/(Real.pi^2*Real.exp (-Real.pi/(2*t))/t^2) else (thetaG t a).re

theorem verticalValueBox_contains {T A : Grid} {t a : ℝ} (hT : T.Contains t) (hA : A.Contains a)
    (ht : 0<t) (ha : 0<a) (hb : a<1) (dual : Bool) :
    (verticalValueBox dual T A).Contains (reportedVertical dual t a) := by
  let q := Real.exp (-Real.pi/(2*t))
  let E := Real.exp (Real.pi*(a-1/2)/t)
  have qp : 0<q := Real.exp_pos _
  have ep : 0<E := Real.exp_pos _
  have hq : q<1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) (by positivity))
  have r : q/E=Real.exp (-Real.pi*a/t) := by dsimp [q,E];rw [← Real.exp_sub];congr 1;ring
  have q2 : q^2=Real.exp (-Real.pi/t) := by dsimp [q];rw [← Real.exp_nat_mul];congr 1;push_cast;ring
  have down : q/E<1 := by rw [r,Real.exp_lt_one_iff];exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) ha) ht
  have up : q*E<1 := by
    dsimp [q,E];rw [← Real.exp_add,Real.exp_lt_one_iff]
    rw [show -Real.pi/(2*t)+Real.pi*(a-1/2)/t=Real.pi*(a-1)/t by ring]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg Real.pi_pos (sub_neg.mpr hb)) ht
  have half : (ofRats (1/2) (1/2)).Contains (1/2) := contains_rats (by norm_num) (by norm_num)
  let u := (Grid.pi.neg.divPos ((ofInt 2).mul T)).exp
  let v := ((Grid.pi.mul (A.sub (ofRats (1/2) (1/2)))).divPos T).exp
  have hu : u.Contains q := contains_exp (contains_div (contains_neg contains_pi) (contains_mul grid_two hT))
  have hv : v.Contains E := contains_exp (contains_div (contains_mul contains_pi (contains_sub hA half)) hT)
  have val := pairedBoxWithTail_contains hu hv qp hq ep down up
  have identity := thetaG_re_eq_jacobiRealE ht ha hb
  rw [← q2,← r] at identity
  cases dual
  · change ((((Grid.pi.mul Grid.pi).mul u).divPos (T.mul T)).mul (pairedBoxWithTail u v)).Contains (thetaG t a).re
    rw [identity,show Real.pi^2/t^2*jacobiRealE (-q^2) (q/E)=
        (Real.pi*Real.pi*q/(t*t))*(jacobiRealE (-q^2) (q/E)/q) by field_simp [ht.ne',qp.ne']]
    exact contains_mul (contains_div (contains_mul (contains_mul contains_pi contains_pi) hu) (contains_mul hT hT)) val
  · change (pairedBoxWithTail u v).Contains ((thetaG t a).re/(Real.pi^2*q/t^2))
    rw [identity,show Real.pi^2/t^2*jacobiRealE (-q^2) (q/E)/(Real.pi^2*q/t^2)=
        jacobiRealE (-q^2) (q/E)/q by field_simp [ht.ne',qp.ne',Real.pi_ne_zero]]
    exact val

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.verticalValueBox_contains
