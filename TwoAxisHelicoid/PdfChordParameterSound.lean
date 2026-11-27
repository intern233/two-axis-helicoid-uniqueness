import TwoAxisHelicoid.PdfChordProductSound
import TwoAxisHelicoid.PdfComplexGridExp
import TwoAxisHelicoid.JacobiChordExpressions
import TwoAxisHelicoid.LeftProductError

namespace TwoAxisHelicoid.PdfVertical
open Complex

structure ChordParams.Sound (p : ChordParams) (t a : ℝ) : Prop where
  q : p.q.Contains (-(leftNome t)^2)
  kappa : p.kappa.Contains (dualProductKappa t a)
  r : p.r.Contains (dualProductR t a)
  beta : p.beta.Contains (Real.exp (-dualProductKappa t a))
  h : p.h.Contains (leftChordH (leftNome t))
  k : p.k.Contains (leftChordK (leftNome t))
  coeff : p.coeff.Contains ((-Real.pi/t/2)*leftChordK (leftNome t))
  normal : p.normal.Contains (jacobiNormalization (jacobiNome (1/t)) (dualProductR t a))

private theorem exp_by_half {a : Grid} {x : ℝ} (h : a.Contains x) :
    (a.divNat 2).exp.squared.Contains (Real.exp x) := by
  have e := Grid.contains_squared (Grid.contains_exp (Grid.contains_divNat (n:=2) h))
  rw [← Real.exp_nat_mul] at e
  convert e using 2
  push_cast
  ring

theorem chordParams_sound {T A : Grid} {t a : ℝ} (hT : T.Contains t) (hA : A.Contains a)
    (ht : 0<t) : (chordParams T A).Sound t a := by
  let one := Grid.ofInt 1
  let two := Grid.ofInt 2
  let piT := Grid.pi.divPos T
  let q0 := (piT.neg.divNat 2).exp
  let q := q0.squared.neg
  let K := piT.mul (one.sub A)
  let r := ((piT.neg.mul A).divNat 2).exp.squared
  let beta := (K.neg.divNat 2).exp.squared
  let qr := -(leftNome t)^2
  let R := dualProductR t a
  have oneOk : one.Contains 1 := by simpa only [Int.cast_one] using Grid.contains_int 1
  have twoOk : two.Contains 2 := by simpa only [Int.cast_ofNat] using Grid.contains_int 2
  have piOk := Grid.contains_div Grid.contains_pi hT
  have piNeg : piT.neg.Contains (-Real.pi/t) := by simpa only [neg_div] using Grid.contains_neg piOk
  have q0Ok : q0.Contains (leftNome t) := by
    change q0.Contains (Real.exp (-Real.pi/(2*t)))
    rw [show -Real.pi/(2*t)=(-Real.pi/t)/(2:ℕ) by push_cast;ring]
    exact Grid.contains_exp (Grid.contains_divNat piNeg)
  have qOk : q.Contains qr := Grid.contains_neg (Grid.contains_squared q0Ok)
  have rOk : r.Contains R := by
    change r.Contains (Real.exp (-Real.pi*a/t))
    rw [show -Real.pi*a/t=(-Real.pi/t)*a by ring]
    exact exp_by_half (Grid.contains_mul piNeg hA)
  have kOk : K.Contains (dualProductKappa t a) := by
    rw [dualProductKappa,show Real.pi*(1-a)/t=Real.pi/t*(1-a) by ring]
    exact Grid.contains_mul piOk (Grid.contains_sub oneOk hA)
  have bOk : beta.Contains (Real.exp (-dualProductKappa t a)) := exp_by_half (Grid.contains_neg kOk)
  have hOk := Grid.contains_div (Grid.contains_mul twoOk q0Ok) (Grid.contains_add oneOk (Grid.contains_squared q0Ok))
  have cOk := Grid.contains_div (Grid.contains_sub oneOk (Grid.contains_squared q0Ok))
    (Grid.contains_add oneOk (Grid.contains_squared q0Ok))
  refine ⟨qOk,kOk,rOk,bOk,hOk,cOk,Grid.contains_mul (Grid.contains_divNat piNeg) cOk,?_⟩
  have Q : (qr:ℂ)=jacobiNome (1/t) := by simpa only [qr,Complex.ofReal_neg] using (jacobiNome_inverse_eq_leftNome ht).symm
  have p0 := chordEulerProduct_contains (x:=1) qOk (by
    simpa only [mul_one] using CGrid.contains_real qOk) false
  have pr := chordEulerProduct_contains (x:=(R:ℂ)) qOk (by
    simpa only [Complex.ofReal_mul] using CGrid.contains_real (Grid.contains_mul qOk rOk)) false
  have negBeta : (qr:ℂ)*(R:ℂ)⁻¹=((-Real.exp (-dualProductKappa t a):ℝ):ℂ) := by
    rw [Q,← div_eq_mul_inv,dual_q_div_r]
    push_cast
    rfl
  have pi := chordEulerProduct_contains (x:=(R:ℂ)⁻¹) qOk (by
    rw [negBeta]
    exact CGrid.contains_real (Grid.contains_neg bOk)) false
  change (chordEulerProduct false q (CGrid.real q)).Contains (jacobiFactorProduct (qr:ℂ) 1) at p0
  change (chordEulerProduct false q (CGrid.real (q.mul r))).Contains (jacobiFactorProduct (qr:ℂ) R) at pr
  change (chordEulerProduct false q (CGrid.real beta.neg)).Contains (jacobiFactorProduct (qr:ℂ) (R:ℂ)⁻¹) at pi
  have num := CGrid.contains_mul p0 p0
  have dx := CGrid.contains_scale (Grid.contains_sub oneOk rOk) (CGrid.contains_mul pr pi)
  have quotient := CGrid.contains_div (CGrid.contains_mul num num) (CGrid.contains_mul dx dx)
  rw [Q] at quotient
  convert quotient using 1 <;> first | rfl | (unfold jacobiNormalization jacobiPairProduct; push_cast; ring)

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.chordParams_sound

