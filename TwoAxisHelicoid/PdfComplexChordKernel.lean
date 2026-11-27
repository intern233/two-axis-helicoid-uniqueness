import TwoAxisHelicoid.PdfComplexChordFrame

namespace TwoAxisHelicoid.PdfVertical
open Complex

def complexChordValue (terms : ℕ) (par : ChordParams) (f : ComplexChordFrame) : CGrid :=
  let one := CGrid.ofInt 1
  let two := Grid.ofInt 2
  let A := f.x.scale par.q
  let B := f.reciprocal.scale par.q
  let C := f.x.scale (par.q.mul par.r)
  let D := f.reciprocal.scale par.beta.neg
  let prod := fun seed => truncatedChordProduct terms false par.q seed
  let euler := fun seed => truncatedChordProduct terms true par.q seed
  let ratio := ((one.sub (f.x.scale par.r)).mul ((prod C).mul (prod D))).div ((prod A).mul (prod B))
  let slope := (euler A).sub (euler B)
  let phase := ((f.u.rot.sub (slope.scale two)).scale par.kappa).exp
  (((par.normal.mul f.x).mul (ratio.mul ratio)).mul phase).scale par.coeff

theorem complexChordValue_sound (N : ℕ) {par : ChordParams} {t a : ℝ} (data : par.Sound t a)
    {frame : ComplexChordFrame} {z : ℂ} (f : frame.Sound t z) (ht : 0<t)
    (regular : frame.regular par=true) :
    (complexChordValue N par frame).Contains (jacobiChordKernel t a z) ∧ DifferentiableAt ℂ (jacobiChordKernel t a) z := by
  let u := jacobiChordPoint t z
  let x := jacobiChordX u
  let Q := jacobiNome (1/t)
  let r := (dualProductR t a:ℂ)
  let X := frame.x
  let IX := frame.reciprocal
  let U := frame.u
  have uOk : U.Contains u := f.1
  have xOk : X.Contains x := f.2.1
  have invOk : IX.Contains x⁻¹ := f.2.2.1
  have oneC : (CGrid.ofInt 1).Contains 1 := by simpa only [Int.cast_one] using CGrid.contains_ofInt 1
  have twoR : (Grid.ofInt 2).Contains 2 := by simpa only [Int.cast_ofNat] using Grid.contains_int 2
  have qEq : ((-(leftNome t)^2:ℝ):ℂ)=Q := by simpa only [Q,Complex.ofReal_neg] using (jacobiNome_inverse_eq_leftNome ht).symm
  have negB : ((-Real.exp (-dualProductKappa t a):ℝ):ℂ)=Q/r := by
    rw [dual_q_div_r]
    push_cast
    rfl
  let A := X.scale par.q
  let B := IX.scale par.q
  let C := X.scale (par.q.mul par.r)
  let D := IX.scale par.beta.neg
  have hA : A.Contains (Q*x) := qEq ▸ CGrid.contains_scale data.q xOk
  have hB : B.Contains (Q*x⁻¹) := qEq ▸ CGrid.contains_scale data.q invOk
  have hC : C.Contains (Q*(r*x)) := by
    have v := CGrid.contains_scale (Grid.contains_mul data.q data.r) xOk
    simpa only [Complex.ofReal_mul,qEq,mul_assoc,r] using v
  have hD : D.Contains (Q*(r*x)⁻¹) := by
    have v := CGrid.contains_scale (Grid.contains_neg data.beta) invOk
    simpa only [negB,div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_comm r⁻¹ x⁻¹] using v
  have product {b : CGrid} {w : ℂ} (hb : b.Contains (Q*w)) :
      (truncatedChordProduct N false par.q b).Contains (jacobiFactorProduct Q w) := by
    rw [← qEq] at hb ⊢
    exact truncatedChordProduct_contains data.q hb false N
  have euler {b : CGrid} {w : ℂ} (hb : b.Contains (Q*w)) :
      (truncatedChordProduct N true par.q b).Contains (w*logDeriv (jacobiFactorProduct Q) w) := by
    rw [← qEq] at hb ⊢
    exact truncatedChordProduct_contains data.q hb true N
  have ratioOk := CGrid.contains_div (CGrid.contains_mul (CGrid.contains_sub oneC (CGrid.contains_scale data.r xOk))
    (CGrid.contains_mul (product hC) (product hD))) (CGrid.contains_mul (product hA) (product hB))
  have j := CGrid.contains_sub (euler hA) (euler hB)
  have phase := CGrid.contains_exp (CGrid.contains_scale data.kappa
    (CGrid.contains_sub (CGrid.contains_rot uOk) (CGrid.contains_scale twoR j)))
  have out := CGrid.contains_scale data.coeff (CGrid.contains_mul
    (CGrid.contains_mul (CGrid.contains_mul data.normal xOk) (CGrid.contains_mul ratioOk ratioOk)) phase)
  obtain ⟨den,num,up,down⟩ := ComplexChordFrame.region data ht f regular
  refine ⟨?_,jacobiChordKernel_differentiableAt ht den num up down⟩
  rw [jacobiChordKernel_eq_result ht (div_ne_zero num den) up down]
  convert out using 2 <;> first | rfl | (simp only [jacobiChordResult,Q,x,u,r,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat,mul_comm (jacobiChordPoint t z) I];ring)

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.complexChordValue_sound
