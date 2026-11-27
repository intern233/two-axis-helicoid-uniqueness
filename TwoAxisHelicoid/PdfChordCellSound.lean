import TwoAxisHelicoid.PdfChordParameterSound
import TwoAxisHelicoid.PdfRealChordCoordinates

namespace TwoAxisHelicoid.PdfVertical
open Complex

/-- Pointwise enclosure on the actual Jacobi chord. The two Möbius
coordinates use the unit circle identity before interval evaluation. -/
theorem chordCellValue_sound {par : ChordParams} {t a : ℝ} (data : par.Sound t a)
    {S : Grid} {s : ℝ} (hs : S.Contains s) (ht : 0<t) (hu : t≤7/5) :
    (chordCellValue par S).Contains (jacobiChordKernel t a (s:ℂ)) := by
  let h := leftChordH (leftNome t)
  let k := leftChordK (leftNome t)
  let y := k*s
  let u := jacobiChordPoint t (s:ℂ)
  let x := jacobiChordX u
  let Q := jacobiNome (1/t)
  let r := (dualProductR t a:ℂ)
  let one := Grid.ofInt 1
  let two := Grid.ofInt 2
  have oneR : one.Contains 1 := by simpa only [Int.cast_one] using Grid.contains_int 1
  have twoR : two.Contains 2 := by simpa only [Int.cast_ofNat] using Grid.contains_int 2
  have oneC : (CGrid.ofInt 1).Contains 1 := by simpa only [Int.cast_one] using CGrid.contains_ofInt 1
  let Y := par.k.mul S
  let U : CGrid := ⟨par.h,Y⟩
  have yu : Y.Contains y := Grid.contains_mul data.k hs
  have ueq : u=(⟨h,y⟩:ℂ) := by
    apply Complex.ext <;> simp [u,jacobiChordPoint,h,k,y]
  have uOk : U.Contains u := by rw [ueq];exact ⟨data.h,yu⟩
  let n := ((par.k.squared.mul (one.sub S)).mul (one.add S)).neg
  let d := par.h.squared.add (Y.sub one).squared
  let b := par.h.squared.add (Y.add one).squared
  let X : CGrid := ⟨n.divPos d,(two.mul par.h).divPos d⟩
  let IX : CGrid := ⟨n.divPos b,(two.mul par.h).neg.divPos b⟩
  have nOk := Grid.contains_neg (Grid.contains_mul (Grid.contains_mul (Grid.contains_squared data.k)
    (Grid.contains_sub oneR hs)) (Grid.contains_add oneR hs))
  have dOk := Grid.contains_add (Grid.contains_squared data.h) (Grid.contains_squared (Grid.contains_sub yu oneR))
  have bOk := Grid.contains_add (Grid.contains_squared data.h) (Grid.contains_squared (Grid.contains_add yu oneR))
  have co := real_chord_coordinates (leftChordH_sq_add_K_sq (leftNome t)) s
  have xOk : X.Contains x := by
    change X.Contains (jacobiChordX u)
    rw [ueq,co.1]
    exact ⟨Grid.contains_div nOk dOk,Grid.contains_div (Grid.contains_mul twoR data.h) dOk⟩
  have invOk : IX.Contains x⁻¹ := by
    change IX.Contains (jacobiChordX u)⁻¹
    rw [ueq,co.2]
    exact ⟨Grid.contains_div nOk bOk,by
      simpa only [neg_mul] using Grid.contains_div (Grid.contains_neg (Grid.contains_mul twoR data.h)) bOk⟩
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
      (chordEulerProduct false par.q b).Contains (jacobiFactorProduct Q w) := by
    rw [← qEq] at hb ⊢
    exact chordEulerProduct_contains data.q hb false
  have euler {b : CGrid} {w : ℂ} (hb : b.Contains (Q*w)) :
      (chordEulerProduct true par.q b).Contains (w*logDeriv (jacobiFactorProduct Q) w) := by
    rw [← qEq] at hb ⊢
    exact chordEulerProduct_contains data.q hb true
  have f := CGrid.contains_div (CGrid.contains_mul (CGrid.contains_sub oneC (CGrid.contains_scale data.r xOk))
    (CGrid.contains_mul (product hC) (product hD))) (CGrid.contains_mul (product hA) (product hB))
  have j := CGrid.contains_sub (euler hA) (euler hB)
  have phase := CGrid.contains_exp (CGrid.contains_scale data.kappa
    (CGrid.contains_sub (CGrid.contains_rot uOk) (CGrid.contains_scale twoR j)))
  have out := CGrid.contains_scale data.coeff (CGrid.contains_mul
    (CGrid.contains_mul (CGrid.contains_mul data.normal xOk) (CGrid.contains_mul f f)) phase)
  obtain ⟨nz,up,down⟩ := real_chord_product_region ht hu s
  rw [jacobiChordKernel_eq_result ht nz up down]
  convert out using 2 <;> first | rfl | (simp only [jacobiChordResult,Q,x,u,r,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat,mul_comm (jacobiChordPoint t (s:ℂ)) I];ring)

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.chordCellValue_sound

