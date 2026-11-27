import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.DerivativeExpressions

namespace TwoAxisHelicoid.PdfVertical
open Complex
attribute [local irreducible] thetaJet

private noncomputable def heatRealJet (t : ℝ) (j : ℕ) (x : ℝ) := (thetaJet t j (x:ℂ)).re

private theorem heatRealJet_cast (t : ℝ) (j : ℕ) (x : ℝ) :
    ((heatRealJet t j x:ℝ):ℂ)=thetaJet t j (x:ℂ) := by
  apply Complex.ext
  · rfl
  · exact (thetaJet_real t j x).symm

noncomputable def heatRealRatio (t a : ℝ) (j : ℕ) :=
  heatRealJet t j (Real.pi*a/2)/heatRealJet t 0 (Real.pi*a/2)

theorem heatRealRatio_cast (t a : ℝ) (j : ℕ) :
    ((heatRealRatio t a j:ℝ):ℂ)=thetaQuotient t j (Real.pi*a/2) := by
  simp only [heatRealRatio,Complex.ofReal_div,heatRealJet_cast,thetaQuotient,
    Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat]

noncomputable def heatZeroRatio (t : ℝ) := heatRealJet t 3 0/heatRealJet t 1 0

theorem heatZeroRatio_cast (t : ℝ) : ((heatZeroRatio t:ℝ):ℂ)=thetaJet t 3 0/thetaJet t 1 0 := by
  simp only [heatZeroRatio,Complex.ofReal_div,heatRealJet_cast,Complex.ofReal_zero]

private noncomputable def gaValue (pi r v₂ v₃ : ℝ) :=
  (pi*pi*pi/8)*(3*r*v₂-2*r*r*r-v₃)

private noncomputable def gtValue (pi t r v₂ v₃ v₄ : ℝ) :=
  (pi*pi*pi/32)*(2*r*(v₃-r*v₂)-(v₄-v₂^2))+pi/t^2

private theorem gaValue_actual (t a : ℝ) :
    gaValue Real.pi (heatRealRatio t a 1) (heatRealRatio t a 2) (heatRealRatio t a 3)=(thetaGa t a).re := by
  have h : ((gaValue Real.pi (heatRealRatio t a 1) (heatRealRatio t a 2) (heatRealRatio t a 3):ℝ):ℂ)=thetaGa t a := by
    unfold gaValue thetaGa
    push_cast
    simp only [heatRealRatio_cast]
    ring
  exact congrArg Complex.re h

private theorem gtValue_actual (t a : ℝ) :
    gtValue Real.pi t (heatRealRatio t a 1) (heatRealRatio t a 2) (heatRealRatio t a 3) (heatRealRatio t a 4)=(thetaGt t a).re := by
  have h : ((gtValue Real.pi t (heatRealRatio t a 1) (heatRealRatio t a 2) (heatRealRatio t a 3) (heatRealRatio t a 4):ℝ):ℂ)=thetaGt t a := by
    unfold gtValue thetaGt
    push_cast
    simp only [heatRealRatio_cast]
    ring
  exact congrArg Complex.re h

private def gaGrid (r v₂ v₃ : Grid) : Grid :=
  let pi₃ := (Grid.pi.mul Grid.pi).mul Grid.pi
  (pi₃.divNat 8).mul (((((Grid.ofInt 3).mul r).mul v₂).sub (((((Grid.ofInt 2).mul r).mul r).mul r))).sub v₃)

private def gtGrid (t r v₂ v₃ v₄ : Grid) : Grid :=
  let pi₃ := (Grid.pi.mul Grid.pi).mul Grid.pi
  ((pi₃.divNat 32).mul ((((Grid.ofInt 2).mul r).mul (v₃.sub (r.mul v₂))).sub
    (v₄.sub v₂.squared))).add (Grid.pi.divPos t.squared)

private theorem gaGrid_sound {r u v : Grid} {x y z : ℝ} (hr : r.Contains x) (hu : u.Contains y) (hv : v.Contains z) :
    (gaGrid r u v).Contains (gaValue Real.pi x y z) := by
  have h₂ : (Grid.ofInt 2).Contains (2:ℝ) := by simpa using Grid.contains_int 2
  have h₃ : (Grid.ofInt 3).Contains (3:ℝ) := by simpa using Grid.contains_int 3
  exact Grid.contains_mul (Grid.contains_divNat (Grid.contains_mul (Grid.contains_mul Grid.contains_pi Grid.contains_pi) Grid.contains_pi))
    (Grid.contains_sub (Grid.contains_sub (Grid.contains_mul (Grid.contains_mul h₃ hr) hu)
      (Grid.contains_mul (Grid.contains_mul (Grid.contains_mul h₂ hr) hr) hr)) hv)

private theorem gtGrid_sound {T r u v w : Grid} {t x y z p : ℝ}
    (ht : T.Contains t) (hr : r.Contains x) (hu : u.Contains y) (hv : v.Contains z) (hw : w.Contains p) :
    (gtGrid T r u v w).Contains (gtValue Real.pi t x y z p) := by
  have h₂ : (Grid.ofInt 2).Contains (2:ℝ) := by simpa using Grid.contains_int 2
  exact Grid.contains_add (Grid.contains_mul
    (Grid.contains_divNat (Grid.contains_mul (Grid.contains_mul Grid.contains_pi Grid.contains_pi) Grid.contains_pi))
    (Grid.contains_sub (Grid.contains_mul (Grid.contains_mul h₂ hr) (Grid.contains_sub hv (Grid.contains_mul hr hu)))
      (Grid.contains_sub hw (Grid.contains_squared hu)))) (Grid.contains_div Grid.contains_pi (Grid.contains_squared ht))

structure HeatGridParameters where
  model : PrimalThetaParameters
  slope : Grid
  firstRatio : Grid
  secondRatio : Grid
  originRatio : Grid
  heatCoefficient : Grid

def heatGridParameters (T A : Grid) : HeatGridParameters :=
  let p := primalThetaParameters T A
  let J := fun j : Fin 5 => (checkedPrimalJet p.q p.aArgument j).re
  let V := fun j : Fin 5 => (J j).divPos (J 0)
  let O := fun j : Fin 5 => (checkedPrimalJet p.q (CGrid.ofInt 0) j).re
  let ga := gaGrid (V 1) (V 2) (V 3)
  let gt := gtGrid T (V 1) (V 2) (V 3) (V 4)
  ⟨p,gt.divPos ga.neg,V 1,V 2,(O 3).divPos (O 1),(p.exponent.mul Grid.pi).divNat 8⟩

def HeatGridParameters.Sound (p : HeatGridParameters) (t a : ℝ) : Prop :=
  p.model.Sound t a ∧ p.slope.Contains (-(thetaGt t a).re/(thetaGa t a).re) ∧
  p.firstRatio.Contains (heatRealRatio t a 1) ∧ p.secondRatio.Contains (heatRealRatio t a 2) ∧
  p.originRatio.Contains (heatZeroRatio t) ∧ p.heatCoefficient.Contains (Real.pi*(a-1)*Real.pi/8)

/-- All coefficients of the original heat integrand, including the
implicit branch slope, are enclosed using only real theta jets. -/
theorem heatGridParameters_sound {T A : Grid} {t a : ℝ} (hb : T.Contains t) (ab : A.Contains a) (ht : 17/20≤t) :
    (heatGridParameters T A).Sound t a := by
  let p := primalThetaParameters T A
  let J := fun j : Fin 5 => (checkedPrimalJet p.q p.aArgument j).re
  let V := fun j : Fin 5 => (J j).divPos (J 0)
  have ps : p.Sound t a := primalThetaParameters_sound hb ab ht
  have ar : p.aArgument.Contains (((Real.pi*a/2:ℝ):ℂ)) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat] using ps.2.1
  have jr (j : Fin 5) : (J j).Contains (heatRealJet t j (Real.pi*a/2)) :=
    (checkedPrimalJet_contains ps.1 ar ht j).1
  have vr (j : Fin 5) : (V j).Contains (heatRealRatio t a j) := Grid.contains_div (jr j) (jr 0)
  have zr (j : Fin 5) : (checkedPrimalJet p.q (CGrid.ofInt 0) j).re.Contains (heatRealJet t j 0) := by
    have z : (CGrid.ofInt 0).Contains ((0:ℝ):ℂ) := by simpa only [Int.cast_zero,Complex.ofReal_zero] using CGrid.contains_ofInt 0
    exact (checkedPrimalJet_contains ps.1 z ht j).1
  have ga := gaGrid_sound (vr 1) (vr 2) (vr 3)
  have gt := gtGrid_sound hb (vr 1) (vr 2) (vr 3) (vr 4)
  change (gaGrid _ _ _).Contains (gaValue _ (heatRealRatio t a 1) (heatRealRatio t a 2) (heatRealRatio t a 3)) at ga
  change (gtGrid _ _ _ _ _).Contains (gtValue _ _ (heatRealRatio t a 1) (heatRealRatio t a 2) (heatRealRatio t a 3) (heatRealRatio t a 4)) at gt
  rw [gaValue_actual] at ga
  rw [gtValue_actual] at gt
  exact ⟨ps,by simpa only [heatGridParameters,p,V,J,div_neg,neg_div] using Grid.contains_div gt (Grid.contains_neg ga),
    vr 1,vr 2,Grid.contains_div (zr 3) (zr 1),Grid.contains_divNat (Grid.contains_mul ps.2.2.1 Grid.contains_pi)⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatGridParameters_sound
