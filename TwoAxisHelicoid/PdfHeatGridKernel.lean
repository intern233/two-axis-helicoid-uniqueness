import TwoAxisHelicoid.PdfHeatGridParameters
import TwoAxisHelicoid.PdfPrimalGridSampling
import TwoAxisHelicoid.PdfHeatPathDerivative

namespace TwoAxisHelicoid.PdfVertical
open Complex Set
attribute [local irreducible] thetaA thetaJet thetaQuotient

def HeatGridParameters.encloses (p q : HeatGridParameters) : Prop :=
  p.model.encloses q.model ∧ p.slope.encloses q.slope=true ∧
  p.firstRatio.encloses q.firstRatio=true ∧ p.secondRatio.encloses q.secondRatio=true ∧
  p.originRatio.encloses q.originRatio=true ∧ p.heatCoefficient.encloses q.heatCoefficient=true

instance (p q : HeatGridParameters) : Decidable (p.encloses q) := by
  unfold HeatGridParameters.encloses
  infer_instance

theorem heat_box_parameters_sound {tl tu al au : ℚ} {p : HeatGridParameters}
    (ok : p.encloses (heatGridParameters (Grid.ofRats tl tu) (Grid.ofRats al au)))
    {t a : ℝ} (tLow : (tl:ℝ)≤t) (tHigh : t≤(tu:ℝ)) (aLow : (al:ℝ)≤a) (aHigh : a≤(au:ℝ))
    (ht : 17/20≤t) : p.Sound t a := by
  obtain ⟨m,v,r,u,o,k⟩ := heatGridParameters_sound (Grid.contains_rats tLow tHigh)
    (Grid.contains_rats aLow aHigh) ht
  obtain ⟨pm,pv,pr,pu,po,pk⟩ := ok
  exact ⟨primal_box_parameters_sound pm tLow tHigh aLow aHigh ht,Grid.contains_of_encloses v pv,
    Grid.contains_of_encloses r pr,Grid.contains_of_encloses u pu,Grid.contains_of_encloses o po,
    Grid.contains_of_encloses k pk⟩

def heatKernelValue (p : HeatGridParameters) (v : CGrid) : CGrid :=
  let S := fun j : Fin 5 => checkedPrimalJet p.model.q v j
  let E := fun j : Fin 5 => checkedPrimalJet p.model.q (v.sub p.model.aArgument) j
  let Z := fun j : Fin 5 => (S j).div (S 0)
  let W := fun j : Fin 5 => (E j).div (E 0)
  let la := CGrid.scale Grid.pi (((Z 1).sub (W 1)).sub (CGrid.real p.firstRatio))
  let lt := (CGrid.scale (Grid.pi.divNat 4)
    (((CGrid.real (p.originRatio.sub p.secondRatio)).add (W 2)).sub (Z 2))).add
    (CGrid.scale p.heatCoefficient ((Z 3).sub ((Z 1).mul (Z 2))))
  (primalThetaValue p.model v).mul (lt.add (CGrid.scale p.slope la))

/-- Every grid evaluation encloses the exact logarithmic heat derivative
on its complex input. The implicit slope is computed on the same rectangle. -/
theorem heatKernelValue_contains {p : HeatGridParameters} {t a : ℝ}
    (hs : p.Sound t a) (ht : 17/20≤t) {v : CGrid} {z : ℂ} (hv : v.Contains (Real.pi*z/2)) :
    (heatKernelValue p v).Contains (pdfHeatKernel t a (-(thetaGt t a).re/(thetaGa t a).re) z) := by
  obtain ⟨ps,slope,base₁,base₂,origin,co⟩ := hs
  let S := fun j : Fin 5 => checkedPrimalJet p.model.q v j
  let E := fun j : Fin 5 => checkedPrimalJet p.model.q (v.sub p.model.aArgument) j
  have shifted := CGrid.contains_sub hv ps.2.1
  rw [show (Real.pi:ℂ)*z/2-Real.pi*a/2=Real.pi*(z-a)/2 by ring] at shifted
  have zR (j : Fin 5) : ((S j).div (S 0)).Contains (thetaQuotient t j (Real.pi*z/2)) := by
    simpa only [S,thetaQuotient,Fin.val_zero] using CGrid.contains_div (checkedPrimalJet_contains ps.1 hv ht j) (checkedPrimalJet_contains ps.1 hv ht 0)
  have mR (j : Fin 5) : ((E j).div (E 0)).Contains (thetaQuotient t j (Real.pi*(z-a)/2)) := by
    simpa only [E,thetaQuotient,Fin.val_zero] using CGrid.contains_div (checkedPrimalJet_contains ps.1 shifted ht j) (checkedPrimalJet_contains ps.1 shifted ht 0)
  have base := CGrid.contains_real base₁
  rw [heatRealRatio_cast] at base
  have la := CGrid.contains_scale Grid.contains_pi (CGrid.contains_sub (CGrid.contains_sub (zR 1) (mR 1)) base)
  have V := CGrid.contains_real (Grid.contains_sub origin base₂)
  rw [Complex.ofReal_sub,heatZeroRatio_cast,heatRealRatio_cast] at V
  have t₁ := CGrid.contains_scale (Grid.contains_divNat (n:=4) Grid.contains_pi)
    (CGrid.contains_sub (CGrid.contains_add V (mR 2)) (zR 2))
  have t₂ := CGrid.contains_scale co (CGrid.contains_sub (zR 3) (CGrid.contains_mul (zR 1) (zR 2)))
  have out := CGrid.contains_mul (primalThetaValue_contains ps ht hv)
    (CGrid.contains_add (CGrid.contains_add t₁ t₂) (CGrid.contains_scale slope la))
  change (heatKernelValue p v).Contains _ at out
  unfold pdfHeatKernel thetaLt thetaLa
  simp only [show ((1:Fin 5):ℕ)=1 by decide, show ((2:Fin 5):ℕ)=2 by decide,
    show ((3:Fin 5):ℕ)=3 by decide] at out
  push_cast at out ⊢
  convert out using 2
  ring

def heatGridOutput (T : Grid) (p : HeatGridParameters) (xl xu yl yu : ℚ) : CGrid :=
  heatKernelValue p (primalStripArgument T (Grid.ofRats xl xu) (Grid.ofRats yl yu))

theorem heatGridOutput_contains {T : Grid} {p : HeatGridParameters} {t a : ℝ}
    (ts : T.Contains t) (ps : p.Sound t a) (ht : 17/20≤t) {z : ℂ} {xl xu yl yu : ℚ}
    (x : z.re∈Icc (xl:ℝ) (xu:ℝ)) (y : z.im∈Icc (yl:ℝ) (yu:ℝ)) :
    (heatGridOutput T p xl xu yl yu).Contains
      (pdfHeatKernel t a (-(thetaGt t a).re/(thetaGa t a).re) (z+I*((t/2:ℝ):ℂ))) :=
  heatKernelValue_contains ps ht (primalStripArgument_contains ts
    (Grid.contains_rats x.1 x.2) (Grid.contains_rats y.1 y.2))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatKernelValue_contains
