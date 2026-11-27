import TwoAxisHelicoid.PdfFactoredThetaJets
import TwoAxisHelicoid.PdfHeatGridKernel

namespace TwoAxisHelicoid.PdfVertical
open Complex
attribute [local irreducible] thetaA thetaJet thetaQuotient

def primalValueOfJets (p : PrimalThetaParameters) (S E : Fin 5 → CGrid) : CGrid :=
  let den := S 0
  let num := E 0
  let first := S 1
  let ratio := num.div den
  (CGrid.real p.coefficient).mul ((ratio.mul ratio).mul ((first.div den).scale p.exponent).exp)

theorem primalValueOfJets_sound {p : PrimalThetaParameters} {t a : ℝ} {S E : Fin 5 → CGrid} {z : ℂ}
    (data : p.Sound t a) (ds : ∀ j, (S j).Contains (thetaJet t j (Real.pi*z/2)))
    (es : ∀ j, (E j).Contains (thetaJet t j (Real.pi*(z-a)/2))) :
    (primalValueOfJets p S E).Contains (thetaA t a z) := by
  have den := ds 0
  have num := es 0
  have first := ds 1
  have ratio := CGrid.contains_div num den
  have quot := CGrid.contains_div first den
  have exp := CGrid.contains_exp (CGrid.contains_scale data.2.2.1 quot)
  have result := CGrid.contains_mul data.2.2.2 (CGrid.contains_mul (CGrid.contains_mul ratio ratio) exp)
  simpa only [primalValueOfJets,Fin.val_zero,Fin.val_one,thetaA,thetaACoefficient,thetaQuotient,pow_two,Complex.ofReal_mul,Complex.ofReal_sub,
    Complex.ofReal_one,mul_comm (Real.pi:ℂ) ((a:ℂ)-1),mul_assoc] using result

def heatValueOfJets (p : HeatGridParameters) (S E : Fin 5 → CGrid) : CGrid :=
  let Z := fun j : Fin 5 => (S j).div (S 0)
  let W := fun j : Fin 5 => (E j).div (E 0)
  let la := CGrid.scale Grid.pi (((Z 1).sub (W 1)).sub (CGrid.real p.firstRatio))
  let lt := (CGrid.scale (Grid.pi.divNat 4)
    (((CGrid.real (p.originRatio.sub p.secondRatio)).add (W 2)).sub (Z 2))).add
    (CGrid.scale p.heatCoefficient ((Z 3).sub ((Z 1).mul (Z 2))))
  (primalValueOfJets p.model S E).mul (lt.add (CGrid.scale p.slope la))


theorem heatValueOfJets_sound {p : HeatGridParameters} {t a : ℝ} {S E : Fin 5 → CGrid} {z : ℂ}
    (hs : p.Sound t a) (ds : ∀ j, (S j).Contains (thetaJet t j (Real.pi*z/2)))
    (es : ∀ j, (E j).Contains (thetaJet t j (Real.pi*(z-a)/2))) :
    (heatValueOfJets p S E).Contains (pdfHeatKernel t a (-(thetaGt t a).re/(thetaGa t a).re) z) := by
  obtain ⟨ps,slope,base₁,base₂,origin,co⟩ := hs
  have zR (j : Fin 5) : ((S j).div (S 0)).Contains (thetaQuotient t j (Real.pi*z/2)) := by
    simpa only [thetaQuotient,Fin.val_zero] using CGrid.contains_div (ds j) (ds 0)
  have mR (j : Fin 5) : ((E j).div (E 0)).Contains (thetaQuotient t j (Real.pi*(z-a)/2)) := by
    simpa only [thetaQuotient,Fin.val_zero] using CGrid.contains_div (es j) (es 0)
  have base := CGrid.contains_real base₁
  rw [heatRealRatio_cast] at base
  have la := CGrid.contains_scale Grid.contains_pi (CGrid.contains_sub (CGrid.contains_sub (zR 1) (mR 1)) base)
  have V := CGrid.contains_real (Grid.contains_sub origin base₂)
  rw [Complex.ofReal_sub,heatZeroRatio_cast,heatRealRatio_cast] at V
  have t₁ := CGrid.contains_scale (Grid.contains_divNat (n:=4) Grid.contains_pi)
    (CGrid.contains_sub (CGrid.contains_add V (mR 2)) (zR 2))
  have t₂ := CGrid.contains_scale co (CGrid.contains_sub (zR 3) (CGrid.contains_mul (zR 1) (zR 2)))
  have out := CGrid.contains_mul (primalValueOfJets_sound ps ds es)
    (CGrid.contains_add (CGrid.contains_add t₁ t₂) (CGrid.contains_scale slope la))
  change (heatValueOfJets p S E).Contains _ at out
  unfold pdfHeatKernel thetaLt thetaLa
  simp only [show ((1:Fin 5):ℕ)=1 by decide, show ((2:Fin 5):ℕ)=2 by decide,
    show ((3:Fin 5):ℕ)=3 by decide] at out
  push_cast at out ⊢
  convert out using 2
  ring


theorem factored_sample_strip {t a x : ℝ} (ht : 17/20≤t) (hu : t≤7/5) (s : Bool) :
    |(sampleThetaArgument t a x s).im|≤2 := by
  have e : (sampleThetaArgument t a x s).im=Real.pi*t/4 := by
    cases s <;> simp [sampleThetaArgument,Complex.mul_im,Complex.mul_re] <;> ring
  rw [e,abs_of_nonneg (by positivity)]
  nlinarith [Real.pi_lt_four,Real.pi_pos,mul_nonneg (show 0≤4-Real.pi by linarith [Real.pi_lt_four]) (show 0≤t by linarith)]

theorem factored_sample_jets {p : Fin 6 → FactoredFrequency} {node : Fin 6 → CGrid} {t a x : ℝ}
    (gp : ∀ n : Fin 6, (p n).Sound t a n) (gn : ∀ n : Fin 6, (node n).Contains (wavePhase n x))
    (ht : 17/20≤t) (hu : t≤7/5) (j : Fin 5) :
    (factoredJet p node j false).Contains (thetaJet t j (Real.pi*((x:ℂ)+I*((t/2:ℝ):ℂ))/2)) ∧
    (factoredJet p node j true).Contains (thetaJet t j (Real.pi*(((x:ℂ)+I*((t/2:ℝ):ℂ))-(a:ℂ))/2)) := by
  exact ⟨by simpa only [sampleThetaArgument,Bool.false_eq_true,ite_false,sub_zero] using
    factoredJet_sound gp gn j false ht (factored_sample_strip ht hu false),
    factoredJet_sound gp gn j true ht (factored_sample_strip ht hu true)⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatValueOfJets_sound
#print axioms TwoAxisHelicoid.PdfVertical.factored_sample_jets
