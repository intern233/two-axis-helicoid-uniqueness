import TwoAxisHelicoid.PdfPrimalGridKernel

namespace TwoAxisHelicoid.PdfVertical

def Grid.encloses (outer inner : Grid) : Bool :=
  inner.ok && decide (outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi)

theorem Grid.contains_of_encloses {outer inner : Grid} {x : ℝ} (h : inner.Contains x)
    (order : outer.encloses inner=true) : outer.Contains x := by
  obtain ⟨ok,limits⟩ := Bool.and_eq_true_iff.mp order
  obtain ⟨l,r⟩ := of_decide_eq_true limits
  intro _
  exact ⟨(show (outer.lo:ℝ)≤(inner.lo:ℝ) by exact_mod_cast l).trans (h ok).1,
    (h ok).2.trans (by exact_mod_cast r)⟩

def CGrid.encloses (outer inner : CGrid) : Bool :=
  outer.re.encloses inner.re && outer.im.encloses inner.im

theorem CGrid.contains_of_encloses {outer inner : CGrid} {z : ℂ} (h : inner.Contains z)
    (order : outer.encloses inner=true) : outer.Contains z := by
  obtain ⟨l,u⟩ := Bool.and_eq_true_iff.mp order
  exact ⟨Grid.contains_of_encloses h.1 l,Grid.contains_of_encloses h.2 u⟩

def PrimalThetaParameters.encloses (p source : PrimalThetaParameters) : Prop :=
  p.q.encloses source.q=true ∧ p.aArgument.encloses source.aArgument=true ∧
    p.exponent.encloses source.exponent=true ∧
    (CGrid.real p.coefficient).encloses (CGrid.real source.coefficient)=true

instance (p s : PrimalThetaParameters) : Decidable (p.encloses s) := by
  unfold PrimalThetaParameters.encloses
  infer_instance

theorem primal_box_parameters_sound {p : PrimalThetaParameters} {tl tu al au : ℚ}
    (ok : p.encloses (primalThetaParameters (Grid.ofRats tl tu) (Grid.ofRats al au)))
    {t a : ℝ} (tLow : (tl:ℝ)≤t) (tHigh : t≤(tu:ℝ)) (aLow : (al:ℝ)≤a) (aHigh : a≤(au:ℝ))
    (ht : 17/20≤t) : p.Sound t a := by
  obtain ⟨q,aa,k,c⟩ := primalThetaParameters_sound (Grid.contains_rats tLow tHigh) (Grid.contains_rats aLow aHigh) ht
  exact ⟨CGrid.contains_of_encloses q ok.1,CGrid.contains_of_encloses aa ok.2.1,
    Grid.contains_of_encloses k ok.2.2.1,CGrid.contains_of_encloses c ok.2.2.2⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.primal_box_parameters_sound
