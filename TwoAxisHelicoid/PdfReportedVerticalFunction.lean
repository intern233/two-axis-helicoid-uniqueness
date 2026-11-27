import TwoAxisHelicoid.PdfVerticalBoxSound
import TwoAxisHelicoid.ManuscriptDualVerticalSeries

namespace TwoAxisHelicoid.PdfVertical

/-- The quantity labeled minus D in the original positive certificate equals
the normalized vertical period that the grid checker actually evaluates. -/
theorem reportedVertical_dual {t a : ℝ} (ht : 0<t) (ha : 0<a) (hb : a<1) :
    reportedVertical true t a= -manuscriptDualVertical (Real.exp (-Real.pi/(2*t)))
      (Real.exp (Real.pi*(a-1/2)/t)) := by
  have period := (thetaG_actual_manuscript_D ht ha hb).2.2.2.2
  have nz : Real.pi^2*Real.exp (-Real.pi/(2*t))/t^2≠0 := by positivity
  change (thetaG t a).re/_=_
  rw [period,neg_mul,neg_div,mul_comm,mul_div_cancel_right₀ _ nz]

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.reportedVertical_dual

