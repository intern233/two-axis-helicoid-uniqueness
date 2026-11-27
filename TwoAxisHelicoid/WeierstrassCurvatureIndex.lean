import TwoAxisHelicoid.WeierstrassSecondForm
import TwoAxisHelicoid.GaussNormalIndex

set_option autoImplicit false
namespace TwoAxisHelicoid
open Complex Set Filter Bornology

/-- Squared second fundamental form times conformal area density, computed
from actual Gauss-normal derivatives and actual Weierstrass tangents.
The first fundamental form is cosh(Re W)^2 times the identity. -/
noncomputable def weierstrassCurvatureDensity (W : ℂ → ℂ) (p : ℝ × ℝ) : ℝ :=
  (∑ i : Fin 2, ∑ j : Fin 2, (logGaussSecondForm W (planeComplex p) i j)^2)/
    (Real.cosh (W (planeComplex p)).re)^2

theorem weierstrassCurvatureDensity_eq_gauss_energy {W : ℂ → ℂ} {D : ℂ} {p : ℝ × ℝ}
    (hW : HasDerivAt W D (planeComplex p)) :
    weierstrassCurvatureDensity W p = gaussNormalDirichletDensity W p := by
  obtain ⟨nx,ny,hx,hy,he⟩ := holomorphicLogGaussNormal_energy hW
  unfold gaussNormalDirichletDensity
  rw [hx.deriv,hy.deriv,he]
  exact (logGaussSecondForm_trace_and_density hW).2

theorem weierstrassCurvatureDensity_end_formula {F : ℂ → ℂ} {α : ℝ}
    {p : ℝ × ℝ} (hF : DifferentiableAt ℂ F (planeComplex p)) :
    weierstrassCurvatureDensity (fun z => I*(α : ℂ)*z+F z) p =
      helicoidEndPotential α F (deriv F) p := by
  have hW := ((hasDerivAt_id (planeComplex p)).const_mul (I*(α : ℂ))).add hF.hasDerivAt
  exact (weierstrassCurvatureDensity_eq_gauss_energy hW).trans
    (gaussNormalDirichletDensity_end_formula hF)

/-- Arbitrarily large negative compact test spaces for the actual squared
second-form density of the height-normalized analytic helicoid end. This
is still an end-coordinate conclusion; the global geometric Morse-index
statement requires the end parametrization and second-variation transfer. -/
theorem analytic_helicoid_second_form_infinite_index {α : ℝ} (hα : α ≠ 0)
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0) :
    HasInfiniteCompactPlanarIndexAtInfinity
      (weierstrassCurvatureDensity (fun z => I*(α : ℂ)*z+infinityCorrection f z)) := by
  obtain ⟨R,_,hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp
    (infinityCorrection_eventually_analytic hf)
  apply (analytic_helicoid_end_potential_infinite_index hα hf h0).congr_outside (B := R)
  intro p hp
  exact (weierstrassCurvatureDensity_end_formula
    (hR (hp.trans (norm_le_planeComplex_norm p))).differentiableAt).symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.analytic_helicoid_second_form_infinite_index
