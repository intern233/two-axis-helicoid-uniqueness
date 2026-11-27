import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Complex.CauchyIntegral

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- A complex implicit germ is holomorphic, hence analytic, when the equation
has a continuous differentiable germ with invertible second partial derivative.
The proof differentiates the actual local inverse on a neighborhood. -/
theorem complex_implicit_germ_analytic {F : ℂ × ℂ → ℂ}
    {D : ℂ × ℂ → (ℂ × ℂ →L[ℂ] ℂ)} {p : ℂ × ℂ}
    (hD : ∀ᶠ q in 𝓝 p, HasStrictFDerivAt F (D q) q)
    (hInv : ∀ᶠ q in 𝓝 p, ((D q) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible) :
    AnalyticAt ℂ (hD.self_of_nhds.implicitFunctionOfProdDomain hInv.self_of_nhds) p.1 := by
  let φ := hD.self_of_nhds.implicitFunctionDataOfProdDomain hInv.self_of_nhds
  let R := φ.toOpenPartialHomeomorph
  have hp : p ∈ R.source := φ.pt_mem_toOpenPartialHomeomorph_source
  have htarget : (F p,p.1) ∈ R.target := R.map_source hp
  have hback : R.symm (F p,p.1) = p := R.left_inv hp
  have hline : ContinuousAt (fun z : ℂ => (F p,z)) p.1 := continuousAt_const.prodMk continuousAt_id
  have hcont := R.continuousAt_symm htarget
  have hlim : Tendsto (fun z : ℂ => R.symm (F p,z)) (𝓝 p.1) (𝓝 p) := by
    simpa only [hback,Function.comp_def] using hcont.tendsto.comp hline.tendsto
  have he : ∀ᶠ z in 𝓝 p.1, (F p,z) ∈ R.target :=
    hline.eventually (R.open_target.mem_nhds htarget)
  change AnalyticAt ℂ (fun z => (R.symm (F p,z)).2) p.1
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [he,hlim.eventually hD,hlim.eventually hInv] with z hz hd hi
  let ψ := hd.implicitFunctionDataOfProdDomain hi
  have hder := ψ.hasStrictFDerivAt.hasFDerivAt
  have hsymm := R.hasFDerivAt_symm hz hder
  have harg : DifferentiableAt ℂ (fun w : ℂ => (F p,w)) z := by fun_prop
  exact (hsymm.differentiableAt.comp z harg).snd

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.complex_implicit_germ_analytic
