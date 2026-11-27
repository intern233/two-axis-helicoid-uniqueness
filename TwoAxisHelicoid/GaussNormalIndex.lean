import TwoAxisHelicoid.WeierstrassLogGauss
import TwoAxisHelicoid.ExteriorPotentialIndex

set_option autoImplicit false
namespace TwoAxisHelicoid
open Complex Set Filter Bornology

/-- Euclidean Dirichlet density of the actual sphere-valued Gauss normal,
using derivatives on the two real coordinate lines. -/
noncomputable def gaussNormalDirichletDensity (W : ℂ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ∑ j : Fin 3, ((deriv (fun s : ℝ =>
      holomorphicLogGaussNormal W (planeComplex p+(s : ℂ))) 0 j)^2+
    (deriv (fun s : ℝ =>
      holomorphicLogGaussNormal W (planeComplex p+I*(s : ℂ))) 0 j)^2)

theorem gaussNormalDirichletDensity_end_formula {F : ℂ → ℂ} {α : ℝ}
    {p : ℝ × ℝ} (hF : DifferentiableAt ℂ F (planeComplex p)) :
    gaussNormalDirichletDensity (fun z => I*(α : ℂ)*z+F z) p =
      helicoidEndPotential α F (deriv F) p := by
  obtain ⟨nx,ny,hx,hy,he⟩ := helicoidEndPotential_eq_gauss_normal_energy (α := α) hF
  unfold gaussNormalDirichletDensity
  rw [hx.deriv,hy.deriv]
  exact he

/-- Infinite negative compact-test index is proved for the derivative energy
of the actual Gauss normal. Transferring this to the geometric Morse index
still requires the surface second-variation theorem and the end chart. -/
theorem analytic_helicoid_gauss_normal_infinite_index {α : ℝ} (hα : α ≠ 0)
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0) :
    HasInfiniteCompactPlanarIndexAtInfinity
      (gaussNormalDirichletDensity (fun z => I*(α : ℂ)*z+infinityCorrection f z)) := by
  obtain ⟨R,_,hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp
    (infinityCorrection_eventually_analytic hf)
  apply (analytic_helicoid_end_potential_infinite_index hα hf h0).congr_outside (B := R)
  intro p hp
  exact (gaussNormalDirichletDensity_end_formula
    (hR (hp.trans (norm_le_planeComplex_norm p))).differentiableAt).symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.analytic_helicoid_gauss_normal_infinite_index
