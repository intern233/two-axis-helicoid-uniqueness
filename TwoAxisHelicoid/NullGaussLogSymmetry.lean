import TwoAxisHelicoid.NullGaussSymmetry

namespace TwoAxisHelicoid
open Complex Filter
open scoped Topology

theorem nullGauss_analyticAt_of_height {p : ℂ → Fin 3 → ℂ} {z : ℂ}
    (ha : ∀ j, AnalyticAt ℂ (fun w => p w j) z)
    (hp : ComplexNull (p z)) (hh : p z 2 ≠ 0) :
    AnalyticAt ℂ (fun w => nullGauss (p w)) z := by
  exact (ha 2).div ((ha 0).sub (analyticAt_const.mul (ha 1)))
    (null_horizontal_nonzero_of_height hp hh).1

theorem nullGauss_ne_zero_of_height {p : Fin 3 → ℂ} (hp : ComplexNull p) (hh : p 2 ≠ 0) :
    nullGauss p ≠ 0 :=
  div_ne_zero hh (null_horizontal_nonzero_of_height hp hh).1

/-- The even logarithmic derivative follows from the actual null reflection
rule and differentiability; it is not an extra symmetry hypothesis. -/
theorem null_gauss_log_derivative_neg {L : PeriodPair} {p : ℂ → Fin 3 → ℂ}
    (hp : TwoAxisNullDifferential L p)
    (ha : ∀ z ∉ L.lattice, ∀ j, AnalyticAt ℂ (fun w => p w j) z)
    {z : ℂ} (hz : z ∉ L.lattice) (hh : p z 2 ≠ 0) :
    deriv (fun w => nullGauss (p w)) (-z)/nullGauss (p (-z)) =
      deriv (fun w => nullGauss (p w)) z/nullGauss (p z) := by
  have hn : -z ∉ L.lattice := by simpa using hz
  have hhn : p (-z) 2 ≠ 0 := by rw [hp.neg z hz]; exact hh
  have hga := nullGauss_analyticAt_of_height (ha z hz) (hp.null z hz) hh
  have hgn := nullGauss_analyticAt_of_height (ha (-z) hn) (hp.null (-z) hn) hhn
  have he : (fun w => nullGauss (p (-w))*nullGauss (p w)) =ᶠ[𝓝 z] fun _ => (-1 : ℂ) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz,
      (ha z hz 2).continuousAt.eventually_ne hh] with w hw hhw
    exact null_gauss_neg_product hp hw hhw
  have hd := ((hgn.differentiableAt.hasDerivAt.comp z (hasDerivAt_id z).neg).mul
    hga.differentiableAt.hasDerivAt).congr_of_eventuallyEq he.symm
  have hh' := hd.unique (hasDerivAt_const z (-1 : ℂ))
  dsimp only [Function.comp_def] at hh'
  have hg0 := nullGauss_ne_zero_of_height (hp.null z hz) hh
  have hgn0 := nullGauss_ne_zero_of_height (hp.null (-z) hn) hhn
  field_simp [hg0,hgn0]
  linear_combination -hh'

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.null_gauss_log_derivative_neg
