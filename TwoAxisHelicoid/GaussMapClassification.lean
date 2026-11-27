import TwoAxisHelicoid.GaussSingleValued
import TwoAxisHelicoid.GaussLogFromMap

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ComplexConjugate
set_option maxHeartbeats 1200000

/-- The complete integer family follows from the analytic Gauss-map data
on the marked punctured torus: a simple zero and pole, one residue-free
double pole of the logarithmic differential at the end, actual lattice
single-valuedness and the two reflections. The geometric reduction from
an arbitrary embedded minimal surface to these inputs is separate. -/
theorem gauss_map_complete_integer_classification {t a : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) {g r₀ : ℂ → ℂ} {κ : ℂ}
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, AnalyticAt ℂ g z)
    (hgn : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, g z ≠ 0)
    (hperiod : ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice →
      z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a → g (z+ω) = g z)
    (hconj : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, g (conj z) = -conj (g z))
    (hneg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, g (-z)*g z = -1)
    (hgPos : AnalyticAt ℂ g a) (hzPos : g a = 0) (hdPos : deriv g a ≠ 0)
    (hgNeg : AnalyticAt ℂ (fun z => (g z)⁻¹) (-a))
    (hzNeg : (g (-a))⁻¹ = 0) (hdNeg : deriv (fun z => (g z)⁻¹) (-a) ≠ 0)
    (hr₀ : AnalyticAt ℂ r₀ 0)
    (hend : ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv g z/g z = κ/z^2+r₀ z) :
    ∃ m : ℤ, κ = 2*((m : ℂ)-a) ∧
      ((∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, g z = thetaGauss t a m z) ∨
       (∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, g z = -thetaGauss t a m z)) := by
  let L := rhombicPeriodPair t ht
  have haL : (a : ℂ) ∉ L.lattice :=
    real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  have h2aL : 2*(a : ℂ) ∉ L.lattice := by
    have h := real_not_mem_rhombic_lattice_of_pos ht
      (show 0 < 2*a by linarith [ha.1]) (show 2*a < 2 by linarith [ha.2])
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using h
  obtain ⟨rPos,hrPos,hePos⟩ := simple_zero_log_derivative_principal_part hgPos hzPos hdPos
  have hregNeg : ∀ᶠ z in 𝓝[≠] (-(a : ℂ)), DifferentiableAt ℂ g z ∧ g z ≠ 0 := by
    filter_upwards [latticePoleSet_punctured_avoids L
      (show ({0,(a : ℂ),-(a : ℂ)} : Set ℂ).Finite by simp) (-(a : ℂ))] with z hz
    exact ⟨(hg z hz).differentiableAt,hgn z hz⟩
  obtain ⟨rNeg,hrNeg,heNeg⟩ := simple_pole_log_derivative_principal_part hgNeg hzNeg hdNeg hregNeg
  have hf (z : ℂ) (hz : z ∉ gaussLogPoleSet L a) :
      AnalyticAt ℂ (fun w => deriv g w/g w) z := gauss_log_from_map_analytic ht hg hgn hz
  have hp (z ω : ℂ) (hω : ω ∈ L.lattice) (hz : z ∉ gaussLogPoleSet L a) :
      deriv g (z+ω)/g (z+ω) = deriv g z/g z := gauss_log_from_map_periodic ht hg hperiod hω hz
  obtain ⟨β,hform⟩ := gauss_log_differential_principal_parts ht haL h2aL hf hp hr₀ hrPos hrNeg
    hend hePos (by simpa only [sub_neg_eq_add] using heNeg)
  have hreal := gauss_log_coefficients_real ht ha hform
    (fun z hz => gauss_log_from_map_conj ht hg hconj hz)
  have hκ : κ = (κ.re : ℂ) := by apply Complex.ext <;> simp [hreal.1]
  have hβ : β = (β.re : ℂ) := by apply Complex.ext <;> simp [hreal.2]
  have hformReal (z : ℂ) (hz : z ∉ gaussLogPoleSet L a) :
      deriv g z/g z = (κ.re : ℂ)*L.weierstrassP z+(β.re : ℂ)+
        thetaZeta t (z-a)-thetaZeta t (z+a) := by
    rw [← hκ,← hβ]
    exact hform z hz
  obtain ⟨m,hmκ,_,hm⟩ := gauss_closed_real_log_differential_integer_family ht ha
    (fun z hz => (hg z hz).differentiableAt) hgn hformReal hperiod hneg
  refine ⟨m,?_,hm⟩
  rw [hκ]
  exact_mod_cast hmκ

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.gauss_map_complete_integer_classification
