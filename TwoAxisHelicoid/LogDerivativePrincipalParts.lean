import TwoAxisHelicoid.RemovableGerms
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Star

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ComplexConjugate
set_option maxHeartbeats 1200000

/-- A genuine simple analytic zero produces residue one in the actual
logarithmic derivative, with an analytic remainder. -/
theorem simple_zero_log_derivative_principal_part {g : ℂ → ℂ} {p : ℂ}
    (hg : AnalyticAt ℂ g p) (hzero : g p = 0) (hderiv : deriv g p ≠ 0) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r p ∧
      ∀ᶠ z in 𝓝[≠] p, deriv g z/g z = (z-p)⁻¹+r z := by
  let U : Set ℂ := {z | AnalyticAt ℂ g z}
  have hU : IsOpen U := isOpen_analyticAt ℂ g
  have hgp : p ∈ U := hg
  have hdg : DifferentiableOn ℂ g U := fun z hz => hz.differentiableAt.differentiableWithinAt
  have hds : DifferentiableOn ℂ (dslope g p) U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds hgp)).mpr hdg
  have hs : AnalyticAt ℂ (dslope g p) p := hds.analyticOnNhd hU p hgp
  have hsp : dslope g p p ≠ 0 := by simpa only [dslope_same] using hderiv
  let r : ℂ → ℂ := fun z => deriv (dslope g p) z/dslope g p z
  refine ⟨r,hs.deriv.div hs hsp,?_⟩
  have hn : ∀ᶠ z in 𝓝 p, dslope g p z ≠ 0 := hs.continuousAt.eventually_ne hsp
  have he (z : ℂ) : (z-p)*dslope g p z = g z := by
    simpa only [smul_eq_mul,hzero,sub_zero] using sub_smul_dslope g p z
  filter_upwards [hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    hs.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    hn.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z hgz hsz hsn hzp
  have hd := ((hasDerivAt_id z).sub_const p).mul hsz.differentiableAt.hasDerivAt
  change HasDerivAt (fun z : ℂ => (z-p)*dslope g p z)
    (1*dslope g p z+(z-p)*deriv (dslope g p) z) z at hd
  have hf : (fun z : ℂ => (z-p)*dslope g p z) = g := funext he
  rw [hf] at hd
  have hde := hd.unique hgz.differentiableAt.hasDerivAt
  simp only [one_mul] at hde
  have hzp' : z-p ≠ 0 := sub_ne_zero.mpr hzp
  rw [← he z]
  dsimp only [r]
  field_simp [hzp',hsn]
  linear_combination -hde

theorem log_derivative_inverse {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) (hn : g z ≠ 0) :
    deriv (fun w => (g w)⁻¹) z/(g z)⁻¹ = -(deriv g z/g z) := by
  change deriv g⁻¹ z/(g z)⁻¹ = -(deriv g z/g z)
  rw [(hg.hasDerivAt.inv hn).deriv]
  field_simp

/-- A simple zero of the reciprocal produces residue minus one. The
reciprocal's analytic extension is the ordinary local definition of a
simple meromorphic pole. -/
theorem simple_pole_log_derivative_principal_part {g : ℂ → ℂ} {p : ℂ}
    (hg : AnalyticAt ℂ (fun z => (g z)⁻¹) p)
    (hzero : (g p)⁻¹ = 0) (hderiv : deriv (fun z => (g z)⁻¹) p ≠ 0)
    (hreg : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ g z ∧ g z ≠ 0) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r p ∧
      ∀ᶠ z in 𝓝[≠] p, deriv g z/g z = -(z-p)⁻¹+r z := by
  obtain ⟨r,hr,he⟩ := simple_zero_log_derivative_principal_part hg hzero hderiv
  refine ⟨fun z => -r z,hr.neg,?_⟩
  filter_upwards [he,hreg] with z hz hgz
  rw [log_derivative_inverse hgz.1 hgz.2] at hz
  linear_combination -hz

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.simple_zero_log_derivative_principal_part
#print axioms TwoAxisHelicoid.simple_pole_log_derivative_principal_part
