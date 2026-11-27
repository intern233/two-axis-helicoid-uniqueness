import TwoAxisHelicoid.SigmaAllIdentities
import TwoAxisHelicoid.RectanglePrimitive
import TwoAxisHelicoid.RhombicRegularPaths
import Mathlib.Analysis.Complex.RemovableSingularity

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaSigma thetaZeta thetaEtaExpression

noncomputable def sigmaDivZero (t : ℝ) : ℂ → ℂ := dslope (thetaSigma t) 0

theorem sigmaDivZero_differentiable {t : ℝ} (ht : 0 < t) : Differentiable ℂ (sigmaDivZero t) := by
  apply differentiableOn_univ.mp
  apply (Complex.differentiableOn_dslope (s := univ) (c := 0) (by simp)).mpr
  exact (show Differentiable ℂ (thetaSigma t) from fun z => (thetaSigma_analyticAt ht z).differentiableAt).differentiableOn

theorem sigmaDivZero_zero {t : ℝ} (ht : 0 < t) : sigmaDivZero t 0 = 1 := by
  rw [sigmaDivZero,dslope_same]
  exact (thetaSigma_hasDerivAt_zero_of_pos ht).deriv

theorem mul_sigmaDivZero (t : ℝ) (z : ℂ) : z*sigmaDivZero t z = thetaSigma t z := by
  simpa only [sigmaDivZero,sub_zero,smul_eq_mul,thetaSigma_zero] using
    sub_smul_dslope (thetaSigma t) 0 z

theorem sigmaDivZero_ne_zero {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice ∨ z = 0) : sigmaDivZero t z ≠ 0 := by
  rcases hz with hz | rfl
  · intro h
    have he := mul_sigmaDivZero t z
    rw [h,mul_zero] at he
    exact hz ((thetaSigma_zero_iff_lattice_of_pos ht ht z).mp he.symm)
  · rw [sigmaDivZero_zero ht]
    exact one_ne_zero

noncomputable def zetaPoleRegular (t : ℝ) (z : ℂ) : ℂ :=
  deriv (sigmaDivZero t) z/sigmaDivZero t z

theorem zetaPoleRegular_analyticAt {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice ∨ z = 0) :
    AnalyticAt ℂ (zetaPoleRegular t) z := by
  have hf := (sigmaDivZero_differentiable ht).analyticAt z
  exact hf.deriv.div hf (sigmaDivZero_ne_zero ht hz)

theorem thetaZeta_eq_inv_add_regular {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    thetaZeta t z = z⁻¹+zetaPoleRegular t z := by
  have hn : z ≠ 0 := by intro he; apply hz; rw [he]; exact (rhombicPeriodPair t ht).lattice.zero_mem
  have hg := sigmaDivZero_ne_zero ht (Or.inl hz)
  have hd := (hasDerivAt_id z).mul ((sigmaDivZero_differentiable ht z).hasDerivAt)
  have hf : (fun z : ℂ => z*sigmaDivZero t z) = thetaSigma t := funext (mul_sigmaDivZero t)
  simp only [id_eq,one_mul] at hd
  change HasDerivAt (fun z : ℂ => z*sigmaDivZero t z)
    (sigmaDivZero t z+z*deriv (sigmaDivZero t) z) z at hd
  rw [hf] at hd
  have he := hd.unique (thetaSigma_hasDerivAt_zeta_of_pos ht ht hz)
  rw [← mul_sigmaDivZero t z] at he
  unfold zetaPoleRegular
  field_simp [hn,hg]
  linear_combination -he

theorem rhombic_central_rectangle_lattice {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ complexOpenRect (-1) 1 (-2*t) (2*t))
    (hL : z ∈ (rhombicPeriodPair t ht).lattice) : z = 0 := by
  obtain ⟨m,n,hr,hi⟩ := (rhombic_mem_lattice_iff ht z).mp hL
  have hnlo : (-2 : ℤ) < n := by
    exact_mod_cast (show (-2 : ℝ) < n by nlinarith [hz.2.1])
  have hnhi : n < (2 : ℤ) := by
    exact_mod_cast (show (n : ℝ) < 2 by nlinarith [hz.2.2])
  have hmlo : (-1 : ℤ) < 2*m+n := by exact_mod_cast (hr ▸ hz.1.1)
  have hmhi : 2*m+n < (1 : ℤ) := by exact_mod_cast (hr ▸ hz.1.2)
  have hm : 2*m+n = 0 := by omega
  have hn : n = 0 := by omega
  have hm0 : m = 0 := by omega
  apply Complex.ext <;> simp [hr,hi,hm0,hn]

theorem zetaPoleRegular_differentiableOn_central_rectangle {t : ℝ} (ht : 0 < t) :
    DifferentiableOn ℂ (zetaPoleRegular t) (complexOpenRect (-1) 1 (-2*t) (2*t)) := by
  intro z hz
  apply (zetaPoleRegular_analyticAt ht _).differentiableAt.differentiableWithinAt
  by_cases hL : z ∈ (rhombicPeriodPair t ht).lattice
  · exact Or.inr (rhombic_central_rectangle_lattice ht hz hL)
  · exact Or.inl hL

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaZeta_eq_inv_add_regular
#print axioms TwoAxisHelicoid.zetaPoleRegular_differentiableOn_central_rectangle
