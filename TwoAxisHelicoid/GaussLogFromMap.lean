import TwoAxisHelicoid.GaussPrincipalParts
import TwoAxisHelicoid.LogDerivativePrincipalParts

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ComplexConjugate
attribute [local irreducible] thetaZeta thetaSigma thetaEtaExpression

theorem gaussLogPoleSet_isClosed (L : PeriodPair) (a : ℂ) : IsClosed (gaussLogPoleSet L a) :=
  latticePoleSet_isClosed L (by simp)

theorem gaussLogPoleSet_conj {t a : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a) :
    conj z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a := by
  have hnot (w : ℂ) (hw : w ∉ (rhombicPeriodPair t ht).lattice) :
      conj w ∉ (rhombicPeriodPair t ht).lattice := by
    intro h
    exact hw (by simpa only [Complex.conj_conj] using rhombic_conj_mem ht h)
  obtain ⟨hz₀,hm,hp⟩ := (not_mem_gaussLogPoleSet _ _ _).mp hz
  apply (not_mem_gaussLogPoleSet _ _ _).mpr
  refine ⟨hnot z hz₀,?_,?_⟩
  · simpa only [map_sub,Complex.conj_ofReal] using hnot (z-a) hm
  · simpa only [map_add,Complex.conj_ofReal] using hnot (z+a) hp

theorem gauss_log_from_map_analytic {t a : ℝ} (ht : 0 < t) {g : ℂ → ℂ}
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, AnalyticAt ℂ g z)
    (hgn : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, g z ≠ 0)
    {z : ℂ} (hz : z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a) :
    AnalyticAt ℂ (fun w => deriv g w/g w) z :=
  (hg z hz).deriv.div (hg z hz) (hgn z hz)

theorem gauss_log_from_map_periodic {t a : ℝ} (ht : 0 < t) {g : ℂ → ℂ}
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, AnalyticAt ℂ g z)
    (hp : ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice →
      z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a → g (z+ω) = g z)
    {z ω : ℂ} (hω : ω ∈ (rhombicPeriodPair t ht).lattice)
    (hz : z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a) :
    deriv g (z+ω)/g (z+ω) = deriv g z/g z := by
  have hzω : z+ω ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a :=
    (latticePoleSet_add_iff _ _ z ω hω).not.mpr hz
  have he : g =ᶠ[𝓝 z] (fun w => g (w+ω)) := by
    filter_upwards [(gaussLogPoleSet_isClosed _ _).isOpen_compl.mem_nhds hz] with w hw
    exact (hp w ω hω hw).symm
  have hshift := (hg (z+ω) hzω).differentiableAt.hasDerivAt.comp z ((hasDerivAt_id z).add_const ω)
  simp only [Function.comp_def,id_eq,mul_one] at hshift
  have hd := (hshift.congr_of_eventuallyEq he).unique (hg z hz).differentiableAt.hasDerivAt
  rw [hd,hp z ω hω hz]

theorem gauss_log_from_map_conj {t a : ℝ} (ht : 0 < t) {g : ℂ → ℂ}
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, AnalyticAt ℂ g z)
    (hconj : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, g (conj z) = -conj (g z))
    {z : ℂ} (hz : z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a) :
    deriv g (conj z)/g (conj z) = conj (deriv g z/g z) := by
  have hzc := gaussLogPoleSet_conj ht hz
  have he : (fun w => -g w) =ᶠ[𝓝 (conj z)] (conj ∘ g ∘ conj) := by
    filter_upwards [(gaussLogPoleSet_isClosed _ _).isOpen_compl.mem_nhds hzc] with w hw
    simp only [Function.comp_def,hconj w hw,map_neg,Complex.conj_conj]
  have h₁ := (hg z hz).differentiableAt.hasDerivAt.conj_conj.congr_of_eventuallyEq he
  have h₂ := (hg (conj z) hzc).differentiableAt.hasDerivAt.neg
  have hd : deriv g (conj z) = -conj (deriv g z) := by
    have h := h₁.unique h₂
    linear_combination h
  rw [hd,hconj z hz,neg_div_neg_eq,map_div₀]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.gauss_log_from_map_periodic
#print axioms TwoAxisHelicoid.gauss_log_from_map_conj
