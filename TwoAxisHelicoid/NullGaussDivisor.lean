import TwoAxisHelicoid.NullGaussSymmetry
import TwoAxisHelicoid.SymmetricHeightRoot
import TwoAxisHelicoid.GaussMapClassification

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ComplexConjugate

structure GaussZeroPoleData (t a : ℝ) (ht : 0 < t) (g : ℂ → ℂ) : Prop where
  analytic : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, AnalyticAt ℂ g z
  nonzero : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, g z ≠ 0
  periodic : ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice →
    z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a → g (z+ω) = g z
  conjugation : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, g (conj z) = -conj (g z)
  neg_product : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, g (-z)*g z = -1
  positive_analytic : AnalyticAt ℂ g a
  positive_zero : g a = 0
  positive_simple : deriv g a ≠ 0
  negative_analytic : AnalyticAt ℂ (fun z => (g z)⁻¹) (-a)
  negative_zero : (g (-a))⁻¹ = 0
  negative_simple : deriv (fun z => (g z)⁻¹) (-a) ≠ 0

theorem null_height_nonzero_away_pair {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) {p : ℂ → Fin 3 → ℂ} {K : ℂ} (hK : K ≠ 0)
    (hheight : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      p z 2 = K*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    {z : ℂ} (hz : z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a) : p z 2 ≠ 0 := by
  have hz' := (not_mem_gaussLogPoleSet _ _ _).mp hz
  have han := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  rw [hheight z hz'.1]
  apply mul_ne_zero hK
  intro he
  have h := (rhombic_weierstrassP_eq_iff ht han hz'.1).mp (sub_eq_zero.mp he)
  exact h.elim hz'.2.1 hz'.2.2

theorem null_height_hasDerivAt {t a : ℝ} (ht : 0 < t)
    {p : ℂ → Fin 3 → ℂ} {K : ℂ}
    (hheight : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      p z 2 = K*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    {z : ℂ} (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    HasDerivAt (fun w => p w 2) (K*(rhombicPeriodPair t ht).derivWeierstrassP z) z := by
  apply (((rhombic_weierstrassP_hasDerivAt ht hz).sub_const
    ((rhombicPeriodPair t ht).weierstrassP a)).const_mul K).congr_of_eventuallyEq
  filter_upwards [(rhombicPeriodPair t ht).isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
  exact hheight w hw

/-- Nullity and simple height zeros force the actual Gauss map's complete
zero/pole pair. No divisor-degree or residue-count assertion is assumed. -/
theorem null_gauss_zero_pole_data {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    {p : ℂ → Fin 3 → ℂ} (hp : TwoAxisNullDifferential (rhombicPeriodPair t ht) p)
    (hanalytic : ∀ z ∉ (rhombicPeriodPair t ht).lattice, ∀ j, AnalyticAt ℂ (fun w => p w j) z)
    {K : ℂ} (hK : K ≠ 0)
    (hheight : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      p z 2 = K*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hminus : nullHorizontalMinus (p a) ≠ 0) :
    GaussZeroPoleData t a ht (fun z => nullGauss (p z)) := by
  let L := rhombicPeriodPair t ht
  have han : (a : ℂ) ∉ L.lattice := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  have hnan : -(a : ℂ) ∉ L.lattice := by
    intro h
    exact han (by simpa using L.lattice.neg_mem h)
  have hzero : p a 2 = 0 := by rw [hheight a han]; ring
  have hnzero : p (-a) 2 = 0 := by rw [hheight _ hnan,L.weierstrassP_neg]; ring
  have hwpa : L.derivWeierstrassP a ≠ 0 :=
    (rhombic_weierstrassP_critical_iff_of_pos ht ht han).not.mpr
      (hp.height_zero_not_two_torsion han hzero)
  have hda : deriv (fun w => p w 2) a ≠ 0 := by
    rw [(null_height_hasDerivAt ht hheight han).deriv]
    exact mul_ne_zero hK hwpa
  have hdna : deriv (fun w => p w 2) (-a) ≠ 0 := by
    rw [(null_height_hasDerivAt ht hheight hnan).deriv,L.derivWeierstrassP_neg]
    exact mul_ne_zero hK (neg_ne_zero.mpr hwpa)
  have hpos := null_gauss_simple_zero (hanalytic a han) hminus hzero hda
  have hplus : nullHorizontalPlus (p (-a)) ≠ 0 := by rwa [null_horizontal_plus_neg hp han]
  have hnullN : ∀ᶠ z in 𝓝 (-(a : ℂ)), ComplexNull (p z) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hnan] with z hz
    exact hp.null z hz
  have hneg := null_gauss_simple_pole (hanalytic _ hnan) hnullN hplus hnzero hdna
  refine ⟨?_,?_,?_,?_,?_,hpos.1,hpos.2.1,hpos.2.2,hneg.1,hneg.2.1,hneg.2.2⟩
  · intro z hz
    have hz' := (not_mem_gaussLogPoleSet _ _ _).mp hz
    have h2 := null_height_nonzero_away_pair ht ha hK hheight hz
    exact (hanalytic z hz'.1 2).div (null_horizontal_minus_analyticAt (hanalytic z hz'.1))
      (null_horizontal_nonzero_of_height (hp.null z hz'.1) h2).1
  · intro z hz
    have hz' := (not_mem_gaussLogPoleSet _ _ _).mp hz
    have h2 := null_height_nonzero_away_pair ht ha hK hheight hz
    exact div_ne_zero h2 (null_horizontal_nonzero_of_height (hp.null z hz'.1) h2).1
  · intro z ω hω _
    exact null_gauss_periodic hp z ω hω
  · intro z hz
    exact null_gauss_conjugation hp ((not_mem_gaussLogPoleSet _ _ _).mp hz).1
  · intro z hz
    exact null_gauss_neg_product hp ((not_mem_gaussLogPoleSet _ _ _).mp hz).1
      (null_height_nonzero_away_pair ht ha hK hheight hz)

theorem GaussZeroPoleData.integer_classification {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    {g r : ℂ → ℂ} (hg : GaussZeroPoleData t a ht g) {κ : ℂ} (hr : AnalyticAt ℂ r 0)
    (hend : ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv g z/g z = κ/z^2+r z) :
    ∃ m : ℤ, κ = 2*((m : ℂ)-a) ∧
      ((∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, g z = thetaGauss t a m z) ∨
       (∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, g z = -thetaGauss t a m z)) :=
  gauss_map_complete_integer_classification ht ha hg.analytic hg.nonzero hg.periodic hg.conjugation
    hg.neg_product hg.positive_analytic hg.positive_zero hg.positive_simple
    hg.negative_analytic hg.negative_zero hg.negative_simple hr hend

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.null_gauss_zero_pole_data
