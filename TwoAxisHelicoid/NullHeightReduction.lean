import TwoAxisHelicoid.SymmetricHeightRoot
import TwoAxisHelicoid.HeightPeriodNecessity

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ComplexConjugate

/-- The complete height-data reduction from an actual periodic real primitive
and regular symmetric null differential. Neither a real height zero nor the
vertical equation is assumed. The end's residue-free double pole remains an
explicit analytic hypothesis. -/
theorem symmetric_null_height_data_reduction {t : ℝ} (ht : 0 < t)
    {p : ℂ → Fin 3 → ℂ} (hp : TwoAxisNullDifferential (rhombicPeriodPair t ht) p)
    {F : ℂ → ℝ}
    (hF : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      HasFDerivAt F (realCoefficientDerivative (p z 2)) z)
    (hFP : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      ∀ ω ∈ (rhombicPeriodPair t ht).lattice, F (z+ω) = F z)
    (hd : ∀ z ∉ (rhombicPeriodPair t ht).lattice, DifferentiableAt ℂ (fun w => p w 2) z)
    {A : ℂ} (hA : A ≠ 0) {r : ℂ → ℂ} (hr : AnalyticAt ℂ r 0)
    (hend : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → p z 2 = A/z^2+r z) :
    ∃ (a c : ℝ), a ∈ Ioo (0 : ℝ) 1 ∧ c ≠ 0 ∧ t < ellipticVerticalUpper ∧ a = verticalA t ∧
      (∀ z ∉ (rhombicPeriodPair t ht).lattice,
        p z 2 = I*c*((rhombicPeriodPair t ht).weierstrassP z-
          (rhombicPeriodPair t ht).weierstrassP a)) ∧
      (rhombicPeriodPair t ht).derivWeierstrassP a ≠ 0 := by
  have hperiod (z ω : ℂ) (hω : ω ∈ (rhombicPeriodPair t ht).lattice) :
      p (z+ω) 2 = p z 2 := congrFun (hp.periodic z ω hω) 2
  have hconj (z : ℂ) (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
      p (conj z) 2 = -conj (p z 2) := by
    have h := congrFun (hp.conjugation z hz) 2
    exact h
  have hP := actual_height_primitive_sloping_period_zero ht hd hF hFP
  obtain ⟨c,hc,hform⟩ := rhombic_height_coefficient_classification ht hA hd hperiod hr hend hconj hP
  have hK : I*(c : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hc)
  obtain ⟨a,ha,hzero⟩ := symmetric_height_has_normalized_real_zero ht hp hK hform
  have hbranch := normalized_height_zero_selects_actual_branch ht ha hA hd hperiod hr hend hconj hP hzero
  have han := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  have hsimple : (rhombicPeriodPair t ht).derivWeierstrassP a ≠ 0 :=
    (rhombic_weierstrassP_critical_iff_of_pos ht ht han).not.mpr
      (hp.height_zero_not_two_torsion han hzero)
  obtain ⟨c',hc',hform'⟩ := hbranch.2.2
  exact ⟨a,c',ha,hc',hbranch.1,hbranch.2.1,hform',hsimple⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.symmetric_null_height_data_reduction
