import TwoAxisHelicoid.CertifiedSpatialConormalPeriod
import TwoAxisHelicoid.GlobalPeriodUniqueness
import TwoAxisHelicoid.PrimitivePeriodNecessity

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

/-- The imaginary-period bound applies to every quotient immersion with
the basic coordinate differential. Single-valuedness supplies both
equations, and their global uniqueness places the data in the box. -/
theorem closed_basic_data_sloping_bound {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 1)
    (hc : c ≠ 0) (X : PuncturedPeriodTorus (rhombicPeriodPair t ht) → Fin 3 → ℝ)
    (hD : HasTwoAxisHelicoidCoordinateDifferential (puncturedTorusPullback (rhombicPeriodPair t ht) X) t a c ht) :
    (originalSlopingPeriod t a).im ≤ -(1/32:ℝ) := by
  obtain ⟨hG,hH⟩ := periodic_actual_primitive_period_equations ht ha hc hD
    (fun z _ w hw => puncturedTorusPullback_periodic _ X z w hw)
  let p := certifiedClosedParameters
  have e : (t,a) = (p.t,p.a) := existsUnique_actual_common_period_full_domain.unique
    ⟨ht,ha,hG,hH⟩ ⟨p.height_pos,p.abscissa_mem,p.vertical_closed,p.horizontal_closed⟩
  have et := congrArg Prod.fst e
  have ea := congrArg Prod.snd e
  change t = p.t at et
  change a = p.a at ea
  rw [et,ea]
  exact original_sloping_imaginary_on_root_rectangle (Ioo_subset_Icc_self certifiedClosedParameters_bounds.1)
    (Ioo_subset_Icc_self certifiedClosedParameters_bounds.2)

/-- A genuine closed spatial conormal period of any scale and any
single-valued normalized basic presentation has magnitude at least
`|c|/32`. Both signs of the height scale are included. -/
theorem closed_basic_data_horizontal_conormal_bound {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0:ℝ) 1) (hc : c ≠ 0) (X : PuncturedPeriodTorus (rhombicPeriodPair t ht) → Fin 3 → ℝ)
    (hD : HasTwoAxisHelicoidCoordinateDifferential (puncturedTorusPullback (rhombicPeriodPair t ht) X) t a c ht)
    (hX : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      (∀ j, HarmonicAt (fun w => puncturedTorusPullback (rhombicPeriodPair t ht) X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback (rhombicPeriodPair t ht) X) z) :
    ∃ (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) (γ : Path q q) (v : ℝ),
      TorusSpatialConormalIntegral (rhombicPeriodPair t ht) X 0 γ v ∧ |c|/32 ≤ |v| := by
  have hb := closed_basic_data_sloping_bound ht ha hc X hD
  obtain ⟨q,γ,hγ⟩ := original_sloping_horizontal_quotient_period ht X hD
  let w : ℂ := -(c:ℂ)*originalSlopingPeriod t a
  refine ⟨q,γ,w.im,(torus_spatial_conormal_integral_iff _ X hX γ 0 w.im).mpr ⟨w,hγ,rfl⟩,?_⟩
  have hv : w.im = -c*(originalSlopingPeriod t a).im := by simp [w,Complex.mul_im]
  rw [hv,abs_mul,abs_neg,abs_of_neg (hb.trans_lt (by norm_num))]
  nlinarith [mul_le_mul_of_nonneg_left (neg_le_neg hb) (abs_nonneg c)]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.closed_basic_data_horizontal_conormal_bound
