import TwoAxisHelicoid.CertifiedSlopingHorizontalFlux
import TwoAxisHelicoid.ActualTorusRigidityHypotheses
import TwoAxisHelicoid.TorusSpatialConormalFlux

namespace TwoAxisHelicoid
open Complex Set

/-- The first spatial component of the conormal arclength integral on a
closed sloping generator of the certified surface is at least 1/32 for
the chosen positive unit scale and right-conormal orientation. -/
theorem certified_horizontal_conormal_period_lower_bound :
    ∃ (q : PuncturedPeriodTorus certifiedPeriodPair) (γ : Path q q) (v : ℝ),
      TorusSpatialConormalIntegral certifiedPeriodPair (fun x => WithLp.ofLp (certifiedTorusImmersion x)) 0 γ v ∧
        (1/32:ℝ) ≤ v := by
  let p := certifiedClosedParameters
  let X := fun q => WithLp.ofLp (certifiedTorusImmersion q)
  have h := actual_torus_rigidity_hypotheses p.height_pos p.abscissa_mem (by norm_num : (1:ℝ) ≠ 0)
    p.vertical_closed p.horizontal_closed
  have hd := actual_torus_pulled_coordinate_differential p.height_pos p.abscissa_mem (by norm_num : (1:ℝ) ≠ 0)
    p.vertical_closed p.horizontal_closed
  obtain ⟨q,γ,hγ⟩ := original_sloping_horizontal_quotient_period p.height_pos X hd
  have hc := original_sloping_imaginary_on_root_rectangle (Ioo_subset_Icc_self certifiedClosedParameters_bounds.1)
    (Ioo_subset_Icc_self certifiedClosedParameters_bounds.2)
  let w : ℂ := -(1:ℂ)*originalSlopingPeriod p.t p.a
  refine ⟨q,γ,w.im,(torus_spatial_conormal_integral_iff certifiedPeriodPair X h.1 γ 0 w.im).mpr ⟨w,hγ,rfl⟩,?_⟩
  simpa only [w,neg_one_mul,Complex.neg_im,neg_neg] using (neg_le_neg hc)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_horizontal_conormal_period_lower_bound
