import TwoAxisHelicoid.SlopingFluxRectangle
import TwoAxisHelicoid.OriginalCycleHorizontalFlux
import TwoAxisHelicoid.CertifiedGlobalImmersion

namespace TwoAxisHelicoid
open Complex Set

/-- A literally closed path on the certified punctured torus has nonzero
horizontal flux for the coordinate differential of its Euclidean position
map. No assertion about abstract embedded surfaces is needed. -/
theorem certified_torus_has_intrinsic_nonvertical_flux : HasIntrinsicNonverticalFlux certifiedPeriodPair
    (fun x => WithLp.ofLp (certifiedTorusImmersion x)) := by
  let p := certifiedClosedParameters
  apply actual_torus_nonvertical_flux_of_original_imaginary p.height_pos p.abscissa_mem (by norm_num : (1:ℝ) ≠ 0)
    p.vertical_closed p.horizontal_closed
  have h := original_sloping_imaginary_on_root_rectangle
    (Ioo_subset_Icc_self certifiedClosedParameters_bounds.1) (Ioo_subset_Icc_self certifiedClosedParameters_bounds.2)
  exact (h.trans_lt (by norm_num)).ne

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_torus_has_intrinsic_nonvertical_flux
