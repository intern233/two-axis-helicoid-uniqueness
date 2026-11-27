import TwoAxisHelicoid.SlopingFluxIntegral
import TwoAxisHelicoid.SlopingFluxRootParameters
import TwoAxisHelicoid.TraceDataSlopingFluxCover

namespace TwoAxisHelicoid
open Complex Set

/-- Uniform strict sign for the imaginary part of the actual manuscript
cycle on the entire rectangle containing the certified closed parameters. -/
theorem original_sloping_imaginary_on_root_rectangle {t a : ℝ} (ht : t ∈ Icc (rootTLower:ℝ) rootTUpper)
    (ha : a ∈ Icc (rootALower:ℝ) rootAUpper) : (originalSlopingPeriod t a).im ≤ -(1/32:ℝ) := by
  obtain ⟨hmin,hq,hA,hc,hv⟩ := sloping_flux_root_parameter_enclosures ht ha
  apply original_sloping_imaginary_negative_of_reflected ((by norm_num [rootTLower] : (0:ℝ) < rootTLower).trans_le ht.1)
  have h : TraceData.CheckedSlopingFluxCover (TraceData.horizontalSetupOf slopingFluxAnalyticSetup)
      TraceData.slopingFluxParams TraceData.slopingFluxWeight.output 0 1 := by
    rw [show TraceData.horizontalSetupOf slopingFluxAnalyticSetup = TraceData.slopingFluxDataSetup from rfl]
    simpa only [zero_div,div_one] using TraceData.original_sloping_flux_checked_cover
  have hc' := h.sound slopingFluxAnalyticSetup slopingFluxAnalyticSetup_valid TraceData.slopingFluxParams
    TraceData.slopingFluxWeight.output hmin hq hA hc hv
  simpa only [Rat.cast_zero,Rat.cast_one] using hc'

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_sloping_imaginary_on_root_rectangle
