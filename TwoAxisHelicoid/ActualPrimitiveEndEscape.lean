import TwoAxisHelicoid.ActualHeightEndCoordinate
import TwoAxisHelicoid.HeightEndEscape

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology

/-- The actual explicit Weierstrass primitive leaves every bounded spatial
set as its parameter tends to the puncture. No properness or embeddedness
assumption occurs in this theorem. -/
theorem actual_coordinate_primitive_end_escape {X : ℂ → Fin 3 → ℝ} {t a c : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht) :
    Tendsto X (𝓝[≠] (0 : ℂ)) (cobounded (Fin 3 → ℝ)) := by
  obtain ⟨K,F,b,R₀,_,hF,hKL,hcoord⟩ := actual_primitive_height_end_coordinate ht ha hc hX
  have hY := height_normalized_helicoidal_end_tendsto (2*(a-1)/c) b R₀
    (fun z hz => (hcoord z hz).2.1) (fun z hz => (hcoord z hz).2.2) hF
  have hcomp := hY.comp (actualComplexHeight_tendsto (a := a) ht hc)
  have hrot : Tendsto (fun z => verticalRotation I (X z)) (𝓝[≠] (0 : ℂ))
      (cobounded (Fin 3 → ℝ)) := by
    apply hcomp.congr'
    filter_upwards [hKL] with z hz
    simp only [Function.comp_def,hz]
  apply tendsto_norm_atTop_iff_cobounded.mp
  simpa only [Function.comp_def,vertical_quarter_turn_norm] using
    (tendsto_norm_atTop_iff_cobounded.mpr hrot)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_coordinate_primitive_end_escape
