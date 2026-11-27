import TwoAxisHelicoid.OriginalPhysicalEndFromTwoPoles
import TwoAxisHelicoid.AsymptoticHorizontalRuling
import TwoAxisHelicoid.AxisHelicoidGauge

namespace TwoAxisHelicoid
open Complex Set

/-- The complete horizontal line specified as part of the original data
is exactly the ruling of the reference helicoid at its physical height.
Both the intersection with the vertical axis and the direction at that
height follow from the positional assumptions on the embedded surface. -/
theorem original_horizontal_line_equals_ruling (s : OriginalPositionallyAsymptoticHelicoid) :
    let P := s.axes.horizontalPoint
    let d := s.axes.horizontalDirection
    range (fun r : ℝ => P+r • ![d.re,d.im,0])=
      range (fun r : ℝ => axisRuledHelicoid I s.axes.pitch 0 ⟨r,P 2⟩) := by
  intro P d
  let V : Fin 3 → ℝ := ![d.re,d.im,0]
  let C : Fin 3 → ℝ := ![0,0,P 2]
  let angle := s.axes.pitch*P 2
  obtain ⟨a,meet⟩ := original_positional_axes_intersect s
  change P+a • V=C at meet
  have parallel := horizontal_line_tangent_to_ruling s.approaches P d s.axes.unit s.axes.horizontal
  obtain ⟨k,knz,scale⟩ := same_span_ruling_vector s.axes.unit angle parallel
  have ruling (r : ℝ) : axisRuledHelicoid I s.axes.pitch 0 ⟨r,P 2⟩=C+r • (k • V) := by
    rw [← scale,axisRuledHelicoid_standard_ruling]
    ext j
    fin_cases j <;> simp [C,angle]
  ext p
  constructor
  · rintro ⟨r,rfl⟩
    refine ⟨(r-a)/k,?_⟩
    change axisRuledHelicoid I s.axes.pitch 0 ⟨(r-a)/k,P 2⟩=P+r • V
    rw [ruling,smul_smul,div_mul_cancel₀ _ knz,← meet,sub_smul]
    abel
  · rintro ⟨r,rfl⟩
    refine ⟨a+r*k,?_⟩
    change P+(a+r*k) • V=axisRuledHelicoid I s.axes.pitch 0 ⟨r,P 2⟩
    rw [ruling,smul_smul,← meet,add_smul,add_assoc]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_horizontal_line_equals_ruling
