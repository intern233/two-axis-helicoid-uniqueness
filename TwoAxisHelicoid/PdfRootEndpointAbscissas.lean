import TwoAxisHelicoid.PdfRootVerticalExact
import TwoAxisHelicoid.VerticalBranchContinuity

namespace TwoAxisHelicoid
open Set

private theorem bracket {t l u : ℝ} (ht : t∈Ioo 0 ellipticVerticalUpper)
    (hl : l∈Ioo (0:ℝ) 1) (hu : u∈Ioo (0:ℝ) 1)
    (pos : 0<(thetaG t l).re) (neg : (thetaG t u).re<0) :
    verticalA t∈Ioo l u := by
  obtain ⟨inside,zero⟩ := verticalA_spec ht
  have zr : (thetaG t (verticalA t)).re=0 := by rw [zero];rfl
  have anti := (thetaG_strictAnti_unit_of_pos ht.1).antitoneOn
  constructor
  · by_contra! h
    have le := anti inside hl h
    change (thetaG t l).re≤(thetaG t (verticalA t)).re at le
    linarith
  · by_contra! h
    have le := anti hu inside h
    change (thetaG t (verticalA t)).re≤(thetaG t u).re at le
    linarith

/-- The vertical branch at each of the two exact heights lies strictly
inside the very narrow abscissa interval supplied to the horizontal
integration in the original root attachment. -/
theorem pdf_root_endpoint_narrow_abscissas :
    verticalA ((54139230899/62500000000:ℚ):ℝ)∈Ioo ((1469895579284285760424119244853/2475880078570760549798248448000:ℚ):ℝ) ((1469895579284285760424119248853/2475880078570760549798248448000:ℚ):ℝ) ∧
    verticalA ((173245538877/200000000000:ℚ):ℝ)∈Ioo ((4409686737855254420087965714223/7427640235712281649394745344000:ℚ):ℝ) ((4409686737855254420087965726223/7427640235712281649394745344000:ℚ):ℝ) := by
  obtain ⟨ld,lu,rd,ru⟩ := pdf_root_actual_vertical_endpoint_intervals
  constructor
  · apply bracket ⟨by norm_num, lt_trans (by norm_num) ellipticVerticalUpper_location.1⟩
      (by constructor <;> norm_num) (by constructor <;> norm_num)
    · exact lt_of_lt_of_le (by norm_num) ld.1
    · exact lt_of_le_of_lt lu.2 (by norm_num)
  · apply bracket ⟨by norm_num, lt_trans (by norm_num) ellipticVerticalUpper_location.1⟩
      (by constructor <;> norm_num) (by constructor <;> norm_num)
    · exact lt_of_lt_of_le (by norm_num) rd.1
    · exact lt_of_le_of_lt ru.2 (by norm_num)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.pdf_root_endpoint_narrow_abscissas
