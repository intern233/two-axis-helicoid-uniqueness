import TwoAxisHelicoid.PdfHorizontalRowTransfer
import TwoAxisHelicoid.PositiveChordBox1041
import TwoAxisHelicoid.PositiveChordBox1042
import TwoAxisHelicoid.PositiveChordBox1043
import TwoAxisHelicoid.PositiveChordBox1044

namespace TwoAxisHelicoid.PdfHorizontal
open ComplexBall
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block1041 : Block := ⟨⟨(107/160),(27/40)⟩,⟨(71451926790979481073/73786976294838206464),(254927468325397188037/73786976294838206464)⟩,⟨(-144248321446408755055/36893488147419103232),(-52510550679199901573/36893488147419103232)⟩,⟨(2259223/4194304),(2285967/4194304)⟩⟩

theorem block1041_rectangle_sound : block1041.RectSound := by
  intro t a ht ha
  change (((107/160):ℚ):ℝ)≤t ∧ t≤(((27/40):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2259223/4194304):ℚ):ℝ)≤a ∧ a≤(((2285967/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1041Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1041Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1041Parameters positiveChordBox1041Parameters_valid hbt hba
    positiveChordBox1041Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1041Radius positiveChordBox1041Cells positiveChordBox1041Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1041Boundary positiveChordBox1041Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1041Boundary positiveChordBox1041Cells).radius=(71451926790979481073/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1041Boundary positiveChordBox1041Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1041Boundary positiveChordBox1041Cells).radius=(254927468325397188037/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1041Boundary positiveChordBox1041Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1041Boundary positiveChordBox1041Cells).radius=(-144248321446408755055/36893488147419103232) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1041Boundary positiveChordBox1041Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1041Boundary positiveChordBox1041Cells).radius=(-52510550679199901573/36893488147419103232) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1041_sound : block1041.Sound := by
  intro t ht
  exact block1041_rectangle_sound t (verticalA t) ht (positiveChordBox1041_vertical_enclosure ht.1 ht.2)

def block1042 : Block := ⟨⟨(27/40),(109/160)⟩,⟨(33143731857717938483/36893488147419103232),(124389884621830208475/36893488147419103232)⟩,⟨(-290320045292625446817/73786976294838206464),(-107827739764400906833/73786976294838206464)⟩,⟨(1132439/2097152),(2291507/4194304)⟩⟩

theorem block1042_rectangle_sound : block1042.RectSound := by
  intro t a ht ha
  change (((27/40):ℚ):ℝ)≤t ∧ t≤(((109/160):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1132439/2097152):ℚ):ℝ)≤a ∧ a≤(((2291507/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1042Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1042Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1042Parameters positiveChordBox1042Parameters_valid hbt hba
    positiveChordBox1042Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1042Radius positiveChordBox1042Cells positiveChordBox1042Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1042Boundary positiveChordBox1042Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1042Boundary positiveChordBox1042Cells).radius=(33143731857717938483/36893488147419103232) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1042Boundary positiveChordBox1042Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1042Boundary positiveChordBox1042Cells).radius=(124389884621830208475/36893488147419103232) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1042Boundary positiveChordBox1042Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1042Boundary positiveChordBox1042Cells).radius=(-290320045292625446817/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1042Boundary positiveChordBox1042Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1042Boundary positiveChordBox1042Cells).radius=(-107827739764400906833/73786976294838206464) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1042_sound : block1042.Sound := by
  intro t ht
  exact block1042_rectangle_sound t (verticalA t) ht (positiveChordBox1042_vertical_enclosure ht.1 ht.2)

def block1043 : Block := ⟨⟨(109/160),(11/16)⟩,⟨(61157623820079190639/73786976294838206464),(121319595076595798239/36893488147419103232)⟩,⟨(-584073493678716328799/147573952589676412928),(-221110361012491517121/147573952589676412928)⟩,⟨(2270623/4194304),(1148571/2097152)⟩⟩

theorem block1043_rectangle_sound : block1043.RectSound := by
  intro t a ht ha
  change (((109/160):ℚ):ℝ)≤t ∧ t≤(((11/16):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2270623/4194304):ℚ):ℝ)≤a ∧ a≤(((1148571/2097152):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1043Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1043Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1043Parameters positiveChordBox1043Parameters_valid hbt hba
    positiveChordBox1043Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1043Radius positiveChordBox1043Cells positiveChordBox1043Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1043Boundary positiveChordBox1043Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1043Boundary positiveChordBox1043Cells).radius=(61157623820079190639/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1043Boundary positiveChordBox1043Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1043Boundary positiveChordBox1043Cells).radius=(121319595076595798239/36893488147419103232) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1043Boundary positiveChordBox1043Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1043Boundary positiveChordBox1043Cells).radius=(-584073493678716328799/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1043Boundary positiveChordBox1043Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1043Boundary positiveChordBox1043Cells).radius=(-221110361012491517121/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1043_sound : block1043.Sound := by
  intro t ht
  exact block1043_rectangle_sound t (verticalA t) ht (positiveChordBox1043_vertical_enclosure ht.1 ht.2)

def block1044 : Block := ⟨⟨(11/16),(111/160)⟩,⟨(112119546162092195799/147573952589676412928),(473013729489584240233/147573952589676412928)⟩,⟨(-293646691521413211407/73786976294838206464),(-56599799928833594595/36893488147419103232)⟩,⟨(1138229/2097152),(287859/524288)⟩⟩

theorem block1044_rectangle_sound : block1044.RectSound := by
  intro t a ht ha
  change (((11/16):ℚ):ℝ)≤t ∧ t≤(((111/160):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1138229/2097152):ℚ):ℝ)≤a ∧ a≤(((287859/524288):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1044Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1044Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1044Parameters positiveChordBox1044Parameters_valid hbt hba
    positiveChordBox1044Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1044Radius positiveChordBox1044Cells positiveChordBox1044Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1044Boundary positiveChordBox1044Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1044Boundary positiveChordBox1044Cells).radius=(112119546162092195799/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1044Boundary positiveChordBox1044Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1044Boundary positiveChordBox1044Cells).radius=(473013729489584240233/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1044Boundary positiveChordBox1044Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1044Boundary positiveChordBox1044Cells).radius=(-293646691521413211407/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1044Boundary positiveChordBox1044Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1044Boundary positiveChordBox1044Cells).radius=(-56599799928833594595/36893488147419103232) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1044_sound : block1044.Sound := by
  intro t ht
  exact block1044_rectangle_sound t (verticalA t) ht (positiveChordBox1044_vertical_enclosure ht.1 ht.2)

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.block1041_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1042_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1043_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1044_sound
