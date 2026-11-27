import TwoAxisHelicoid.PdfHorizontalRowTransfer
import TwoAxisHelicoid.PositiveChordBox1053
import TwoAxisHelicoid.PositiveChordBox1056
import TwoAxisHelicoid.PositiveChordBox1057
import TwoAxisHelicoid.PositiveChordBox1058

namespace TwoAxisHelicoid.PdfHorizontal
open ComplexBall
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block1053 : Block := ⟨⟨(119/160),(3/4)⟩,⟨(11568374609553300919/73786976294838206464),(181763831794213072125/73786976294838206464)⟩,⟨(-303158145141328509171/73786976294838206464),(-132962687956668737965/73786976294838206464)⟩,⟨(145815/262144),(2358691/4194304)⟩⟩

theorem block1053_rectangle_sound : block1053.RectSound := by
  intro t a ht ha
  change (((119/160):ℚ):ℝ)≤t ∧ t≤(((3/4):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((145815/262144):ℚ):ℝ)≤a ∧ a≤(((2358691/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1053Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1053Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1053Parameters positiveChordBox1053Parameters_valid hbt hba
    positiveChordBox1053Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1053Radius positiveChordBox1053Cells positiveChordBox1053Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1053Boundary positiveChordBox1053Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1053Boundary positiveChordBox1053Cells).radius=(11568374609553300919/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1053Boundary positiveChordBox1053Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1053Boundary positiveChordBox1053Cells).radius=(181763831794213072125/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1053Boundary positiveChordBox1053Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1053Boundary positiveChordBox1053Cells).radius=(-303158145141328509171/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1053Boundary positiveChordBox1053Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1053Boundary positiveChordBox1053Cells).radius=(-132962687956668737965/73786976294838206464) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1053_sound : block1053.Sound := by
  intro t ht
  exact block1053_rectangle_sound t (verticalA t) ht (positiveChordBox1053_vertical_enclosure ht.1 ht.2)

def block1056 : Block := ⟨⟨(61/80),(49/64)⟩,⟨(83855461677334489593/147573952589676412928),(243702216610655636797/147573952589676412928)⟩,⟨(-130408266209065464679/36893488147419103232),(-45223288737867588939/18446744073709551616)⟩,⟨(589549/1048576),(2370863/4194304)⟩⟩

theorem block1056_rectangle_sound : block1056.RectSound := by
  intro t a ht ha
  change (((61/80):ℚ):ℝ)≤t ∧ t≤(((49/64):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((589549/1048576):ℚ):ℝ)≤a ∧ a≤(((2370863/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1056Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1056Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1056Parameters positiveChordBox1056Parameters_valid hbt hba
    positiveChordBox1056Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1056Radius positiveChordBox1056Cells positiveChordBox1056Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1056Boundary positiveChordBox1056Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1056Boundary positiveChordBox1056Cells).radius=(83855461677334489593/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1056Boundary positiveChordBox1056Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1056Boundary positiveChordBox1056Cells).radius=(243702216610655636797/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1056Boundary positiveChordBox1056Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1056Boundary positiveChordBox1056Cells).radius=(-130408266209065464679/36893488147419103232) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1056Boundary positiveChordBox1056Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1056Boundary positiveChordBox1056Cells).radius=(-45223288737867588939/18446744073709551616) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1056_sound : block1056.Sound := by
  intro t ht
  exact block1056_rectangle_sound t (verticalA t) ht (positiveChordBox1056_vertical_enclosure ht.1 ht.2)

def block1057 : Block := ⟨⟨(49/64),(123/160)⟩,⟨(39411232862152415103/73786976294838206464),(930010340041810297/576460752303423488)⟩,⟨(-130546194537180909055/36893488147419103232),(-181462298411162515197/73786976294838206464)⟩,⟨(295209/524288),(2374325/4194304)⟩⟩

theorem block1057_rectangle_sound : block1057.RectSound := by
  intro t a ht ha
  change (((49/64):ℚ):ℝ)≤t ∧ t≤(((123/160):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((295209/524288):ℚ):ℝ)≤a ∧ a≤(((2374325/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1057Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1057Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1057Parameters positiveChordBox1057Parameters_valid hbt hba
    positiveChordBox1057Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1057Radius positiveChordBox1057Cells positiveChordBox1057Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1057Boundary positiveChordBox1057Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1057Boundary positiveChordBox1057Cells).radius=(39411232862152415103/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1057Boundary positiveChordBox1057Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1057Boundary positiveChordBox1057Cells).radius=(930010340041810297/576460752303423488) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1057Boundary positiveChordBox1057Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1057Boundary positiveChordBox1057Cells).radius=(-130546194537180909055/36893488147419103232) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1057Boundary positiveChordBox1057Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1057Boundary positiveChordBox1057Cells).radius=(-181462298411162515197/73786976294838206464) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1057_sound : block1057.Sound := by
  intro t ht
  exact block1057_rectangle_sound t (verticalA t) ht (positiveChordBox1057_vertical_enclosure ht.1 ht.2)

def block1058 : Block := ⟨⟨(123/160),(247/320)⟩,⟨(73805517736252580459/147573952589676412928),(232477890909650525559/147573952589676412928)⟩,⟨(-65335405422756895943/18446744073709551616),(-91002717552164305611/36893488147419103232)⟩,⟨(2365171/4194304),(2377811/4194304)⟩⟩

theorem block1058_rectangle_sound : block1058.RectSound := by
  intro t a ht ha
  change (((123/160):ℚ):ℝ)≤t ∧ t≤(((247/320):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2365171/4194304):ℚ):ℝ)≤a ∧ a≤(((2377811/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1058Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1058Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1058Parameters positiveChordBox1058Parameters_valid hbt hba
    positiveChordBox1058Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1058Radius positiveChordBox1058Cells positiveChordBox1058Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1058Boundary positiveChordBox1058Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1058Boundary positiveChordBox1058Cells).radius=(73805517736252580459/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1058Boundary positiveChordBox1058Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1058Boundary positiveChordBox1058Cells).radius=(232477890909650525559/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1058Boundary positiveChordBox1058Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1058Boundary positiveChordBox1058Cells).radius=(-65335405422756895943/18446744073709551616) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1058Boundary positiveChordBox1058Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1058Boundary positiveChordBox1058Cells).radius=(-91002717552164305611/36893488147419103232) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1058_sound : block1058.Sound := by
  intro t ht
  exact block1058_rectangle_sound t (verticalA t) ht (positiveChordBox1058_vertical_enclosure ht.1 ht.2)

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.block1053_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1056_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1057_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1058_sound
