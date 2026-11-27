import TwoAxisHelicoid.PdfHorizontalRowTransfer
import TwoAxisHelicoid.PositiveChordBox1092
import TwoAxisHelicoid.PositiveChordBox1093
import TwoAxisHelicoid.PositiveChordBox1094
import TwoAxisHelicoid.PositiveChordBox1095

namespace TwoAxisHelicoid.PdfHorizontal
open ComplexBall
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block1092 : Block := ⟨⟨(1081/1280),(541/640)⟩,⟨(7294125012925061751/73786976294838206464),(24777305246007641973/73786976294838206464)⟩,⟨(-232281424353739654095/73786976294838206464),(-214798244120657073873/73786976294838206464)⟩,⟨(2460273/4194304),(2463371/4194304)⟩⟩

theorem block1092_rectangle_sound : block1092.RectSound := by
  intro t a ht ha
  change (((1081/1280):ℚ):ℝ)≤t ∧ t≤(((541/640):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2460273/4194304):ℚ):ℝ)≤a ∧ a≤(((2463371/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1092Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1092Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1092Parameters positiveChordBox1092Parameters_valid hbt hba
    positiveChordBox1092Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1092Radius positiveChordBox1092Cells positiveChordBox1092Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1092Boundary positiveChordBox1092Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1092Boundary positiveChordBox1092Cells).radius=(7294125012925061751/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1092Boundary positiveChordBox1092Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1092Boundary positiveChordBox1092Cells).radius=(24777305246007641973/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1092Boundary positiveChordBox1092Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1092Boundary positiveChordBox1092Cells).radius=(-232281424353739654095/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1092Boundary positiveChordBox1092Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1092Boundary positiveChordBox1092Cells).radius=(-214798244120657073873/73786976294838206464) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1092_sound : block1092.Sound := by
  intro t ht
  exact block1092_rectangle_sound t (verticalA t) ht (positiveChordBox1092_vertical_enclosure ht.1 ht.2)

def block1093 : Block := ⟨⟨(541/640),(1083/1280)⟩,⟨(6704099495931708017/73786976294838206464),(24168939153631099811/73786976294838206464)⟩,⟨(-464436027184165351695/147573952589676412928),(-429506347868766568107/147573952589676412928)⟩,⟨(1230645/2097152),(616097/1048576)⟩⟩

theorem block1093_rectangle_sound : block1093.RectSound := by
  intro t a ht ha
  change (((541/640):ℚ):ℝ)≤t ∧ t≤(((1083/1280):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1230645/2097152):ℚ):ℝ)≤a ∧ a≤(((616097/1048576):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1093Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1093Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1093Parameters positiveChordBox1093Parameters_valid hbt hba
    positiveChordBox1093Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1093Radius positiveChordBox1093Cells positiveChordBox1093Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1093Boundary positiveChordBox1093Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1093Boundary positiveChordBox1093Cells).radius=(6704099495931708017/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1093Boundary positiveChordBox1093Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1093Boundary positiveChordBox1093Cells).radius=(24168939153631099811/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1093Boundary positiveChordBox1093Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1093Boundary positiveChordBox1093Cells).radius=(-464436027184165351695/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1093Boundary positiveChordBox1093Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1093Boundary positiveChordBox1093Cells).radius=(-429506347868766568107/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1093_sound : block1093.Sound := by
  intro t ht
  exact block1093_rectangle_sound t (verticalA t) ht (positiveChordBox1093_vertical_enclosure ht.1 ht.2)

def block1094 : Block := ⟨⟨(1083/1280),(271/320)⟩,⟨(6115739208793326837/73786976294838206464),(5890140431176830067/18446744073709551616)⟩,⟨(-232152321753167003443/73786976294838206464),(-53676874809313252503/18446744073709551616)⟩,⟨(2462309/4194304),(1232703/2097152)⟩⟩

theorem block1094_rectangle_sound : block1094.RectSound := by
  intro t a ht ha
  change (((1083/1280):ℚ):ℝ)≤t ∧ t≤(((271/320):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2462309/4194304):ℚ):ℝ)≤a ∧ a≤(((1232703/2097152):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1094Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1094Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1094Parameters positiveChordBox1094Parameters_valid hbt hba
    positiveChordBox1094Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1094Radius positiveChordBox1094Cells positiveChordBox1094Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1094Boundary positiveChordBox1094Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1094Boundary positiveChordBox1094Cells).radius=(6115739208793326837/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1094Boundary positiveChordBox1094Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1094Boundary positiveChordBox1094Cells).radius=(5890140431176830067/18446744073709551616) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1094Boundary positiveChordBox1094Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1094Boundary positiveChordBox1094Cells).radius=(-232152321753167003443/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1094Boundary positiveChordBox1094Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1094Boundary positiveChordBox1094Cells).radius=(-53676874809313252503/18446744073709551616) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1094_sound : block1094.Sound := by
  intro t ht
  exact block1094_rectangle_sound t (verticalA t) ht (positiveChordBox1094_vertical_enclosure ht.1 ht.2)

def block1095 : Block := ⟨⟨(271/320),(217/256)⟩,⟨(1381842056968216253/18446744073709551616),(5738463831470053357/18446744073709551616)⟩,⟨(-464172062615330664313/147573952589676412928),(-429319088419315967481/147573952589676412928)⟩,⟨(2463329/4194304),(1233213/2097152)⟩⟩

theorem block1095_rectangle_sound : block1095.RectSound := by
  intro t a ht ha
  change (((271/320):ℚ):ℝ)≤t ∧ t≤(((217/256):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2463329/4194304):ℚ):ℝ)≤a ∧ a≤(((1233213/2097152):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1095Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1095Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1095Parameters positiveChordBox1095Parameters_valid hbt hba
    positiveChordBox1095Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1095Radius positiveChordBox1095Cells positiveChordBox1095Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1095Boundary positiveChordBox1095Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1095Boundary positiveChordBox1095Cells).radius=(1381842056968216253/18446744073709551616) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1095Boundary positiveChordBox1095Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1095Boundary positiveChordBox1095Cells).radius=(5738463831470053357/18446744073709551616) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1095Boundary positiveChordBox1095Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1095Boundary positiveChordBox1095Cells).radius=(-464172062615330664313/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1095Boundary positiveChordBox1095Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1095Boundary positiveChordBox1095Cells).radius=(-429319088419315967481/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1095_sound : block1095.Sound := by
  intro t ht
  exact block1095_rectangle_sound t (verticalA t) ht (positiveChordBox1095_vertical_enclosure ht.1 ht.2)

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.block1092_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1093_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1094_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1095_sound
