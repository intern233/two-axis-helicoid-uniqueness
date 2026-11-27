import TwoAxisHelicoid.PdfHorizontalRowTransfer
import TwoAxisHelicoid.PositiveChordBox1049
import TwoAxisHelicoid.PositiveChordBox1050
import TwoAxisHelicoid.PositiveChordBox1051
import TwoAxisHelicoid.PositiveChordBox1052

namespace TwoAxisHelicoid.PdfHorizontal
open ComplexBall
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block1049 : Block := ⟨⟨(23/32),(29/40)⟩,⟨(31031343551551455285/73786976294838206464),(102988621691896153457/36893488147419103232)⟩,⟨(-600105083648881391403/147573952589676412928),(-250213283984399688145/147573952589676412928)⟩,⟨(576747/1048576),(2332939/4194304)⟩⟩

theorem block1049_rectangle_sound : block1049.RectSound := by
  intro t a ht ha
  change (((23/32):ℚ):ℝ)≤t ∧ t≤(((29/40):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((576747/1048576):ℚ):ℝ)≤a ∧ a≤(((2332939/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1049Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1049Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1049Parameters positiveChordBox1049Parameters_valid hbt hba
    positiveChordBox1049Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1049Radius positiveChordBox1049Cells positiveChordBox1049Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1049Boundary positiveChordBox1049Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1049Boundary positiveChordBox1049Cells).radius=(31031343551551455285/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1049Boundary positiveChordBox1049Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1049Boundary positiveChordBox1049Cells).radius=(102988621691896153457/36893488147419103232) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1049Boundary positiveChordBox1049Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1049Boundary positiveChordBox1049Cells).radius=(-600105083648881391403/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1049Boundary positiveChordBox1049Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1049Boundary positiveChordBox1049Cells).radius=(-250213283984399688145/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1049_sound : block1049.Sound := by
  intro t ht
  exact block1049_rectangle_sound t (verticalA t) ht (positiveChordBox1049_vertical_enclosure ht.1 ht.2)

def block1050 : Block := ⟨⟨(29/40),(117/160)⟩,⟨(52236857976982120637/147573952589676412928),(399803924612800573189/147573952589676412928)⟩,⟨(-601995760361949927441/147573952589676412928),(-254428693726131474889/147573952589676412928)⟩,⟨(2313365/4194304),(2339235/4194304)⟩⟩

theorem block1050_rectangle_sound : block1050.RectSound := by
  intro t a ht ha
  change (((29/40):ℚ):ℝ)≤t ∧ t≤(((117/160):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2313365/4194304):ℚ):ℝ)≤a ∧ a≤(((2339235/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1050Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1050Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1050Parameters positiveChordBox1050Parameters_valid hbt hba
    positiveChordBox1050Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1050Radius positiveChordBox1050Cells positiveChordBox1050Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1050Boundary positiveChordBox1050Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1050Boundary positiveChordBox1050Cells).radius=(52236857976982120637/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1050Boundary positiveChordBox1050Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1050Boundary positiveChordBox1050Cells).radius=(399803924612800573189/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1050Boundary positiveChordBox1050Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1050Boundary positiveChordBox1050Cells).radius=(-601995760361949927441/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1050Boundary positiveChordBox1050Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1050Boundary positiveChordBox1050Cells).radius=(-254428693726131474889/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1050_sound : block1050.Sound := by
  intro t ht
  exact block1050_rectangle_sound t (verticalA t) ht (positiveChordBox1050_vertical_enclosure ht.1 ht.2)

def block1051 : Block := ⟨⟨(117/160),(59/80)⟩,⟨(21236534472650665015/73786976294838206464),(193840124959596711583/73786976294838206464)⟩,⟨(-603661136280194110173/147573952589676412928),(-258453955306302017037/147573952589676412928)⟩,⟨(2319833/4194304),(1172813/2097152)⟩⟩

theorem block1051_rectangle_sound : block1051.RectSound := by
  intro t a ht ha
  change (((117/160):ℚ):ℝ)≤t ∧ t≤(((59/80):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2319833/4194304):ℚ):ℝ)≤a ∧ a≤(((1172813/2097152):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1051Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1051Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1051Parameters positiveChordBox1051Parameters_valid hbt hba
    positiveChordBox1051Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1051Radius positiveChordBox1051Cells positiveChordBox1051Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1051Boundary positiveChordBox1051Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1051Boundary positiveChordBox1051Cells).radius=(21236534472650665015/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1051Boundary positiveChordBox1051Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1051Boundary positiveChordBox1051Cells).radius=(193840124959596711583/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1051Boundary positiveChordBox1051Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1051Boundary positiveChordBox1051Cells).radius=(-603661136280194110173/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1051Boundary positiveChordBox1051Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1051Boundary positiveChordBox1051Cells).radius=(-258453955306302017037/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1051_sound : block1051.Sound := by
  intro t ht
  exact block1051_rectangle_sound t (verticalA t) ht (positiveChordBox1051_vertical_enclosure ht.1 ht.2)

def block1052 : Block := ⟨⟨(59/80),(119/160)⟩,⟨(8192781462270746423/36893488147419103232),(23474287469748824273/9223372036854775808)⟩,⟨(-605102858738146066503/147573952589676412928),(-262285385071247863827/147573952589676412928)⟩,⟨(2326391/4194304),(2352111/4194304)⟩⟩

theorem block1052_rectangle_sound : block1052.RectSound := by
  intro t a ht ha
  change (((59/80):ℚ):ℝ)≤t ∧ t≤(((119/160):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2326391/4194304):ℚ):ℝ)≤a ∧ a≤(((2352111/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1052Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1052Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1052Parameters positiveChordBox1052Parameters_valid hbt hba
    positiveChordBox1052Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1052Radius positiveChordBox1052Cells positiveChordBox1052Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1052Boundary positiveChordBox1052Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1052Boundary positiveChordBox1052Cells).radius=(8192781462270746423/36893488147419103232) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1052Boundary positiveChordBox1052Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1052Boundary positiveChordBox1052Cells).radius=(23474287469748824273/9223372036854775808) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1052Boundary positiveChordBox1052Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1052Boundary positiveChordBox1052Cells).radius=(-605102858738146066503/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1052Boundary positiveChordBox1052Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1052Boundary positiveChordBox1052Cells).radius=(-262285385071247863827/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1052_sound : block1052.Sound := by
  intro t ht
  exact block1052_rectangle_sound t (verticalA t) ht (positiveChordBox1052_vertical_enclosure ht.1 ht.2)

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.block1049_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1050_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1051_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1052_sound
