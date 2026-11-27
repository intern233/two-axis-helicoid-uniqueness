import TwoAxisHelicoid.PdfHorizontalRowTransfer
import TwoAxisHelicoid.PositiveChordBox1081
import TwoAxisHelicoid.PositiveChordBox1089
import TwoAxisHelicoid.PositiveChordBox1090
import TwoAxisHelicoid.PositiveChordBox1091

namespace TwoAxisHelicoid.PdfHorizontal
open ComplexBall
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block1081 : Block := ⟨⟨(531/640),(133/160)⟩,⟨(9262381963443308855/73786976294838206464),(5658820102271201513/9223372036854775808)⟩,⟨(-242283857051287632621/73786976294838206464),(-51568919549140332343/18446744073709551616)⟩,⟨(1220083/2097152),(611595/1048576)⟩⟩

theorem block1081_rectangle_sound : block1081.RectSound := by
  intro t a ht ha
  change (((531/640):ℚ):ℝ)≤t ∧ t≤(((133/160):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1220083/2097152):ℚ):ℝ)≤a ∧ a≤(((611595/1048576):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1081Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1081Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1081Parameters positiveChordBox1081Parameters_valid hbt hba
    positiveChordBox1081Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1081Radius positiveChordBox1081Cells positiveChordBox1081Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1081Boundary positiveChordBox1081Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1081Boundary positiveChordBox1081Cells).radius=(9262381963443308855/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1081Boundary positiveChordBox1081Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1081Boundary positiveChordBox1081Cells).radius=(5658820102271201513/9223372036854775808) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1081Boundary positiveChordBox1081Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1081Boundary positiveChordBox1081Cells).radius=(-242283857051287632621/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1081Boundary positiveChordBox1081Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1081Boundary positiveChordBox1081Cells).radius=(-51568919549140332343/18446744073709551616) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1081_sound : block1081.Sound := by
  intro t ht
  exact block1081_rectangle_sound t (verticalA t) ht (positiveChordBox1081_vertical_enclosure ht.1 ht.2)

def block1089 : Block := ⟨⟨(539/640),(1079/1280)⟩,⟨(18138584409761365897/147573952589676412928),(53214729947888397503/147573952589676412928)⟩,⟨(-116231520807288040127/36893488147419103232),(-214924968845512564451/73786976294838206464)⟩,⟨(1228615/2097152),(307541/524288)⟩⟩

theorem block1089_rectangle_sound : block1089.RectSound := by
  intro t a ht ha
  change (((539/640):ℚ):ℝ)≤t ∧ t≤(((1079/1280):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1228615/2097152):ℚ):ℝ)≤a ∧ a≤(((307541/524288):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1089Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1089Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1089Parameters positiveChordBox1089Parameters_valid hbt hba
    positiveChordBox1089Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1089Radius positiveChordBox1089Cells positiveChordBox1089Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1089Boundary positiveChordBox1089Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1089Boundary positiveChordBox1089Cells).radius=(18138584409761365897/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1089Boundary positiveChordBox1089Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1089Boundary positiveChordBox1089Cells).radius=(53214729947888397503/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1089Boundary positiveChordBox1089Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1089Boundary positiveChordBox1089Cells).radius=(-116231520807288040127/36893488147419103232) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1089Boundary positiveChordBox1089Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1089Boundary positiveChordBox1089Cells).radius=(-214924968845512564451/73786976294838206464) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1089_sound : block1089.Sound := by
  intro t ht
  exact block1089_rectangle_sound t (verticalA t) ht (positiveChordBox1089_vertical_enclosure ht.1 ht.2)

def block1090 : Block := ⟨⟨(1079/1280),(27/32)⟩,⟨(16951828759778933411/147573952589676412928),(51994855441349225987/147573952589676412928)⟩,⟨(-464809739463202725655/147573952589676412928),(-429766712781632433079/147573952589676412928)⟩,⟨(1229121/2097152),(2461341/4194304)⟩⟩

theorem block1090_rectangle_sound : block1090.RectSound := by
  intro t a ht ha
  change (((1079/1280):ℚ):ℝ)≤t ∧ t≤(((27/32):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1229121/2097152):ℚ):ℝ)≤a ∧ a≤(((2461341/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1090Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1090Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1090Parameters positiveChordBox1090Parameters_valid hbt hba
    positiveChordBox1090Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1090Radius positiveChordBox1090Cells positiveChordBox1090Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1090Boundary positiveChordBox1090Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1090Boundary positiveChordBox1090Cells).radius=(16951828759778933411/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1090Boundary positiveChordBox1090Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1090Boundary positiveChordBox1090Cells).radius=(51994855441349225987/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1090Boundary positiveChordBox1090Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1090Boundary positiveChordBox1090Cells).radius=(-464809739463202725655/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1090Boundary positiveChordBox1090Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1090Boundary positiveChordBox1090Cells).radius=(-429766712781632433079/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1090_sound : block1090.Sound := by
  intro t ht
  exact block1090_rectangle_sound t (verticalA t) ht (positiveChordBox1090_vertical_enclosure ht.1 ht.2)

def block1091 : Block := ⟨⟨(27/32),(1081/1280)⟩,⟨(15770061324297550729/147573952589676412928),(50773069464931709895/147573952589676412928)⟩,⟨(-232343450452783668079/73786976294838206464),(-13427621648904161781/4611686018427387904)⟩,⟨(2459257/4194304),(2462355/4194304)⟩⟩

theorem block1091_rectangle_sound : block1091.RectSound := by
  intro t a ht ha
  change (((27/32):ℚ):ℝ)≤t ∧ t≤(((1081/1280):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2459257/4194304):ℚ):ℝ)≤a ∧ a≤(((2462355/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1091Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1091Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1091Parameters positiveChordBox1091Parameters_valid hbt hba
    positiveChordBox1091Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1091Radius positiveChordBox1091Cells positiveChordBox1091Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1091Boundary positiveChordBox1091Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1091Boundary positiveChordBox1091Cells).radius=(15770061324297550729/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1091Boundary positiveChordBox1091Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1091Boundary positiveChordBox1091Cells).radius=(50773069464931709895/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1091Boundary positiveChordBox1091Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1091Boundary positiveChordBox1091Cells).radius=(-232343450452783668079/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1091Boundary positiveChordBox1091Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1091Boundary positiveChordBox1091Cells).radius=(-13427621648904161781/4611686018427387904) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1091_sound : block1091.Sound := by
  intro t ht
  exact block1091_rectangle_sound t (verticalA t) ht (positiveChordBox1091_vertical_enclosure ht.1 ht.2)

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.block1081_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1089_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1090_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1091_sound
