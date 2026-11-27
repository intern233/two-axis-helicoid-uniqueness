import TwoAxisHelicoid.PdfHorizontalRowTransfer
import TwoAxisHelicoid.PositiveChordBox1077
import TwoAxisHelicoid.PositiveChordBox1078
import TwoAxisHelicoid.PositiveChordBox1079
import TwoAxisHelicoid.PositiveChordBox1080

namespace TwoAxisHelicoid.PdfHorizontal
open ComplexBall
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block1077 : Block := ⟨⟨(527/640),(33/40)⟩,⟨(14050251853111131313/73786976294838206464),(12590007326357922419/18446744073709551616)⟩,⟨(-485192974280626442057/147573952589676412928),(-412573419375985325331/147573952589676412928)⟩,⟨(608075/1048576),(304815/524288)⟩⟩

theorem block1077_rectangle_sound : block1077.RectSound := by
  intro t a ht ha
  change (((527/640):ℚ):ℝ)≤t ∧ t≤(((33/40):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((608075/1048576):ℚ):ℝ)≤a ∧ a≤(((304815/524288):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1077Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1077Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1077Parameters positiveChordBox1077Parameters_valid hbt hba
    positiveChordBox1077Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1077Radius positiveChordBox1077Cells positiveChordBox1077Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1077Boundary positiveChordBox1077Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1077Boundary positiveChordBox1077Cells).radius=(14050251853111131313/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1077Boundary positiveChordBox1077Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1077Boundary positiveChordBox1077Cells).radius=(12590007326357922419/18446744073709551616) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1077Boundary positiveChordBox1077Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1077Boundary positiveChordBox1077Cells).radius=(-485192974280626442057/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1077Boundary positiveChordBox1077Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1077Boundary positiveChordBox1077Cells).radius=(-412573419375985325331/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1077_sound : block1077.Sound := by
  intro t ht
  exact block1077_rectangle_sound t (verticalA t) ht (positiveChordBox1077_vertical_enclosure ht.1 ht.2)

def block1078 : Block := ⟨⟨(33/40),(529/640)⟩,⟨(25698637341854482151/147573952589676412928),(98165244856663438217/147573952589676412928)⟩,⟨(-121263429713870717771/36893488147419103232),(-206293555670336957509/73786976294838206464)⟩,⟨(1217129/2097152),(610119/1048576)⟩⟩

theorem block1078_rectangle_sound : block1078.RectSound := by
  intro t a ht ha
  change (((33/40):ℚ):ℝ)≤t ∧ t≤(((529/640):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1217129/2097152):ℚ):ℝ)≤a ∧ a≤(((610119/1048576):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1078Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1078Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1078Parameters positiveChordBox1078Parameters_valid hbt hba
    positiveChordBox1078Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1078Radius positiveChordBox1078Cells positiveChordBox1078Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1078Boundary positiveChordBox1078Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1078Boundary positiveChordBox1078Cells).radius=(25698637341854482151/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1078Boundary positiveChordBox1078Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1078Boundary positiveChordBox1078Cells).radius=(98165244856663438217/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1078Boundary positiveChordBox1078Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1078Boundary positiveChordBox1078Cells).radius=(-121263429713870717771/36893488147419103232) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1078Boundary positiveChordBox1078Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1078Boundary positiveChordBox1078Cells).radius=(-206293555670336957509/73786976294838206464) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1078_sound : block1078.Sound := by
  intro t ht
  exact block1078_rectangle_sound t (verticalA t) ht (positiveChordBox1078_vertical_enclosure ht.1 ht.2)

def block1079 : Block := ⟨⟨(529/640),(53/64)⟩,⟨(11650336036406165589/73786976294838206464),(2988081279087029671/4611686018427387904)⟩,⟨(-60613071174632836501/18446744073709551616),(-206293320269545036857/73786976294838206464)⟩,⟨(2436221/4194304),(1221219/2097152)⟩⟩

theorem block1079_rectangle_sound : block1079.RectSound := by
  intro t a ht ha
  change (((529/640):ℚ):ℝ)≤t ∧ t≤(((53/64):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2436221/4194304):ℚ):ℝ)≤a ∧ a≤(((1221219/2097152):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1079Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1079Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1079Parameters positiveChordBox1079Parameters_valid hbt hba
    positiveChordBox1079Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1079Radius positiveChordBox1079Cells positiveChordBox1079Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1079Boundary positiveChordBox1079Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1079Boundary positiveChordBox1079Cells).radius=(11650336036406165589/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1079Boundary positiveChordBox1079Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1079Boundary positiveChordBox1079Cells).radius=(2988081279087029671/4611686018427387904) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1079Boundary positiveChordBox1079Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1079Boundary positiveChordBox1079Cells).radius=(-60613071174632836501/18446744073709551616) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1079Boundary positiveChordBox1079Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1079Boundary positiveChordBox1079Cells).radius=(-206293320269545036857/73786976294838206464) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1079_sound : block1079.Sound := by
  intro t ht
  exact block1079_rectangle_sound t (verticalA t) ht (positiveChordBox1079_vertical_enclosure ht.1 ht.2)

def block1080 : Block := ⟨⟨(53/64),(531/640)⟩,⟨(2613808493219144591/18446744073709551616),(5817247897831882731/9223372036854775808)⟩,⟨(-484741288380387617459/147573952589676412928),(-412575789960830650491/147573952589676412928)⟩,⟨(2438191/4194304),(1222203/2097152)⟩⟩

theorem block1080_rectangle_sound : block1080.RectSound := by
  intro t a ht ha
  change (((53/64):ℚ):ℝ)≤t ∧ t≤(((531/640):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2438191/4194304):ℚ):ℝ)≤a ∧ a≤(((1222203/2097152):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1080Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1080Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1080Parameters positiveChordBox1080Parameters_valid hbt hba
    positiveChordBox1080Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1080Radius positiveChordBox1080Cells positiveChordBox1080Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1080Boundary positiveChordBox1080Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1080Boundary positiveChordBox1080Cells).radius=(2613808493219144591/18446744073709551616) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1080Boundary positiveChordBox1080Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1080Boundary positiveChordBox1080Cells).radius=(5817247897831882731/9223372036854775808) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1080Boundary positiveChordBox1080Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1080Boundary positiveChordBox1080Cells).radius=(-484741288380387617459/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1080Boundary positiveChordBox1080Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1080Boundary positiveChordBox1080Cells).radius=(-412575789960830650491/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1080_sound : block1080.Sound := by
  intro t ht
  exact block1080_rectangle_sound t (verticalA t) ht (positiveChordBox1080_vertical_enclosure ht.1 ht.2)

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.block1077_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1078_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1079_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1080_sound
