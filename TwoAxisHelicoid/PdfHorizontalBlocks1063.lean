import TwoAxisHelicoid.PdfHorizontalRowTransfer
import TwoAxisHelicoid.PositiveChordBox1063
import TwoAxisHelicoid.PositiveChordBox1074
import TwoAxisHelicoid.PositiveChordBox1075
import TwoAxisHelicoid.PositiveChordBox1076

namespace TwoAxisHelicoid.PdfHorizontal
open ComplexBall
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block1063 : Block := ⟨⟨(251/320),(63/80)⟩,⟨(6124092605431522919/18446744073709551616),(102338431985319905995/73786976294838206464)⟩,⟨(-262182805153181841351/73786976294838206464),(-23042592948698503379/9223372036854775808)⟩,⟨(2383013/4194304),(299449/524288)⟩⟩

theorem block1063_rectangle_sound : block1063.RectSound := by
  intro t a ht ha
  change (((251/320):ℚ):ℝ)≤t ∧ t≤(((63/80):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2383013/4194304):ℚ):ℝ)≤a ∧ a≤(((299449/524288):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1063Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1063Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1063Parameters positiveChordBox1063Parameters_valid hbt hba
    positiveChordBox1063Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1063Radius positiveChordBox1063Cells positiveChordBox1063Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1063Boundary positiveChordBox1063Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1063Boundary positiveChordBox1063Cells).radius=(6124092605431522919/18446744073709551616) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1063Boundary positiveChordBox1063Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1063Boundary positiveChordBox1063Cells).radius=(102338431985319905995/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1063Boundary positiveChordBox1063Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1063Boundary positiveChordBox1063Cells).radius=(-262182805153181841351/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1063Boundary positiveChordBox1063Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1063Boundary positiveChordBox1063Cells).radius=(-23042592948698503379/9223372036854775808) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1063_sound : block1063.Sound := by
  intro t ht
  exact block1063_rectangle_sound t (verticalA t) ht (positiveChordBox1063_vertical_enclosure ht.1 ht.2)

def block1074 : Block := ⟨⟨(131/160),(105/128)⟩,⟨(17672176622140119729/73786976294838206464),(54208269394556610133/73786976294838206464)⟩,⟨(-242767175140723645487/73786976294838206464),(-206231082368307155083/73786976294838206464)⟩,⟨(1213231/2097152),(2432687/4194304)⟩⟩

theorem block1074_rectangle_sound : block1074.RectSound := by
  intro t a ht ha
  change (((131/160):ℚ):ℝ)≤t ∧ t≤(((105/128):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1213231/2097152):ℚ):ℝ)≤a ∧ a≤(((2432687/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1074Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1074Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1074Parameters positiveChordBox1074Parameters_valid hbt hba
    positiveChordBox1074Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1074Radius positiveChordBox1074Cells positiveChordBox1074Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1074Boundary positiveChordBox1074Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1074Boundary positiveChordBox1074Cells).radius=(17672176622140119729/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1074Boundary positiveChordBox1074Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1074Boundary positiveChordBox1074Cells).radius=(54208269394556610133/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1074Boundary positiveChordBox1074Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1074Boundary positiveChordBox1074Cells).radius=(-242767175140723645487/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1074Boundary positiveChordBox1074Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1074Boundary positiveChordBox1074Cells).radius=(-206231082368307155083/73786976294838206464) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1074_sound : block1074.Sound := by
  intro t ht
  exact block1074_rectangle_sound t (verticalA t) ht (positiveChordBox1074_vertical_enclosure ht.1 ht.2)

def block1075 : Block := ⟨⟨(105/128),(263/320)⟩,⟨(16462125138351172813/73786976294838206464),(52922516707486329269/73786976294838206464)⟩,⟨(-485432619479311528547/147573952589676412928),(-412511836341041215635/147573952589676412928)⟩,⟨(1214201/2097152),(2434625/4194304)⟩⟩

theorem block1075_rectangle_sound : block1075.RectSound := by
  intro t a ht ha
  change (((105/128):ℚ):ℝ)≤t ∧ t≤(((263/320):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1214201/2097152):ℚ):ℝ)≤a ∧ a≤(((2434625/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1075Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1075Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1075Parameters positiveChordBox1075Parameters_valid hbt hba
    positiveChordBox1075Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1075Radius positiveChordBox1075Cells positiveChordBox1075Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1075Boundary positiveChordBox1075Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1075Boundary positiveChordBox1075Cells).radius=(16462125138351172813/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1075Boundary positiveChordBox1075Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1075Boundary positiveChordBox1075Cells).radius=(52922516707486329269/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1075Boundary positiveChordBox1075Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1075Boundary positiveChordBox1075Cells).radius=(-485432619479311528547/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1075Boundary positiveChordBox1075Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1075Boundary positiveChordBox1075Cells).radius=(-412511836341041215635/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1075_sound : block1075.Sound := by
  intro t ht
  exact block1075_rectangle_sound t (verticalA t) ht (positiveChordBox1075_vertical_enclosure ht.1 ht.2)

def block1076 : Block := ⟨⟨(263/320),(527/640)⟩,⟨(7627568126546400667/36893488147419103232),(6454933312087897435/9223372036854775808)⟩,⟨(-485318235688700994749/147573952589676412928),(-412549575201480238457/147573952589676412928)⟩,⟨(607587/1048576),(2436569/4194304)⟩⟩

theorem block1076_rectangle_sound : block1076.RectSound := by
  intro t a ht ha
  change (((263/320):ℚ):ℝ)≤t ∧ t≤(((527/640):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((607587/1048576):ℚ):ℝ)≤a ∧ a≤(((2436569/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1076Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1076Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1076Parameters positiveChordBox1076Parameters_valid hbt hba
    positiveChordBox1076Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1076Radius positiveChordBox1076Cells positiveChordBox1076Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1076Boundary positiveChordBox1076Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1076Boundary positiveChordBox1076Cells).radius=(7627568126546400667/36893488147419103232) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1076Boundary positiveChordBox1076Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1076Boundary positiveChordBox1076Cells).radius=(6454933312087897435/9223372036854775808) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1076Boundary positiveChordBox1076Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1076Boundary positiveChordBox1076Cells).radius=(-485318235688700994749/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1076Boundary positiveChordBox1076Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1076Boundary positiveChordBox1076Cells).radius=(-412549575201480238457/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1076_sound : block1076.Sound := by
  intro t ht
  exact block1076_rectangle_sound t (verticalA t) ht (positiveChordBox1076_vertical_enclosure ht.1 ht.2)

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.block1063_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1074_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1075_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1076_sound
