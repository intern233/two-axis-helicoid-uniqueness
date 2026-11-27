import TwoAxisHelicoid.PdfHorizontalRowTransfer
import TwoAxisHelicoid.PositiveChordBox1019
import TwoAxisHelicoid.PositiveChordBox1020
import TwoAxisHelicoid.PositiveChordBox1021
import TwoAxisHelicoid.PositiveChordBox1022

namespace TwoAxisHelicoid.PdfHorizontal
open ComplexBall
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block1019 : Block := ⟨⟨(7/16),(9/20)⟩,⟨(1688304365820347087245/590295810358705651712),(5536871100405519087393/590295810358705651712)⟩,⟨(-317412015340841348077/73786976294838206464),(327317652964610303883/147573952589676412928)⟩,⟨(1/2),(542089/1048576)⟩⟩

theorem block1019_rectangle_sound : block1019.RectSound := by
  intro t a ht ha
  change (((7/16):ℚ):ℝ)≤t ∧ t≤(((9/20):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1/2):ℚ):ℝ)≤a ∧ a≤(((542089/1048576):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1019Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1019Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1019Parameters positiveChordBox1019Parameters_valid hbt hba
    positiveChordBox1019Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1019Radius positiveChordBox1019Cells positiveChordBox1019Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1019Boundary positiveChordBox1019Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1019Boundary positiveChordBox1019Cells).radius=(1688304365820347087245/590295810358705651712) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1019Boundary positiveChordBox1019Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1019Boundary positiveChordBox1019Cells).radius=(5536871100405519087393/590295810358705651712) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1019Boundary positiveChordBox1019Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1019Boundary positiveChordBox1019Cells).radius=(-317412015340841348077/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1019Boundary positiveChordBox1019Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1019Boundary positiveChordBox1019Cells).radius=(327317652964610303883/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1019_sound : block1019.Sound := by
  intro t ht
  exact block1019_rectangle_sound t (verticalA t) ht (positiveChordBox1019_vertical_enclosure ht.1 ht.2)

def block1020 : Block := ⟨⟨(9/20),(37/80)⟩,⟨(1471677043777980236201/590295810358705651712),(5307789245304816216275/590295810358705651712)⟩,⟨(-2587173466093917678769/590295810358705651712),(1248938735432918301305/590295810358705651712)⟩,⟨(1050189/2097152),(271499/524288)⟩⟩

theorem block1020_rectangle_sound : block1020.RectSound := by
  intro t a ht ha
  change (((9/20):ℚ):ℝ)≤t ∧ t≤(((37/80):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1050189/2097152):ℚ):ℝ)≤a ∧ a≤(((271499/524288):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1020Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1020Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1020Parameters positiveChordBox1020Parameters_valid hbt hba
    positiveChordBox1020Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1020Radius positiveChordBox1020Cells positiveChordBox1020Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1020Boundary positiveChordBox1020Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1020Boundary positiveChordBox1020Cells).radius=(1471677043777980236201/590295810358705651712) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1020Boundary positiveChordBox1020Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1020Boundary positiveChordBox1020Cells).radius=(5307789245304816216275/590295810358705651712) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1020Boundary positiveChordBox1020Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1020Boundary positiveChordBox1020Cells).radius=(-2587173466093917678769/590295810358705651712) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1020Boundary positiveChordBox1020Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1020Boundary positiveChordBox1020Cells).radius=(1248938735432918301305/590295810358705651712) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1020_sound : block1020.Sound := by
  intro t ht
  exact block1020_rectangle_sound t (verticalA t) ht (positiveChordBox1020_vertical_enclosure ht.1 ht.2)

def block1021 : Block := ⟨⟨(37/80),(19/40)⟩,⟨(649942727062429049759/295147905179352825856),(1269684538820298737465/147573952589676412928)⟩,⟨(-2613813997850436618319/590295810358705651712),(1165038703305900232023/590295810358705651712)⟩,⟨(2106185/4194304),(2176053/4194304)⟩⟩

theorem block1021_rectangle_sound : block1021.RectSound := by
  intro t a ht ha
  change (((37/80):ℚ):ℝ)≤t ∧ t≤(((19/40):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2106185/4194304):ℚ):ℝ)≤a ∧ a≤(((2176053/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1021Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1021Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1021Parameters positiveChordBox1021Parameters_valid hbt hba
    positiveChordBox1021Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1021Radius positiveChordBox1021Cells positiveChordBox1021Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1021Boundary positiveChordBox1021Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1021Boundary positiveChordBox1021Cells).radius=(649942727062429049759/295147905179352825856) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1021Boundary positiveChordBox1021Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1021Boundary positiveChordBox1021Cells).radius=(1269684538820298737465/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1021Boundary positiveChordBox1021Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1021Boundary positiveChordBox1021Cells).radius=(-2613813997850436618319/590295810358705651712) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1021Boundary positiveChordBox1021Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1021Boundary positiveChordBox1021Cells).radius=(1165038703305900232023/590295810358705651712) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1021_sound : block1021.Sound := by
  intro t ht
  exact block1021_rectangle_sound t (verticalA t) ht (positiveChordBox1021_vertical_enclosure ht.1 ht.2)

def block1022 : Block := ⟨⟨(19/40),(39/80)⟩,⟨(572268181445453838543/295147905179352825856),(2437758877970038045879/295147905179352825856)⟩,⟨(-1323069968587516146437/295147905179352825856),(542420727937068060899/295147905179352825856)⟩,⟨(264035/524288),(272567/524288)⟩⟩

theorem block1022_rectangle_sound : block1022.RectSound := by
  intro t a ht ha
  change (((19/40):ℚ):ℝ)≤t ∧ t≤(((39/80):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((264035/524288):ℚ):ℝ)≤a ∧ a≤(((272567/524288):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1022Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1022Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1022Parameters positiveChordBox1022Parameters_valid hbt hba
    positiveChordBox1022Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1022Radius positiveChordBox1022Cells positiveChordBox1022Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1022Boundary positiveChordBox1022Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1022Boundary positiveChordBox1022Cells).radius=(572268181445453838543/295147905179352825856) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1022Boundary positiveChordBox1022Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1022Boundary positiveChordBox1022Cells).radius=(2437758877970038045879/295147905179352825856) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1022Boundary positiveChordBox1022Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1022Boundary positiveChordBox1022Cells).radius=(-1323069968587516146437/295147905179352825856) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1022Boundary positiveChordBox1022Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1022Boundary positiveChordBox1022Cells).radius=(542420727937068060899/295147905179352825856) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1022_sound : block1022.Sound := by
  intro t ht
  exact block1022_rectangle_sound t (verticalA t) ht (positiveChordBox1022_vertical_enclosure ht.1 ht.2)

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.block1019_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1020_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1021_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1022_sound
