import TwoAxisHelicoid.PdfHorizontalRowTransfer
import TwoAxisHelicoid.PositiveChordBox1001
import TwoAxisHelicoid.PositiveChordBox1002
import TwoAxisHelicoid.PositiveChordBox1003
import TwoAxisHelicoid.PositiveChordBox1004

namespace TwoAxisHelicoid.PdfHorizontal
open ComplexBall
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block1001 : Block := ⟨⟨(21/160),(11/80)⟩,⟨(9656167966629822778178350917/2417851639229258349412352),(17457666403139213912984189561/2417851639229258349412352)⟩,⟨(-3900751113565405691252206597/2417851639229258349412352),(3900747322943985443553632047/2417851639229258349412352)⟩,⟨(1/2),(368937099383829368217/737869762948382064640)⟩⟩

theorem block1001_rectangle_sound : block1001.RectSound := by
  intro t a ht ha
  change (((21/160):ℚ):ℝ)≤t ∧ t≤(((11/80):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1/2):ℚ):ℝ)≤a ∧ a≤(((368937099383829368217/737869762948382064640):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1001Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1001Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1001Parameters positiveChordBox1001Parameters_valid hbt hba
    positiveChordBox1001Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1001Radius positiveChordBox1001Cells positiveChordBox1001Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1001Boundary positiveChordBox1001Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1001Boundary positiveChordBox1001Cells).radius=(9656167966629822778178350917/2417851639229258349412352) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1001Boundary positiveChordBox1001Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1001Boundary positiveChordBox1001Cells).radius=(17457666403139213912984189561/2417851639229258349412352) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1001Boundary positiveChordBox1001Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1001Boundary positiveChordBox1001Cells).radius=(-3900751113565405691252206597/2417851639229258349412352) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1001Boundary positiveChordBox1001Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1001Boundary positiveChordBox1001Cells).radius=(3900747322943985443553632047/2417851639229258349412352) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1001_sound : block1001.Sound := by
  intro t ht
  exact block1001_rectangle_sound t (verticalA t) ht (positiveChordBox1001_vertical_enclosure ht.1 ht.2)

def block1002 : Block := ⟨⟨(11/80),(23/160)⟩,⟨(196538021890807301704166687/75557863725914323419136),(2666853823328318689729903137/604462909807314587353088)⟩,⟨(-1094551170869710393720536215/1208925819614629174706176),(1094548125534010158472603067/1208925819614629174706176)⟩,⟨(1/2),(147575476714972744995/295147905179352825856)⟩⟩

theorem block1002_rectangle_sound : block1002.RectSound := by
  intro t a ht ha
  change (((11/80):ℚ):ℝ)≤t ∧ t≤(((23/160):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1/2):ℚ):ℝ)≤a ∧ a≤(((147575476714972744995/295147905179352825856):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1002Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1002Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1002Parameters positiveChordBox1002Parameters_valid hbt hba
    positiveChordBox1002Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1002Radius positiveChordBox1002Cells positiveChordBox1002Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1002Boundary positiveChordBox1002Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1002Boundary positiveChordBox1002Cells).radius=(196538021890807301704166687/75557863725914323419136) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1002Boundary positiveChordBox1002Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1002Boundary positiveChordBox1002Cells).radius=(2666853823328318689729903137/604462909807314587353088) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1002Boundary positiveChordBox1002Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1002Boundary positiveChordBox1002Cells).radius=(-1094551170869710393720536215/1208925819614629174706176) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1002Boundary positiveChordBox1002Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1002Boundary positiveChordBox1002Cells).radius=(1094548125534010158472603067/1208925819614629174706176) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1002_sound : block1002.Sound := by
  intro t ht
  exact block1002_rectangle_sound t (verticalA t) ht (positiveChordBox1002_vertical_enclosure ht.1 ht.2)

def block1003 : Block := ⟨⟨(23/160),(3/20)⟩,⟨(2120738847061018705855004429/1208925819614629174706176),(3410050085811497257392603755/1208925819614629174706176)⟩,⟨(-80582245615047550429067681/151115727451828646838272),(322326636915049074052528939/604462909807314587353088)⟩,⟨(1/2),(92235287551857135233/184467440737095516160)⟩⟩

theorem block1003_rectangle_sound : block1003.RectSound := by
  intro t a ht ha
  change (((23/160):ℚ):ℝ)≤t ∧ t≤(((3/20):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1/2):ℚ):ℝ)≤a ∧ a≤(((92235287551857135233/184467440737095516160):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1003Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1003Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1003Parameters positiveChordBox1003Parameters_valid hbt hba
    positiveChordBox1003Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1003Radius positiveChordBox1003Cells positiveChordBox1003Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1003Boundary positiveChordBox1003Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1003Boundary positiveChordBox1003Cells).radius=(2120738847061018705855004429/1208925819614629174706176) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1003Boundary positiveChordBox1003Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1003Boundary positiveChordBox1003Cells).radius=(3410050085811497257392603755/1208925819614629174706176) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1003Boundary positiveChordBox1003Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1003Boundary positiveChordBox1003Cells).radius=(-80582245615047550429067681/151115727451828646838272) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1003Boundary positiveChordBox1003Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1003Boundary positiveChordBox1003Cells).radius=(322326636915049074052528939/604462909807314587353088) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1003_sound : block1003.Sound := by
  intro t ht
  exact block1003_rectangle_sound t (verticalA t) ht (positiveChordBox1003_vertical_enclosure ht.1 ht.2)

def block1004 : Block := ⟨⟨(3/20),(13/80)⟩,⟨(26399358402380338778291625/37778931862957161709568),(1136873326106805714057687055/604462909807314587353088)⟩,⟨(-714487782127884592312652835/1208925819614629174706176),(714479401209555994897389275/1208925819614629174706176)⟩,⟨(1/2),(92237519829580351709/184467440737095516160)⟩⟩

theorem block1004_rectangle_sound : block1004.RectSound := by
  intro t a ht ha
  change (((3/20):ℚ):ℝ)≤t ∧ t≤(((13/80):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1/2):ℚ):ℝ)≤a ∧ a≤(((92237519829580351709/184467440737095516160):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1004Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1004Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1004Parameters positiveChordBox1004Parameters_valid hbt hba
    positiveChordBox1004Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1004Radius positiveChordBox1004Cells positiveChordBox1004Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1004Boundary positiveChordBox1004Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1004Boundary positiveChordBox1004Cells).radius=(26399358402380338778291625/37778931862957161709568) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1004Boundary positiveChordBox1004Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1004Boundary positiveChordBox1004Cells).radius=(1136873326106805714057687055/604462909807314587353088) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1004Boundary positiveChordBox1004Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1004Boundary positiveChordBox1004Cells).radius=(-714487782127884592312652835/1208925819614629174706176) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1004Boundary positiveChordBox1004Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1004Boundary positiveChordBox1004Cells).radius=(714479401209555994897389275/1208925819614629174706176) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1004_sound : block1004.Sound := by
  intro t ht
  exact block1004_rectangle_sound t (verticalA t) ht (positiveChordBox1004_vertical_enclosure ht.1 ht.2)

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.block1001_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1002_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1003_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1004_sound
