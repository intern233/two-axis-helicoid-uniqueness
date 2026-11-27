import TwoAxisHelicoid.PdfHorizontalRowTransfer
import TwoAxisHelicoid.PositiveChordBox1096
import TwoAxisHelicoid.PositiveChordBox1097
import TwoAxisHelicoid.PositiveChordBox1098

namespace TwoAxisHelicoid.PdfHorizontal
open ComplexBall
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block1096 : Block := ⟨⟨(217/256),(543/640)⟩,⟨(9879513981334014239/147573952589676412928),(44695922704223352765/147573952589676412928)⟩,⟨(-464036521782161865209/147573952589676412928),(-429220113059272526683/147573952589676412928)⟩,⟨(2464351/4194304),(308431/524288)⟩⟩

theorem block1096_rectangle_sound : block1096.RectSound := by
  intro t a ht ha
  change (((217/256):ℚ):ℝ)≤t ∧ t≤(((543/640):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2464351/4194304):ℚ):ℝ)≤a ∧ a≤(((308431/524288):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1096Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1096Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1096Parameters positiveChordBox1096Parameters_valid hbt hba
    positiveChordBox1096Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1096Radius positiveChordBox1096Cells positiveChordBox1096Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1096Boundary positiveChordBox1096Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1096Boundary positiveChordBox1096Cells).radius=(9879513981334014239/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1096Boundary positiveChordBox1096Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1096Boundary positiveChordBox1096Cells).radius=(44695922704223352765/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1096Boundary positiveChordBox1096Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1096Boundary positiveChordBox1096Cells).radius=(-464036521782161865209/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1096Boundary positiveChordBox1096Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1096Boundary positiveChordBox1096Cells).radius=(-429220113059272526683/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1096_sound : block1096.Sound := by
  intro t ht
  exact block1096_rectangle_sound t (verticalA t) ht (positiveChordBox1096_vertical_enclosure ht.1 ht.2)

def block1097 : Block := ⟨⟨(543/640),(1087/1280)⟩,⟨(8706000429849165219/147573952589676412928),(43485961825835238093/147573952589676412928)⟩,⟨(-463898314756024478077/147573952589676412928),(-429118353360038405203/147573952589676412928)⟩,⟨(1232687/2097152),(2468471/4194304)⟩⟩

theorem block1097_rectangle_sound : block1097.RectSound := by
  intro t a ht ha
  change (((543/640):ℚ):ℝ)≤t ∧ t≤(((1087/1280):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1232687/2097152):ℚ):ℝ)≤a ∧ a≤(((2468471/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1097Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1097Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1097Parameters positiveChordBox1097Parameters_valid hbt hba
    positiveChordBox1097Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1097Radius positiveChordBox1097Cells positiveChordBox1097Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1097Boundary positiveChordBox1097Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1097Boundary positiveChordBox1097Cells).radius=(8706000429849165219/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1097Boundary positiveChordBox1097Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1097Boundary positiveChordBox1097Cells).radius=(43485961825835238093/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1097Boundary positiveChordBox1097Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1097Boundary positiveChordBox1097Cells).radius=(-463898314756024478077/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1097Boundary positiveChordBox1097Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1097Boundary positiveChordBox1097Cells).radius=(-429118353360038405203/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1097_sound : block1097.Sound := by
  intro t ht
  exact block1097_rectangle_sound t (verticalA t) ht (positiveChordBox1097_vertical_enclosure ht.1 ht.2)

def block1098 : Block := ⟨⟨(1087/1280),(17/20)⟩,⟨(7535887046438889161/147573952589676412928),(42275959738481514319/147573952589676412928)⟩,⟨(-463755528293639346699/147573952589676412928),(-429015455601596721541/147573952589676412928)⟩,⟨(2466399/4194304),(2469495/4194304)⟩⟩

theorem block1098_rectangle_sound : block1098.RectSound := by
  intro t a ht ha
  change (((1087/1280):ℚ):ℝ)≤t ∧ t≤(((17/20):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2466399/4194304):ℚ):ℝ)≤a ∧ a≤(((2469495/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1098Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1098Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1098Parameters positiveChordBox1098Parameters_valid hbt hba
    positiveChordBox1098Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1098Radius positiveChordBox1098Cells positiveChordBox1098Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1098Boundary positiveChordBox1098Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1098Boundary positiveChordBox1098Cells).radius=(7535887046438889161/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1098Boundary positiveChordBox1098Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1098Boundary positiveChordBox1098Cells).radius=(42275959738481514319/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1098Boundary positiveChordBox1098Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1098Boundary positiveChordBox1098Cells).radius=(-463755528293639346699/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1098Boundary positiveChordBox1098Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1098Boundary positiveChordBox1098Cells).radius=(-429015455601596721541/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1098_sound : block1098.Sound := by
  intro t ht
  exact block1098_rectangle_sound t (verticalA t) ht (positiveChordBox1098_vertical_enclosure ht.1 ht.2)

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.block1096_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1097_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1098_sound
