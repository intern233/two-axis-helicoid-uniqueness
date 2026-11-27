import TwoAxisHelicoid.PdfHorizontalRowTransfer
import TwoAxisHelicoid.PositiveChordBox1000

namespace TwoAxisHelicoid.PdfHorizontal
open ComplexBall
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block1000 : Block := ⟨⟨(1/8),(21/160)⟩,⟨(30819721858231481713663238487/4835703278458516698824704),(60200511773446557327687127103/4835703278458516698824704)⟩,⟨(-14690397205133076615368799477/4835703278458516698824704),(14690392710081998998655089139/4835703278458516698824704)⟩,⟨(1/2),(147574444113766369163/295147905179352825856)⟩⟩

theorem block1000_rectangle_sound : block1000.RectSound := by
  intro t a ht ha
  change (((1/8):ℚ):ℝ)≤t ∧ t≤(((21/160):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1/2):ℚ):ℝ)≤a ∧ a≤(((147574444113766369163/295147905179352825856):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1000Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1000Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1000Parameters positiveChordBox1000Parameters_valid hbt hba
    positiveChordBox1000Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1000Radius positiveChordBox1000Cells positiveChordBox1000Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1000Boundary positiveChordBox1000Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1000Boundary positiveChordBox1000Cells).radius=(30819721858231481713663238487/4835703278458516698824704) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1000Boundary positiveChordBox1000Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1000Boundary positiveChordBox1000Cells).radius=(60200511773446557327687127103/4835703278458516698824704) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1000Boundary positiveChordBox1000Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1000Boundary positiveChordBox1000Cells).radius=(-14690397205133076615368799477/4835703278458516698824704) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1000Boundary positiveChordBox1000Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1000Boundary positiveChordBox1000Cells).radius=(14690392710081998998655089139/4835703278458516698824704) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1000_sound : block1000.Sound := by
  intro t ht
  exact block1000_rectangle_sound t (verticalA t) ht (positiveChordBox1000_vertical_enclosure ht.1 ht.2)

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.block1000_sound
