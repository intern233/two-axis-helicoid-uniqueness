import TwoAxisHelicoid.PdfHorizontalRowTransfer
import TwoAxisHelicoid.PositiveChordBox1009
import TwoAxisHelicoid.PositiveChordBox1010
import TwoAxisHelicoid.PositiveChordBox1011
import TwoAxisHelicoid.PositiveChordBox1012

namespace TwoAxisHelicoid.PdfHorizontal
open ComplexBall
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block1009 : Block := ⟨⟨(9/40),(1/4)⟩,⟨(605647321797270020649659/18889465931478580854784),(1877618179649363668937681/18889465931478580854784)⟩,⟨(-637356133291265030563707/18889465931478580854784),(634614724560828617724315/18889465931478580854784)⟩,⟨(1/2),(9240596155926838973/18446744073709551616)⟩⟩

theorem block1009_rectangle_sound : block1009.RectSound := by
  intro t a ht ha
  change (((9/40):ℚ):ℝ)≤t ∧ t≤(((1/4):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1/2):ℚ):ℝ)≤a ∧ a≤(((9240596155926838973/18446744073709551616):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1009Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1009Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1009Parameters positiveChordBox1009Parameters_valid hbt hba
    positiveChordBox1009Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1009Radius positiveChordBox1009Cells positiveChordBox1009Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1009Boundary positiveChordBox1009Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1009Boundary positiveChordBox1009Cells).radius=(605647321797270020649659/18889465931478580854784) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1009Boundary positiveChordBox1009Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1009Boundary positiveChordBox1009Cells).radius=(1877618179649363668937681/18889465931478580854784) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1009Boundary positiveChordBox1009Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1009Boundary positiveChordBox1009Cells).radius=(-637356133291265030563707/18889465931478580854784) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1009Boundary positiveChordBox1009Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1009Boundary positiveChordBox1009Cells).radius=(634614724560828617724315/18889465931478580854784) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1009_sound : block1009.Sound := by
  intro t ht
  exact block1009_rectangle_sound t (verticalA t) ht (positiveChordBox1009_vertical_enclosure ht.1 ht.2)

def block1010 : Block := ⟨⟨(1/4),(11/40)⟩,⟨(42088083204109124876255/9444732965739290427392),(597338071731596968057185/9444732965739290427392)⟩,⟨(-278809215777092250115451/9444732965739290427392),(276440772750395593065479/9444732965739290427392)⟩,⟨(1/2),(2255871/4194304)⟩⟩

theorem block1010_rectangle_sound : block1010.RectSound := by
  intro t a ht ha
  change (((1/4):ℚ):ℝ)≤t ∧ t≤(((11/40):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1/2):ℚ):ℝ)≤a ∧ a≤(((2255871/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1010Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1010Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1010Parameters positiveChordBox1010Parameters_valid hbt hba
    positiveChordBox1010Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1010Radius positiveChordBox1010Cells positiveChordBox1010Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1010Boundary positiveChordBox1010Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1010Boundary positiveChordBox1010Cells).radius=(42088083204109124876255/9444732965739290427392) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1010Boundary positiveChordBox1010Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1010Boundary positiveChordBox1010Cells).radius=(597338071731596968057185/9444732965739290427392) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1010Boundary positiveChordBox1010Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1010Boundary positiveChordBox1010Cells).radius=(-278809215777092250115451/9444732965739290427392) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1010Boundary positiveChordBox1010Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1010Boundary positiveChordBox1010Cells).radius=(276440772750395593065479/9444732965739290427392) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1010_sound : block1010.Sound := by
  intro t ht
  exact block1010_rectangle_sound t (verticalA t) ht (positiveChordBox1010_vertical_enclosure ht.1 ht.2)

def block1011 : Block := ⟨⟨(11/40),(3/10)⟩,⟨(1368689260818409580331/295147905179352825856),(24454172435766658674151/590295810358705651712)⟩,⟨(-43897266423527206267139/2361183241434822606848),(42969909232992151786817/2361183241434822606848)⟩,⟨(1/2),(558827/1048576)⟩⟩

theorem block1011_rectangle_sound : block1011.RectSound := by
  intro t a ht ha
  change (((11/40):ℚ):ℝ)≤t ∧ t≤(((3/10):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1/2):ℚ):ℝ)≤a ∧ a≤(((558827/1048576):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1011Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1011Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1011Parameters positiveChordBox1011Parameters_valid hbt hba
    positiveChordBox1011Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1011Radius positiveChordBox1011Cells positiveChordBox1011Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1011Boundary positiveChordBox1011Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1011Boundary positiveChordBox1011Cells).radius=(1368689260818409580331/295147905179352825856) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1011Boundary positiveChordBox1011Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1011Boundary positiveChordBox1011Cells).radius=(24454172435766658674151/590295810358705651712) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1011Boundary positiveChordBox1011Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1011Boundary positiveChordBox1011Cells).radius=(-43897266423527206267139/2361183241434822606848) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1011Boundary positiveChordBox1011Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1011Boundary positiveChordBox1011Cells).radius=(42969909232992151786817/2361183241434822606848) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1011_sound : block1011.Sound := by
  intro t ht
  exact block1011_rectangle_sound t (verticalA t) ht (positiveChordBox1011_vertical_enclosure ht.1 ht.2)

def block1012 : Block := ⟨⟨(3/10),(13/40)⟩,⟨(8076126485027337476239/2361183241434822606848),(70830442469304443285603/2361183241434822606848)⟩,⟨(-32053012051132795117775/2361183241434822606848),(30701303933144310691589/2361183241434822606848)⟩,⟨(1/2),(2221577/4194304)⟩⟩

theorem block1012_rectangle_sound : block1012.RectSound := by
  intro t a ht ha
  change (((3/10):ℚ):ℝ)≤t ∧ t≤(((13/40):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1/2):ℚ):ℝ)≤a ∧ a≤(((2221577/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1012Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1012Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1012Parameters positiveChordBox1012Parameters_valid hbt hba
    positiveChordBox1012Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1012Radius positiveChordBox1012Cells positiveChordBox1012Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1012Boundary positiveChordBox1012Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1012Boundary positiveChordBox1012Cells).radius=(8076126485027337476239/2361183241434822606848) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1012Boundary positiveChordBox1012Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1012Boundary positiveChordBox1012Cells).radius=(70830442469304443285603/2361183241434822606848) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1012Boundary positiveChordBox1012Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1012Boundary positiveChordBox1012Cells).radius=(-32053012051132795117775/2361183241434822606848) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1012Boundary positiveChordBox1012Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1012Boundary positiveChordBox1012Cells).radius=(30701303933144310691589/2361183241434822606848) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1012_sound : block1012.Sound := by
  intro t ht
  exact block1012_rectangle_sound t (verticalA t) ht (positiveChordBox1012_vertical_enclosure ht.1 ht.2)

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.block1009_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1010_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1011_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1012_sound
