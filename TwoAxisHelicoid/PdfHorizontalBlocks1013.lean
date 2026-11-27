import TwoAxisHelicoid.PdfHorizontalRowTransfer
import TwoAxisHelicoid.PositiveChordBox1013
import TwoAxisHelicoid.PositiveChordBox1016
import TwoAxisHelicoid.PositiveChordBox1017
import TwoAxisHelicoid.PositiveChordBox1018

namespace TwoAxisHelicoid.PdfHorizontal
open ComplexBall
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block1013 : Block := ⟨⟨(13/40),(7/20)⟩,⟨(5005334741859347754071/2361183241434822606848),(55312307630633279605725/2361183241434822606848)⟩,⟨(-26085713034960169624987/2361183241434822606848),(24221259853813762226667/2361183241434822606848)⟩,⟨(1/2),(2212591/4194304)⟩⟩

theorem block1013_rectangle_sound : block1013.RectSound := by
  intro t a ht ha
  change (((13/40):ℚ):ℝ)≤t ∧ t≤(((7/20):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1/2):ℚ):ℝ)≤a ∧ a≤(((2212591/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1013Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1013Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1013Parameters positiveChordBox1013Parameters_valid hbt hba
    positiveChordBox1013Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1013Radius positiveChordBox1013Cells positiveChordBox1013Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1013Boundary positiveChordBox1013Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1013Boundary positiveChordBox1013Cells).radius=(5005334741859347754071/2361183241434822606848) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1013Boundary positiveChordBox1013Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1013Boundary positiveChordBox1013Cells).radius=(55312307630633279605725/2361183241434822606848) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1013Boundary positiveChordBox1013Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1013Boundary positiveChordBox1013Cells).radius=(-26085713034960169624987/2361183241434822606848) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1013Boundary positiveChordBox1013Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1013Boundary positiveChordBox1013Cells).radius=(24221259853813762226667/2361183241434822606848) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1013_sound : block1013.Sound := by
  intro t ht
  exact block1013_rectangle_sound t (verticalA t) ht (positiveChordBox1013_vertical_enclosure ht.1 ht.2)

def block1016 : Block := ⟨⟨(2/5),(33/80)⟩,⟨(2588477399182747726821/590295810358705651712),(6370726430024212411759/590295810358705651712)⟩,⟨(-1176722297294558346855/295147905179352825856),(357201109063086997807/147573952589676412928)⟩,⟨(1/2),(2160015/4194304)⟩⟩

theorem block1016_rectangle_sound : block1016.RectSound := by
  intro t a ht ha
  change (((2/5):ℚ):ℝ)≤t ∧ t≤(((33/80):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1/2):ℚ):ℝ)≤a ∧ a≤(((2160015/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1016Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1016Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1016Parameters positiveChordBox1016Parameters_valid hbt hba
    positiveChordBox1016Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1016Radius positiveChordBox1016Cells positiveChordBox1016Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1016Boundary positiveChordBox1016Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1016Boundary positiveChordBox1016Cells).radius=(2588477399182747726821/590295810358705651712) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1016Boundary positiveChordBox1016Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1016Boundary positiveChordBox1016Cells).radius=(6370726430024212411759/590295810358705651712) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1016Boundary positiveChordBox1016Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1016Boundary positiveChordBox1016Cells).radius=(-1176722297294558346855/295147905179352825856) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1016Boundary positiveChordBox1016Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1016Boundary positiveChordBox1016Cells).radius=(357201109063086997807/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1016_sound : block1016.Sound := by
  intro t ht
  exact block1016_rectangle_sound t (verticalA t) ht (positiveChordBox1016_vertical_enclosure ht.1 ht.2)

def block1017 : Block := ⟨⟨(33/80),(17/40)⟩,⟨(2258239324228203681307/590295810358705651712),(6036990529089492954763/590295810358705651712)⟩,⟨(-2400751115853525131105/590295810358705651712),(1378000089007764142351/590295810358705651712)⟩,⟨(1/2),(540591/1048576)⟩⟩

theorem block1017_rectangle_sound : block1017.RectSound := by
  intro t a ht ha
  change (((33/80):ℚ):ℝ)≤t ∧ t≤(((17/40):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1/2):ℚ):ℝ)≤a ∧ a≤(((540591/1048576):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1017Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1017Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1017Parameters positiveChordBox1017Parameters_valid hbt hba
    positiveChordBox1017Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1017Radius positiveChordBox1017Cells positiveChordBox1017Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1017Boundary positiveChordBox1017Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1017Boundary positiveChordBox1017Cells).radius=(2258239324228203681307/590295810358705651712) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1017Boundary positiveChordBox1017Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1017Boundary positiveChordBox1017Cells).radius=(6036990529089492954763/590295810358705651712) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1017Boundary positiveChordBox1017Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1017Boundary positiveChordBox1017Cells).radius=(-2400751115853525131105/590295810358705651712) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1017Boundary positiveChordBox1017Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1017Boundary positiveChordBox1017Cells).radius=(1378000089007764142351/590295810358705651712) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1017_sound : block1017.Sound := by
  intro t ht
  exact block1017_rectangle_sound t (verticalA t) ht (positiveChordBox1017_vertical_enclosure ht.1 ht.2)

def block1018 : Block := ⟨⟨(17/40),(7/16)⟩,⟨(490113098026653564925/147573952589676412928),(2881257013294554235473/295147905179352825856)⟩,⟨(-615840539465178144555/147573952589676412928),(669349738310890816513/295147905179352825856)⟩,⟨(1/2),(2165145/4194304)⟩⟩

theorem block1018_rectangle_sound : block1018.RectSound := by
  intro t a ht ha
  change (((17/40):ℚ):ℝ)≤t ∧ t≤(((7/16):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1/2):ℚ):ℝ)≤a ∧ a≤(((2165145/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1018Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1018Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1018Parameters positiveChordBox1018Parameters_valid hbt hba
    positiveChordBox1018Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1018Radius positiveChordBox1018Cells positiveChordBox1018Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1018Boundary positiveChordBox1018Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1018Boundary positiveChordBox1018Cells).radius=(490113098026653564925/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1018Boundary positiveChordBox1018Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1018Boundary positiveChordBox1018Cells).radius=(2881257013294554235473/295147905179352825856) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1018Boundary positiveChordBox1018Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1018Boundary positiveChordBox1018Cells).radius=(-615840539465178144555/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1018Boundary positiveChordBox1018Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1018Boundary positiveChordBox1018Cells).radius=(669349738310890816513/295147905179352825856) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1018_sound : block1018.Sound := by
  intro t ht
  exact block1018_rectangle_sound t (verticalA t) ht (positiveChordBox1018_vertical_enclosure ht.1 ht.2)

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.block1013_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1016_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1017_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1018_sound
