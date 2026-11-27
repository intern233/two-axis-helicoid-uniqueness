import TwoAxisHelicoid.PdfHorizontalRowTransfer
import TwoAxisHelicoid.PositiveChordBox1005
import TwoAxisHelicoid.PositiveChordBox1006
import TwoAxisHelicoid.PositiveChordBox1007
import TwoAxisHelicoid.PositiveChordBox1008

namespace TwoAxisHelicoid.PdfHorizontal
open ComplexBall
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block1005 : Block := ⟨⟨(13/80),(7/40)⟩,⟨(125256831874879609650932507/302231454903657293676544),(278139145232646037644685607/302231454903657293676544)⟩,⟨(-76443201401844589966957949/302231454903657293676544),(76439111955921838026795151/302231454903657293676544)⟩,⟨(1/2),(36896752744623146505/73786976294838206464)⟩⟩

theorem block1005_rectangle_sound : block1005.RectSound := by
  intro t a ht ha
  change (((13/80):ℚ):ℝ)≤t ∧ t≤(((7/40):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1/2):ℚ):ℝ)≤a ∧ a≤(((36896752744623146505/73786976294838206464):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1005Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1005Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1005Parameters positiveChordBox1005Parameters_valid hbt hba
    positiveChordBox1005Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1005Radius positiveChordBox1005Cells positiveChordBox1005Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1005Boundary positiveChordBox1005Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1005Boundary positiveChordBox1005Cells).radius=(125256831874879609650932507/302231454903657293676544) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1005Boundary positiveChordBox1005Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1005Boundary positiveChordBox1005Cells).radius=(278139145232646037644685607/302231454903657293676544) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1005Boundary positiveChordBox1005Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1005Boundary positiveChordBox1005Cells).radius=(-76443201401844589966957949/302231454903657293676544) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1005Boundary positiveChordBox1005Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1005Boundary positiveChordBox1005Cells).radius=(76439111955921838026795151/302231454903657293676544) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1005_sound : block1005.Sound := by
  intro t ht
  exact block1005_rectangle_sound t (verticalA t) ht (positiveChordBox1005_vertical_enclosure ht.1 ht.2)

def block1006 : Block := ⟨⟨(7/40),(3/16)⟩,⟨(19512611169281219198689137/75557863725914323419136),(18982161358587804137348065/37778931862957161709568)⟩,⟨(-9226761601480228867399839/75557863725914323419136),(4612474973207080104303577/37778931862957161709568)⟩,⟨(1/2),(36899851324918803599/73786976294838206464)⟩⟩

theorem block1006_rectangle_sound : block1006.RectSound := by
  intro t a ht ha
  change (((7/40):ℚ):ℝ)≤t ∧ t≤(((3/16):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1/2):ℚ):ℝ)≤a ∧ a≤(((36899851324918803599/73786976294838206464):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1006Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1006Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1006Parameters positiveChordBox1006Parameters_valid hbt hba
    positiveChordBox1006Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1006Radius positiveChordBox1006Cells positiveChordBox1006Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1006Boundary positiveChordBox1006Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1006Boundary positiveChordBox1006Cells).radius=(19512611169281219198689137/75557863725914323419136) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1006Boundary positiveChordBox1006Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1006Boundary positiveChordBox1006Cells).radius=(18982161358587804137348065/37778931862957161709568) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1006Boundary positiveChordBox1006Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1006Boundary positiveChordBox1006Cells).radius=(-9226761601480228867399839/75557863725914323419136) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1006Boundary positiveChordBox1006Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1006Boundary positiveChordBox1006Cells).radius=(4612474973207080104303577/37778931862957161709568) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1006_sound : block1006.Sound := by
  intro t ht
  exact block1006_rectangle_sound t (verticalA t) ht (positiveChordBox1006_vertical_enclosure ht.1 ht.2)

def block1007 : Block := ⟨⟨(3/16),(1/5)⟩,⟨(12777664624954109497326297/75557863725914323419136),(22615126796222217363358427/75557863725914323419136)⟩,⟨(-1230054200040852521223907/18889465931478580854784),(2458622685552348890568251/37778931862957161709568)⟩,⟨(1/2),(1153279558864418533/2305843009213693952)⟩⟩

theorem block1007_rectangle_sound : block1007.RectSound := by
  intro t a ht ha
  change (((3/16):ℚ):ℝ)≤t ∧ t≤(((1/5):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1/2):ℚ):ℝ)≤a ∧ a≤(((1153279558864418533/2305843009213693952):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1007Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1007Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1007Parameters positiveChordBox1007Parameters_valid hbt hba
    positiveChordBox1007Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1007Radius positiveChordBox1007Cells positiveChordBox1007Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1007Boundary positiveChordBox1007Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1007Boundary positiveChordBox1007Cells).radius=(12777664624954109497326297/75557863725914323419136) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1007Boundary positiveChordBox1007Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1007Boundary positiveChordBox1007Cells).radius=(22615126796222217363358427/75557863725914323419136) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1007Boundary positiveChordBox1007Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1007Boundary positiveChordBox1007Cells).radius=(-1230054200040852521223907/18889465931478580854784) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1007Boundary positiveChordBox1007Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1007Boundary positiveChordBox1007Cells).radius=(2458622685552348890568251/37778931862957161709568) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1007_sound : block1007.Sound := by
  intro t ht
  exact block1007_rectangle_sound t (verticalA t) ht (positiveChordBox1007_vertical_enclosure ht.1 ht.2)

def block1008 : Block := ⟨⟨(1/5),(9/40)⟩,⟨(696458423407589833743035/18889465931478580854784),(8187689202187455689957023/37778931862957161709568)⟩,⟨(-13595113947715654377441229/151115727451828646838272),(13583975473773449712442583/151115727451828646838272)⟩,⟨(1/2),(184621687045551444769/368934881474191032320)⟩⟩

theorem block1008_rectangle_sound : block1008.RectSound := by
  intro t a ht ha
  change (((1/5):ℚ):ℝ)≤t ∧ t≤(((9/40):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1/2):ℚ):ℝ)≤a ∧ a≤(((184621687045551444769/368934881474191032320):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1008Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1008Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1008Parameters positiveChordBox1008Parameters_valid hbt hba
    positiveChordBox1008Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1008Radius positiveChordBox1008Cells positiveChordBox1008Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1008Boundary positiveChordBox1008Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1008Boundary positiveChordBox1008Cells).radius=(696458423407589833743035/18889465931478580854784) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1008Boundary positiveChordBox1008Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1008Boundary positiveChordBox1008Cells).radius=(8187689202187455689957023/37778931862957161709568) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1008Boundary positiveChordBox1008Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1008Boundary positiveChordBox1008Cells).radius=(-13595113947715654377441229/151115727451828646838272) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1008Boundary positiveChordBox1008Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1008Boundary positiveChordBox1008Cells).radius=(13583975473773449712442583/151115727451828646838272) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1008_sound : block1008.Sound := by
  intro t ht
  exact block1008_rectangle_sound t (verticalA t) ht (positiveChordBox1008_vertical_enclosure ht.1 ht.2)

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.block1005_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1006_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1007_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1008_sound
