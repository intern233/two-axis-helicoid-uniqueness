import TwoAxisHelicoid.PdfHorizontalRowTransfer
import TwoAxisHelicoid.PositiveChordBox1059
import TwoAxisHelicoid.PositiveChordBox1060
import TwoAxisHelicoid.PositiveChordBox1061
import TwoAxisHelicoid.PositiveChordBox1062

namespace TwoAxisHelicoid.PdfHorizontal
open ComplexBall
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block1059 : Block := ⟨⟨(247/320),(31/40)⟩,⟨(68808709241173373673/147573952589676412928),(226884705879863822489/147573952589676412928)⟩,⟨(-65390608538080380141/18446744073709551616),(-45631108958244074039/18446744073709551616)⟩,⟨(1184347/2097152),(297665/524288)⟩⟩

theorem block1059_rectangle_sound : block1059.RectSound := by
  intro t a ht ha
  change (((247/320):ℚ):ℝ)≤t ∧ t≤(((31/40):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1184347/2097152):ℚ):ℝ)≤a ∧ a≤(((297665/524288):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1059Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1059Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1059Parameters positiveChordBox1059Parameters_valid hbt hba
    positiveChordBox1059Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1059Radius positiveChordBox1059Cells positiveChordBox1059Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1059Boundary positiveChordBox1059Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1059Boundary positiveChordBox1059Cells).radius=(68808709241173373673/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1059Boundary positiveChordBox1059Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1059Boundary positiveChordBox1059Cells).radius=(226884705879863822489/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1059Boundary positiveChordBox1059Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1059Boundary positiveChordBox1059Cells).radius=(-65390608538080380141/18446744073709551616) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1059Boundary positiveChordBox1059Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1059Boundary positiveChordBox1059Cells).radius=(-45631108958244074039/18446744073709551616) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1059_sound : block1059.Sound := by
  intro t ht
  exact block1059_rectangle_sound t (verticalA t) ht (positiveChordBox1059_vertical_enclosure ht.1 ht.2)

def block1060 : Block := ⟨⟨(31/40),(249/320)⟩,⟨(3989132468725665967/9223372036854775808),(55327529373573241173/36893488147419103232)⟩,⟨(-65439542566583086285/18446744073709551616),(-91508085634495595265/36893488147419103232)⟩,⟨(2372239/4194304),(2384853/4194304)⟩⟩

theorem block1060_rectangle_sound : block1060.RectSound := by
  intro t a ht ha
  change (((31/40):ℚ):ℝ)≤t ∧ t≤(((249/320):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2372239/4194304):ℚ):ℝ)≤a ∧ a≤(((2384853/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1060Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1060Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1060Parameters positiveChordBox1060Parameters_valid hbt hba
    positiveChordBox1060Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1060Radius positiveChordBox1060Cells positiveChordBox1060Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1060Boundary positiveChordBox1060Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1060Boundary positiveChordBox1060Cells).radius=(3989132468725665967/9223372036854775808) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1060Boundary positiveChordBox1060Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1060Boundary positiveChordBox1060Cells).radius=(55327529373573241173/36893488147419103232) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1060Boundary positiveChordBox1060Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1060Boundary positiveChordBox1060Cells).radius=(-65439542566583086285/18446744073709551616) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1060Boundary positiveChordBox1060Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1060Boundary positiveChordBox1060Cells).radius=(-91508085634495595265/36893488147419103232) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1060_sound : block1060.Sound := by
  intro t ht
  exact block1060_rectangle_sound t (verticalA t) ht (positiveChordBox1060_vertical_enclosure ht.1 ht.2)

def block1061 : Block := ⟨⟨(249/320),(25/32)⟩,⟨(58863369141500892557/147573952589676412928),(215749372094976316557/147573952589676412928)⟩,⟨(-130963146513083943889/36893488147419103232),(-91741645774715087889/36893488147419103232)⟩,⟨(2375807/4194304),(2388409/4194304)⟩⟩

theorem block1061_rectangle_sound : block1061.RectSound := by
  intro t a ht ha
  change (((249/320):ℚ):ℝ)≤t ∧ t≤(((25/32):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2375807/4194304):ℚ):ℝ)≤a ∧ a≤(((2388409/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1061Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1061Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1061Parameters positiveChordBox1061Parameters_valid hbt hba
    positiveChordBox1061Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1061Radius positiveChordBox1061Cells positiveChordBox1061Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1061Boundary positiveChordBox1061Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1061Boundary positiveChordBox1061Cells).radius=(58863369141500892557/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1061Boundary positiveChordBox1061Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1061Boundary positiveChordBox1061Cells).radius=(215749372094976316557/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1061Boundary positiveChordBox1061Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1061Boundary positiveChordBox1061Cells).radius=(-130963146513083943889/36893488147419103232) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1061Boundary positiveChordBox1061Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1061Boundary positiveChordBox1061Cells).radius=(-91741645774715087889/36893488147419103232) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1061_sound : block1061.Sound := by
  intro t ht
  exact block1061_rectangle_sound t (verticalA t) ht (positiveChordBox1061_vertical_enclosure ht.1 ht.2)

def block1062 : Block := ⟨⟨(25/32),(251/320)⟩,⟨(13479696037798691963/36893488147419103232),(6568892005629968149/4611686018427387904)⟩,⟨(-262067680794715808195/73786976294838206464),(-183924800780233701737/73786976294838206464)⟩,⟨(2379399/4194304),(2391989/4194304)⟩⟩

theorem block1062_rectangle_sound : block1062.RectSound := by
  intro t a ht ha
  change (((25/32):ℚ):ℝ)≤t ∧ t≤(((251/320):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2379399/4194304):ℚ):ℝ)≤a ∧ a≤(((2391989/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1062Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1062Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1062Parameters positiveChordBox1062Parameters_valid hbt hba
    positiveChordBox1062Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1062Radius positiveChordBox1062Cells positiveChordBox1062Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1062Boundary positiveChordBox1062Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1062Boundary positiveChordBox1062Cells).radius=(13479696037798691963/36893488147419103232) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1062Boundary positiveChordBox1062Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1062Boundary positiveChordBox1062Cells).radius=(6568892005629968149/4611686018427387904) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1062Boundary positiveChordBox1062Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1062Boundary positiveChordBox1062Cells).radius=(-262067680794715808195/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1062Boundary positiveChordBox1062Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1062Boundary positiveChordBox1062Cells).radius=(-183924800780233701737/73786976294838206464) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1062_sound : block1062.Sound := by
  intro t ht
  exact block1062_rectangle_sound t (verticalA t) ht (positiveChordBox1062_vertical_enclosure ht.1 ht.2)

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.block1059_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1060_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1061_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1062_sound
