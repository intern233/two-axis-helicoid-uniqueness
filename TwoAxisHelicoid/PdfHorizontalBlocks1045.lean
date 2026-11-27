import TwoAxisHelicoid.PdfHorizontalRowTransfer
import TwoAxisHelicoid.PositiveChordBox1045
import TwoAxisHelicoid.PositiveChordBox1046
import TwoAxisHelicoid.PositiveChordBox1047
import TwoAxisHelicoid.PositiveChordBox1048

namespace TwoAxisHelicoid.PdfHorizontal
open ComplexBall
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block1045 : Block := ⟨⟨(111/160),(7/10)⟩,⟨(101982280177604616741/147573952589676412928),(460769097007113044503/147573952589676412928)⟩,⟨(-73787580524782409931/18446744073709551616),(-115756913684375425843/73786976294838206464)⟩,⟨(142649/262144),(2308697/4194304)⟩⟩

theorem block1045_rectangle_sound : block1045.RectSound := by
  intro t a ht ha
  change (((111/160):ℚ):ℝ)≤t ∧ t≤(((7/10):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((142649/262144):ℚ):ℝ)≤a ∧ a≤(((2308697/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1045Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1045Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1045Parameters positiveChordBox1045Parameters_valid hbt hba
    positiveChordBox1045Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1045Radius positiveChordBox1045Cells positiveChordBox1045Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1045Boundary positiveChordBox1045Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1045Boundary positiveChordBox1045Cells).radius=(101982280177604616741/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1045Boundary positiveChordBox1045Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1045Boundary positiveChordBox1045Cells).radius=(460769097007113044503/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1045Boundary positiveChordBox1045Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1045Boundary positiveChordBox1045Cells).radius=(-73787580524782409931/18446744073709551616) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1045Boundary positiveChordBox1045Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1045Boundary positiveChordBox1045Cells).radius=(-115756913684375425843/73786976294838206464) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1045_sound : block1045.Sound := by
  intro t ht
  exact block1045_rectangle_sound t (verticalA t) ht (positiveChordBox1045_vertical_enclosure ht.1 ht.2)

def block1046 : Block := ⟨⟨(7/10),(113/160)⟩,⟨(22977658345496599865/36893488147419103232),(224268800679765903555/73786976294838206464)⟩,⟨(-74135663053972644739/18446744073709551616),(-118229168227117875131/73786976294838206464)⟩,⟨(2288399/4194304),(289327/524288)⟩⟩

theorem block1046_rectangle_sound : block1046.RectSound := by
  intro t a ht ha
  change (((7/10):ℚ):ℝ)≤t ∧ t≤(((113/160):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2288399/4194304):ℚ):ℝ)≤a ∧ a≤(((289327/524288):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1046Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1046Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1046Parameters positiveChordBox1046Parameters_valid hbt hba
    positiveChordBox1046Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1046Radius positiveChordBox1046Cells positiveChordBox1046Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1046Boundary positiveChordBox1046Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1046Boundary positiveChordBox1046Cells).radius=(22977658345496599865/36893488147419103232) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1046Boundary positiveChordBox1046Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1046Boundary positiveChordBox1046Cells).radius=(224268800679765903555/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1046Boundary positiveChordBox1046Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1046Boundary positiveChordBox1046Cells).radius=(-74135663053972644739/18446744073709551616) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1046Boundary positiveChordBox1046Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1046Boundary positiveChordBox1046Cells).radius=(-118229168227117875131/73786976294838206464) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1046_sound : block1046.Sound := by
  intro t ht
  exact block1046_rectangle_sound t (verticalA t) ht (positiveChordBox1046_vertical_enclosure ht.1 ht.2)

def block1047 : Block := ⟨⟨(113/160),(57/80)⟩,⟨(20474688259541761353/36893488147419103232),(218162485019560916321/73786976294838206464)⟩,⟨(-297825046012385733045/73786976294838206464),(-60305968755954169715/36893488147419103232)⟩,⟨(2294505/4194304),(2320629/4194304)⟩⟩

theorem block1047_rectangle_sound : block1047.RectSound := by
  intro t a ht ha
  change (((113/160):ℚ):ℝ)≤t ∧ t≤(((57/80):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2294505/4194304):ℚ):ℝ)≤a ∧ a≤(((2320629/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1047Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1047Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1047Parameters positiveChordBox1047Parameters_valid hbt hba
    positiveChordBox1047Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1047Radius positiveChordBox1047Cells positiveChordBox1047Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1047Boundary positiveChordBox1047Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1047Boundary positiveChordBox1047Cells).radius=(20474688259541761353/36893488147419103232) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1047Boundary positiveChordBox1047Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1047Boundary positiveChordBox1047Cells).radius=(218162485019560916321/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1047Boundary positiveChordBox1047Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1047Boundary positiveChordBox1047Cells).radius=(-297825046012385733045/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1047Boundary positiveChordBox1047Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1047Boundary positiveChordBox1047Cells).radius=(-60305968755954169715/36893488147419103232) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1047_sound : block1047.Sound := by
  intro t ht
  exact block1047_rectangle_sound t (verticalA t) ht (positiveChordBox1047_vertical_enclosure ht.1 ht.2)

def block1048 : Block := ⟨⟨(57/80),(23/32)⟩,⟨(71952143824350722425/147573952589676412928),(424126844074810506293/147573952589676412928)⟩,⟨(-298993713363690257779/73786976294838206464),(-122906363238460365845/73786976294838206464)⟩,⟨(1150351/2097152),(2326737/4194304)⟩⟩

theorem block1048_rectangle_sound : block1048.RectSound := by
  intro t a ht ha
  change (((57/80):ℚ):ℝ)≤t ∧ t≤(((23/32):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1150351/2097152):ℚ):ℝ)≤a ∧ a≤(((2326737/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1048Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1048Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1048Parameters positiveChordBox1048Parameters_valid hbt hba
    positiveChordBox1048Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1048Radius positiveChordBox1048Cells positiveChordBox1048Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1048Boundary positiveChordBox1048Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1048Boundary positiveChordBox1048Cells).radius=(71952143824350722425/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1048Boundary positiveChordBox1048Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1048Boundary positiveChordBox1048Cells).radius=(424126844074810506293/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1048Boundary positiveChordBox1048Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1048Boundary positiveChordBox1048Cells).radius=(-298993713363690257779/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1048Boundary positiveChordBox1048Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1048Boundary positiveChordBox1048Cells).radius=(-122906363238460365845/73786976294838206464) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1048_sound : block1048.Sound := by
  intro t ht
  exact block1048_rectangle_sound t (verticalA t) ht (positiveChordBox1048_vertical_enclosure ht.1 ht.2)

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.block1045_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1046_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1047_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1048_sound
