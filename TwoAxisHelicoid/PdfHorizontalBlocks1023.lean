import TwoAxisHelicoid.PdfHorizontalRowTransfer
import TwoAxisHelicoid.PositiveChordBox1023
import TwoAxisHelicoid.PositiveChordBox1034
import TwoAxisHelicoid.PositiveChordBox1035
import TwoAxisHelicoid.PositiveChordBox1036

namespace TwoAxisHelicoid.PdfHorizontal
open ComplexBall
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block1023 : Block := ⟨⟨(39/80),(1/2)⟩,⟨(7837377552890054423/4611686018427387904),(293305931081488083995/36893488147419103232)⟩,⟨(-1341253494391488045899/295147905179352825856),(503601790875453142989/295147905179352825856)⟩,⟨(2118675/4194304),(2185439/4194304)⟩⟩

theorem block1023_rectangle_sound : block1023.RectSound := by
  intro t a ht ha
  change (((39/80):ℚ):ℝ)≤t ∧ t≤(((1/2):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2118675/4194304):ℚ):ℝ)≤a ∧ a≤(((2185439/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1023Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1023Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1023Parameters positiveChordBox1023Parameters_valid hbt hba
    positiveChordBox1023Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1023Radius positiveChordBox1023Cells positiveChordBox1023Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1023Boundary positiveChordBox1023Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1023Boundary positiveChordBox1023Cells).radius=(7837377552890054423/4611686018427387904) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1023Boundary positiveChordBox1023Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1023Boundary positiveChordBox1023Cells).radius=(293305931081488083995/36893488147419103232) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1023Boundary positiveChordBox1023Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1023Boundary positiveChordBox1023Cells).radius=(-1341253494391488045899/295147905179352825856) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1023Boundary positiveChordBox1023Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1023Boundary positiveChordBox1023Cells).radius=(503601790875453142989/295147905179352825856) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1023_sound : block1023.Sound := by
  intro t ht
  exact block1023_rectangle_sound t (verticalA t) ht (positiveChordBox1023_vertical_enclosure ht.1 ht.2)

def block1034 : Block := ⟨⟨(5/8),(101/160)⟩,⟨(217391491760611377301/147573952589676412928),(596647366384062749259/147573952589676412928)⟩,⟨(-68240408890685759447/18446744073709551616),(-83333698251017351809/73786976294838206464)⟩,⟨(1111081/2097152),(281231/524288)⟩⟩

theorem block1034_rectangle_sound : block1034.RectSound := by
  intro t a ht ha
  change (((5/8):ℚ):ℝ)≤t ∧ t≤(((101/160):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((1111081/2097152):ℚ):ℝ)≤a ∧ a≤(((281231/524288):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1034Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1034Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1034Parameters positiveChordBox1034Parameters_valid hbt hba
    positiveChordBox1034Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1034Radius positiveChordBox1034Cells positiveChordBox1034Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1034Boundary positiveChordBox1034Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1034Boundary positiveChordBox1034Cells).radius=(217391491760611377301/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1034Boundary positiveChordBox1034Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1034Boundary positiveChordBox1034Cells).radius=(596647366384062749259/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1034Boundary positiveChordBox1034Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1034Boundary positiveChordBox1034Cells).radius=(-68240408890685759447/18446744073709551616) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1034Boundary positiveChordBox1034Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1034Boundary positiveChordBox1034Cells).radius=(-83333698251017351809/73786976294838206464) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1034_sound : block1034.Sound := by
  intro t ht
  exact block1034_rectangle_sound t (verticalA t) ht (positiveChordBox1034_vertical_enclosure ht.1 ht.2)

def block1035 : Block := ⟨⟨(101/160),(51/80)⟩,⟨(206480770037884292827/147573952589676412928),(584133882499728355609/147573952589676412928)⟩,⟨(-137729468883690029831/36893488147419103232),(-86632381536458028271/73786976294838206464)⟩,⟨(2227187/4194304),(2254721/4194304)⟩⟩

theorem block1035_rectangle_sound : block1035.RectSound := by
  intro t a ht ha
  change (((101/160):ℚ):ℝ)≤t ∧ t≤(((51/80):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2227187/4194304):ℚ):ℝ)≤a ∧ a≤(((2254721/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1035Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1035Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1035Parameters positiveChordBox1035Parameters_valid hbt hba
    positiveChordBox1035Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1035Radius positiveChordBox1035Cells positiveChordBox1035Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1035Boundary positiveChordBox1035Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1035Boundary positiveChordBox1035Cells).radius=(206480770037884292827/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1035Boundary positiveChordBox1035Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1035Boundary positiveChordBox1035Cells).radius=(584133882499728355609/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1035Boundary positiveChordBox1035Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1035Boundary positiveChordBox1035Cells).radius=(-137729468883690029831/36893488147419103232) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1035Boundary positiveChordBox1035Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1035Boundary positiveChordBox1035Cells).radius=(-86632381536458028271/73786976294838206464) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1035_sound : block1035.Sound := by
  intro t ht
  exact block1035_rectangle_sound t (verticalA t) ht (positiveChordBox1035_vertical_enclosure ht.1 ht.2)

def block1036 : Block := ⟨⟨(51/80),(103/160)⟩,⟨(195670148888845445667/147573952589676412928),(571670434781977343757/147573952589676412928)⟩,⟨(-555737505029172450267/147573952589676412928),(-179737219136040552177/147573952589676412928)⟩,⟨(2232301/4194304),(2259691/4194304)⟩⟩

theorem block1036_rectangle_sound : block1036.RectSound := by
  intro t a ht ha
  change (((51/80):ℚ):ℝ)≤t ∧ t≤(((103/160):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2232301/4194304):ℚ):ℝ)≤a ∧ a≤(((2259691/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1036Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1036Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1036Parameters positiveChordBox1036Parameters_valid hbt hba
    positiveChordBox1036Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1036Radius positiveChordBox1036Cells positiveChordBox1036Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1036Boundary positiveChordBox1036Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1036Boundary positiveChordBox1036Cells).radius=(195670148888845445667/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1036Boundary positiveChordBox1036Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1036Boundary positiveChordBox1036Cells).radius=(571670434781977343757/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1036Boundary positiveChordBox1036Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1036Boundary positiveChordBox1036Cells).radius=(-555737505029172450267/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1036Boundary positiveChordBox1036Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1036Boundary positiveChordBox1036Cells).radius=(-179737219136040552177/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1036_sound : block1036.Sound := by
  intro t ht
  exact block1036_rectangle_sound t (verticalA t) ht (positiveChordBox1036_vertical_enclosure ht.1 ht.2)

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.block1023_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1034_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1035_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1036_sound
