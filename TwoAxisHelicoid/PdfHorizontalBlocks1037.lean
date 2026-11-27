import TwoAxisHelicoid.PdfHorizontalRowTransfer
import TwoAxisHelicoid.PositiveChordBox1037
import TwoAxisHelicoid.PositiveChordBox1038
import TwoAxisHelicoid.PositiveChordBox1039
import TwoAxisHelicoid.PositiveChordBox1040

namespace TwoAxisHelicoid.PdfHorizontal
open ComplexBall
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block1037 : Block := ⟨⟨(103/160),(13/20)⟩,⟨(92474781369160338749/73786976294838206464),(34953245225507413497/9223372036854775808)⟩,⟨(-70047332459767175701/18446744073709551616),(-93038149404169733577/73786976294838206464)⟩,⟨(2237505/4194304),(566189/1048576)⟩⟩

theorem block1037_rectangle_sound : block1037.RectSound := by
  intro t a ht ha
  change (((103/160):ℚ):ℝ)≤t ∧ t≤(((13/20):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2237505/4194304):ℚ):ℝ)≤a ∧ a≤(((566189/1048576):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1037Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1037Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1037Parameters positiveChordBox1037Parameters_valid hbt hba
    positiveChordBox1037Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1037Radius positiveChordBox1037Cells positiveChordBox1037Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1037Boundary positiveChordBox1037Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1037Boundary positiveChordBox1037Cells).radius=(92474781369160338749/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1037Boundary positiveChordBox1037Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1037Boundary positiveChordBox1037Cells).radius=(34953245225507413497/9223372036854775808) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1037Boundary positiveChordBox1037Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1037Boundary positiveChordBox1037Cells).radius=(-70047332459767175701/18446744073709551616) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1037Boundary positiveChordBox1037Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1037Boundary positiveChordBox1037Cells).radius=(-93038149404169733577/73786976294838206464) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1037_sound : block1037.Sound := by
  intro t ht
  exact block1037_rectangle_sound t (verticalA t) ht (positiveChordBox1037_vertical_enclosure ht.1 ht.2)

def block1038 : Block := ⟨⟨(13/20),(21/32)⟩,⟨(174319117483019987161/147573952589676412928),(546864659343141243399/147573952589676412928)⟩,⟨(-564828608247019575099/147573952589676412928),(-192283066386898318861/147573952589676412928)⟩,⟨(140175/262144),(567479/1048576)⟩⟩

theorem block1038_rectangle_sound : block1038.RectSound := by
  intro t a ht ha
  change (((13/20):ℚ):ℝ)≤t ∧ t≤(((21/32):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((140175/262144):ℚ):ℝ)≤a ∧ a≤(((567479/1048576):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1038Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1038Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1038Parameters positiveChordBox1038Parameters_valid hbt hba
    positiveChordBox1038Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1038Radius positiveChordBox1038Cells positiveChordBox1038Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1038Boundary positiveChordBox1038Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1038Boundary positiveChordBox1038Cells).radius=(174319117483019987161/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1038Boundary positiveChordBox1038Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1038Boundary positiveChordBox1038Cells).radius=(546864659343141243399/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1038Boundary positiveChordBox1038Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1038Boundary positiveChordBox1038Cells).radius=(-564828608247019575099/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1038Boundary positiveChordBox1038Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1038Boundary positiveChordBox1038Cells).radius=(-192283066386898318861/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1038_sound : block1038.Sound := by
  intro t ht
  exact block1038_rectangle_sound t (verticalA t) ht (positiveChordBox1038_vertical_enclosure ht.1 ht.2)

def block1039 : Block := ⟨⟨(21/32),(53/80)⟩,⟨(163772635641595565795/147573952589676412928),(534504276749683483029/147573952589676412928)⟩,⟨(-569082938514854741951/147573952589676412928),(-198351297406766824717/147573952589676412928)⟩,⟨(281023/524288),(2275171/4194304)⟩⟩

theorem block1039_rectangle_sound : block1039.RectSound := by
  intro t a ht ha
  change (((21/32):ℚ):ℝ)≤t ∧ t≤(((53/80):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((281023/524288):ℚ):ℝ)≤a ∧ a≤(((2275171/4194304):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1039Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1039Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1039Parameters positiveChordBox1039Parameters_valid hbt hba
    positiveChordBox1039Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1039Radius positiveChordBox1039Cells positiveChordBox1039Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1039Boundary positiveChordBox1039Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1039Boundary positiveChordBox1039Cells).radius=(163772635641595565795/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1039Boundary positiveChordBox1039Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1039Boundary positiveChordBox1039Cells).radius=(534504276749683483029/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1039Boundary positiveChordBox1039Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1039Boundary positiveChordBox1039Cells).radius=(-569082938514854741951/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1039Boundary positiveChordBox1039Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1039Boundary positiveChordBox1039Cells).radius=(-198351297406766824717/147573952589676412928) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1039_sound : block1039.Sound := by
  intro t ht
  exact block1039_rectangle_sound t (verticalA t) ht (positiveChordBox1039_vertical_enclosure ht.1 ht.2)

def block1040 : Block := ⟨⟨(53/80),(107/160)⟩,⟨(153301898603023572535/147573952589676412928),(522168767678912808625/147573952589676412928)⟩,⟨(-286569683777209487971/73786976294838206464),(-51068124619632434963/36893488147419103232)⟩,⟨(2253659/4194304),(1140261/2097152)⟩⟩

theorem block1040_rectangle_sound : block1040.RectSound := by
  intro t a ht ha
  change (((53/80):ℚ):ℝ)≤t ∧ t≤(((107/160):ℚ):ℝ) at ht
  obtain ⟨htl,htu⟩ := ht
  change (((2253659/4194304):ℚ):ℝ)≤a ∧ a≤(((1140261/2097152):ℚ):ℝ) at ha
  obtain ⟨hal,hau⟩ := ha
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htl
  have ht85 : t ≤ 17/20 := htu.trans (by norm_num)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) hal
  have ha1 : a < 1 := hau.trans_lt (by norm_num)
  have hbt : (positiveChordBox1040Parameters.base.base.height.toBall 64).Contains (t : ℂ) :=
    coarsen_contains (realInterval_contains htl htu) (by decide +kernel)
  have hba : (positiveChordBox1040Parameters.base.base.abscissa.toBall 64).Contains (a : ℂ) :=
    coarsen_contains (realInterval_contains hal hau) (by decide +kernel)
  have hb := jacobiChord_composite_contains ⟨64,12,6⟩ 18446744074 9223372037
    rationalQuadrature32 32 rationalQuadrature32_exact rationalQuadrature32_nodes
    ht0 ht85 positiveChordBox1040Parameters positiveChordBox1040Parameters_valid hbt hba
    positiveChordBox1040Boundary (by decide +kernel) (by decide +kernel)
    positiveChordBox1040Radius positiveChordBox1040Cells positiveChordBox1040Cells_valid
  rw [← pdf_dual_horizontal_integral_chord ht0 (ht85.trans (by norm_num)) ha0 ha1] at hb
  have re := ComplexBall.re_bounds hb
  have im := pdf_horizontal_imag_bounds hb
  have values : (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1040Boundary positiveChordBox1040Cells).center.re-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1040Boundary positiveChordBox1040Cells).radius=(153301898603023572535/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1040Boundary positiveChordBox1040Cells).center.re+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1040Boundary positiveChordBox1040Cells).radius=(522168767678912808625/147573952589676412928) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1040Boundary positiveChordBox1040Cells).center.im-(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1040Boundary positiveChordBox1040Cells).radius=(-286569683777209487971/73786976294838206464) ∧
      (combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1040Boundary positiveChordBox1040Cells).center.im+(combineJacobiChordCells ⟨64,12,6⟩ positiveChordBox1040Boundary positiveChordBox1040Cells).radius=(-51068124619632434963/36893488147419103232) := by decide +kernel
  rw [values.1,values.2.1] at re
  rw [values.2.2.1,values.2.2.2] at im
  exact ⟨re,im⟩

theorem block1040_sound : block1040.Sound := by
  intro t ht
  exact block1040_rectangle_sound t (verticalA t) ht (positiveChordBox1040_vertical_enclosure ht.1 ht.2)

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.block1037_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1038_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1039_sound
#print axioms TwoAxisHelicoid.PdfHorizontal.block1040_sound
