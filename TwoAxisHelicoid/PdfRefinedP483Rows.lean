import TwoAxisHelicoid.PdfRefinedChordOriginal
import TwoAxisHelicoid.PositiveChordBox1031

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open ComplexBall CertificateData CertificateSemantics

def refinedP483Box : HorizontalRectangle := ⟨(119/200), (3/5), (3455122271501/6597069766656), (3506661879053/6597069766656), (729196590693933642360590213086305/1298074214633706907132624082305024), (3726958289998923037577913585647153/649037107316853453566312041152512), (-3190197504254372091141127004458701/649037107316853453566312041152512), (645344163572542221721265186595431/1298074214633706907132624082305024), true, []⟩
def refinedP483Block1031Params : ChordParams := ⟨⟨(-6433377908091911306819),(-6156447082510568837991),true⟩,⟨2965261521762099533554447,3040047759256375824034985,true⟩,⟨73033519206881844322647,77883391882467751557804,true⟩,⟨97789667700789362799550,104030138452242299224611,true⟩,⟨171628694415989021381129,175486343262772223245485,true⟩,⟨1196127172636380157458460,1196675311086726712814176,true⟩,⟨(-3159215433649026129343528),(-3131453615261318551621408),true⟩,⟨⟨1163408862926786130589300,1230013387724330342874536,true⟩,⟨(-48),48,true⟩⟩⟩
theorem refinedP483Block1031Params_ok : chordParams (Grid.ofRats (119/200) (3/5)) (Grid.ofRats (3455122271501/6597069766656) (3506661879053/6597069766656))=refinedP483Block1031Params := by decide +kernel
def refinedP483Block1031Nodes (i : Fin 10) (j : Fin 32) : Bool :=
  match i.val,j.val with
  | 0, 12 => true
  | 7, 6 => true
  | 7, 7 => true
  | 7, 8 => true
  | 7, 9 => true
  | 7, 10 => true
  | 7, 11 => true
  | 7, 12 => true
  | 7, 13 => true
  | 7, 14 => true
  | 7, 15 => true
  | 7, 29 => true
  | 7, 30 => true
  | 7, 31 => true
  | 8, 12 => true
  | 8, 13 => true
  | 8, 14 => true
  | 8, 15 => true
  | 8, 28 => true
  | 8, 29 => true
  | 8, 30 => true
  | 8, 31 => true
  | _, _ => false
noncomputable def refinedP483Block1031Grid : CGrid := refinedChordQuadrature ⟨64,12,6⟩ rationalQuadrature32 32 4 refinedP483Block1031Params positiveChordBox1031Boundary positiveChordBox1031Radius positiveChordBox1031Cells refinedP483Block1031Nodes
theorem refinedP483Block1031Columns : containedInReported refinedP483Block1031Grid.re refinedP483Box.reLo refinedP483Box.reHi=true ∧ containedInReported refinedP483Block1031Grid.im refinedP483Box.imLo refinedP483Box.imHi=true := by decide +kernel
theorem refinedP483Block1031Sound {t a : ℝ} (tl : (((119/200):ℚ):ℝ)≤t) (tu : t≤(((3/5):ℚ):ℝ)) (al : (((3455122271501/6597069766656):ℚ):ℝ)≤a) (au : a≤(((3506661879053/6597069766656):ℚ):ℝ)) : refinedP483Box.Encloses (sourceHorizontalIntegral true t a) := by
  have tp : 0<t := lt_of_lt_of_le (by norm_num) tl
  have up : t≤7/5 := tu.trans (by norm_num)
  have bt : (positiveChordBox1031Parameters.base.base.height.toBall 64).Contains (t:ℂ) := coarsen_contains (realInterval_contains tl tu) (by decide +kernel)
  have ba : (positiveChordBox1031Parameters.base.base.abscissa.toBall 64).Contains (a:ℂ) := coarsen_contains (realInterval_contains al au) (by decide +kernel)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) tp
  rw [refinedP483Block1031Params_ok] at ps
  have result := refinedChordQuadrature_sound ⟨64,12,6⟩ rationalQuadrature32 rationalQuadrature32_exact rationalQuadrature32_nodes tp up positiveChordBox1031Parameters_valid bt ba ps 4 positiveChordBox1031Boundary (by decide +kernel) (by decide +kernel) positiveChordBox1031Radius positiveChordBox1031Cells positiveChordBox1031Cells_valid refinedP483Block1031Nodes
  exact refined_dual_output_encloses tp up (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result refinedP483Block1031Columns.1 refinedP483Block1031Columns.2

theorem refinedP483Sound : refinedP483Box.Sound := by
  intro t a t0 t1 a0 a1
  change (((119/200):ℚ):ℝ)≤t at t0
  change t≤(((3/5):ℚ):ℝ) at t1
  change (((3455122271501/6597069766656):ℚ):ℝ)≤a at a0
  change a≤(((3506661879053/6597069766656):ℚ):ℝ) at a1
  exact refinedP483Block1031Sound t0 t1 a0 a1
def refinedP483Rows : List SignRow := [positive_483.toSignRow]
theorem refinedP483Rows_actual : ∀ r∈refinedP483Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have cover : refinedP483Rows.all (refinedP483Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound refinedP483Sound (List.all_eq_true.mp cover r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.refinedP483Rows_actual
