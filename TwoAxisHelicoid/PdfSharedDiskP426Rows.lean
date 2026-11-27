import TwoAxisHelicoid.PdfSharedChord426Disks
import TwoAxisHelicoid.PdfSharedDiskP426RowsSamples

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP426Box : HorizontalRectangle := ⟨(143/400),(77/200),(1105678609191/2199023255552),(3326240168225/6597069766656),(1392970588874784508656782746898009/324518553658426726783156020576256),(4432420655578112894602209436159577/324518553658426726783156020576256),(-446540245821503979201329274274551/81129638414606681695789005144064),(2730830531052250286143559052683337/649037107316853453566312041152512),true,[]⟩
noncomputable def sharedDiskP426Grid : CGrid := momentChordGrid sharedDiskP426Params chordGaussRule6 1 sharedChord426Bd sharedChord426M (995300573/4503599627370496)
theorem sharedDiskP426Columns : containedInReported sharedDiskP426Grid.re sharedDiskP426Box.reLo sharedDiskP426Box.reHi=true ∧ containedInReported sharedDiskP426Grid.im sharedDiskP426Box.imLo sharedDiskP426Box.imHi=true := by
  rw [sharedDiskP426Grid,momentChordGrid_eq_tabulated sharedDiskP426Params chordGaussRule6 1 sharedChord426Bd sharedChord426M (995300573/4503599627370496) sharedChord426Gauss6Points sharedChord426Gauss6Weights sharedDiskP426Values sharedChord426Gauss6Points_eq sharedChord426Gauss6Weights_eq sharedDiskP426Values_eq]
  decide +kernel
theorem sharedDiskP426Sound : sharedDiskP426Box.Sound := by
  intro t a tl tu al au
  change (((143/400):ℚ):ℝ)≤t at tl
  change t≤(((77/200):ℚ):ℝ) at tu
  change (((1105678609191/2199023255552):ℚ):ℝ)≤a at al
  change a≤(((3326240168225/6597069766656):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP426Params_ok] at ps
  have band := sharedChord426ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((143/400):ℚ)≤(143/400))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/200):ℚ)≤(31/80)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((1105678609191/2199023255552):ℚ)≤(1105678609191/2199023255552))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3326240168225/6597069766656):ℚ)≤(1109047628555/2199023255552)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule6 chordGaussRule6_nodes chordGaussRule6_half_disk 1 sharedChord426Bd (by decide +kernel) (by decide +kernel) sharedChord426M (by decide +kernel) (sharedChord426Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP426Columns.1 sharedDiskP426Columns.2
def sharedDiskP426Rows : List SignRow := [positive_426.toSignRow, positive_427.toSignRow, positive_428.toSignRow, positive_429.toSignRow, positive_430.toSignRow, positive_431.toSignRow, positive_432.toSignRow, positive_433.toSignRow, positive_434.toSignRow, positive_435.toSignRow, positive_436.toSignRow]
theorem sharedDiskP426Rows_actual : ∀ r∈sharedDiskP426Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP426Rows.all (sharedDiskP426Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP426Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP426Rows_actual
