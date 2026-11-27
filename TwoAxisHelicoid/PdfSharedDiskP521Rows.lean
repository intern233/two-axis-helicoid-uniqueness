import TwoAxisHelicoid.PdfSharedChord521Disks
import TwoAxisHelicoid.PdfSharedDiskP521RowsSamples

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP521Box : HorizontalRectangle := ⟨(77/100),(31/40),(930253465593763/1649267441664000),(936695916537763/1649267441664000),(298018361568119735078733850719983/2596148429267413814265248164610048),(4953608767772332923894681176749807/2596148429267413814265248164610048),(-1273653828139148703976996434279137/324518553658426726783156020576256),(-678509396525139043446125407435489/324518553658426726783156020576256),true,[]⟩
noncomputable def sharedDiskP521Grid : CGrid := momentChordGrid sharedDiskP521Params rationalQuadrature12 2 sharedChord521Bd sharedChord521M (3/10^9)
theorem sharedDiskP521Columns : containedInReported sharedDiskP521Grid.re sharedDiskP521Box.reLo sharedDiskP521Box.reHi=true ∧ containedInReported sharedDiskP521Grid.im sharedDiskP521Box.imLo sharedDiskP521Box.imHi=true := by
  rw [sharedDiskP521Grid,momentChordGrid_eq_tabulated sharedDiskP521Params rationalQuadrature12 2 sharedChord521Bd sharedChord521M (3/10^9) sharedChord521Rule12Points sharedChord521Rule12Weights sharedDiskP521Values sharedChord521Rule12Points_eq sharedChord521Rule12Weights_eq sharedDiskP521Values_eq]
  decide +kernel
theorem sharedDiskP521Sound : sharedDiskP521Box.Sound := by
  intro t a tl tu al au
  change (((77/100):ℚ):ℝ)≤t at tl
  change t≤(((31/40):ℚ):ℝ) at tu
  change (((930253465593763/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((936695916537763/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP521Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(77/100))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((31/40):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(930253465593763/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((936695916537763/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu rationalQuadrature12 rationalQuadrature12_nodes twelve_point_half_disk_factor 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP521Columns.1 sharedDiskP521Columns.2
def sharedDiskP521Rows : List SignRow := [positive_521.toSignRow]
theorem sharedDiskP521Rows_actual : ∀ r∈sharedDiskP521Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP521Rows.all (sharedDiskP521Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP521Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP521Rows_actual
