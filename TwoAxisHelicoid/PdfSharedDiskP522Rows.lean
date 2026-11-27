import TwoAxisHelicoid.PdfSharedChord521Disks
import TwoAxisHelicoid.PdfSharedDiskP522RowsSamples

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP522Box : HorizontalRectangle := ⟨(31/40),(39/50),(932480001480701/1649267441664000),(938922452424701/1649267441664000),(380645794654803861846333402180881/5192296858534827628530496329220096),(4764225716837036615928097928803977/2596148429267413814265248164610048),(-5083555271244064231714764246287437/1298074214633706907132624082305024),(-2744432193844856278243217122329677/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP522Grid : CGrid := momentChordGrid sharedDiskP522Params rationalQuadrature12 2 sharedChord521Bd sharedChord521M (3/10^9)
theorem sharedDiskP522Columns : containedInReported sharedDiskP522Grid.re sharedDiskP522Box.reLo sharedDiskP522Box.reHi=true ∧ containedInReported sharedDiskP522Grid.im sharedDiskP522Box.imLo sharedDiskP522Box.imHi=true := by
  rw [sharedDiskP522Grid,momentChordGrid_eq_tabulated sharedDiskP522Params rationalQuadrature12 2 sharedChord521Bd sharedChord521M (3/10^9) sharedChord521Rule12Points sharedChord521Rule12Weights sharedDiskP522Values sharedChord521Rule12Points_eq sharedChord521Rule12Weights_eq sharedDiskP522Values_eq]
  decide +kernel
theorem sharedDiskP522Sound : sharedDiskP522Box.Sound := by
  intro t a tl tu al au
  change (((31/40):ℚ):ℝ)≤t at tl
  change t≤(((39/50):ℚ):ℝ) at tu
  change (((932480001480701/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((938922452424701/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP522Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(31/40))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((39/50):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(932480001480701/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((938922452424701/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu rationalQuadrature12 rationalQuadrature12_nodes twelve_point_half_disk_factor 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP522Columns.1 sharedDiskP522Columns.2
def sharedDiskP522Rows : List SignRow := [positive_522.toSignRow]
theorem sharedDiskP522Rows_actual : ∀ r∈sharedDiskP522Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP522Rows.all (sharedDiskP522Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP522Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP522Rows_actual
