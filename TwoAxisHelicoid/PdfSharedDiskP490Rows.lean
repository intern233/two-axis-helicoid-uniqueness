import TwoAxisHelicoid.PdfSharedChord490Disks
import TwoAxisHelicoid.PdfMomentChordQuadrature

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP490Box : HorizontalRectangle := ⟨(63/100),(129/200),(291382337698939/549755813888000),(296734670424149/549755813888000),(89053402486384538373668149727189/162259276829213363391578010288128),(3001020171344898243627459551136799/649037107316853453566312041152512),(-751380526336769422450713919642099/162259276829213363391578010288128),(-60894425318069437467744170564083/162259276829213363391578010288128),true,[]⟩
def sharedDiskP490Params : ChordParams := ⟨⟨(-9270165264322248947552),(-8255110690802907805332),true⟩,⟨2710046822240459639347395,2833264197946857373122177,true⟩,⟨81933213273781702719538,91461635766597394293732,true⟩,⟨116032030401088281343712,128482062281660397166641,true⟩,⟨198277649592620448774696,210289735156063185606732,true⟩,⟨1190526576341392739902660,1192527573126518129999062,true⟩,⟨(-2973361795982170076186840),(-2899340733439943857673502),true⟩,⟨⟨1126341143940947658780743,1259983290581186804086220,true⟩,⟨(-470),470,true⟩⟩⟩
theorem sharedDiskP490Params_ok : chordParams (Grid.ofRats (63/100) (129/200)) (Grid.ofRats (291382337698939/549755813888000) (296734670424149/549755813888000))=sharedDiskP490Params := by decide +kernel
noncomputable def sharedDiskP490Grid : CGrid := momentChordGrid sharedDiskP490Params rationalQuadrature12 2 sharedChord490Bd sharedChord490M (3/10^9)
theorem sharedDiskP490Columns : containedInReported sharedDiskP490Grid.re sharedDiskP490Box.reLo sharedDiskP490Box.reHi=true ∧ containedInReported sharedDiskP490Grid.im sharedDiskP490Box.imLo sharedDiskP490Box.imHi=true := by decide +kernel
theorem sharedDiskP490Sound : sharedDiskP490Box.Sound := by
  intro t a tl tu al au
  change (((63/100):ℚ):ℝ)≤t at tl
  change t≤(((129/200):ℚ):ℝ) at tu
  change (((291382337698939/549755813888000):ℚ):ℝ)≤a at al
  change a≤(((296734670424149/549755813888000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP490Params_ok] at ps
  have band := sharedChord490ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((63/100):ℚ)≤(63/100))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((129/200):ℚ)≤(129/200)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((291382337698939/549755813888000):ℚ)≤(291382337698939/549755813888000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((296734670424149/549755813888000):ℚ)≤(296734670424149/549755813888000)))) ht
  have result := momentChordGrid_sound ps ht hu rationalQuadrature12 rationalQuadrature12_nodes twelve_point_half_disk_factor 2 sharedChord490Bd (by decide +kernel) (by decide +kernel) sharedChord490M (by decide +kernel) (sharedChord490Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP490Columns.1 sharedDiskP490Columns.2
def sharedDiskP490Rows : List SignRow := [positive_490.toSignRow, positive_491.toSignRow, positive_492.toSignRow]
theorem sharedDiskP490Rows_actual : ∀ r∈sharedDiskP490Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP490Rows.all (sharedDiskP490Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP490Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP490Rows_actual
