import TwoAxisHelicoid.PdfSharedChord521Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord521Disk7Cell0_0 : chordRectangleTest 4 sharedChord521Params (11/16) (13/16) (-1/8) 0 3362141=true := by decide +kernel
theorem sharedChord521Disk7Cell0_1 : chordRectangleTest 4 sharedChord521Params (11/16) (13/16) 0 (1/8) 3362141=true := by decide +kernel
theorem sharedChord521Disk7Cell1_0 : chordRectangleTest 4 sharedChord521Params (13/16) (15/16) (-1/8) 0 3362141=true := by decide +kernel
theorem sharedChord521Disk7Cell1_1 : chordRectangleTest 4 sharedChord521Params (13/16) (15/16) 0 (1/8) 3362141=true := by decide +kernel
theorem sharedChord521Disk7 {t a : ℝ} (ps : sharedChord521Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord521Bd (7:Fin 9)) (2*jacobiCellRadius sharedChord521Bd (7:Fin 9)) (sharedChord521M 7) t a := by
  rw [show jacobiCellCenter sharedChord521Bd (7:Fin 9)=(13/16) by decide +kernel, show 2*jacobiCellRadius sharedChord521Bd (7:Fin 9)=(1/8) by decide +kernel, show sharedChord521M 7=3362141 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((13/16):ℚ)-(1/8)=(11/16) by decide +kernel, show ((13/16):ℚ)+(1/8)=(15/16) by decide +kernel, show -((1/8):ℚ)=(-1/8) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord521Disk7Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord521Disk7Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord521Disk7Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord521Disk7Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord521Disk7
