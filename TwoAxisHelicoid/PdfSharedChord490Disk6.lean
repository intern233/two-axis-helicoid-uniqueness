import TwoAxisHelicoid.PdfSharedChord490Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord490Disk6Cell0_0 : chordRectangleTest 4 sharedChord490Params (3/8) (5/8) (-1/4) 0 619095=true := by decide +kernel
theorem sharedChord490Disk6Cell0_1 : chordRectangleTest 4 sharedChord490Params (3/8) (5/8) 0 (1/4) 619095=true := by decide +kernel
theorem sharedChord490Disk6Cell1_0 : chordRectangleTest 4 sharedChord490Params (5/8) (7/8) (-1/4) 0 619095=true := by decide +kernel
theorem sharedChord490Disk6Cell1_1 : chordRectangleTest 4 sharedChord490Params (5/8) (7/8) 0 (1/4) 619095=true := by decide +kernel
theorem sharedChord490Disk6 {t a : ℝ} (ps : sharedChord490Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord490Bd (6:Fin 10)) (2*jacobiCellRadius sharedChord490Bd (6:Fin 10)) (sharedChord490M 6) t a := by
  rw [show jacobiCellCenter sharedChord490Bd (6:Fin 10)=(5/8) by decide +kernel, show 2*jacobiCellRadius sharedChord490Bd (6:Fin 10)=(1/4) by decide +kernel, show sharedChord490M 6=619095 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((5/8):ℚ)-(1/4)=(3/8) by decide +kernel, show ((5/8):ℚ)+(1/4)=(7/8) by decide +kernel, show -((1/4):ℚ)=(-1/4) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord490Disk6Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord490Disk6Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord490Disk6Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord490Disk6Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord490Disk6
