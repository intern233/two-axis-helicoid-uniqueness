import TwoAxisHelicoid.PdfSharedChord490Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord490Disk2Cell0_0 : chordRectangleTest 4 sharedChord490Params (-15/16) (-13/16) (-1/8) 0 297201=true := by decide +kernel
theorem sharedChord490Disk2Cell0_1 : chordRectangleTest 4 sharedChord490Params (-15/16) (-13/16) 0 (1/8) 297201=true := by decide +kernel
theorem sharedChord490Disk2Cell1_0 : chordRectangleTest 4 sharedChord490Params (-13/16) (-11/16) (-1/8) 0 297201=true := by decide +kernel
theorem sharedChord490Disk2Cell1_1 : chordRectangleTest 4 sharedChord490Params (-13/16) (-11/16) 0 (1/8) 297201=true := by decide +kernel
theorem sharedChord490Disk2 {t a : ℝ} (ps : sharedChord490Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord490Bd (2:Fin 10)) (2*jacobiCellRadius sharedChord490Bd (2:Fin 10)) (sharedChord490M 2) t a := by
  rw [show jacobiCellCenter sharedChord490Bd (2:Fin 10)=(-13/16) by decide +kernel, show 2*jacobiCellRadius sharedChord490Bd (2:Fin 10)=(1/8) by decide +kernel, show sharedChord490M 2=297201 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-13/16):ℚ)-(1/8)=(-15/16) by decide +kernel, show ((-13/16):ℚ)+(1/8)=(-11/16) by decide +kernel, show -((1/8):ℚ)=(-1/8) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord490Disk2Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord490Disk2Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord490Disk2Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord490Disk2Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord490Disk2
