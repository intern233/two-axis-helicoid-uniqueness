import TwoAxisHelicoid.PdfSharedChord490Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord490Disk9Cell0_0 : chordRectangleTest 4 sharedChord490Params (29/32) (33/32) (-1/16) (1/16) 22003=true := by decide +kernel
theorem sharedChord490Disk9 {t a : ℝ} (ps : sharedChord490Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord490Bd (9:Fin 10)) (2*jacobiCellRadius sharedChord490Bd (9:Fin 10)) (sharedChord490M 9) t a := by
  rw [show jacobiCellCenter sharedChord490Bd (9:Fin 10)=(31/32) by decide +kernel, show 2*jacobiCellRadius sharedChord490Bd (9:Fin 10)=(1/16) by decide +kernel, show sharedChord490M 9=22003 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((31/32):ℚ)-(1/16)=(29/32) by decide +kernel, show ((31/32):ℚ)+(1/16)=(33/32) by decide +kernel, show -((1/16):ℚ)=(-1/16) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord490Disk9Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord490Disk9
