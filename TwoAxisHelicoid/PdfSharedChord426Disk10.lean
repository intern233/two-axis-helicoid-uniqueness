import TwoAxisHelicoid.PdfSharedChord426Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord426Disk10Cell0_0 : chordRectangleTest 4 sharedChord426Params (27/32) (31/32) (-1/16) (1/16) 61603=true := by decide +kernel
theorem sharedChord426Disk10 {t a : ℝ} (ps : sharedChord426Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord426Bd (10:Fin 14)) (2*jacobiCellRadius sharedChord426Bd (10:Fin 14)) (sharedChord426M 10) t a := by
  rw [show jacobiCellCenter sharedChord426Bd (10:Fin 14)=(29/32) by decide +kernel, show 2*jacobiCellRadius sharedChord426Bd (10:Fin 14)=(1/16) by decide +kernel, show sharedChord426M 10=61603 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((29/32):ℚ)-(1/16)=(27/32) by decide +kernel, show ((29/32):ℚ)+(1/16)=(31/32) by decide +kernel, show -((1/16):ℚ)=(-1/16) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord426Disk10Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord426Disk10
