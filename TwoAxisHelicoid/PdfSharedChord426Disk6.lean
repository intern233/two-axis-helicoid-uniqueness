import TwoAxisHelicoid.PdfSharedChord426Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord426Disk6Cell0_0 : chordRectangleTest 4 sharedChord426Params (-3/4) (1/4) (-1/2) (1/2) 8747=true := by decide +kernel
theorem sharedChord426Disk6 {t a : ℝ} (ps : sharedChord426Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord426Bd (6:Fin 14)) (2*jacobiCellRadius sharedChord426Bd (6:Fin 14)) (sharedChord426M 6) t a := by
  rw [show jacobiCellCenter sharedChord426Bd (6:Fin 14)=(-1/4) by decide +kernel, show 2*jacobiCellRadius sharedChord426Bd (6:Fin 14)=(1/2) by decide +kernel, show sharedChord426M 6=8747 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-1/4):ℚ)-(1/2)=(-3/4) by decide +kernel, show ((-1/4):ℚ)+(1/2)=(1/4) by decide +kernel, show -((1/2):ℚ)=(-1/2) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord426Disk6Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord426Disk6
