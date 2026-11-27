import TwoAxisHelicoid.PdfSharedChord426Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord426Disk9Cell0_0 : chordRectangleTest 4 sharedChord426Params (11/16) (15/16) (-1/8) (1/8) 7658=true := by decide +kernel
theorem sharedChord426Disk9 {t a : ℝ} (ps : sharedChord426Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord426Bd (9:Fin 14)) (2*jacobiCellRadius sharedChord426Bd (9:Fin 14)) (sharedChord426M 9) t a := by
  rw [show jacobiCellCenter sharedChord426Bd (9:Fin 14)=(13/16) by decide +kernel, show 2*jacobiCellRadius sharedChord426Bd (9:Fin 14)=(1/8) by decide +kernel, show sharedChord426M 9=7658 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((13/16):ℚ)-(1/8)=(11/16) by decide +kernel, show ((13/16):ℚ)+(1/8)=(15/16) by decide +kernel, show -((1/8):ℚ)=(-1/8) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord426Disk9Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord426Disk9
