import TwoAxisHelicoid.PdfSharedChord490Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord490Disk3Cell0_0 : chordRectangleTest 4 sharedChord490Params (-7/8) (-3/8) (-1/4) (1/4) 9204457=true := by decide +kernel
theorem sharedChord490Disk3 {t a : ℝ} (ps : sharedChord490Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord490Bd (3:Fin 10)) (2*jacobiCellRadius sharedChord490Bd (3:Fin 10)) (sharedChord490M 3) t a := by
  rw [show jacobiCellCenter sharedChord490Bd (3:Fin 10)=(-5/8) by decide +kernel, show 2*jacobiCellRadius sharedChord490Bd (3:Fin 10)=(1/4) by decide +kernel, show sharedChord490M 3=9204457 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-5/8):ℚ)-(1/4)=(-7/8) by decide +kernel, show ((-5/8):ℚ)+(1/4)=(-3/8) by decide +kernel, show -((1/4):ℚ)=(-1/4) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord490Disk3Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord490Disk3
