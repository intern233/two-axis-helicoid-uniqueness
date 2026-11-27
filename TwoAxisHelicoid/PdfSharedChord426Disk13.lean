import TwoAxisHelicoid.PdfSharedChord426Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord426Disk13Cell0_0 : chordRectangleTest 4 sharedChord426Params (125/128) (127/128) (-1/64) 0 418193=true := by decide +kernel
theorem sharedChord426Disk13Cell0_1 : chordRectangleTest 4 sharedChord426Params (125/128) (127/128) 0 (1/64) 418193=true := by decide +kernel
theorem sharedChord426Disk13Cell1_0 : chordRectangleTest 4 sharedChord426Params (127/128) (129/128) (-1/64) 0 418193=true := by decide +kernel
theorem sharedChord426Disk13Cell1_1 : chordRectangleTest 4 sharedChord426Params (127/128) (129/128) 0 (1/64) 418193=true := by decide +kernel
theorem sharedChord426Disk13 {t a : ℝ} (ps : sharedChord426Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord426Bd (13:Fin 14)) (2*jacobiCellRadius sharedChord426Bd (13:Fin 14)) (sharedChord426M 13) t a := by
  rw [show jacobiCellCenter sharedChord426Bd (13:Fin 14)=(127/128) by decide +kernel, show 2*jacobiCellRadius sharedChord426Bd (13:Fin 14)=(1/64) by decide +kernel, show sharedChord426M 13=418193 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((127/128):ℚ)-(1/64)=(125/128) by decide +kernel, show ((127/128):ℚ)+(1/64)=(129/128) by decide +kernel, show -((1/64):ℚ)=(-1/64) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord426Disk13Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord426Disk13Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord426Disk13Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord426Disk13Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord426Disk13
