import TwoAxisHelicoid.PdfSharedChord490Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord490Disk7Cell0_0 : chordRectangleTest 4 sharedChord490Params (11/16) (3/4) (-1/8) (-1/16) 166035=true := by decide +kernel
theorem sharedChord490Disk7Cell0_1 : chordRectangleTest 4 sharedChord490Params (11/16) (3/4) (-1/16) 0 166035=true := by decide +kernel
theorem sharedChord490Disk7Cell0_2 : chordRectangleTest 4 sharedChord490Params (11/16) (3/4) 0 (1/16) 166035=true := by decide +kernel
theorem sharedChord490Disk7Cell0_3 : chordRectangleTest 4 sharedChord490Params (11/16) (3/4) (1/16) (1/8) 166035=true := by decide +kernel
theorem sharedChord490Disk7Cell1_0 : chordRectangleTest 4 sharedChord490Params (3/4) (13/16) (-1/8) (-1/16) 166035=true := by decide +kernel
theorem sharedChord490Disk7Cell1_1 : chordRectangleTest 4 sharedChord490Params (3/4) (13/16) (-1/16) 0 166035=true := by decide +kernel
theorem sharedChord490Disk7Cell1_2 : chordRectangleTest 4 sharedChord490Params (3/4) (13/16) 0 (1/16) 166035=true := by decide +kernel
theorem sharedChord490Disk7Cell1_3 : chordRectangleTest 4 sharedChord490Params (3/4) (13/16) (1/16) (1/8) 166035=true := by decide +kernel
theorem sharedChord490Disk7Cell2_0 : chordRectangleTest 4 sharedChord490Params (13/16) (7/8) (-1/8) (-1/16) 166035=true := by decide +kernel
theorem sharedChord490Disk7Cell2_1 : chordRectangleTest 4 sharedChord490Params (13/16) (7/8) (-1/16) 0 166035=true := by decide +kernel
theorem sharedChord490Disk7Cell2_2 : chordRectangleTest 4 sharedChord490Params (13/16) (7/8) 0 (1/16) 166035=true := by decide +kernel
theorem sharedChord490Disk7Cell2_3 : chordRectangleTest 4 sharedChord490Params (13/16) (7/8) (1/16) (1/8) 166035=true := by decide +kernel
theorem sharedChord490Disk7Cell3_0 : chordRectangleTest 4 sharedChord490Params (7/8) (15/16) (-1/8) (-1/16) 166035=true := by decide +kernel
theorem sharedChord490Disk7Cell3_1 : chordRectangleTest 4 sharedChord490Params (7/8) (15/16) (-1/16) 0 166035=true := by decide +kernel
theorem sharedChord490Disk7Cell3_2 : chordRectangleTest 4 sharedChord490Params (7/8) (15/16) 0 (1/16) 166035=true := by decide +kernel
theorem sharedChord490Disk7Cell3_3 : chordRectangleTest 4 sharedChord490Params (7/8) (15/16) (1/16) (1/8) 166035=true := by decide +kernel
theorem sharedChord490Disk7 {t a : ℝ} (ps : sharedChord490Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord490Bd (7:Fin 10)) (2*jacobiCellRadius sharedChord490Bd (7:Fin 10)) (sharedChord490M 7) t a := by
  rw [show jacobiCellCenter sharedChord490Bd (7:Fin 10)=(13/16) by decide +kernel, show 2*jacobiCellRadius sharedChord490Bd (7:Fin 10)=(1/8) by decide +kernel, show sharedChord490M 7=166035 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((13/16):ℚ)-(1/8)=(11/16) by decide +kernel, show ((13/16):ℚ)+(1/8)=(15/16) by decide +kernel, show -((1/8):ℚ)=(-1/8) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord490Disk7Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord490Disk7Cell0_1
  have piece0_2 := chordRectangleTest_sound ps ht sharedChord490Disk7Cell0_2
  have piece0_3 := chordRectangleTest_sound ps ht sharedChord490Disk7Cell0_3
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord490Disk7Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord490Disk7Cell1_1
  have piece1_2 := chordRectangleTest_sound ps ht sharedChord490Disk7Cell1_2
  have piece1_3 := chordRectangleTest_sound ps ht sharedChord490Disk7Cell1_3
  have piece2_0 := chordRectangleTest_sound ps ht sharedChord490Disk7Cell2_0
  have piece2_1 := chordRectangleTest_sound ps ht sharedChord490Disk7Cell2_1
  have piece2_2 := chordRectangleTest_sound ps ht sharedChord490Disk7Cell2_2
  have piece2_3 := chordRectangleTest_sound ps ht sharedChord490Disk7Cell2_3
  have piece3_0 := chordRectangleTest_sound ps ht sharedChord490Disk7Cell3_0
  have piece3_1 := chordRectangleTest_sound ps ht sharedChord490Disk7Cell3_1
  have piece3_2 := chordRectangleTest_sound ps ht sharedChord490Disk7Cell3_2
  have piece3_3 := chordRectangleTest_sound ps ht sharedChord490Disk7Cell3_3
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinX (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece0_2 piece0_3)) (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece1_0 piece1_1) (ChordRectangleBound.joinY piece1_2 piece1_3))) (ChordRectangleBound.joinX (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece2_0 piece2_1) (ChordRectangleBound.joinY piece2_2 piece2_3)) (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece3_0 piece3_1) (ChordRectangleBound.joinY piece3_2 piece3_3))))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord490Disk7
