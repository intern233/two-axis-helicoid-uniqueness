import TwoAxisHelicoid.PdfSharedChord469Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord469Disk0Cell0_0 : chordRectangleTest 4 sharedChord469Params (-65/64) (-61/64) (-1/32) (1/32) 693405=true := by decide +kernel
theorem sharedChord469Disk0 {t a : ℝ} (ps : sharedChord469Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord469Bd (0:Fin 15)) (2*jacobiCellRadius sharedChord469Bd (0:Fin 15)) (sharedChord469M 0) t a := by
  rw [show jacobiCellCenter sharedChord469Bd (0:Fin 15)=(-63/64) by decide +kernel, show 2*jacobiCellRadius sharedChord469Bd (0:Fin 15)=(1/32) by decide +kernel, show sharedChord469M 0=693405 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-63/64):ℚ)-(1/32)=(-65/64) by decide +kernel, show ((-63/64):ℚ)+(1/32)=(-61/64) by decide +kernel, show -((1/32):ℚ)=(-1/32) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord469Disk0Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord469Disk1Cell0_0 : chordRectangleTest 4 sharedChord469Params (-63/64) (-59/64) (-1/32) (1/32) 445802=true := by decide +kernel
theorem sharedChord469Disk1 {t a : ℝ} (ps : sharedChord469Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord469Bd (1:Fin 15)) (2*jacobiCellRadius sharedChord469Bd (1:Fin 15)) (sharedChord469M 1) t a := by
  rw [show jacobiCellCenter sharedChord469Bd (1:Fin 15)=(-61/64) by decide +kernel, show 2*jacobiCellRadius sharedChord469Bd (1:Fin 15)=(1/32) by decide +kernel, show sharedChord469M 1=445802 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-61/64):ℚ)-(1/32)=(-63/64) by decide +kernel, show ((-61/64):ℚ)+(1/32)=(-59/64) by decide +kernel, show -((1/32):ℚ)=(-1/32) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord469Disk1Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord469Disk2Cell0_0 : chordRectangleTest 4 sharedChord469Params (-61/64) (-57/64) (-1/32) (1/32) 36386=true := by decide +kernel
theorem sharedChord469Disk2 {t a : ℝ} (ps : sharedChord469Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord469Bd (2:Fin 15)) (2*jacobiCellRadius sharedChord469Bd (2:Fin 15)) (sharedChord469M 2) t a := by
  rw [show jacobiCellCenter sharedChord469Bd (2:Fin 15)=(-59/64) by decide +kernel, show 2*jacobiCellRadius sharedChord469Bd (2:Fin 15)=(1/32) by decide +kernel, show sharedChord469M 2=36386 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-59/64):ℚ)-(1/32)=(-61/64) by decide +kernel, show ((-59/64):ℚ)+(1/32)=(-57/64) by decide +kernel, show -((1/32):ℚ)=(-1/32) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord469Disk2Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord469Disk3Cell0_0 : chordRectangleTest 4 sharedChord469Params (-59/64) (-55/64) (-1/32) (1/32) 3480=true := by decide +kernel
theorem sharedChord469Disk3 {t a : ℝ} (ps : sharedChord469Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord469Bd (3:Fin 15)) (2*jacobiCellRadius sharedChord469Bd (3:Fin 15)) (sharedChord469M 3) t a := by
  rw [show jacobiCellCenter sharedChord469Bd (3:Fin 15)=(-57/64) by decide +kernel, show 2*jacobiCellRadius sharedChord469Bd (3:Fin 15)=(1/32) by decide +kernel, show sharedChord469M 3=3480 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-57/64):ℚ)-(1/32)=(-59/64) by decide +kernel, show ((-57/64):ℚ)+(1/32)=(-55/64) by decide +kernel, show -((1/32):ℚ)=(-1/32) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord469Disk3Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord469Disk4Cell0_0 : chordRectangleTest 4 sharedChord469Params (-15/16) (-7/8) (-1/8) (-1/16) 477114=true := by decide +kernel
theorem sharedChord469Disk4Cell0_1 : chordRectangleTest 4 sharedChord469Params (-15/16) (-7/8) (-1/16) 0 477114=true := by decide +kernel
theorem sharedChord469Disk4Cell0_2 : chordRectangleTest 4 sharedChord469Params (-15/16) (-7/8) 0 (1/16) 477114=true := by decide +kernel
theorem sharedChord469Disk4Cell0_3 : chordRectangleTest 4 sharedChord469Params (-15/16) (-7/8) (1/16) (1/8) 477114=true := by decide +kernel
theorem sharedChord469Disk4Cell1_0 : chordRectangleTest 4 sharedChord469Params (-7/8) (-13/16) (-1/8) (-1/16) 477114=true := by decide +kernel
theorem sharedChord469Disk4Cell1_1 : chordRectangleTest 4 sharedChord469Params (-7/8) (-13/16) (-1/16) 0 477114=true := by decide +kernel
theorem sharedChord469Disk4Cell1_2 : chordRectangleTest 4 sharedChord469Params (-7/8) (-13/16) 0 (1/16) 477114=true := by decide +kernel
theorem sharedChord469Disk4Cell1_3 : chordRectangleTest 4 sharedChord469Params (-7/8) (-13/16) (1/16) (1/8) 477114=true := by decide +kernel
theorem sharedChord469Disk4Cell2_0 : chordRectangleTest 4 sharedChord469Params (-13/16) (-3/4) (-1/8) (-1/16) 477114=true := by decide +kernel
theorem sharedChord469Disk4Cell2_1 : chordRectangleTest 4 sharedChord469Params (-13/16) (-3/4) (-1/16) 0 477114=true := by decide +kernel
theorem sharedChord469Disk4Cell2_2 : chordRectangleTest 4 sharedChord469Params (-13/16) (-3/4) 0 (1/16) 477114=true := by decide +kernel
theorem sharedChord469Disk4Cell2_3 : chordRectangleTest 4 sharedChord469Params (-13/16) (-3/4) (1/16) (1/8) 477114=true := by decide +kernel
theorem sharedChord469Disk4Cell3_0 : chordRectangleTest 4 sharedChord469Params (-3/4) (-11/16) (-1/8) (-1/16) 477114=true := by decide +kernel
theorem sharedChord469Disk4Cell3_1 : chordRectangleTest 4 sharedChord469Params (-3/4) (-11/16) (-1/16) 0 477114=true := by decide +kernel
theorem sharedChord469Disk4Cell3_2 : chordRectangleTest 4 sharedChord469Params (-3/4) (-11/16) 0 (1/16) 477114=true := by decide +kernel
theorem sharedChord469Disk4Cell3_3 : chordRectangleTest 4 sharedChord469Params (-3/4) (-11/16) (1/16) (1/8) 477114=true := by decide +kernel
theorem sharedChord469Disk4 {t a : ℝ} (ps : sharedChord469Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord469Bd (4:Fin 15)) (2*jacobiCellRadius sharedChord469Bd (4:Fin 15)) (sharedChord469M 4) t a := by
  rw [show jacobiCellCenter sharedChord469Bd (4:Fin 15)=(-13/16) by decide +kernel, show 2*jacobiCellRadius sharedChord469Bd (4:Fin 15)=(1/8) by decide +kernel, show sharedChord469M 4=477114 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-13/16):ℚ)-(1/8)=(-15/16) by decide +kernel, show ((-13/16):ℚ)+(1/8)=(-11/16) by decide +kernel, show -((1/8):ℚ)=(-1/8) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord469Disk4Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord469Disk4Cell0_1
  have piece0_2 := chordRectangleTest_sound ps ht sharedChord469Disk4Cell0_2
  have piece0_3 := chordRectangleTest_sound ps ht sharedChord469Disk4Cell0_3
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord469Disk4Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord469Disk4Cell1_1
  have piece1_2 := chordRectangleTest_sound ps ht sharedChord469Disk4Cell1_2
  have piece1_3 := chordRectangleTest_sound ps ht sharedChord469Disk4Cell1_3
  have piece2_0 := chordRectangleTest_sound ps ht sharedChord469Disk4Cell2_0
  have piece2_1 := chordRectangleTest_sound ps ht sharedChord469Disk4Cell2_1
  have piece2_2 := chordRectangleTest_sound ps ht sharedChord469Disk4Cell2_2
  have piece2_3 := chordRectangleTest_sound ps ht sharedChord469Disk4Cell2_3
  have piece3_0 := chordRectangleTest_sound ps ht sharedChord469Disk4Cell3_0
  have piece3_1 := chordRectangleTest_sound ps ht sharedChord469Disk4Cell3_1
  have piece3_2 := chordRectangleTest_sound ps ht sharedChord469Disk4Cell3_2
  have piece3_3 := chordRectangleTest_sound ps ht sharedChord469Disk4Cell3_3
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinX (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece0_2 piece0_3)) (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece1_0 piece1_1) (ChordRectangleBound.joinY piece1_2 piece1_3))) (ChordRectangleBound.joinX (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece2_0 piece2_1) (ChordRectangleBound.joinY piece2_2 piece2_3)) (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece3_0 piece3_1) (ChordRectangleBound.joinY piece3_2 piece3_3))))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord469Disk5Cell0_0 : chordRectangleTest 4 sharedChord469Params (-7/8) (-5/8) (-1/4) 0 32300=true := by decide +kernel
theorem sharedChord469Disk5Cell0_1 : chordRectangleTest 4 sharedChord469Params (-7/8) (-5/8) 0 (1/4) 32300=true := by decide +kernel
theorem sharedChord469Disk5Cell1_0 : chordRectangleTest 4 sharedChord469Params (-5/8) (-3/8) (-1/4) 0 32300=true := by decide +kernel
theorem sharedChord469Disk5Cell1_1 : chordRectangleTest 4 sharedChord469Params (-5/8) (-3/8) 0 (1/4) 32300=true := by decide +kernel
theorem sharedChord469Disk5 {t a : ℝ} (ps : sharedChord469Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord469Bd (5:Fin 15)) (2*jacobiCellRadius sharedChord469Bd (5:Fin 15)) (sharedChord469M 5) t a := by
  rw [show jacobiCellCenter sharedChord469Bd (5:Fin 15)=(-5/8) by decide +kernel, show 2*jacobiCellRadius sharedChord469Bd (5:Fin 15)=(1/4) by decide +kernel, show sharedChord469M 5=32300 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-5/8):ℚ)-(1/4)=(-7/8) by decide +kernel, show ((-5/8):ℚ)+(1/4)=(-3/8) by decide +kernel, show -((1/4):ℚ)=(-1/4) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord469Disk5Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord469Disk5Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord469Disk5Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord469Disk5Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord469Disk6Cell0_0 : chordRectangleTest 4 sharedChord469Params (-3/4) (1/4) (-1/2) (1/2) 611288=true := by decide +kernel
theorem sharedChord469Disk6 {t a : ℝ} (ps : sharedChord469Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord469Bd (6:Fin 15)) (2*jacobiCellRadius sharedChord469Bd (6:Fin 15)) (sharedChord469M 6) t a := by
  rw [show jacobiCellCenter sharedChord469Bd (6:Fin 15)=(-1/4) by decide +kernel, show 2*jacobiCellRadius sharedChord469Bd (6:Fin 15)=(1/2) by decide +kernel, show sharedChord469M 6=611288 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-1/4):ℚ)-(1/2)=(-3/4) by decide +kernel, show ((-1/4):ℚ)+(1/2)=(1/4) by decide +kernel, show -((1/2):ℚ)=(-1/2) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord469Disk6Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord469Disk7Cell0_0 : chordRectangleTest 4 sharedChord469Params (-1/4) (3/4) (-1/2) (1/2) 8967982=true := by decide +kernel
theorem sharedChord469Disk7 {t a : ℝ} (ps : sharedChord469Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord469Bd (7:Fin 15)) (2*jacobiCellRadius sharedChord469Bd (7:Fin 15)) (sharedChord469M 7) t a := by
  rw [show jacobiCellCenter sharedChord469Bd (7:Fin 15)=(1/4) by decide +kernel, show 2*jacobiCellRadius sharedChord469Bd (7:Fin 15)=(1/2) by decide +kernel, show sharedChord469M 7=8967982 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((1/4):ℚ)-(1/2)=(-1/4) by decide +kernel, show ((1/4):ℚ)+(1/2)=(3/4) by decide +kernel, show -((1/2):ℚ)=(-1/2) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord469Disk7Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord469Disk8Cell0_0 : chordRectangleTest 4 sharedChord469Params (3/8) (5/8) (-1/4) 0 3543046=true := by decide +kernel
theorem sharedChord469Disk8Cell0_1 : chordRectangleTest 4 sharedChord469Params (3/8) (5/8) 0 (1/4) 3543046=true := by decide +kernel
theorem sharedChord469Disk8Cell1_0 : chordRectangleTest 4 sharedChord469Params (5/8) (7/8) (-1/4) 0 3543046=true := by decide +kernel
theorem sharedChord469Disk8Cell1_1 : chordRectangleTest 4 sharedChord469Params (5/8) (7/8) 0 (1/4) 3543046=true := by decide +kernel
theorem sharedChord469Disk8 {t a : ℝ} (ps : sharedChord469Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord469Bd (8:Fin 15)) (2*jacobiCellRadius sharedChord469Bd (8:Fin 15)) (sharedChord469M 8) t a := by
  rw [show jacobiCellCenter sharedChord469Bd (8:Fin 15)=(5/8) by decide +kernel, show 2*jacobiCellRadius sharedChord469Bd (8:Fin 15)=(1/4) by decide +kernel, show sharedChord469M 8=3543046 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((5/8):ℚ)-(1/4)=(3/8) by decide +kernel, show ((5/8):ℚ)+(1/4)=(7/8) by decide +kernel, show -((1/4):ℚ)=(-1/4) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord469Disk8Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord469Disk8Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord469Disk8Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord469Disk8Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord469Disk9Cell0_0 : chordRectangleTest 4 sharedChord469Params (23/32) (27/32) (-1/16) (1/16) 3330=true := by decide +kernel
theorem sharedChord469Disk9 {t a : ℝ} (ps : sharedChord469Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord469Bd (9:Fin 15)) (2*jacobiCellRadius sharedChord469Bd (9:Fin 15)) (sharedChord469M 9) t a := by
  rw [show jacobiCellCenter sharedChord469Bd (9:Fin 15)=(25/32) by decide +kernel, show 2*jacobiCellRadius sharedChord469Bd (9:Fin 15)=(1/16) by decide +kernel, show sharedChord469M 9=3330 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((25/32):ℚ)-(1/16)=(23/32) by decide +kernel, show ((25/32):ℚ)+(1/16)=(27/32) by decide +kernel, show -((1/16):ℚ)=(-1/16) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord469Disk9Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord469Disk10Cell0_0 : chordRectangleTest 4 sharedChord469Params (25/32) (29/32) (-1/16) (1/16) 573705=true := by decide +kernel
theorem sharedChord469Disk10 {t a : ℝ} (ps : sharedChord469Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord469Bd (10:Fin 15)) (2*jacobiCellRadius sharedChord469Bd (10:Fin 15)) (sharedChord469M 10) t a := by
  rw [show jacobiCellCenter sharedChord469Bd (10:Fin 15)=(27/32) by decide +kernel, show 2*jacobiCellRadius sharedChord469Bd (10:Fin 15)=(1/16) by decide +kernel, show sharedChord469M 10=573705 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((27/32):ℚ)-(1/16)=(25/32) by decide +kernel, show ((27/32):ℚ)+(1/16)=(29/32) by decide +kernel, show -((1/16):ℚ)=(-1/16) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord469Disk10Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord469Disk11Cell0_0 : chordRectangleTest 4 sharedChord469Params (55/64) (59/64) (-1/32) (1/32) 18391=true := by decide +kernel
theorem sharedChord469Disk11 {t a : ℝ} (ps : sharedChord469Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord469Bd (11:Fin 15)) (2*jacobiCellRadius sharedChord469Bd (11:Fin 15)) (sharedChord469M 11) t a := by
  rw [show jacobiCellCenter sharedChord469Bd (11:Fin 15)=(57/64) by decide +kernel, show 2*jacobiCellRadius sharedChord469Bd (11:Fin 15)=(1/32) by decide +kernel, show sharedChord469M 11=18391 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((57/64):ℚ)-(1/32)=(55/64) by decide +kernel, show ((57/64):ℚ)+(1/32)=(59/64) by decide +kernel, show -((1/32):ℚ)=(-1/32) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord469Disk11Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord469Disk12Cell0_0 : chordRectangleTest 4 sharedChord469Params (57/64) (61/64) (-1/32) (1/32) 145212=true := by decide +kernel
theorem sharedChord469Disk12 {t a : ℝ} (ps : sharedChord469Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord469Bd (12:Fin 15)) (2*jacobiCellRadius sharedChord469Bd (12:Fin 15)) (sharedChord469M 12) t a := by
  rw [show jacobiCellCenter sharedChord469Bd (12:Fin 15)=(59/64) by decide +kernel, show 2*jacobiCellRadius sharedChord469Bd (12:Fin 15)=(1/32) by decide +kernel, show sharedChord469M 12=145212 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((59/64):ℚ)-(1/32)=(57/64) by decide +kernel, show ((59/64):ℚ)+(1/32)=(61/64) by decide +kernel, show -((1/32):ℚ)=(-1/32) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord469Disk12Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord469Disk13Cell0_0 : chordRectangleTest 4 sharedChord469Params (59/64) (63/64) (-1/32) (1/32) 618041=true := by decide +kernel
theorem sharedChord469Disk13 {t a : ℝ} (ps : sharedChord469Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord469Bd (13:Fin 15)) (2*jacobiCellRadius sharedChord469Bd (13:Fin 15)) (sharedChord469M 13) t a := by
  rw [show jacobiCellCenter sharedChord469Bd (13:Fin 15)=(61/64) by decide +kernel, show 2*jacobiCellRadius sharedChord469Bd (13:Fin 15)=(1/32) by decide +kernel, show sharedChord469M 13=618041 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((61/64):ℚ)-(1/32)=(59/64) by decide +kernel, show ((61/64):ℚ)+(1/32)=(63/64) by decide +kernel, show -((1/32):ℚ)=(-1/32) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord469Disk13Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord469Disk14Cell0_0 : chordRectangleTest 4 sharedChord469Params (61/64) (65/64) (-1/32) (1/32) 250656=true := by decide +kernel
theorem sharedChord469Disk14 {t a : ℝ} (ps : sharedChord469Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord469Bd (14:Fin 15)) (2*jacobiCellRadius sharedChord469Bd (14:Fin 15)) (sharedChord469M 14) t a := by
  rw [show jacobiCellCenter sharedChord469Bd (14:Fin 15)=(63/64) by decide +kernel, show 2*jacobiCellRadius sharedChord469Bd (14:Fin 15)=(1/32) by decide +kernel, show sharedChord469M 14=250656 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((63/64):ℚ)-(1/32)=(61/64) by decide +kernel, show ((63/64):ℚ)+(1/32)=(65/64) by decide +kernel, show -((1/32):ℚ)=(-1/32) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord469Disk14Cell0_0
  exact piece0_0

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord469Disks {t a : ℝ} (ps : sharedChord469Params.Sound t a) (ht : 0<t) :
    ∀ i : Fin 15, ChordDiskBound (jacobiCellCenter sharedChord469Bd i) (2*jacobiCellRadius sharedChord469Bd i) (sharedChord469M i) t a := by
  intro i
  fin_cases i
  · exact sharedChord469Disk0 ps ht
  · exact sharedChord469Disk1 ps ht
  · exact sharedChord469Disk2 ps ht
  · exact sharedChord469Disk3 ps ht
  · exact sharedChord469Disk4 ps ht
  · exact sharedChord469Disk5 ps ht
  · exact sharedChord469Disk6 ps ht
  · exact sharedChord469Disk7 ps ht
  · exact sharedChord469Disk8 ps ht
  · exact sharedChord469Disk9 ps ht
  · exact sharedChord469Disk10 ps ht
  · exact sharedChord469Disk11 ps ht
  · exact sharedChord469Disk12 ps ht
  · exact sharedChord469Disk13 ps ht
  · exact sharedChord469Disk14 ps ht

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord469Disks
