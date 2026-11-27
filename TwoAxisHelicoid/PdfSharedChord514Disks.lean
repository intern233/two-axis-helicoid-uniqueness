import TwoAxisHelicoid.PdfSharedChord514Parameters
import TwoAxisHelicoid.JacobiRangeComposite

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord514Disk0Cell0_0 : chordRectangleTest 4 sharedChord514Params (-17/16) (-15/16) (-1/8) 0 231159=true := by decide +kernel
theorem sharedChord514Disk0Cell0_1 : chordRectangleTest 4 sharedChord514Params (-17/16) (-15/16) 0 (1/8) 231159=true := by decide +kernel
theorem sharedChord514Disk0Cell1_0 : chordRectangleTest 4 sharedChord514Params (-15/16) (-13/16) (-1/8) 0 231159=true := by decide +kernel
theorem sharedChord514Disk0Cell1_1 : chordRectangleTest 4 sharedChord514Params (-15/16) (-13/16) 0 (1/8) 231159=true := by decide +kernel
theorem sharedChord514Disk0 {t a : ℝ} (ps : sharedChord514Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord514Bd (0:Fin 8)) (2*jacobiCellRadius sharedChord514Bd (0:Fin 8)) (sharedChord514M 0) t a := by
  rw [show jacobiCellCenter sharedChord514Bd (0:Fin 8)=(-15/16) by decide +kernel, show 2*jacobiCellRadius sharedChord514Bd (0:Fin 8)=(1/8) by decide +kernel, show sharedChord514M 0=231159 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-15/16):ℚ)-(1/8)=(-17/16) by decide +kernel, show ((-15/16):ℚ)+(1/8)=(-13/16) by decide +kernel, show -((1/8):ℚ)=(-1/8) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord514Disk0Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord514Disk0Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord514Disk0Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord514Disk0Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord514Disk1Cell0_0 : chordRectangleTest 4 sharedChord514Params (-15/16) (-13/16) (-1/8) 0 11194=true := by decide +kernel
theorem sharedChord514Disk1Cell0_1 : chordRectangleTest 4 sharedChord514Params (-15/16) (-13/16) 0 (1/8) 11194=true := by decide +kernel
theorem sharedChord514Disk1Cell1_0 : chordRectangleTest 4 sharedChord514Params (-13/16) (-11/16) (-1/8) 0 11194=true := by decide +kernel
theorem sharedChord514Disk1Cell1_1 : chordRectangleTest 4 sharedChord514Params (-13/16) (-11/16) 0 (1/8) 11194=true := by decide +kernel
theorem sharedChord514Disk1 {t a : ℝ} (ps : sharedChord514Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord514Bd (1:Fin 8)) (2*jacobiCellRadius sharedChord514Bd (1:Fin 8)) (sharedChord514M 1) t a := by
  rw [show jacobiCellCenter sharedChord514Bd (1:Fin 8)=(-13/16) by decide +kernel, show 2*jacobiCellRadius sharedChord514Bd (1:Fin 8)=(1/8) by decide +kernel, show sharedChord514M 1=11194 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-13/16):ℚ)-(1/8)=(-15/16) by decide +kernel, show ((-13/16):ℚ)+(1/8)=(-11/16) by decide +kernel, show -((1/8):ℚ)=(-1/8) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord514Disk1Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord514Disk1Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord514Disk1Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord514Disk1Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord514Disk2Cell0_0 : chordRectangleTest 4 sharedChord514Params (-7/8) (-5/8) (-1/4) 0 6846043=true := by decide +kernel
theorem sharedChord514Disk2Cell0_1 : chordRectangleTest 4 sharedChord514Params (-7/8) (-5/8) 0 (1/4) 6846043=true := by decide +kernel
theorem sharedChord514Disk2Cell1_0 : chordRectangleTest 4 sharedChord514Params (-5/8) (-3/8) (-1/4) 0 6846043=true := by decide +kernel
theorem sharedChord514Disk2Cell1_1 : chordRectangleTest 4 sharedChord514Params (-5/8) (-3/8) 0 (1/4) 6846043=true := by decide +kernel
theorem sharedChord514Disk2 {t a : ℝ} (ps : sharedChord514Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord514Bd (2:Fin 8)) (2*jacobiCellRadius sharedChord514Bd (2:Fin 8)) (sharedChord514M 2) t a := by
  rw [show jacobiCellCenter sharedChord514Bd (2:Fin 8)=(-5/8) by decide +kernel, show 2*jacobiCellRadius sharedChord514Bd (2:Fin 8)=(1/4) by decide +kernel, show sharedChord514M 2=6846043 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-5/8):ℚ)-(1/4)=(-7/8) by decide +kernel, show ((-5/8):ℚ)+(1/4)=(-3/8) by decide +kernel, show -((1/4):ℚ)=(-1/4) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord514Disk2Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord514Disk2Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord514Disk2Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord514Disk2Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord514Disk3Cell0_0 : chordRectangleTest 4 sharedChord514Params (-3/4) (-1/4) (-1/2) 0 7815=true := by decide +kernel
theorem sharedChord514Disk3Cell0_1 : chordRectangleTest 4 sharedChord514Params (-3/4) (-1/4) 0 (1/2) 7815=true := by decide +kernel
theorem sharedChord514Disk3Cell1_0 : chordRectangleTest 4 sharedChord514Params (-1/4) (1/4) (-1/2) 0 7815=true := by decide +kernel
theorem sharedChord514Disk3Cell1_1 : chordRectangleTest 4 sharedChord514Params (-1/4) (1/4) 0 (1/2) 7815=true := by decide +kernel
theorem sharedChord514Disk3 {t a : ℝ} (ps : sharedChord514Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord514Bd (3:Fin 8)) (2*jacobiCellRadius sharedChord514Bd (3:Fin 8)) (sharedChord514M 3) t a := by
  rw [show jacobiCellCenter sharedChord514Bd (3:Fin 8)=(-1/4) by decide +kernel, show 2*jacobiCellRadius sharedChord514Bd (3:Fin 8)=(1/2) by decide +kernel, show sharedChord514M 3=7815 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((-1/4):ℚ)-(1/2)=(-3/4) by decide +kernel, show ((-1/4):ℚ)+(1/2)=(1/4) by decide +kernel, show -((1/2):ℚ)=(-1/2) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord514Disk3Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord514Disk3Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord514Disk3Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord514Disk3Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord514Disk4Cell0_0 : chordRectangleTest 4 sharedChord514Params (-1/4) (1/4) (-1/2) 0 363502=true := by decide +kernel
theorem sharedChord514Disk4Cell0_1 : chordRectangleTest 4 sharedChord514Params (-1/4) (1/4) 0 (1/2) 363502=true := by decide +kernel
theorem sharedChord514Disk4Cell1_0 : chordRectangleTest 4 sharedChord514Params (1/4) (3/4) (-1/2) 0 363502=true := by decide +kernel
theorem sharedChord514Disk4Cell1_1 : chordRectangleTest 4 sharedChord514Params (1/4) (3/4) 0 (1/2) 363502=true := by decide +kernel
theorem sharedChord514Disk4 {t a : ℝ} (ps : sharedChord514Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord514Bd (4:Fin 8)) (2*jacobiCellRadius sharedChord514Bd (4:Fin 8)) (sharedChord514M 4) t a := by
  rw [show jacobiCellCenter sharedChord514Bd (4:Fin 8)=(1/4) by decide +kernel, show 2*jacobiCellRadius sharedChord514Bd (4:Fin 8)=(1/2) by decide +kernel, show sharedChord514M 4=363502 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((1/4):ℚ)-(1/2)=(-1/4) by decide +kernel, show ((1/4):ℚ)+(1/2)=(3/4) by decide +kernel, show -((1/2):ℚ)=(-1/2) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord514Disk4Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord514Disk4Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord514Disk4Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord514Disk4Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord514Disk5Cell0_0 : chordRectangleTest 4 sharedChord514Params (3/8) (1/2) (-1/4) (-1/8) 914206=true := by decide +kernel
theorem sharedChord514Disk5Cell0_1 : chordRectangleTest 4 sharedChord514Params (3/8) (1/2) (-1/8) 0 914206=true := by decide +kernel
theorem sharedChord514Disk5Cell0_2 : chordRectangleTest 4 sharedChord514Params (3/8) (1/2) 0 (1/8) 914206=true := by decide +kernel
theorem sharedChord514Disk5Cell0_3 : chordRectangleTest 4 sharedChord514Params (3/8) (1/2) (1/8) (1/4) 914206=true := by decide +kernel
theorem sharedChord514Disk5Cell1_0 : chordRectangleTest 4 sharedChord514Params (1/2) (5/8) (-1/4) (-1/8) 914206=true := by decide +kernel
theorem sharedChord514Disk5Cell1_1 : chordRectangleTest 4 sharedChord514Params (1/2) (5/8) (-1/8) 0 914206=true := by decide +kernel
theorem sharedChord514Disk5Cell1_2 : chordRectangleTest 4 sharedChord514Params (1/2) (5/8) 0 (1/8) 914206=true := by decide +kernel
theorem sharedChord514Disk5Cell1_3 : chordRectangleTest 4 sharedChord514Params (1/2) (5/8) (1/8) (1/4) 914206=true := by decide +kernel
theorem sharedChord514Disk5Cell2_0 : chordRectangleTest 4 sharedChord514Params (5/8) (3/4) (-1/4) (-1/8) 914206=true := by decide +kernel
theorem sharedChord514Disk5Cell2_1 : chordRectangleTest 4 sharedChord514Params (5/8) (3/4) (-1/8) 0 914206=true := by decide +kernel
theorem sharedChord514Disk5Cell2_2 : chordRectangleTest 4 sharedChord514Params (5/8) (3/4) 0 (1/8) 914206=true := by decide +kernel
theorem sharedChord514Disk5Cell2_3 : chordRectangleTest 4 sharedChord514Params (5/8) (3/4) (1/8) (1/4) 914206=true := by decide +kernel
theorem sharedChord514Disk5Cell3_0 : chordRectangleTest 4 sharedChord514Params (3/4) (7/8) (-1/4) (-1/8) 914206=true := by decide +kernel
theorem sharedChord514Disk5Cell3_1 : chordRectangleTest 4 sharedChord514Params (3/4) (7/8) (-1/8) 0 914206=true := by decide +kernel
theorem sharedChord514Disk5Cell3_2 : chordRectangleTest 4 sharedChord514Params (3/4) (7/8) 0 (1/8) 914206=true := by decide +kernel
theorem sharedChord514Disk5Cell3_3 : chordRectangleTest 4 sharedChord514Params (3/4) (7/8) (1/8) (1/4) 914206=true := by decide +kernel
theorem sharedChord514Disk5 {t a : ℝ} (ps : sharedChord514Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord514Bd (5:Fin 8)) (2*jacobiCellRadius sharedChord514Bd (5:Fin 8)) (sharedChord514M 5) t a := by
  rw [show jacobiCellCenter sharedChord514Bd (5:Fin 8)=(5/8) by decide +kernel, show 2*jacobiCellRadius sharedChord514Bd (5:Fin 8)=(1/4) by decide +kernel, show sharedChord514M 5=914206 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((5/8):ℚ)-(1/4)=(3/8) by decide +kernel, show ((5/8):ℚ)+(1/4)=(7/8) by decide +kernel, show -((1/4):ℚ)=(-1/4) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord514Disk5Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord514Disk5Cell0_1
  have piece0_2 := chordRectangleTest_sound ps ht sharedChord514Disk5Cell0_2
  have piece0_3 := chordRectangleTest_sound ps ht sharedChord514Disk5Cell0_3
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord514Disk5Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord514Disk5Cell1_1
  have piece1_2 := chordRectangleTest_sound ps ht sharedChord514Disk5Cell1_2
  have piece1_3 := chordRectangleTest_sound ps ht sharedChord514Disk5Cell1_3
  have piece2_0 := chordRectangleTest_sound ps ht sharedChord514Disk5Cell2_0
  have piece2_1 := chordRectangleTest_sound ps ht sharedChord514Disk5Cell2_1
  have piece2_2 := chordRectangleTest_sound ps ht sharedChord514Disk5Cell2_2
  have piece2_3 := chordRectangleTest_sound ps ht sharedChord514Disk5Cell2_3
  have piece3_0 := chordRectangleTest_sound ps ht sharedChord514Disk5Cell3_0
  have piece3_1 := chordRectangleTest_sound ps ht sharedChord514Disk5Cell3_1
  have piece3_2 := chordRectangleTest_sound ps ht sharedChord514Disk5Cell3_2
  have piece3_3 := chordRectangleTest_sound ps ht sharedChord514Disk5Cell3_3
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinX (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece0_2 piece0_3)) (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece1_0 piece1_1) (ChordRectangleBound.joinY piece1_2 piece1_3))) (ChordRectangleBound.joinX (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece2_0 piece2_1) (ChordRectangleBound.joinY piece2_2 piece2_3)) (ChordRectangleBound.joinY (ChordRectangleBound.joinY piece3_0 piece3_1) (ChordRectangleBound.joinY piece3_2 piece3_3))))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord514Disk6Cell0_0 : chordRectangleTest 4 sharedChord514Params (11/16) (13/16) (-1/8) 0 112516=true := by decide +kernel
theorem sharedChord514Disk6Cell0_1 : chordRectangleTest 4 sharedChord514Params (11/16) (13/16) 0 (1/8) 112516=true := by decide +kernel
theorem sharedChord514Disk6Cell1_0 : chordRectangleTest 4 sharedChord514Params (13/16) (15/16) (-1/8) 0 112516=true := by decide +kernel
theorem sharedChord514Disk6Cell1_1 : chordRectangleTest 4 sharedChord514Params (13/16) (15/16) 0 (1/8) 112516=true := by decide +kernel
theorem sharedChord514Disk6 {t a : ℝ} (ps : sharedChord514Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord514Bd (6:Fin 8)) (2*jacobiCellRadius sharedChord514Bd (6:Fin 8)) (sharedChord514M 6) t a := by
  rw [show jacobiCellCenter sharedChord514Bd (6:Fin 8)=(13/16) by decide +kernel, show 2*jacobiCellRadius sharedChord514Bd (6:Fin 8)=(1/8) by decide +kernel, show sharedChord514M 6=112516 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((13/16):ℚ)-(1/8)=(11/16) by decide +kernel, show ((13/16):ℚ)+(1/8)=(15/16) by decide +kernel, show -((1/8):ℚ)=(-1/8) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord514Disk6Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord514Disk6Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord514Disk6Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord514Disk6Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord514Disk7Cell0_0 : chordRectangleTest 4 sharedChord514Params (13/16) (15/16) (-1/8) 0 112516=true := by decide +kernel
theorem sharedChord514Disk7Cell0_1 : chordRectangleTest 4 sharedChord514Params (13/16) (15/16) 0 (1/8) 112516=true := by decide +kernel
theorem sharedChord514Disk7Cell1_0 : chordRectangleTest 4 sharedChord514Params (15/16) (17/16) (-1/8) 0 112516=true := by decide +kernel
theorem sharedChord514Disk7Cell1_1 : chordRectangleTest 4 sharedChord514Params (15/16) (17/16) 0 (1/8) 112516=true := by decide +kernel
theorem sharedChord514Disk7 {t a : ℝ} (ps : sharedChord514Params.Sound t a) (ht : 0<t) :
    ChordDiskBound (jacobiCellCenter sharedChord514Bd (7:Fin 8)) (2*jacobiCellRadius sharedChord514Bd (7:Fin 8)) (sharedChord514M 7) t a := by
  rw [show jacobiCellCenter sharedChord514Bd (7:Fin 8)=(15/16) by decide +kernel, show 2*jacobiCellRadius sharedChord514Bd (7:Fin 8)=(1/8) by decide +kernel, show sharedChord514M 7=112516 by decide +kernel]
  apply chordDiskBound_of_square
  rw [show ((15/16):ℚ)-(1/8)=(13/16) by decide +kernel, show ((15/16):ℚ)+(1/8)=(17/16) by decide +kernel, show -((1/8):ℚ)=(-1/8) by decide +kernel]
  have piece0_0 := chordRectangleTest_sound ps ht sharedChord514Disk7Cell0_0
  have piece0_1 := chordRectangleTest_sound ps ht sharedChord514Disk7Cell0_1
  have piece1_0 := chordRectangleTest_sound ps ht sharedChord514Disk7Cell1_0
  have piece1_1 := chordRectangleTest_sound ps ht sharedChord514Disk7Cell1_1
  exact (ChordRectangleBound.joinX (ChordRectangleBound.joinY piece0_0 piece0_1) (ChordRectangleBound.joinY piece1_0 piece1_1))

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord514Disks {t a : ℝ} (ps : sharedChord514Params.Sound t a) (ht : 0<t) :
    ∀ i : Fin 8, ChordDiskBound (jacobiCellCenter sharedChord514Bd i) (2*jacobiCellRadius sharedChord514Bd i) (sharedChord514M i) t a := by
  intro i
  fin_cases i
  · exact sharedChord514Disk0 ps ht
  · exact sharedChord514Disk1 ps ht
  · exact sharedChord514Disk2 ps ht
  · exact sharedChord514Disk3 ps ht
  · exact sharedChord514Disk4 ps ht
  · exact sharedChord514Disk5 ps ht
  · exact sharedChord514Disk6 ps ht
  · exact sharedChord514Disk7 ps ht

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord514Disks
