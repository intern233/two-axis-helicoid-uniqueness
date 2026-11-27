import TwoAxisHelicoid.PdfSharedChord426Disk0
import TwoAxisHelicoid.PdfSharedChord426Disk1
import TwoAxisHelicoid.PdfSharedChord426Disk2
import TwoAxisHelicoid.PdfSharedChord426Disk3
import TwoAxisHelicoid.PdfSharedChord426Disk4
import TwoAxisHelicoid.PdfSharedChord426Disk5
import TwoAxisHelicoid.PdfSharedChord426Disk6
import TwoAxisHelicoid.PdfSharedChord426Disk7
import TwoAxisHelicoid.PdfSharedChord426Disk8
import TwoAxisHelicoid.PdfSharedChord426Disk9
import TwoAxisHelicoid.PdfSharedChord426Disk10
import TwoAxisHelicoid.PdfSharedChord426Disk11
import TwoAxisHelicoid.PdfSharedChord426Disk12
import TwoAxisHelicoid.PdfSharedChord426Disk13

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedChord426Disks {t a : ℝ} (ps : sharedChord426Params.Sound t a) (ht : 0<t) :
    ∀ i : Fin 14, ChordDiskBound (jacobiCellCenter sharedChord426Bd i) (2*jacobiCellRadius sharedChord426Bd i) (sharedChord426M i) t a := by
  intro i
  fin_cases i
  · exact sharedChord426Disk0 ps ht
  · exact sharedChord426Disk1 ps ht
  · exact sharedChord426Disk2 ps ht
  · exact sharedChord426Disk3 ps ht
  · exact sharedChord426Disk4 ps ht
  · exact sharedChord426Disk5 ps ht
  · exact sharedChord426Disk6 ps ht
  · exact sharedChord426Disk7 ps ht
  · exact sharedChord426Disk8 ps ht
  · exact sharedChord426Disk9 ps ht
  · exact sharedChord426Disk10 ps ht
  · exact sharedChord426Disk11 ps ht
  · exact sharedChord426Disk12 ps ht
  · exact sharedChord426Disk13 ps ht

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord426Disks
