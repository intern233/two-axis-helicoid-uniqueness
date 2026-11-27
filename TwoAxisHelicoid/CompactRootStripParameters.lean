import TwoAxisHelicoid.PdfPrimalParameterBox

namespace TwoAxisHelicoid.PdfVertical
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def compactRootT : Grid := Grid.ofRats (43311/50000) (86623/100000)
def compactRootP : PrimalThetaParameters := ⟨⟨⟨79530904947759667618902,79533403524142899946106,true⟩,⟨0,0,true⟩⟩, ⟨⟨1127384212274176384581789,1127403202036613285755021,true⟩,⟨0,0,true⟩⟩, ⟨(-1543184049087951451887762),(-1543146069563146369020301),true⟩, ⟨6258781869920338883256910,6259180383544853228573659,true⟩⟩
theorem compactRootP_ok : compactRootP.encloses (primalThetaParameters compactRootT (Grid.ofRats (7421/12500) (59369/100000))) := by decide +kernel
theorem compactRootP_sound {t a : ℝ} (tl : ((43311/50000):ℝ)≤t) (tu : t≤((86623/100000):ℝ)) (al : ((7421/12500):ℝ)≤a) (au : a≤((59369/100000):ℝ)) : compactRootP.Sound t a :=
  primal_box_parameters_sound compactRootP_ok (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.compactRootP_sound
