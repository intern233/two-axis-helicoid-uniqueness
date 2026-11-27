import TwoAxisHelicoid.PdfFactoredNodes24
import TwoAxisHelicoid.PdfFactoredNodes32

namespace TwoAxisHelicoid.PdfVertical
open Complex

def shortNegativeNodes12 (k : Fin 12) : Fin 6 → CGrid :=
  factoredNodes24 ⟨2*k.val,by omega⟩

theorem shortNegativeNodes12Sound (k : Fin 12) (n : Fin 6) :
    (shortNegativeNodes12 k n).Contains (wavePhase n (-1+(k:ℝ)/12)) := by
  have h := factoredNodes24Sound (⟨2*k.val,by omega⟩ : Fin 24) n
  change (shortNegativeNodes12 k n).Contains (wavePhase n (-1+((2*k.val:ℕ):ℝ)/24)) at h
  have eqn : -1+((2*k.val:ℕ):ℝ)/24= -1+(k:ℝ)/12 := by push_cast;ring
  rwa [eqn] at h

def shortNegativeNodes16 (k : Fin 16) : Fin 6 → CGrid :=
  factoredNodes32 ⟨k.val,by omega⟩

theorem shortNegativeNodes16Sound (k : Fin 16) (n : Fin 6) :
    (shortNegativeNodes16 k n).Contains (wavePhase n (-1+(k:ℝ)/16)) := by
  have h := factoredNodes32Sound (⟨k.val,by omega⟩ : Fin 32) n
  change (shortNegativeNodes16 k n).Contains (wavePhase n (2*((k:ℝ)/32)-1)) at h
  have eqn : 2*((k:ℝ)/32)-1= -1+(k:ℝ)/16 := by ring
  rwa [eqn] at h

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.shortNegativeNodes12Sound
#print axioms TwoAxisHelicoid.PdfVertical.shortNegativeNodes16Sound
