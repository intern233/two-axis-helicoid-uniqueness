import TwoAxisHelicoid.PdfComplexChordDisk

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def sharedChord442Params : ChordParams := ⟨⟨(-3045001778040279689751),(-446690082326940401689),true⟩,⟨3494120446995233693228528,4731237407873395470866695,true⟩,⟨20316751746141148365863,58947462254962887950739,true⟩,⟨24140710186863035632459,67169468080344912019757,true⟩,⟨46359683914369476648909,121300658415967385780957,true⟩,⟨1202851116816066216313016,1208032769426104318445316,true⟩,⟨(-4773769652484002405656719),(-3598922125668220793431094),true⟩,⟨⟨981691903747586978885717,1485392146839468596656763,true⟩,⟨(-53),53,true⟩⟩⟩
theorem sharedChord442Params_ok : chordParams (Grid.ofRats (159/400) (21/40)) (Grid.ofRats (1110112793673/2199023255552) (3410681265479/6597069766656))=sharedChord442Params := by decide +kernel
theorem sharedChord442ParamSound {t a : ℝ} (tl : (((159/400):ℚ):ℝ)≤t) (tu : t≤(((21/40):ℚ):ℝ)) (al : (((1110112793673/2199023255552):ℚ):ℝ)≤a) (au : a≤(((3410681265479/6597069766656):ℚ):ℝ)) (ht : 0<t) : sharedChord442Params.Sound t a := by
  rw [← sharedChord442Params_ok]
  exact chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
def sharedChord442Bd (i : ℕ) : ℚ := match i with
  | 0 => (-1)
  | 1 => (-127/128)
  | 2 => (-63/64)
  | 3 => (-125/128)
  | 4 => (-31/32)
  | 5 => (-61/64)
  | 6 => (-15/16)
  | 7 => (-29/32)
  | 8 => (-7/8)
  | 9 => (-3/4)
  | 10 => (-1/2)
  | 11 => 0
  | 12 => (1/2)
  | 13 => (3/4)
  | 14 => (7/8)
  | 15 => (29/32)
  | 16 => (15/16)
  | 17 => (61/64)
  | 18 => (31/32)
  | 19 => (63/64)
  | _ => 1
def sharedChord442M (i : Fin 20) : ℚ := match i.val with
  | 0 => 1676777
  | 1 => 1787477
  | 2 => 797374
  | 3 => 185299
  | 4 => 920547
  | 5 => 50928
  | 6 => 201580
  | 7 => 1967
  | 8 => 49802
  | 9 => 98188
  | 10 => 57084
  | 11 => 304253
  | 12 => 1168885
  | 13 => 1525568
  | 14 => 7725
  | 15 => 1996916
  | 16 => 228242
  | 17 => 1579338
  | 18 => 5620714
  | _ => 5620714

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord442ParamSound
