import TwoAxisHelicoid.PdfComplexChordDisk

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def sharedChord493Params : ChordParams := ⟨⟨(-18332900498891248935737),(-9270165264322248947326),true⟩,⟨2211106203611825492752785,2750261597609105345108391,true⟩,⟨77752212134488897419448,129692404806798347073031,true⟩,⟨124278425929753393067960,194125199274925000072743,true⟩,⟨208562914466204619614166,295479872026543002937450,true⟩,⟨1172807735630698749477372,1190526576341392739903106,true⟩,⟨(-2899340733439943857683825),(-2456322777553789056735310),true⟩,⟨⟨861518472123345041738649,1626946825737095753519327,true⟩,⟨(-818289),818289,true⟩⟩⟩
theorem sharedChord493Params_ok : chordParams (Grid.ofRats (129/200) (3/4)) (Grid.ofRats (878940159632233/1649267441664000) (929134916903873/1649267441664000))=sharedChord493Params := by decide +kernel
theorem sharedChord493ParamSound {t a : ℝ} (tl : (((129/200):ℚ):ℝ)≤t) (tu : t≤(((3/4):ℚ):ℝ)) (al : (((878940159632233/1649267441664000):ℚ):ℝ)≤a) (au : a≤(((929134916903873/1649267441664000):ℚ):ℝ)) (ht : 0<t) : sharedChord493Params.Sound t a := by
  rw [← sharedChord493Params_ok]
  exact chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
def sharedChord493Bd (i : ℕ) : ℚ := match i with
  | 0 => (-1)
  | 1 => (-15/16)
  | 2 => (-7/8)
  | 3 => (-13/16)
  | 4 => (-3/4)
  | 5 => (-1/2)
  | 6 => 0
  | 7 => (1/2)
  | 8 => (5/8)
  | 9 => (3/4)
  | 10 => (13/16)
  | 11 => (7/8)
  | 12 => (15/16)
  | _ => 1
def sharedChord493M (i : Fin 13) : ℚ := match i.val with
  | 0 => 96466
  | 1 => 8386107
  | 2 => 41309
  | 3 => 1849
  | 4 => 74314
  | 5 => 31440
  | 6 => 1941435
  | 7 => 1430
  | 8 => 282574
  | 9 => 9650
  | 10 => 215687
  | 11 => 8092339
  | _ => 101100

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord493ParamSound
