import TwoAxisHelicoid.PdfComplexChordDisk

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def sharedChord426Params : ChordParams := ⟨⟨(-364274203612359759078),(-184485526382058978665),true⟩,⟨4858081356661445941373140,5282028500099138606137905,true⟩,⟨14375769680274087841492,20513499659466631508777,true⟩,⟨15306780829461186851226,21736150138916362265467,true⟩,⟨29859334907321161845653,41964085324960039979788,true⟩,⟨1208197490667889736171948,1208556904859308391327148,true⟩,⟨(-5310200690561149554750878),(-4897631433248858282441487),true⟩,⟨⟨1170965703430670033249936,1247074899868193480842747,true⟩,⟨(-47),47,true⟩⟩⟩
theorem sharedChord426Params_ok : chordParams (Grid.ofRats (143/400) (31/80)) (Grid.ofRats (1105678609191/2199023255552) (1109047628555/2199023255552))=sharedChord426Params := by decide +kernel
theorem sharedChord426ParamSound {t a : ℝ} (tl : (((143/400):ℚ):ℝ)≤t) (tu : t≤(((31/80):ℚ):ℝ)) (al : (((1105678609191/2199023255552):ℚ):ℝ)≤a) (au : a≤(((1109047628555/2199023255552):ℚ):ℝ)) (ht : 0<t) : sharedChord426Params.Sound t a := by
  rw [← sharedChord426Params_ok]
  exact chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
def sharedChord426Bd (i : ℕ) : ℚ := match i with
  | 0 => (-1)
  | 1 => (-63/64)
  | 2 => (-31/32)
  | 3 => (-15/16)
  | 4 => (-7/8)
  | 5 => (-3/4)
  | 6 => (-1/2)
  | 7 => 0
  | 8 => (1/2)
  | 9 => (3/4)
  | 10 => (7/8)
  | 11 => (15/16)
  | 12 => (31/32)
  | 13 => (63/64)
  | _ => 1
def sharedChord426M (i : Fin 14) : ℚ := match i.val with
  | 0 => 4493738
  | 1 => 92348
  | 2 => 118139
  | 3 => 11085
  | 4 => 2787
  | 5 => 1937
  | 6 => 8747
  | 7 => 17246
  | 8 => 4267
  | 9 => 7658
  | 10 => 61603
  | 11 => 4279585
  | 12 => 2498823
  | _ => 418193

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedChord426ParamSound
