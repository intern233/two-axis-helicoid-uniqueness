import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip008

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR008Q00T := Grid.ofRats (37/40) (93/100)
def shortNegativeR008Q00P : PrimalThetaParameters := ⟨⟨⟨65092303998787964389535,66122844173152483540205,true⟩,⟨0,0,true⟩⟩, ⟨⟨1163392882874762148673025,1167101820837366355048777,true⟩,⟨0,0,true⟩⟩, ⟨(-1471166707886779923705062),(-1463748831961640230433043),true⟩, ⟨5735427556850732193715319,5818661266055313893885188,true⟩⟩
theorem shortNegativeR008Q00P_ok : shortNegativeR008Q00P.encloses (primalThetaParameters shortNegativeR008Q00T (Grid.ofRats (202082149990879/329853488332800) (202726395085279/329853488332800))) := by decide +kernel

def shortNegativeR008Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨582347413447157937445068,584638782540174696253464,true⟩,⟨2499836960834083108966469,2509673098193391389806186,true⟩,⟨⟨687650826684718008228712,691359764647322214652324,true⟩,⟨991163196812925902941437,994872134775530109369318,true⟩⟩⟩
  | 1 => ⟨⟨7275739433226325318114,7478516054932362106976,true⟩,⟨582347413447157937445068,584638782540174696253464,true⟩,⟨⟨(-1176911854914225847408406),(-1165785041026550667166434),true⟩,⟨293509244377318072556167,304636058264993252786123,true⟩⟩⟩
  | 2 => ⟨⟨4894429886053687167,5232329856029260693,true⟩,⟨7275739433226325318114,7478516054932362106976,true⟩,⟨⟨119789282937163039362234,138333972749909193412293,true⟩,⟨(-1211289288859027806524411),(-1192744599046281652459584),true⟩⟩⟩
  | 3 => ⟨⟨177244554346905,200263215955930,true⟩,⟨4894429886053687167,5232329856029260693,true⟩,⟨⟨1068175745263879528129311,1094138311001696655979478,true⟩,⟨527944883858104722897209,553907449595921850739940,true⟩⟩⟩
  | 4 => ⟨⟨(-34014004407),34778831066,true⟩,⟨177244554346905,200263215955930,true⟩,⟨⟨(-901290803699714110453891),(-867910362036826008778268),true⟩,⟨807314297432879420530721,840694739095767522205509,true⟩⟩⟩
  | _ => ⟨⟨(-34359738332),34359738416,true⟩,⟨(-34014004407),34778831066,true⟩,⟨⟨(-483375679744719034714522),(-442577362156759959243751),true⟩,⟨(-1137159821773855629070182),(-1096361504185896553590412),true⟩⟩⟩
theorem shortNegativeR008Q00F_ok : ∀ n : Fin 6, (shortNegativeR008Q00F n).encloses (FactoredFrequency.build shortNegativeR008Q00T (Grid.ofRats (202082149990879/329853488332800) (202726395085279/329853488332800)) n) := by decide +kernel
def shortNegativeR008Q00L : ℕ → ℚ
  | 0 => (388117/200000)
  | 1 => (2657049/1000000)
  | 2 => (2472109/1000000)
  | 3 => (1907633/1000000)
  | 4 => (1086759/1000000)
  | 5 => (-29151/250000)
  | 6 => (-447411/250000)
  | 7 => (-1890573/500000)
  | 8 => (-171989/31250)
  | 9 => (-5803089/1000000)
  | 10 => (-3885181/1000000)
  | 11 => (-340213/500000)
  | _ => 0
def shortNegativeR008Q00U : ℕ → ℚ
  | 0 => (1220301/500000)
  | 1 => (3172857/1000000)
  | 2 => (2979507/1000000)
  | 3 => (149443/62500)
  | 4 => (308117/200000)
  | 5 => (394551/1000000)
  | 6 => (-1149863/1000000)
  | 7 => (-3005897/1000000)
  | 8 => (-2276379/500000)
  | 9 => (-4576083/1000000)
  | 10 => (-1231577/500000)
  | 11 => (590849/1000000)
  | _ => 0
private theorem shortNegativeR008Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR008Q00P shortNegativeR008Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR008Q00L (0:Fin 12)) (shortNegativeR008Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR008Q00P shortNegativeR008Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR008Q00L (1:Fin 12)) (shortNegativeR008Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR008Q00P shortNegativeR008Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR008Q00L (2:Fin 12)) (shortNegativeR008Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR008Q00P shortNegativeR008Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR008Q00L (3:Fin 12)) (shortNegativeR008Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR008Q00P shortNegativeR008Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR008Q00L (4:Fin 12)) (shortNegativeR008Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR008Q00P shortNegativeR008Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR008Q00L (5:Fin 12)) (shortNegativeR008Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR008Q00P shortNegativeR008Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR008Q00L (6:Fin 12)) (shortNegativeR008Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR008Q00P shortNegativeR008Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR008Q00L (7:Fin 12)) (shortNegativeR008Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR008Q00P shortNegativeR008Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR008Q00L (8:Fin 12)) (shortNegativeR008Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR008Q00P shortNegativeR008Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR008Q00L (9:Fin 12)) (shortNegativeR008Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR008Q00P shortNegativeR008Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR008Q00L (10:Fin 12)) (shortNegativeR008Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR008Q00P shortNegativeR008Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR008Q00L (11:Fin 12)) (shortNegativeR008Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR008Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR008Q00P shortNegativeR008Q00F (shortNegativeNodes12 k)).re (shortNegativeR008Q00L k) (shortNegativeR008Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR008Q00Point00
  · exact shortNegativeR008Q00Point01
  · exact shortNegativeR008Q00Point02
  · exact shortNegativeR008Q00Point03
  · exact shortNegativeR008Q00Point04
  · exact shortNegativeR008Q00Point05
  · exact shortNegativeR008Q00Point06
  · exact shortNegativeR008Q00Point07
  · exact shortNegativeR008Q00Point08
  · exact shortNegativeR008Q00Point09
  · exact shortNegativeR008Q00Point10
  · exact shortNegativeR008Q00Point11

theorem shortNegativeR008Q00Bound {t a : ℝ} (tl : ((37/40):ℝ)≤t) (tu : t≤((93/100):ℝ)) (al : ((202082149990879/329853488332800):ℝ)≤a) (au : a≤((202726395085279/329853488332800):ℝ)) : (((-652467882933619357789226975351363/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-89785421646892503577513399669315/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR008Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (202082149990879/329853488332800) (202726395085279/329853488332800)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR008Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR008Q00F_ok n) ts asb
  exact factored_negative_12_samples 17660 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip008Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR008Q00L shortNegativeR008Q00U (-652467882933619357789226975351363/649037107316853453566312041152512) (-89785421646892503577513399669315/649037107316853453566312041152512) shortNegativeR008Q00Samples (by decide +kernel)

def shortNegativeR008Q01T := Grid.ofRats (37/40) (93/100)
def shortNegativeR008Q01P : PrimalThetaParameters := ⟨⟨⟨65092303998787964389535,66122844173152483540205,true⟩,⟨0,0,true⟩⟩, ⟨⟨1167101820837297635568322,1170810758799901841944086,true⟩,⟨0,0,true⟩⟩, ⟨(-1463748831961708949914443),(-1456330956036569256642448),true⟩, ⟨5718237458864616659128332,5801027219461824570602942,true⟩⟩
theorem shortNegativeR008Q01P_ok : shortNegativeR008Q01P.encloses (primalThetaParameters shortNegativeR008Q01T (Grid.ofRats (202726395085279/329853488332800) (203370640179679/329853488332800))) := by decide +kernel

def shortNegativeR008Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨582347413447157937445068,584638782540174696253464,true⟩,⟨2499836960834083108966469,2509673098193391389806186,true⟩,⟨⟨684601046477980276361442,688309984440584482784854,true⟩,⟨993273895917635871075661,996982833880240077503349,true⟩⟩⟩
  | 1 => ⟨⟨7275739433226325318114,7478516054932362106976,true⟩,⟨582347413447157937445068,584638782540174696253464,true⟩,⟨⟨(-1179614833270686027178158),(-1168488019383010846936048),true⟩,⟨282715773141710202244814,293842587029385382474734,true⟩⟩⟩
  | 2 => ⟨⟨4894429886053687167,5232329856029260693,true⟩,⟨7275739433226325318114,7478516054932362106976,true⟩,⟨⟨138212084369424523175085,156756774182170677225495,true⟩,⟨(-1209168165572523732309484),(-1190623475759777578244591),true⟩⟩⟩
  | 3 => ⟨⟨177244554346905,200263215955930,true⟩,⟨4894429886053687167,5232329856029260693,true⟩,⟨⟨1056310544311298275076512,1082273110049115402927665,true⟩,⟨551037001991181401001219,576999567728998528845419,true⟩⟩⟩
  | 4 => ⟨⟨(-34014004407),34778831066,true⟩,⟨177244554346905,200263215955930,true⟩,⟨⟨(-923702850719540706028378),(-890322409056652604353055),true⟩,⟨782578023598660598841519,815958465261548700515356,true⟩⟩⟩
  | _ => ⟨⟨(-34359738332),34359738416,true⟩,⟨(-34014004407),34778831066,true⟩,⟨⟨(-445431249576299161337056),(-404632931988340085866480),true⟩,⟨(-1152145313696267212509673),(-1111346996108308137029367),true⟩⟩⟩
theorem shortNegativeR008Q01F_ok : ∀ n : Fin 6, (shortNegativeR008Q01F n).encloses (FactoredFrequency.build shortNegativeR008Q01T (Grid.ofRats (202726395085279/329853488332800) (203370640179679/329853488332800)) n) := by decide +kernel
def shortNegativeR008Q01L : ℕ → ℚ
  | 0 => (1894097/1000000)
  | 1 => (1313249/500000)
  | 2 => (1227753/500000)
  | 3 => (1900997/1000000)
  | 4 => (544387/500000)
  | 5 => (-26193/250000)
  | 6 => (-441679/250000)
  | 7 => (-187469/50000)
  | 8 => (-5470063/1000000)
  | 9 => (-1158277/200000)
  | 10 => (-781723/200000)
  | 11 => (-45449/62500)
  | _ => 0
def shortNegativeR008Q01U : ℕ → ℚ
  | 0 => (2390943/1000000)
  | 1 => (1569997/500000)
  | 2 => (2961437/1000000)
  | 3 => (1191807/500000)
  | 4 => (385529/250000)
  | 5 => (202859/500000)
  | 6 => (-225671/200000)
  | 7 => (-2976049/1000000)
  | 8 => (-4528973/1000000)
  | 9 => (-4575261/1000000)
  | 10 => (-312333/125000)
  | 11 => (106507/200000)
  | _ => 0
private theorem shortNegativeR008Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR008Q01P shortNegativeR008Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR008Q01L (0:Fin 12)) (shortNegativeR008Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR008Q01P shortNegativeR008Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR008Q01L (1:Fin 12)) (shortNegativeR008Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR008Q01P shortNegativeR008Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR008Q01L (2:Fin 12)) (shortNegativeR008Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR008Q01P shortNegativeR008Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR008Q01L (3:Fin 12)) (shortNegativeR008Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR008Q01P shortNegativeR008Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR008Q01L (4:Fin 12)) (shortNegativeR008Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR008Q01P shortNegativeR008Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR008Q01L (5:Fin 12)) (shortNegativeR008Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR008Q01P shortNegativeR008Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR008Q01L (6:Fin 12)) (shortNegativeR008Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR008Q01P shortNegativeR008Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR008Q01L (7:Fin 12)) (shortNegativeR008Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR008Q01P shortNegativeR008Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR008Q01L (8:Fin 12)) (shortNegativeR008Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR008Q01P shortNegativeR008Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR008Q01L (9:Fin 12)) (shortNegativeR008Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR008Q01P shortNegativeR008Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR008Q01L (10:Fin 12)) (shortNegativeR008Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR008Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR008Q01P shortNegativeR008Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR008Q01L (11:Fin 12)) (shortNegativeR008Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR008Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR008Q01P shortNegativeR008Q01F (shortNegativeNodes12 k)).re (shortNegativeR008Q01L k) (shortNegativeR008Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR008Q01Point00
  · exact shortNegativeR008Q01Point01
  · exact shortNegativeR008Q01Point02
  · exact shortNegativeR008Q01Point03
  · exact shortNegativeR008Q01Point04
  · exact shortNegativeR008Q01Point05
  · exact shortNegativeR008Q01Point06
  · exact shortNegativeR008Q01Point07
  · exact shortNegativeR008Q01Point08
  · exact shortNegativeR008Q01Point09
  · exact shortNegativeR008Q01Point10
  · exact shortNegativeR008Q01Point11

theorem shortNegativeR008Q01Bound {t a : ℝ} (tl : ((37/40):ℝ)≤t) (tu : t≤((93/100):ℝ)) (al : ((202726395085279/329853488332800):ℝ)≤a) (au : a≤((203370640179679/329853488332800):ℝ)) : (((-652467882933619357789226975351363/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-89785421646892503577513399669315/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR008Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (202726395085279/329853488332800) (203370640179679/329853488332800)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR008Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR008Q01F_ok n) ts asb
  exact factored_negative_12_samples 17660 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip008Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR008Q01L shortNegativeR008Q01U (-652467882933619357789226975351363/649037107316853453566312041152512) (-89785421646892503577513399669315/649037107316853453566312041152512) shortNegativeR008Q01Samples (by decide +kernel)

theorem short_original_negative_008 {t a : ℝ} (tb : RealMem negative_008.t t) (ab : RealMem negative_008.a a) : RealMem negative_008.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((37/40):ℝ) ((93/100):ℝ) := by simpa [negative_008,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((37/40):ℝ)<((93/100):ℝ)) tB
  have aB : a∈Icc ((202082149990879/329853488332800):ℝ) ((203370640179679/329853488332800):ℝ) := by simpa [negative_008,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((202082149990879/329853488332800):ℝ)<((203370640179679/329853488332800):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR008Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_008,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR008Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_008,RealMem] using v

def shortNegativeR009Q00T := Grid.ofRats (93/100) (373/400)
def shortNegativeR009Q00P : PrimalThetaParameters := ⟨⟨⟨64583072603341797195728,65092303998856683867166,true⟩,⟨0,0,true⟩⟩, ⟨⟨1166827616046997828441792,1174245491972137521712864,true⟩,⟨0,0,true⟩⟩, ⟨(-1464297241542308564167506),(-1449461489692097897104913),true⟩, ⟨5675230566780114023218499,5796856941214108513794726,true⟩⟩
theorem shortNegativeR009Q00P_ok : shortNegativeR009Q00P.encloses (primalThetaParameters shortNegativeR009Q00T (Grid.ofRats (202678765523179/329853488332800) (203967255711979/329853488332800))) := by decide +kernel

def shortNegativeR009Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨581205098806480717685016,582347413447226656942826,true⟩,⟨2509673098193322670239341,2514605670755584977719654,true⟩,⟨⟨681445195525765819546758,688863071450905512865626,true⟩,⟨992315886374028115914711,999733762299167809237996,true⟩⟩⟩
  | 1 => ⟨⟨7176422360089300259631,7275739433295044795218,true⟩,⟨581205098806480717685016,582347413447226656942826,true⟩,⟨⟨(-1186299694403409989152118),(-1164046066628128348224047),true⟩,⟨272546128479396785543647,294799756254678426459444,true⟩⟩⟩
  | 2 => ⟨⟨4733753210205153187,4894429954773163904,true⟩,⟨7176422360089300259631,7275739433295044795218,true⟩,⟨⟨136778836111278980500383,173868215736702569027736,true⟩,⟨(-1217450957886009626065022),(-1180361578260586037523306),true⟩⟩⟩
  | 3 => ⟨⟨166775720378721,177313273823642,true⟩,⟨4733753210205153187,4894429954773163904,true⟩,⟨⟨1038123720043966896761577,1090048851519532432880162,true⟩,⟨547816149223049060912124,599741280698614597023966,true⟩⟩⟩
  | 4 => ⟨⟨(-34045717857),34705472330,true⟩,⟨166775720378721,177313273823642,true⟩,⟨⟨(-949733060169448628364041),(-882972176843741144630571),true⟩,⟨755162211518957275464672,821923094844664759196381,true⟩⟩⟩
  | _ => ⟨⟨(-34359738337),34359738405,true⟩,⟨(-34045717857),34705472330,true⟩,⟨⟨(-449513877267860879182851),(-367917242092011447864467),true⟩,⟨(-1178538722340440946887879),(-1096942087164591515559460),true⟩⟩⟩
theorem shortNegativeR009Q00F_ok : ∀ n : Fin 6, (shortNegativeR009Q00F n).encloses (FactoredFrequency.build shortNegativeR009Q00T (Grid.ofRats (202678765523179/329853488332800) (203967255711979/329853488332800)) n) := by decide +kernel
def shortNegativeR009Q00L : ℕ → ℚ
  | 0 => (1842169/1000000)
  | 1 => (1292083/500000)
  | 2 => (2426579/1000000)
  | 3 => (939043/500000)
  | 4 => (267173/250000)
  | 5 => (-14571/125000)
  | 6 => (-27543/15625)
  | 7 => (-58084/15625)
  | 8 => (-2699537/500000)
  | 9 => (-2856469/500000)
  | 10 => (-1922919/500000)
  | 11 => (-706759/1000000)
  | _ => 0
def shortNegativeR009Q00U : ℕ → ℚ
  | 0 => (452577/200000)
  | 1 => (1518449/500000)
  | 2 => (45087/15625)
  | 3 => (581719/250000)
  | 4 => (748749/500000)
  | 5 => (73421/200000)
  | 6 => (-9271/8000)
  | 7 => (-748083/250000)
  | 8 => (-4537053/1000000)
  | 9 => (-4602017/1000000)
  | 10 => (-2604411/1000000)
  | 11 => (355809/1000000)
  | _ => 0
private theorem shortNegativeR009Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR009Q00P shortNegativeR009Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR009Q00L (0:Fin 12)) (shortNegativeR009Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR009Q00P shortNegativeR009Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR009Q00L (1:Fin 12)) (shortNegativeR009Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR009Q00P shortNegativeR009Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR009Q00L (2:Fin 12)) (shortNegativeR009Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR009Q00P shortNegativeR009Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR009Q00L (3:Fin 12)) (shortNegativeR009Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR009Q00P shortNegativeR009Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR009Q00L (4:Fin 12)) (shortNegativeR009Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR009Q00P shortNegativeR009Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR009Q00L (5:Fin 12)) (shortNegativeR009Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR009Q00P shortNegativeR009Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR009Q00L (6:Fin 12)) (shortNegativeR009Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR009Q00P shortNegativeR009Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR009Q00L (7:Fin 12)) (shortNegativeR009Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR009Q00P shortNegativeR009Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR009Q00L (8:Fin 12)) (shortNegativeR009Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR009Q00P shortNegativeR009Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR009Q00L (9:Fin 12)) (shortNegativeR009Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR009Q00P shortNegativeR009Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR009Q00L (10:Fin 12)) (shortNegativeR009Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR009Q00P shortNegativeR009Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR009Q00L (11:Fin 12)) (shortNegativeR009Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR009Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR009Q00P shortNegativeR009Q00F (shortNegativeNodes12 k)).re (shortNegativeR009Q00L k) (shortNegativeR009Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR009Q00Point00
  · exact shortNegativeR009Q00Point01
  · exact shortNegativeR009Q00Point02
  · exact shortNegativeR009Q00Point03
  · exact shortNegativeR009Q00Point04
  · exact shortNegativeR009Q00Point05
  · exact shortNegativeR009Q00Point06
  · exact shortNegativeR009Q00Point07
  · exact shortNegativeR009Q00Point08
  · exact shortNegativeR009Q00Point09
  · exact shortNegativeR009Q00Point10
  · exact shortNegativeR009Q00Point11

theorem shortNegativeR009Q00Bound {t a : ℝ} (tl : ((93/100):ℝ)≤t) (tu : t≤((373/400):ℝ)) (al : ((202678765523179/329853488332800):ℝ)≤a) (au : a≤((203967255711979/329853488332800):ℝ)) : (((-1343982098697844460209157028981971/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-251779991576912558810508454014163/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR009Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (202678765523179/329853488332800) (203967255711979/329853488332800)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR009Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR009Q00F_ok n) ts asb
  exact factored_negative_12_samples 17660 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip008Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR009Q00L shortNegativeR009Q00U (-1343982098697844460209157028981971/1298074214633706907132624082305024) (-251779991576912558810508454014163/1298074214633706907132624082305024) shortNegativeR009Q00Samples (by decide +kernel)

def shortNegativeR009Q10T := Grid.ofRats (373/400) (187/200)
def shortNegativeR009Q10P : PrimalThetaParameters := ⟨⟨⟨64077825036984130884760,64583072603410516673362,true⟩,⟨0,0,true⟩⟩, ⟨⟨1166827616046997828441792,1174245491972137521712864,true⟩,⟨0,0,true⟩⟩, ⟨(-1464297241542308564167506),(-1449461489692097897104913),true⟩, ⟨5664613376346629316072563,5785737709135449482881072,true⟩⟩
theorem shortNegativeR009Q10P_ok : shortNegativeR009Q10P.encloses (primalThetaParameters shortNegativeR009Q10T (Grid.ofRats (202678765523179/329853488332800) (203967255711979/329853488332800))) := by decide +kernel

def shortNegativeR009Q10F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨580065024894805076728034,581205098806549437182969,true⟩,⟨2514605670755516258151075,2519547937915891291822719,true⟩,⟨⟨681445195525765819546758,688863071450905512865626,true⟩,⟨992315886374028115914711,999733762299167809237996,true⟩⟩⟩
  | 1 => ⟨⟨7078461009089796088372,7176422360158019736734,true⟩,⟨580065024894805076728034,581205098806549437182969,true⟩,⟨⟨(-1186299694403409989152118),(-1164046066628128348224047),true⟩,⟨272546128479396785543647,294799756254678426459444,true⟩⟩⟩
  | 2 => ⟨⟨4578351304775551703,4733753278924629925,true⟩,⟨7078461009089796088372,7176422360158019736734,true⟩,⟨⟨136778836111278980500383,173868215736702569027736,true⟩,⟨(-1217450957886009626065022),(-1180361578260586037523306),true⟩⟩⟩
  | 3 => ⟨⟨156925101414950,166844439855458,true⟩,⟨4578351304775551703,4733753278924629925,true⟩,⟨⟨1038123720043966896761577,1090048851519532432880162,true⟩,⟨547816149223049060912124,599741280698614597023966,true⟩⟩⟩
  | 4 => ⟨⟨(-34074522299),34673758880,true⟩,⟨156925101414950,166844439855458,true⟩,⟨⟨(-949733060169448628364041),(-882972176843741144630571),true⟩,⟨755162211518957275464672,821923094844664759196381,true⟩⟩⟩
  | _ => ⟨⟨(-34359738341),34359738400,true⟩,⟨(-34074522299),34673758880,true⟩,⟨⟨(-449513877267860879182851),(-367917242092011447864467),true⟩,⟨(-1178538722340440946887879),(-1096942087164591515559460),true⟩⟩⟩
theorem shortNegativeR009Q10F_ok : ∀ n : Fin 6, (shortNegativeR009Q10F n).encloses (FactoredFrequency.build shortNegativeR009Q10T (Grid.ofRats (202678765523179/329853488332800) (203967255711979/329853488332800)) n) := by decide +kernel
def shortNegativeR009Q10L : ℕ → ℚ
  | 0 => (1796637/1000000)
  | 1 => (2545181/1000000)
  | 2 => (599181/250000)
  | 3 => (926719/500000)
  | 4 => (1046353/1000000)
  | 5 => (-137091/1000000)
  | 6 => (-355499/200000)
  | 7 => (-3720479/1000000)
  | 8 => (-2693423/500000)
  | 9 => (-5695781/1000000)
  | 10 => (-1923681/500000)
  | 11 => (-369223/500000)
  | _ => 0
def shortNegativeR009Q10U : ℕ → ℚ
  | 0 => (69259/31250)
  | 1 => (93663/31250)
  | 2 => (356913/125000)
  | 3 => (2302069/1000000)
  | 4 => (184393/125000)
  | 5 => (86757/250000)
  | 6 => (-586771/500000)
  | 7 => (-599331/200000)
  | 8 => (-1132169/250000)
  | 9 => (-2295507/500000)
  | 10 => (-653461/250000)
  | 11 => (158589/500000)
  | _ => 0
private theorem shortNegativeR009Q10Point00 : containedInReported (sampledFactoredPrimal shortNegativeR009Q10P shortNegativeR009Q10F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR009Q10L (0:Fin 12)) (shortNegativeR009Q10U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q10Point01 : containedInReported (sampledFactoredPrimal shortNegativeR009Q10P shortNegativeR009Q10F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR009Q10L (1:Fin 12)) (shortNegativeR009Q10U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q10Point02 : containedInReported (sampledFactoredPrimal shortNegativeR009Q10P shortNegativeR009Q10F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR009Q10L (2:Fin 12)) (shortNegativeR009Q10U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q10Point03 : containedInReported (sampledFactoredPrimal shortNegativeR009Q10P shortNegativeR009Q10F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR009Q10L (3:Fin 12)) (shortNegativeR009Q10U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q10Point04 : containedInReported (sampledFactoredPrimal shortNegativeR009Q10P shortNegativeR009Q10F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR009Q10L (4:Fin 12)) (shortNegativeR009Q10U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q10Point05 : containedInReported (sampledFactoredPrimal shortNegativeR009Q10P shortNegativeR009Q10F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR009Q10L (5:Fin 12)) (shortNegativeR009Q10U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q10Point06 : containedInReported (sampledFactoredPrimal shortNegativeR009Q10P shortNegativeR009Q10F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR009Q10L (6:Fin 12)) (shortNegativeR009Q10U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q10Point07 : containedInReported (sampledFactoredPrimal shortNegativeR009Q10P shortNegativeR009Q10F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR009Q10L (7:Fin 12)) (shortNegativeR009Q10U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q10Point08 : containedInReported (sampledFactoredPrimal shortNegativeR009Q10P shortNegativeR009Q10F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR009Q10L (8:Fin 12)) (shortNegativeR009Q10U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q10Point09 : containedInReported (sampledFactoredPrimal shortNegativeR009Q10P shortNegativeR009Q10F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR009Q10L (9:Fin 12)) (shortNegativeR009Q10U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q10Point10 : containedInReported (sampledFactoredPrimal shortNegativeR009Q10P shortNegativeR009Q10F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR009Q10L (10:Fin 12)) (shortNegativeR009Q10U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR009Q10Point11 : containedInReported (sampledFactoredPrimal shortNegativeR009Q10P shortNegativeR009Q10F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR009Q10L (11:Fin 12)) (shortNegativeR009Q10U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR009Q10Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR009Q10P shortNegativeR009Q10F (shortNegativeNodes12 k)).re (shortNegativeR009Q10L k) (shortNegativeR009Q10U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR009Q10Point00
  · exact shortNegativeR009Q10Point01
  · exact shortNegativeR009Q10Point02
  · exact shortNegativeR009Q10Point03
  · exact shortNegativeR009Q10Point04
  · exact shortNegativeR009Q10Point05
  · exact shortNegativeR009Q10Point06
  · exact shortNegativeR009Q10Point07
  · exact shortNegativeR009Q10Point08
  · exact shortNegativeR009Q10Point09
  · exact shortNegativeR009Q10Point10
  · exact shortNegativeR009Q10Point11

theorem shortNegativeR009Q10Bound {t a : ℝ} (tl : ((373/400):ℝ)≤t) (tu : t≤((187/200):ℝ)) (al : ((202678765523179/329853488332800):ℝ)≤a) (au : a≤((203967255711979/329853488332800):ℝ)) : (((-1343982098697844460209157028981971/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-251779991576912558810508454014163/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR009Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (202678765523179/329853488332800) (203967255711979/329853488332800)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR009Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR009Q10F_ok n) ts asb
  exact factored_negative_12_samples 17660 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip008Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR009Q10L shortNegativeR009Q10U (-1343982098697844460209157028981971/1298074214633706907132624082305024) (-251779991576912558810508454014163/1298074214633706907132624082305024) shortNegativeR009Q10Samples (by decide +kernel)

theorem short_original_negative_009 {t a : ℝ} (tb : RealMem negative_009.t t) (ab : RealMem negative_009.a a) : RealMem negative_009.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((93/100):ℝ) ((187/200):ℝ) := by simpa [negative_009,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((93/100):ℝ)<((187/200):ℝ)) tB
  have aB : a∈Icc ((202678765523179/329853488332800):ℝ) ((203967255711979/329853488332800):ℝ) := by simpa [negative_009,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((202678765523179/329853488332800):ℝ)<((203967255711979/329853488332800):ℝ)) aB
  fin_cases ti <;> fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR009Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_009,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR009Q10Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_009,RealMem] using v

def shortNegativeR010Q00T := Grid.ofRats (187/200) (15/16)
def shortNegativeR010Q00P : PrimalThetaParameters := ⟨⟨⟨63576530133344729229606,64077825037052850362383,true⟩,⟨0,0,true⟩⟩, ⟨⟨1170292558197127968362600,1177710434122267661633684,true⟩,⟨0,0,true⟩⟩, ⟨(-1457367357242048284325867),(-1442531605391837617263296),true⟩, ⟨5638277503562711986889947,5758362460628045743821038,true⟩⟩
theorem shortNegativeR010Q00P_ok : shortNegativeR010Q00P.encloses (primalThetaParameters shortNegativeR010Q00T (Grid.ofRats (1016403141879371/1649267441664000) (1022845592823371/1649267441664000))) := by decide +kernel

def shortNegativeR010Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨578927187316786439860864,580065024894873796225828,true⟩,⟨2519547937915822572254475,2524499918728309311812910,true⟩,⟨⟨678587645673930596187951,686005521599070289506663,true⟩,⟨994275535508266709686218,1001693411433406403009368,true⟩⟩⟩
  | 1 => ⟨⟨6981836874018798485225,7078461009158515565470,true⟩,⟨578927187316786439860864,580065024894873796225828,true⟩,⟨⟨(-1188695356021360671099061),(-1166441728246079030171040),true⟩,⟨262431161517881902694179,284684789293163543609752,true⟩⟩⟩
  | 2 => ⟨⟨4428051007090054454,4578351373495028440,true⟩,⟨6981836874018798485225,7078461009158515565470,true⟩,⟨⟨153943422992997592294442,191032802618421180822083,true⟩,⟨(-1215102038322020725228692),(-1178012658696597136686958),true⟩⟩⟩
  | 3 => ⟨⟨147656190066817,156993820891687,true⟩,⟨4428051007090054454,4578351373495028440,true⟩,⟨⟨1026398658206746495226579,1078323789682312031345366,true⟩,⟨569047931370356700581624,620973062845922236694116,true⟩⟩⟩
  | 4 => ⟨⟨(-34100684570),34644954438,true⟩,⟨147656190066817,156993820891687,true⟩,⟨⟨(-969766567340945478728260),(-903005684015237994994452),true⟩,⟨731265006220330811521880,798025889546038295253320,true⟩⟩⟩
  | _ => ⟨⟨(-34359738345),34359738396,true⟩,⟨(-34100684570),34644954438,true⟩,⟨⟨(-413446640285849957132686),(-331850005110000525814606),true⟩,⟨(-1190856953015408427528573),(-1109260317839558996199791),true⟩⟩⟩
theorem shortNegativeR010Q00F_ok : ∀ n : Fin 6, (shortNegativeR010Q00F n).encloses (FactoredFrequency.build shortNegativeR010Q00T (Grid.ofRats (1016403141879371/1649267441664000) (1022845592823371/1649267441664000)) n) := by decide +kernel
def shortNegativeR010Q00L : ℕ → ℚ
  | 0 => (68363/40000)
  | 1 => (1238913/500000)
  | 2 => (2351069/1000000)
  | 3 => (911147/500000)
  | 4 => (512829/500000)
  | 5 => (-146801/1000000)
  | 6 => (-1771297/1000000)
  | 7 => (-1847409/500000)
  | 8 => (-5344537/1000000)
  | 9 => (-2834081/500000)
  | 10 => (-193507/50000)
  | 11 => (-812771/1000000)
  | _ => 0
def shortNegativeR010Q00U : ℕ → ℚ
  | 0 => (17001/8000)
  | 1 => (1463659/500000)
  | 2 => (2808067/1000000)
  | 3 => (1135051/500000)
  | 4 => (181763/125000)
  | 5 => (337339/1000000)
  | 6 => (-292071/250000)
  | 7 => (-1486667/500000)
  | 8 => (-140563/31250)
  | 9 => (-286127/62500)
  | 10 => (-331611/125000)
  | 11 => (228301/1000000)
  | _ => 0
private theorem shortNegativeR010Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR010Q00P shortNegativeR010Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR010Q00L (0:Fin 12)) (shortNegativeR010Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR010Q00P shortNegativeR010Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR010Q00L (1:Fin 12)) (shortNegativeR010Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR010Q00P shortNegativeR010Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR010Q00L (2:Fin 12)) (shortNegativeR010Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR010Q00P shortNegativeR010Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR010Q00L (3:Fin 12)) (shortNegativeR010Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR010Q00P shortNegativeR010Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR010Q00L (4:Fin 12)) (shortNegativeR010Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR010Q00P shortNegativeR010Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR010Q00L (5:Fin 12)) (shortNegativeR010Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR010Q00P shortNegativeR010Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR010Q00L (6:Fin 12)) (shortNegativeR010Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR010Q00P shortNegativeR010Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR010Q00L (7:Fin 12)) (shortNegativeR010Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR010Q00P shortNegativeR010Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR010Q00L (8:Fin 12)) (shortNegativeR010Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR010Q00P shortNegativeR010Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR010Q00L (9:Fin 12)) (shortNegativeR010Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR010Q00P shortNegativeR010Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR010Q00L (10:Fin 12)) (shortNegativeR010Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR010Q00P shortNegativeR010Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR010Q00L (11:Fin 12)) (shortNegativeR010Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR010Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR010Q00P shortNegativeR010Q00F (shortNegativeNodes12 k)).re (shortNegativeR010Q00L k) (shortNegativeR010Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR010Q00Point00
  · exact shortNegativeR010Q00Point01
  · exact shortNegativeR010Q00Point02
  · exact shortNegativeR010Q00Point03
  · exact shortNegativeR010Q00Point04
  · exact shortNegativeR010Q00Point05
  · exact shortNegativeR010Q00Point06
  · exact shortNegativeR010Q00Point07
  · exact shortNegativeR010Q00Point08
  · exact shortNegativeR010Q00Point09
  · exact shortNegativeR010Q00Point10
  · exact shortNegativeR010Q00Point11

theorem shortNegativeR010Q00Bound {t a : ℝ} (tl : ((187/200):ℝ)≤t) (tu : t≤((15/16):ℝ)) (al : ((1016403141879371/1649267441664000):ℝ)≤a) (au : a≤((1022845592823371/1649267441664000):ℝ)) : (((-694366871508304093343045345597967/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-158362606210588426572501391497743/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR010Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1016403141879371/1649267441664000) (1022845592823371/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR010Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR010Q00F_ok n) ts asb
  exact factored_negative_12_samples 17660 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip008Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR010Q00L shortNegativeR010Q00U (-694366871508304093343045345597967/649037107316853453566312041152512) (-158362606210588426572501391497743/649037107316853453566312041152512) shortNegativeR010Q00Samples (by decide +kernel)

def shortNegativeR010Q10T := Grid.ofRats (15/16) (47/50)
def shortNegativeR010Q10P : PrimalThetaParameters := ⟨⟨⟨63079156969874717844620,63576530133413448707220,true⟩,⟨0,0,true⟩⟩, ⟨⟨1170292558197127968362600,1177710434122267661633684,true⟩,⟨0,0,true⟩⟩, ⟨(-1457367357242048284325867),(-1442531605391837617263296),true⟩, ⟨5627813570034850339196011,5747407205211429457079774,true⟩⟩
theorem shortNegativeR010Q10P_ok : shortNegativeR010Q10P.encloses (primalThetaParameters shortNegativeR010Q10T (Grid.ofRats (1016403141879371/1649267441664000) (1022845592823371/1649267441664000))) := by decide +kernel

def shortNegativeR010Q10F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨577791581685702004086577,578927187316855159358643,true⟩,⟨2524499918728240592244472,2529461632284287210505032,true⟩,⟨⟨678587645673930596187951,686005521599070289506663,true⟩,⟨994275535508266709686218,1001693411433406403009368,true⟩⟩⟩
  | 1 => ⟨⟨6886531701285261520914,6981836874087517962316,true⟩,⟨577791581685702004086577,578927187316855159358643,true⟩,⟨⟨(-1188695356021360671099061),(-1166441728246079030171040),true⟩,⟨262431161517881902694179,284684789293163543609752,true⟩⟩⟩
  | 2 => ⟨⟨4282684839140571672,4428051075809531191,true⟩,⟨6886531701285261520914,6981836874087517962316,true⟩,⟨⟨153943422992997592294442,191032802618421180822083,true⟩,⟨(-1215102038322020725228692),(-1178012658696597136686958),true⟩⟩⟩
  | 3 => ⟨⟨138934634812725,147724909543554,true⟩,⟨4282684839140571672,4428051075809531191,true⟩,⟨⟨1026398658206746495226579,1078323789682312031345366,true⟩,⟨569047931370356700581624,620973062845922236694116,true⟩⟩⟩
  | 4 => ⟨⟨(-34124447031),34618792167,true⟩,⟨138934634812725,147724909543554,true⟩,⟨⟨(-969766567340945478728260),(-903005684015237994994452),true⟩,⟨731265006220330811521880,798025889546038295253320,true⟩⟩⟩
  | _ => ⟨⟨(-34359738348),34359738392,true⟩,⟨(-34124447031),34618792167,true⟩,⟨⟨(-413446640285849957132686),(-331850005110000525814606),true⟩,⟨(-1190856953015408427528573),(-1109260317839558996199791),true⟩⟩⟩
theorem shortNegativeR010Q10F_ok : ∀ n : Fin 6, (shortNegativeR010Q10F n).encloses (FactoredFrequency.build shortNegativeR010Q10T (Grid.ofRats (1016403141879371/1649267441664000) (1022845592823371/1649267441664000)) n) := by decide +kernel
def shortNegativeR010Q10L : ℕ → ℚ
  | 0 => (1664599/1000000)
  | 1 => (2439183/1000000)
  | 2 => (2321173/1000000)
  | 3 => (1797549/1000000)
  | 4 => (501649/500000)
  | 5 => (-167239/1000000)
  | 6 => (-1785919/1000000)
  | 7 => (-369793/100000)
  | 8 => (-5332619/1000000)
  | 9 => (-1412829/250000)
  | 10 => (-387121/100000)
  | 11 => (-843193/1000000)
  | _ => 0
def shortNegativeR010Q10U : ℕ → ℚ
  | 0 => (2079589/1000000)
  | 1 => (90249/31250)
  | 2 => (694437/250000)
  | 3 => (112259/50000)
  | 4 => (143171/100000)
  | 5 => (317321/1000000)
  | 6 => (-295713/250000)
  | 7 => (-595533/200000)
  | 8 => (-2244931/500000)
  | 9 => (-2283591/500000)
  | 10 => (-1330829/500000)
  | 11 => (191121/1000000)
  | _ => 0
private theorem shortNegativeR010Q10Point00 : containedInReported (sampledFactoredPrimal shortNegativeR010Q10P shortNegativeR010Q10F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR010Q10L (0:Fin 12)) (shortNegativeR010Q10U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q10Point01 : containedInReported (sampledFactoredPrimal shortNegativeR010Q10P shortNegativeR010Q10F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR010Q10L (1:Fin 12)) (shortNegativeR010Q10U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q10Point02 : containedInReported (sampledFactoredPrimal shortNegativeR010Q10P shortNegativeR010Q10F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR010Q10L (2:Fin 12)) (shortNegativeR010Q10U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q10Point03 : containedInReported (sampledFactoredPrimal shortNegativeR010Q10P shortNegativeR010Q10F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR010Q10L (3:Fin 12)) (shortNegativeR010Q10U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q10Point04 : containedInReported (sampledFactoredPrimal shortNegativeR010Q10P shortNegativeR010Q10F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR010Q10L (4:Fin 12)) (shortNegativeR010Q10U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q10Point05 : containedInReported (sampledFactoredPrimal shortNegativeR010Q10P shortNegativeR010Q10F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR010Q10L (5:Fin 12)) (shortNegativeR010Q10U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q10Point06 : containedInReported (sampledFactoredPrimal shortNegativeR010Q10P shortNegativeR010Q10F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR010Q10L (6:Fin 12)) (shortNegativeR010Q10U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q10Point07 : containedInReported (sampledFactoredPrimal shortNegativeR010Q10P shortNegativeR010Q10F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR010Q10L (7:Fin 12)) (shortNegativeR010Q10U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q10Point08 : containedInReported (sampledFactoredPrimal shortNegativeR010Q10P shortNegativeR010Q10F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR010Q10L (8:Fin 12)) (shortNegativeR010Q10U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q10Point09 : containedInReported (sampledFactoredPrimal shortNegativeR010Q10P shortNegativeR010Q10F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR010Q10L (9:Fin 12)) (shortNegativeR010Q10U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q10Point10 : containedInReported (sampledFactoredPrimal shortNegativeR010Q10P shortNegativeR010Q10F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR010Q10L (10:Fin 12)) (shortNegativeR010Q10U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR010Q10Point11 : containedInReported (sampledFactoredPrimal shortNegativeR010Q10P shortNegativeR010Q10F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR010Q10L (11:Fin 12)) (shortNegativeR010Q10U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR010Q10Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR010Q10P shortNegativeR010Q10F (shortNegativeNodes12 k)).re (shortNegativeR010Q10L k) (shortNegativeR010Q10U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR010Q10Point00
  · exact shortNegativeR010Q10Point01
  · exact shortNegativeR010Q10Point02
  · exact shortNegativeR010Q10Point03
  · exact shortNegativeR010Q10Point04
  · exact shortNegativeR010Q10Point05
  · exact shortNegativeR010Q10Point06
  · exact shortNegativeR010Q10Point07
  · exact shortNegativeR010Q10Point08
  · exact shortNegativeR010Q10Point09
  · exact shortNegativeR010Q10Point10
  · exact shortNegativeR010Q10Point11

theorem shortNegativeR010Q10Bound {t a : ℝ} (tl : ((15/16):ℝ)≤t) (tu : t≤((47/50):ℝ)) (al : ((1016403141879371/1649267441664000):ℝ)≤a) (au : a≤((1022845592823371/1649267441664000):ℝ)) : (((-694366871508304093343045345597967/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-158362606210588426572501391497743/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR010Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1016403141879371/1649267441664000) (1022845592823371/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR010Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR010Q10F_ok n) ts asb
  exact factored_negative_12_samples 17660 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip008Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR010Q10L shortNegativeR010Q10U (-694366871508304093343045345597967/649037107316853453566312041152512) (-158362606210588426572501391497743/649037107316853453566312041152512) shortNegativeR010Q10Samples (by decide +kernel)

theorem short_original_negative_010 {t a : ℝ} (tb : RealMem negative_010.t t) (ab : RealMem negative_010.a a) : RealMem negative_010.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((187/200):ℝ) ((47/50):ℝ) := by simpa [negative_010,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((187/200):ℝ)<((47/50):ℝ)) tB
  have aB : a∈Icc ((1016403141879371/1649267441664000):ℝ) ((1022845592823371/1649267441664000):ℝ) := by simpa [negative_010,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((1016403141879371/1649267441664000):ℝ)<((1022845592823371/1649267441664000):ℝ)) aB
  fin_cases ti <;> fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR010Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_010,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR010Q10Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_010,RealMem] using v

def shortNegativeR011Q00T := Grid.ofRats (47/50) (377/400)
def shortNegativeR011Q00P : PrimalThetaParameters := ⟨⟨⟨62585674865939116102503,63079156969943437322231,true⟩,⟨0,0,true⟩⟩, ⟨⟨1173787918332155201607764,1181205794257294894878859,true⟩,⟨0,0,true⟩⟩, ⟨(-1450376636971993817835516),(-1435540885121783150772968),true⟩, ⟨5601623814922939126464935,5720191592192753077464068,true⟩⟩
theorem shortNegativeR011Q00P_ok : shortNegativeR011Q00P.encloses (primalThetaParameters shortNegativeR011Q00T (Grid.ofRats (1019438874268129/1649267441664000) (1025881325212129/1649267441664000))) := by decide +kernel

def shortNegativeR011Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨576658203623433825925128,577791581685770723584427,true⟩,⟨2529461632284218490936464,2534433097712795957425306,true⟩,⟨⟨675699331181536036143000,683117207106675729461894,true⟩,⟨996244081508601659039692,1003661957433741352363026,true⟩⟩⟩
  | 1 => ⟨⟨6792527486467760244414,6886531701353980998001,true⟩,⟨576658203623433825925128,577791581685770723584427,true⟩,⟨⟨(-1191023838344963648614782),(-1168770210569682007686694),true⟩,⟨252206907856572285003465,274460535631853925918935,true⟩⟩⟩
  | 2 => ⟨⟨4142090820966805704,4282684907860048409,true⟩,⟨6792527486467760244414,6886531701353980998001,true⟩,⟨⟨171222792925531661376811,208312172550955249904795,true⟩,⟨(-1212483524019093319111947),(-1175394144393669730570148),true⟩⟩⟩
  | 3 => ⟨⟨130728112688040,139003354289462,true⟩,⟨4142090820966805704,4282684907860048409,true⟩,⟨⟨1014141501306416697395089,1066066632781982233515205,true⟩,⟨590223418400949765678305,642148549876515301792592,true⟩⟩⟩
  | 4 => ⟨⟨(-34146029811),34595029706,true⟩,⟨130728112688040,139003354289462,true⟩,⟨⟨(-989344648157417396024057),(-922583764831709912290924),true⟩,⟨706642580433163335847662,773403463758870819577819,true⟩⟩⟩
  | _ => ⟨⟨(-34359738350),34359738389,true⟩,⟨(-34146029811),34595029706,true⟩,⟨⟨(-376687617809835511702779),(-295090982633986080386185),true⟩,⟨(-1202125151570218433275453),(-1120528516394369001947498),true⟩⟩⟩
theorem shortNegativeR011Q00F_ok : ∀ n : Fin 6, (shortNegativeR011Q00F n).encloses (FactoredFrequency.build shortNegativeR011Q00T (Grid.ofRats (1019438874268129/1649267441664000) (1025881325212129/1649267441664000)) n) := by decide +kernel
def shortNegativeR011Q00L : ℕ → ℚ
  | 0 => (39461/25000)
  | 1 => (2372061/1000000)
  | 2 => (2275263/1000000)
  | 3 => (353231/200000)
  | 4 => (982507/1000000)
  | 5 => (-176901/1000000)
  | 6 => (-88983/50000)
  | 7 => (-734477/200000)
  | 8 => (-132267/25000)
  | 9 => (-1405911/250000)
  | 10 => (-19463/5000)
  | 11 => (-114413/125000)
  | _ => 0
def shortNegativeR011Q00U : ℕ → ℚ
  | 0 => (1989829/1000000)
  | 1 => (88071/31250)
  | 2 => (1365107/500000)
  | 3 => (1106459/500000)
  | 4 => (1410533/1000000)
  | 5 => (153817/500000)
  | 6 => (-1177569/1000000)
  | 7 => (-2954479/1000000)
  | 8 => (-4459451/1000000)
  | 9 => (-2276987/500000)
  | 10 => (-674781/250000)
  | 11 => (837/8000)
  | _ => 0
private theorem shortNegativeR011Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR011Q00P shortNegativeR011Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR011Q00L (0:Fin 12)) (shortNegativeR011Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR011Q00P shortNegativeR011Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR011Q00L (1:Fin 12)) (shortNegativeR011Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR011Q00P shortNegativeR011Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR011Q00L (2:Fin 12)) (shortNegativeR011Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR011Q00P shortNegativeR011Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR011Q00L (3:Fin 12)) (shortNegativeR011Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR011Q00P shortNegativeR011Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR011Q00L (4:Fin 12)) (shortNegativeR011Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR011Q00P shortNegativeR011Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR011Q00L (5:Fin 12)) (shortNegativeR011Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR011Q00P shortNegativeR011Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR011Q00L (6:Fin 12)) (shortNegativeR011Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR011Q00P shortNegativeR011Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR011Q00L (7:Fin 12)) (shortNegativeR011Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR011Q00P shortNegativeR011Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR011Q00L (8:Fin 12)) (shortNegativeR011Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR011Q00P shortNegativeR011Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR011Q00L (9:Fin 12)) (shortNegativeR011Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR011Q00P shortNegativeR011Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR011Q00L (10:Fin 12)) (shortNegativeR011Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR011Q00P shortNegativeR011Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR011Q00L (11:Fin 12)) (shortNegativeR011Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR011Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR011Q00P shortNegativeR011Q00F (shortNegativeNodes12 k)).re (shortNegativeR011Q00L k) (shortNegativeR011Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR011Q00Point00
  · exact shortNegativeR011Q00Point01
  · exact shortNegativeR011Q00Point02
  · exact shortNegativeR011Q00Point03
  · exact shortNegativeR011Q00Point04
  · exact shortNegativeR011Q00Point05
  · exact shortNegativeR011Q00Point06
  · exact shortNegativeR011Q00Point07
  · exact shortNegativeR011Q00Point08
  · exact shortNegativeR011Q00Point09
  · exact shortNegativeR011Q00Point10
  · exact shortNegativeR011Q00Point11

theorem shortNegativeR011Q00Bound {t a : ℝ} (tl : ((47/50):ℝ)≤t) (tu : t≤((377/400):ℝ)) (al : ((1019438874268129/1649267441664000):ℝ)≤a) (au : a≤((1025881325212129/1649267441664000):ℝ)) : (((-1434359650989120188987676607833659/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-379225216314433378369949401278011/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR011Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1019438874268129/1649267441664000) (1025881325212129/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR011Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR011Q00F_ok n) ts asb
  exact factored_negative_12_samples 17660 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip008Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR011Q00L shortNegativeR011Q00U (-1434359650989120188987676607833659/1298074214633706907132624082305024) (-379225216314433378369949401278011/1298074214633706907132624082305024) shortNegativeR011Q00Samples (by decide +kernel)

def shortNegativeR011Q10T := Grid.ofRats (377/400) (189/200)
def shortNegativeR011Q10P : PrimalThetaParameters := ⟨⟨⟨62096053380924291593107,62585674866007835580109,true⟩,⟨0,0,true⟩⟩, ⟨⟨1173787918332155201607764,1181205794257294894878859,true⟩,⟨0,0,true⟩⟩, ⟨(-1450376636971993817835516),(-1435540885121783150772968),true⟩, ⟨5591311464006998525658867,5709398420626717529729372,true⟩⟩
theorem shortNegativeR011Q10P_ok : shortNegativeR011Q10P.encloses (primalThetaParameters shortNegativeR011Q10T (Grid.ofRats (1019438874268129/1649267441664000) (1025881325212129/1649267441664000))) := by decide +kernel

def shortNegativeR011Q10F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨575527048760451942386675,576658203623502545422568,true⟩,⟨2534433097712727237857035,2539414334180403067002443,true⟩,⟨⟨675699331181536036143000,683117207106675729461894,true⟩,⟨996244081508601659039692,1003661957433741352363026,true⟩⟩⟩
  | 1 => ⟨⟨6699806470913214744263,6792527486536479721497,true⟩,⟨575527048760451942386675,576658203623502545422568,true⟩,⟨⟨(-1191023838344963648614782),(-1168770210569682007686694),true⟩,⟨252206907856572285003465,274460535631853925918935,true⟩⟩⟩
  | 2 => ⟨⟨4006112290163720269,4142090889686282441,true⟩,⟨6699806470913214744263,6792527486536479721497,true⟩,⟨⟨171222792925531661376811,208312172550955249904795,true⟩,⟨(-1212483524019093319111947),(-1175394144393669730570148),true⟩⟩⟩
  | 3 => ⟨⟨123006209492927,130796832164777,true⟩,⟨4006112290163720269,4142090889686282441,true⟩,⟨⟨1014141501306416697395089,1066066632781982233515205,true⟩,⟨590223418400949765678305,642148549876515301792592,true⟩⟩⟩
  | 4 => ⟨⟨(-34165632848),34573446926,true⟩,⟨123006209492927,130796832164777,true⟩,⟨⟨(-989344648157417396024057),(-922583764831709912290924),true⟩,⟨706642580433163335847662,773403463758870819577819,true⟩⟩⟩
  | _ => ⟨⟨(-34359738353),34359738387,true⟩,⟨(-34165632848),34573446926,true⟩,⟨⟨(-376687617809835511702779),(-295090982633986080386185),true⟩,⟨(-1202125151570218433275453),(-1120528516394369001947498),true⟩⟩⟩
theorem shortNegativeR011Q10F_ok : ∀ n : Fin 6, (shortNegativeR011Q10F n).encloses (FactoredFrequency.build shortNegativeR011Q10T (Grid.ofRats (1019438874268129/1649267441664000) (1025881325212129/1649267441664000)) n) := by decide +kernel
def shortNegativeR011Q10L : ℕ → ℚ
  | 0 => (1535013/1000000)
  | 1 => (2333781/1000000)
  | 2 => (2245349/1000000)
  | 3 => (174133/100000)
  | 4 => (120017/125000)
  | 5 => (-3082/15625)
  | 6 => (-22427/12500)
  | 7 => (-1837753/500000)
  | 8 => (-2639533/500000)
  | 9 => (-1121421/200000)
  | 10 => (-1946619/500000)
  | 11 => (-1889/2000)
  | _ => 0
def shortNegativeR011Q10U : ℕ → ℚ
  | 0 => (1945347/1000000)
  | 1 => (2779277/1000000)
  | 2 => (337483/125000)
  | 3 => (1093949/500000)
  | 4 => (138811/100000)
  | 5 => (287681/1000000)
  | 6 => (-1192039/1000000)
  | 7 => (-1479409/500000)
  | 8 => (-1112879/250000)
  | 9 => (-1135819/250000)
  | 10 => (-1353629/500000)
  | 11 => (68853/1000000)
  | _ => 0
private theorem shortNegativeR011Q10Point00 : containedInReported (sampledFactoredPrimal shortNegativeR011Q10P shortNegativeR011Q10F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR011Q10L (0:Fin 12)) (shortNegativeR011Q10U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q10Point01 : containedInReported (sampledFactoredPrimal shortNegativeR011Q10P shortNegativeR011Q10F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR011Q10L (1:Fin 12)) (shortNegativeR011Q10U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q10Point02 : containedInReported (sampledFactoredPrimal shortNegativeR011Q10P shortNegativeR011Q10F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR011Q10L (2:Fin 12)) (shortNegativeR011Q10U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q10Point03 : containedInReported (sampledFactoredPrimal shortNegativeR011Q10P shortNegativeR011Q10F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR011Q10L (3:Fin 12)) (shortNegativeR011Q10U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q10Point04 : containedInReported (sampledFactoredPrimal shortNegativeR011Q10P shortNegativeR011Q10F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR011Q10L (4:Fin 12)) (shortNegativeR011Q10U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q10Point05 : containedInReported (sampledFactoredPrimal shortNegativeR011Q10P shortNegativeR011Q10F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR011Q10L (5:Fin 12)) (shortNegativeR011Q10U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q10Point06 : containedInReported (sampledFactoredPrimal shortNegativeR011Q10P shortNegativeR011Q10F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR011Q10L (6:Fin 12)) (shortNegativeR011Q10U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q10Point07 : containedInReported (sampledFactoredPrimal shortNegativeR011Q10P shortNegativeR011Q10F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR011Q10L (7:Fin 12)) (shortNegativeR011Q10U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q10Point08 : containedInReported (sampledFactoredPrimal shortNegativeR011Q10P shortNegativeR011Q10F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR011Q10L (8:Fin 12)) (shortNegativeR011Q10U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q10Point09 : containedInReported (sampledFactoredPrimal shortNegativeR011Q10P shortNegativeR011Q10F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR011Q10L (9:Fin 12)) (shortNegativeR011Q10U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q10Point10 : containedInReported (sampledFactoredPrimal shortNegativeR011Q10P shortNegativeR011Q10F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR011Q10L (10:Fin 12)) (shortNegativeR011Q10U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR011Q10Point11 : containedInReported (sampledFactoredPrimal shortNegativeR011Q10P shortNegativeR011Q10F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR011Q10L (11:Fin 12)) (shortNegativeR011Q10U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR011Q10Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR011Q10P shortNegativeR011Q10F (shortNegativeNodes12 k)).re (shortNegativeR011Q10L k) (shortNegativeR011Q10U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR011Q10Point00
  · exact shortNegativeR011Q10Point01
  · exact shortNegativeR011Q10Point02
  · exact shortNegativeR011Q10Point03
  · exact shortNegativeR011Q10Point04
  · exact shortNegativeR011Q10Point05
  · exact shortNegativeR011Q10Point06
  · exact shortNegativeR011Q10Point07
  · exact shortNegativeR011Q10Point08
  · exact shortNegativeR011Q10Point09
  · exact shortNegativeR011Q10Point10
  · exact shortNegativeR011Q10Point11

theorem shortNegativeR011Q10Bound {t a : ℝ} (tl : ((377/400):ℝ)≤t) (tu : t≤((189/200):ℝ)) (al : ((1019438874268129/1649267441664000):ℝ)≤a) (au : a≤((1025881325212129/1649267441664000):ℝ)) : (((-1434359650989120188987676607833659/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-379225216314433378369949401278011/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR011Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1019438874268129/1649267441664000) (1025881325212129/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR011Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR011Q10F_ok n) ts asb
  exact factored_negative_12_samples 17660 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip008Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR011Q10L shortNegativeR011Q10U (-1434359650989120188987676607833659/1298074214633706907132624082305024) (-379225216314433378369949401278011/1298074214633706907132624082305024) shortNegativeR011Q10Samples (by decide +kernel)

theorem short_original_negative_011 {t a : ℝ} (tb : RealMem negative_011.t t) (ab : RealMem negative_011.a a) : RealMem negative_011.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((47/50):ℝ) ((189/200):ℝ) := by simpa [negative_011,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((47/50):ℝ)<((189/200):ℝ)) tB
  have aB : a∈Icc ((1019438874268129/1649267441664000):ℝ) ((1025881325212129/1649267441664000):ℝ) := by simpa [negative_011,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((1019438874268129/1649267441664000):ℝ)<((1025881325212129/1649267441664000):ℝ)) aB
  fin_cases ti <;> fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR011Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_011,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR011Q10Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_011,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_008
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_009
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_010
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_011
