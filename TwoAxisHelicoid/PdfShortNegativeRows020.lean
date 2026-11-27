import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip016

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR020Q00T := Grid.ofRats (101/100) (51/50)
def shortNegativeR020Q00P : PrimalThetaParameters := ⟨⟨⟨49060929520564803374793,50626690213142961079189,true⟩,⟨0,0,true⟩⟩, ⟨⟨1224336489908505498260667,1231754365833645191531923,true⟩,⟨0,0,true⟩⟩, ⟨(-1349279493819293224529389),(-1334443741969082557467163),true⟩, ⟨5099512753173081499386975,5227037210318241654387674,true⟩⟩
theorem shortNegativeR020Q00P_ok : shortNegativeR020Q00P.encloses (primalThetaParameters shortNegativeR020Q00T (Grid.ofRats (212668096766783/329853488332800) (213956586955583/329853488332800))) := by decide +kernel

def shortNegativeR020Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨542604864447285543855548,546883252284292554198196,true⟩,⟨2672419810309398352763203,2693491586772928679535145,true⟩,⟨⟨633306857504432484772244,640724733429572178091600,true⟩,⟨1023769778924765572045144,1031187654849905265369932,true⟩⟩⟩
  | 1 => ⟨⟨4435962452821396696770,4686670786218614038062,true⟩,⟨542604864447285543855548,546883252284292554198196,true⟩,⟨⟨(-1214698889124651960408985),(-1192445261349370319482066),true⟩,⟨102521314300100635822368,124774942075382276734281,true⟩⟩⟩
  | 2 => ⟨⟨1471730021597837709,1681954190086149397,true⟩,⟨4435962452821396696770,4686670786218614038062,true⟩,⟨⟨414885996948327286161672,451975376573750874692252,true⟩,⟨(-1147101058411443746957750),(-1110011678786020158417606),true⟩⟩⟩
  | 3 => ⟨⟨19781119306884,25312419916967,true⟩,⟨1471730021597837709,1681954190086149397,true⟩,⟨⟨792120045694849970357878,844045177170415506486625,true⟩,⟨864117474597055296835219,916042606072620832964958,true⟩⟩⟩
  | 4 => ⟨⟨(-34348911145),34375647747,true⟩,⟨19781119306884,25312419916967,true⟩,⟨⟨(-1194406651448588426199838),(-1127645768122880942470962),true⟩,⟨303546520038750234896001,370307403364457718613534,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34348911145),34375647747,true⟩,⟨⟨173725632406149346574836,255322267581998777886937,true⟩,⟨(-1230538252283672805461738),(-1148941617107823374136215),true⟩⟩⟩
theorem shortNegativeR020Q00F_ok : ∀ n : Fin 6, (shortNegativeR020Q00F n).encloses (FactoredFrequency.build shortNegativeR020Q00T (Grid.ofRats (212668096766783/329853488332800) (213956586955583/329853488332800)) n) := by decide +kernel
def shortNegativeR020Q00L : ℕ → ℚ
  | 0 => (-270947/1000000)
  | 1 => (10878/15625)
  | 2 => (927793/1000000)
  | 3 => (137209/200000)
  | 4 => (110427/1000000)
  | 5 => (-893227/1000000)
  | 6 => (-2243073/1000000)
  | 7 => (-755763/200000)
  | 8 => (-5036549/1000000)
  | 9 => (-5513703/1000000)
  | 10 => (-1147711/250000)
  | 11 => (-632819/250000)
  | _ => 0
def shortNegativeR020Q00U : ℕ → ℚ
  | 0 => (282647/500000)
  | 1 => (25007/15625)
  | 2 => (371863/200000)
  | 3 => (1609061/1000000)
  | 4 => (999833/1000000)
  | 5 => (3557/25000)
  | 6 => (-1011727/1000000)
  | 7 => (-474919/200000)
  | 8 => (-89407/25000)
  | 9 => (-3766027/1000000)
  | 10 => (-2631927/1000000)
  | 11 => (-12278/15625)
  | _ => 0
private theorem shortNegativeR020Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR020Q00P shortNegativeR020Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR020Q00L (0:Fin 12)) (shortNegativeR020Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR020Q00P shortNegativeR020Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR020Q00L (1:Fin 12)) (shortNegativeR020Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR020Q00P shortNegativeR020Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR020Q00L (2:Fin 12)) (shortNegativeR020Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR020Q00P shortNegativeR020Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR020Q00L (3:Fin 12)) (shortNegativeR020Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR020Q00P shortNegativeR020Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR020Q00L (4:Fin 12)) (shortNegativeR020Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR020Q00P shortNegativeR020Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR020Q00L (5:Fin 12)) (shortNegativeR020Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR020Q00P shortNegativeR020Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR020Q00L (6:Fin 12)) (shortNegativeR020Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR020Q00P shortNegativeR020Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR020Q00L (7:Fin 12)) (shortNegativeR020Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR020Q00P shortNegativeR020Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR020Q00L (8:Fin 12)) (shortNegativeR020Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR020Q00P shortNegativeR020Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR020Q00L (9:Fin 12)) (shortNegativeR020Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR020Q00P shortNegativeR020Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR020Q00L (10:Fin 12)) (shortNegativeR020Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR020Q00P shortNegativeR020Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR020Q00L (11:Fin 12)) (shortNegativeR020Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR020Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR020Q00P shortNegativeR020Q00F (shortNegativeNodes12 k)).re (shortNegativeR020Q00L k) (shortNegativeR020Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR020Q00Point00
  · exact shortNegativeR020Q00Point01
  · exact shortNegativeR020Q00Point02
  · exact shortNegativeR020Q00Point03
  · exact shortNegativeR020Q00Point04
  · exact shortNegativeR020Q00Point05
  · exact shortNegativeR020Q00Point06
  · exact shortNegativeR020Q00Point07
  · exact shortNegativeR020Q00Point08
  · exact shortNegativeR020Q00Point09
  · exact shortNegativeR020Q00Point10
  · exact shortNegativeR020Q00Point11

theorem shortNegativeR020Q00Bound {t a : ℝ} (tl : ((101/100):ℝ)≤t) (tu : t≤((51/50):ℝ)) (al : ((212668096766783/329853488332800):ℝ)≤a) (au : a≤((213956586955583/329853488332800):ℝ)) : (((-5003126512980718146935060592904509/2596148429267413814265248164610048):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1395085827901588597548034504051005/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : shortNegativeR020Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (212668096766783/329853488332800) (213956586955583/329853488332800)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR020Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR020Q00F_ok n) ts asb
  exact factored_negative_12_samples 16770 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip016Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR020Q00L shortNegativeR020Q00U (-5003126512980718146935060592904509/2596148429267413814265248164610048) (-1395085827901588597548034504051005/2596148429267413814265248164610048) shortNegativeR020Q00Samples (by decide +kernel)

def shortNegativeR020Q01T := Grid.ofRats (101/100) (51/50)
def shortNegativeR020Q01P : PrimalThetaParameters := ⟨⟨⟨49060929520564803374793,50626690213142961079189,true⟩,⟨0,0,true⟩⟩, ⟨⟨1231754365833576472051262,1239172241758716165322542,true⟩,⟨0,0,true⟩⟩, ⟨(-1334443741969151276948151),(-1319607990118940609885972),true⟩, ⟨5070531333397019930149893,5196759764274176202806600,true⟩⟩
theorem shortNegativeR020Q01P_ok : shortNegativeR020Q01P.encloses (primalThetaParameters shortNegativeR020Q01T (Grid.ofRats (213956586955583/329853488332800) (215245077144383/329853488332800))) := by decide +kernel

def shortNegativeR020Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨542604864447285543855548,546883252284292554198196,true⟩,⟨2672419810309398352763203,2693491586772928679535145,true⟩,⟨⟨626990374975822271540904,634408250900961964860153,true⟩,⟨1027659092368961734039724,1035076968294101427364523,true⟩⟩⟩
  | 1 => ⟨⟨4435962452821396696770,4686670786218614038062,true⟩,⟨542604864447285543855548,546883252284292554198196,true⟩,⟨⟨(-1216586872504920269285526),(-1194333244729638628358841),true⟩,⟨80348234127258376226299,102601861902540017137649,true⟩⟩⟩
  | 2 => ⟨⟨1471730021597837709,1681954190086149397,true⟩,⟨4435962452821396696770,4686670786218614038062,true⟩,⟨⟨449300276533154247737150,486389656158577836268015,true⟩,⟨(-1133274578528242014381022),(-1096185198902818425841258),true⟩⟩⟩
  | 3 => ⟨⟨19781119306884,25312419916967,true⟩,⟨1471730021597837709,1681954190086149397,true⟩,⟨⟨753147065341722494116705,805072196817288030245589,true⟩,⟨898423619841631938841615,950348751317197474972502,true⟩⟩⟩
  | 4 => ⟨⟨(-34348911145),34375647747,true⟩,⟨19781119306884,25312419916967,true⟩,⟨⟨(-1211233526518595745424342),(-1144472643192888261697423),true⟩,⟨238949776687433535746052,305710660013141019460511,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34348911145),34375647747,true⟩,⟨⟨253477900126087031488240,335074535301936462799866,true⟩,⟨(-1213360957713746939109102),(-1131764322537897507785390),true⟩⟩⟩
theorem shortNegativeR020Q01F_ok : ∀ n : Fin 6, (shortNegativeR020Q01F n).encloses (FactoredFrequency.build shortNegativeR020Q01T (Grid.ofRats (213956586955583/329853488332800) (215245077144383/329853488332800)) n) := by decide +kernel
def shortNegativeR020Q01L : ℕ → ℚ
  | 0 => (-41941/125000)
  | 1 => (645917/1000000)
  | 2 => (448089/500000)
  | 3 => (671833/1000000)
  | 4 => (56279/500000)
  | 5 => (-872873/1000000)
  | 6 => (-2203923/1000000)
  | 7 => (-465681/125000)
  | 8 => (-4984501/1000000)
  | 9 => (-2737071/500000)
  | 10 => (-4594217/1000000)
  | 11 => (-2573359/1000000)
  | _ => 0
def shortNegativeR020Q01U : ℕ → ℚ
  | 0 => (490929/1000000)
  | 1 => (1540767/1000000)
  | 2 => (455163/250000)
  | 3 => (1589887/1000000)
  | 4 => (124811/125000)
  | 5 => (79167/500000)
  | 6 => (-979147/1000000)
  | 7 => (-2329363/1000000)
  | 8 => (-1413/400)
  | 9 => (-940599/250000)
  | 10 => (-2675301/1000000)
  | 11 => (-216049/250000)
  | _ => 0
private theorem shortNegativeR020Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR020Q01P shortNegativeR020Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR020Q01L (0:Fin 12)) (shortNegativeR020Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR020Q01P shortNegativeR020Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR020Q01L (1:Fin 12)) (shortNegativeR020Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR020Q01P shortNegativeR020Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR020Q01L (2:Fin 12)) (shortNegativeR020Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR020Q01P shortNegativeR020Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR020Q01L (3:Fin 12)) (shortNegativeR020Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR020Q01P shortNegativeR020Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR020Q01L (4:Fin 12)) (shortNegativeR020Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR020Q01P shortNegativeR020Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR020Q01L (5:Fin 12)) (shortNegativeR020Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR020Q01P shortNegativeR020Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR020Q01L (6:Fin 12)) (shortNegativeR020Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR020Q01P shortNegativeR020Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR020Q01L (7:Fin 12)) (shortNegativeR020Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR020Q01P shortNegativeR020Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR020Q01L (8:Fin 12)) (shortNegativeR020Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR020Q01P shortNegativeR020Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR020Q01L (9:Fin 12)) (shortNegativeR020Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR020Q01P shortNegativeR020Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR020Q01L (10:Fin 12)) (shortNegativeR020Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR020Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR020Q01P shortNegativeR020Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR020Q01L (11:Fin 12)) (shortNegativeR020Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR020Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR020Q01P shortNegativeR020Q01F (shortNegativeNodes12 k)).re (shortNegativeR020Q01L k) (shortNegativeR020Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR020Q01Point00
  · exact shortNegativeR020Q01Point01
  · exact shortNegativeR020Q01Point02
  · exact shortNegativeR020Q01Point03
  · exact shortNegativeR020Q01Point04
  · exact shortNegativeR020Q01Point05
  · exact shortNegativeR020Q01Point06
  · exact shortNegativeR020Q01Point07
  · exact shortNegativeR020Q01Point08
  · exact shortNegativeR020Q01Point09
  · exact shortNegativeR020Q01Point10
  · exact shortNegativeR020Q01Point11

theorem shortNegativeR020Q01Bound {t a : ℝ} (tl : ((101/100):ℝ)≤t) (tu : t≤((51/50):ℝ)) (al : ((213956586955583/329853488332800):ℝ)≤a) (au : a≤((215245077144383/329853488332800):ℝ)) : (((-5003126512980718146935060592904509/2596148429267413814265248164610048):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1395085827901588597548034504051005/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : shortNegativeR020Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (213956586955583/329853488332800) (215245077144383/329853488332800)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR020Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR020Q01F_ok n) ts asb
  exact factored_negative_12_samples 16770 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip016Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR020Q01L shortNegativeR020Q01U (-5003126512980718146935060592904509/2596148429267413814265248164610048) (-1395085827901588597548034504051005/2596148429267413814265248164610048) shortNegativeR020Q01Samples (by decide +kernel)

theorem short_original_negative_020 {t a : ℝ} (tb : RealMem negative_020.t t) (ab : RealMem negative_020.a a) : RealMem negative_020.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((101/100):ℝ) ((51/50):ℝ) := by simpa [negative_020,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((101/100):ℝ)<((51/50):ℝ)) tB
  have aB : a∈Icc ((212668096766783/329853488332800):ℝ) ((215245077144383/329853488332800):ℝ) := by simpa [negative_020,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((212668096766783/329853488332800):ℝ)<((215245077144383/329853488332800):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR020Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_020,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR020Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_020,RealMem] using v

def shortNegativeR021Q00T := Grid.ofRats (51/50) (103/100)
def shortNegativeR021Q00P : PrimalThetaParameters := ⟨⟨⟨47543594007261981526617,49060929520633522852252,true⟩,⟨0,0,true⟩⟩, ⟨⟨1232374786754403360911833,1239792662679543054183114,true⟩,⟨0,0,true⟩⟩, ⟨(-1333202900127497499227006),(-1318367148277286832164831),true⟩, ⟨5035891999534044351995119,5159678046532212754883857,true⟩⟩
theorem shortNegativeR021Q00P_ok : shortNegativeR021Q00P.encloses (primalThetaParameters shortNegativeR021Q00T (Grid.ofRats (1070321772497423/1649267441664000) (1076764223441423/1649267441664000))) := by decide +kernel

def shortNegativeR021Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨538359947378389253986113,542604864447354263352087,true⟩,⟨2693491586772859959960723,2714729512193082342777761,true⟩,⟨⟨626460993708599414707679,633878869633739108026796,true⟩,⟨1027982631523416009671890,1035400507448555702996569,true⟩⟩⟩
  | 1 => ⟨⟨4198665487875256997679,4435962452890116173739,true⟩,⟨538359947378389253986113,542604864447354263352087,true⟩,⟨⟨(-1216726278783716574621969),(-1194472651008434933695300),true⟩,⟨78492199570434712899702,100745827345716353811008,true⟩⟩⟩
  | 2 => ⟨⟨1287781413329857764,1471730090317314446,true⟩,⟨4198665487875256997679,4435962452890116173739,true⟩,⟨⟨452159130936516941486520,489248510561940530017802,true⟩,⟨(-1132070419404525430014034),(-1094981039779101841473914),true⟩⟩⟩
  | 3 => ⟨⟨15499000298699,19849838783621,true⟩,⟨1287781413329857764,1471730090317314446,true⟩,⟨⟨749821279199063743180901,801746410674629279310147,true⟩,⟨901216523363080100322555,953141654838645636453894,true⟩⟩⟩
  | 4 => ⟨⟨(-34352369836),34370565592,true⟩,⟨15499000298699,19849838783621,true⟩,⟨⟨(-1212478797504522788470234),(-1145717914178815304742619),true⟩,⟨233506621684877138525353,300267505010584622240415,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34352369836),34370565592,true⟩,⟨⟨260092528584213724226719,341689163760063155538862,true⟩,⟨(-1211681034182852271245771),(-1130084399007002839921656),true⟩⟩⟩
theorem shortNegativeR021Q00F_ok : ∀ n : Fin 6, (shortNegativeR021Q00F n).encloses (FactoredFrequency.build shortNegativeR021Q00T (Grid.ofRats (1070321772497423/1649267441664000) (1076764223441423/1649267441664000)) n) := by decide +kernel
def shortNegativeR021Q00L : ℕ → ℚ
  | 0 => (-456101/1000000)
  | 1 => (64969/125000)
  | 2 => (97931/125000)
  | 3 => (143521/250000)
  | 4 => (13549/500000)
  | 5 => (-189171/200000)
  | 6 => (-2250729/1000000)
  | 7 => (-3731623/1000000)
  | 8 => (-2473049/500000)
  | 9 => (-5412011/1000000)
  | 10 => (-456663/100000)
  | 11 => (-2623323/1000000)
  | _ => 0
def shortNegativeR021Q00U : ℕ → ℚ
  | 0 => (73009/200000)
  | 1 => (1408191/1000000)
  | 2 => (425851/250000)
  | 3 => (1489523/1000000)
  | 4 => (182361/200000)
  | 5 => (21683/250000)
  | 6 => (-1028201/1000000)
  | 7 => (-469139/200000)
  | 8 => (-702389/200000)
  | 9 => (-467021/125000)
  | 10 => (-539009/200000)
  | 11 => (-191059/200000)
  | _ => 0
private theorem shortNegativeR021Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR021Q00P shortNegativeR021Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR021Q00L (0:Fin 12)) (shortNegativeR021Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR021Q00P shortNegativeR021Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR021Q00L (1:Fin 12)) (shortNegativeR021Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR021Q00P shortNegativeR021Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR021Q00L (2:Fin 12)) (shortNegativeR021Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR021Q00P shortNegativeR021Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR021Q00L (3:Fin 12)) (shortNegativeR021Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR021Q00P shortNegativeR021Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR021Q00L (4:Fin 12)) (shortNegativeR021Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR021Q00P shortNegativeR021Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR021Q00L (5:Fin 12)) (shortNegativeR021Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR021Q00P shortNegativeR021Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR021Q00L (6:Fin 12)) (shortNegativeR021Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR021Q00P shortNegativeR021Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR021Q00L (7:Fin 12)) (shortNegativeR021Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR021Q00P shortNegativeR021Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR021Q00L (8:Fin 12)) (shortNegativeR021Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR021Q00P shortNegativeR021Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR021Q00L (9:Fin 12)) (shortNegativeR021Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR021Q00P shortNegativeR021Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR021Q00L (10:Fin 12)) (shortNegativeR021Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR021Q00P shortNegativeR021Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR021Q00L (11:Fin 12)) (shortNegativeR021Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR021Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR021Q00P shortNegativeR021Q00F (shortNegativeNodes12 k)).re (shortNegativeR021Q00L k) (shortNegativeR021Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR021Q00Point00
  · exact shortNegativeR021Q00Point01
  · exact shortNegativeR021Q00Point02
  · exact shortNegativeR021Q00Point03
  · exact shortNegativeR021Q00Point04
  · exact shortNegativeR021Q00Point05
  · exact shortNegativeR021Q00Point06
  · exact shortNegativeR021Q00Point07
  · exact shortNegativeR021Q00Point08
  · exact shortNegativeR021Q00Point09
  · exact shortNegativeR021Q00Point10
  · exact shortNegativeR021Q00Point11

theorem shortNegativeR021Q00Bound {t a : ℝ} (tl : ((51/50):ℝ)≤t) (tu : t≤((103/100):ℝ)) (al : ((1070321772497423/1649267441664000):ℝ)≤a) (au : a≤((1076764223441423/1649267441664000):ℝ)) : (((-5102751485497468909037267555441845/2596148429267413814265248164610048):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1624168249462619483517866514046133/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : shortNegativeR021Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1070321772497423/1649267441664000) (1076764223441423/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR021Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR021Q00F_ok n) ts asb
  exact factored_negative_12_samples 16770 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip016Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR021Q00L shortNegativeR021Q00U (-5102751485497468909037267555441845/2596148429267413814265248164610048) (-1624168249462619483517866514046133/2596148429267413814265248164610048) shortNegativeR021Q00Samples (by decide +kernel)

def shortNegativeR021Q01T := Grid.ofRats (51/50) (103/100)
def shortNegativeR021Q01P : PrimalThetaParameters := ⟨⟨⟨47543594007261981526617,49060929520633522852252,true⟩,⟨0,0,true⟩⟩, ⟨⟨1239792662679474334702429,1247210538604614027973733,true⟩,⟨0,0,true⟩⟩, ⟨(-1318367148277355551645768),(-1303531396427144884583640),true⟩, ⟨5007497557305310133595117,5130035323103951443327600,true⟩⟩
theorem shortNegativeR021Q01P_ok : shortNegativeR021Q01P.encloses (primalThetaParameters shortNegativeR021Q01T (Grid.ofRats (1076764223441423/1649267441664000) (1083206674385423/1649267441664000))) := by decide +kernel

def shortNegativeR021Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨538359947378389253986113,542604864447354263352087,true⟩,⟨2693491586772859959960723,2714729512193082342777761,true⟩,⟨⟨620118790473851299342346,627536666398990992661607,true⟩,⟨1031829860231277504507746,1039247736156417197832690,true⟩⟩⟩
  | 1 => ⟨⟨4198665487875256997679,4435962452890116173739,true⟩,⟨538359947378389253986113,542604864447354263352087,true⟩,⟨⟨(-1218171621262565121738495),(-1195917993487283480811825),true⟩,⟨56285872753189682188210,78539500528471323099195,true⟩⟩⟩
  | 2 => ⟨⟨1287781413329857764,1471730090317314446,true⟩,⟨4198665487875256997679,4435962452890116173739,true⟩,⟨⟨486094808543653355048513,523184188169076943579494,true⟩,⟨(-1117107666628123617006700),(-1080018287002700028467547),true⟩⟩⟩
  | 3 => ⟨⟨15499000298699,19849838783621,true⟩,⟨1287781413329857764,1471730090317314446,true⟩,⟨⟨709294341336415191581763,761219472811980727711532,true⟩,⟨933672217880749446592107,985597349356314982724967,true⟩⟩⟩
  | 4 => ⟨⟨(-34352369836),34370565592,true⟩,⟨15499000298699,19849838783621,true⟩,⟨⟨(-1225412253740130714990027),(-1158651370414423231263788),true⟩,⟨168019151997774961989273,234780035323482445701879,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34352369836),34370565592,true⟩,⟨⟨338376339936619724172848,419972975112469155484653,true⟩,⟨(-1188721754243021218279136),(-1107125119067171786956749),true⟩⟩⟩
theorem shortNegativeR021Q01F_ok : ∀ n : Fin 6, (shortNegativeR021Q01F n).encloses (FactoredFrequency.build shortNegativeR021Q01T (Grid.ofRats (1076764223441423/1649267441664000) (1083206674385423/1649267441664000)) n) := by decide +kernel
def shortNegativeR021Q01L : ℕ → ℚ
  | 0 => (-258791/500000)
  | 1 => (235451/500000)
  | 2 => (376137/500000)
  | 3 => (55991/100000)
  | 4 => (454/15625)
  | 5 => (-925947/1000000)
  | 6 => (-88499/40000)
  | 7 => (-919887/250000)
  | 8 => (-979007/200000)
  | 9 => (-1343077/250000)
  | 10 => (-1141891/250000)
  | 11 => (-1330889/500000)
  | _ => 0
def shortNegativeR021Q01U : ℕ → ℚ
  | 0 => (146917/500000)
  | 1 => (1349959/1000000)
  | 2 => (1665093/1000000)
  | 3 => (1470239/1000000)
  | 4 => (227533/250000)
  | 5 => (20433/200000)
  | 6 => (-62289/62500)
  | 7 => (-1150911/500000)
  | 8 => (-3469287/1000000)
  | 9 => (-3731563/1000000)
  | 10 => (-683751/250000)
  | 11 => (-25731/25000)
  | _ => 0
private theorem shortNegativeR021Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR021Q01P shortNegativeR021Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR021Q01L (0:Fin 12)) (shortNegativeR021Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR021Q01P shortNegativeR021Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR021Q01L (1:Fin 12)) (shortNegativeR021Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR021Q01P shortNegativeR021Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR021Q01L (2:Fin 12)) (shortNegativeR021Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR021Q01P shortNegativeR021Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR021Q01L (3:Fin 12)) (shortNegativeR021Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR021Q01P shortNegativeR021Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR021Q01L (4:Fin 12)) (shortNegativeR021Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR021Q01P shortNegativeR021Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR021Q01L (5:Fin 12)) (shortNegativeR021Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR021Q01P shortNegativeR021Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR021Q01L (6:Fin 12)) (shortNegativeR021Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR021Q01P shortNegativeR021Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR021Q01L (7:Fin 12)) (shortNegativeR021Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR021Q01P shortNegativeR021Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR021Q01L (8:Fin 12)) (shortNegativeR021Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR021Q01P shortNegativeR021Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR021Q01L (9:Fin 12)) (shortNegativeR021Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR021Q01P shortNegativeR021Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR021Q01L (10:Fin 12)) (shortNegativeR021Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR021Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR021Q01P shortNegativeR021Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR021Q01L (11:Fin 12)) (shortNegativeR021Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR021Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR021Q01P shortNegativeR021Q01F (shortNegativeNodes12 k)).re (shortNegativeR021Q01L k) (shortNegativeR021Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR021Q01Point00
  · exact shortNegativeR021Q01Point01
  · exact shortNegativeR021Q01Point02
  · exact shortNegativeR021Q01Point03
  · exact shortNegativeR021Q01Point04
  · exact shortNegativeR021Q01Point05
  · exact shortNegativeR021Q01Point06
  · exact shortNegativeR021Q01Point07
  · exact shortNegativeR021Q01Point08
  · exact shortNegativeR021Q01Point09
  · exact shortNegativeR021Q01Point10
  · exact shortNegativeR021Q01Point11

theorem shortNegativeR021Q01Bound {t a : ℝ} (tl : ((51/50):ℝ)≤t) (tu : t≤((103/100):ℝ)) (al : ((1076764223441423/1649267441664000):ℝ)≤a) (au : a≤((1083206674385423/1649267441664000):ℝ)) : (((-5102751485497468909037267555441845/2596148429267413814265248164610048):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1624168249462619483517866514046133/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : shortNegativeR021Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1076764223441423/1649267441664000) (1083206674385423/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR021Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR021Q01F_ok n) ts asb
  exact factored_negative_12_samples 16770 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip016Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR021Q01L shortNegativeR021Q01U (-5102751485497468909037267555441845/2596148429267413814265248164610048) (-1624168249462619483517866514046133/2596148429267413814265248164610048) shortNegativeR021Q01Samples (by decide +kernel)

theorem short_original_negative_021 {t a : ℝ} (tb : RealMem negative_021.t t) (ab : RealMem negative_021.a a) : RealMem negative_021.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((51/50):ℝ) ((103/100):ℝ) := by simpa [negative_021,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((51/50):ℝ)<((103/100):ℝ)) tB
  have aB : a∈Icc ((1070321772497423/1649267441664000):ℝ) ((1083206674385423/1649267441664000):ℝ) := by simpa [negative_021,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((1070321772497423/1649267441664000):ℝ)<((1083206674385423/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR021Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_021,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR021Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_021,RealMem] using v

def shortNegativeR022Q00T := Grid.ofRats (103/100) (26/25)
def shortNegativeR022Q00P : PrimalThetaParameters := ⟨⟨⟨46073185999867160677672,47543594007330701004053,true⟩,⟨0,0,true⟩⟩, ⟨⟨1240556761467748039195235,1247974637392887732466542,true⟩,⟨0,0,true⟩⟩, ⟨(-1316838950700808142660151),(-1302003198850597475598028),true⟩, ⟨4973323646054210985922821,5093507392063029087803316,true⟩⟩
theorem shortNegativeR022Q00P_ok : shortNegativeR022Q00P.encloses (primalThetaParameters shortNegativeR022Q00T (Grid.ofRats (215485569177331/329853488332800) (216774059366131/329853488332800))) := by decide +kernel

def shortNegativeR022Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨534148239228362795808088,538359947378457973482537,true⟩,⟨2714729512193013623202397,2736134896638676073247814,true⟩,⟨⟨619464155993214340466657,626882031918354033786037,true⟩,⟨1032223942247571128871541,1039641818172710822196621,true⟩⟩⟩
  | 1 => ⟨⟨3974062464812326577532,4198665487943976474635,true⟩,⟨534148239228362795808088,538359947378457973482537,true⟩,⟨⟨(-1218297275408477923945629),(-1196043647633196283019179),true⟩,⟨53997023241877771039030,76250651017159411949761,true⟩⟩⟩
  | 2 => ⟨⟨1126824175216176091,1287781482049334501,true⟩,⟨3974062464812326577532,4198665487943976474635,true⟩,⟨⟨489564003857077303902345,526653383482500892433715,true⟩,⟨(-1115507402373208693789758),(-1078418022747785105250291),true⟩⟩⟩
  | 3 => ⟨⟨12142245908669,15567719775436,true⟩,⟨1126824175216176091,1287781482049334501,true⟩,⟨⟨705041414241845837728571,756966545717411373858986,true⟩,⟨936915837065419407219704,988840968540984943353313,true⟩⟩⟩
  | 4 => ⟨⟨(-34354723669),34367106901,true⟩,⟨12142245908669,15567719775436,true⟩,⟨⟨(-1226538608951235509103518),(-1159777725625528025378127),true⟩,⟨161235141382114441718051,227996024707821925429698,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34354723669),34367106901,true⟩,⟨⟨346348077574602465545246,427944712750451896858507,true⟩,⟨(-1186057810473080096592258),(-1104461175297230665268565),true⟩⟩⟩
theorem shortNegativeR022Q00F_ok : ∀ n : Fin 6, (shortNegativeR022Q00F n).encloses (FactoredFrequency.build shortNegativeR022Q00T (Grid.ofRats (215485569177331/329853488332800) (216774059366131/329853488332800)) n) := by decide +kernel
def shortNegativeR022Q00L : ℕ → ℚ
  | 0 => (-9876/15625)
  | 1 => (174203/500000)
  | 2 => (320619/500000)
  | 3 => (231583/500000)
  | 4 => (-56989/1000000)
  | 5 => (-249303/250000)
  | 6 => (-1128773/500000)
  | 7 => (-3684919/1000000)
  | 8 => (-4857483/1000000)
  | 9 => (-5311789/1000000)
  | 10 => (-2269611/500000)
  | 11 => (-676793/250000)
  | _ => 0
def shortNegativeR022Q00U : ℕ → ℚ
  | 0 => (17377/100000)
  | 1 => (610449/500000)
  | 2 => (387327/250000)
  | 3 => (685291/500000)
  | 4 => (824611/1000000)
  | 5 => (1271/40000)
  | 6 => (-1044403/1000000)
  | 7 => (-1158757/500000)
  | 8 => (-3449359/1000000)
  | 9 => (-3705849/1000000)
  | 10 => (-344019/125000)
  | 11 => (-69637/62500)
  | _ => 0
private theorem shortNegativeR022Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR022Q00P shortNegativeR022Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR022Q00L (0:Fin 12)) (shortNegativeR022Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR022Q00P shortNegativeR022Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR022Q00L (1:Fin 12)) (shortNegativeR022Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR022Q00P shortNegativeR022Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR022Q00L (2:Fin 12)) (shortNegativeR022Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR022Q00P shortNegativeR022Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR022Q00L (3:Fin 12)) (shortNegativeR022Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR022Q00P shortNegativeR022Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR022Q00L (4:Fin 12)) (shortNegativeR022Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR022Q00P shortNegativeR022Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR022Q00L (5:Fin 12)) (shortNegativeR022Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR022Q00P shortNegativeR022Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR022Q00L (6:Fin 12)) (shortNegativeR022Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR022Q00P shortNegativeR022Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR022Q00L (7:Fin 12)) (shortNegativeR022Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR022Q00P shortNegativeR022Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR022Q00L (8:Fin 12)) (shortNegativeR022Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR022Q00P shortNegativeR022Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR022Q00L (9:Fin 12)) (shortNegativeR022Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR022Q00P shortNegativeR022Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR022Q00L (10:Fin 12)) (shortNegativeR022Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR022Q00P shortNegativeR022Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR022Q00L (11:Fin 12)) (shortNegativeR022Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR022Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR022Q00P shortNegativeR022Q00F (shortNegativeNodes12 k)).re (shortNegativeR022Q00L k) (shortNegativeR022Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR022Q00Point00
  · exact shortNegativeR022Q00Point01
  · exact shortNegativeR022Q00Point02
  · exact shortNegativeR022Q00Point03
  · exact shortNegativeR022Q00Point04
  · exact shortNegativeR022Q00Point05
  · exact shortNegativeR022Q00Point06
  · exact shortNegativeR022Q00Point07
  · exact shortNegativeR022Q00Point08
  · exact shortNegativeR022Q00Point09
  · exact shortNegativeR022Q00Point10
  · exact shortNegativeR022Q00Point11

theorem shortNegativeR022Q00Bound {t a : ℝ} (tl : ((103/100):ℝ)≤t) (tu : t≤((26/25):ℝ)) (al : ((215485569177331/329853488332800):ℝ)≤a) (au : a≤((216774059366131/329853488332800):ℝ)) : (((-652095729277753857853708323923001/324518553658426726783156020576256):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-228243316419704562050730014942265/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : shortNegativeR022Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (215485569177331/329853488332800) (216774059366131/329853488332800)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR022Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR022Q00F_ok n) ts asb
  exact factored_negative_12_samples 16770 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip016Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR022Q00L shortNegativeR022Q00U (-652095729277753857853708323923001/324518553658426726783156020576256) (-228243316419704562050730014942265/324518553658426726783156020576256) shortNegativeR022Q00Samples (by decide +kernel)

def shortNegativeR022Q01T := Grid.ofRats (103/100) (26/25)
def shortNegativeR022Q01P : PrimalThetaParameters := ⟨⟨⟨46073185999867160677672,47543594007330701004053,true⟩,⟨0,0,true⟩⟩, ⟨⟨1247974637392819012985830,1255392513317958706257161,true⟩,⟨0,0,true⟩⟩, ⟨(-1302003198850666195078913),(-1287167447000455528016837),true⟩, ⟨4945518486819703627715215,5064500333164022209599671,true⟩⟩
theorem shortNegativeR022Q01P_ok : shortNegativeR022Q01P.encloses (primalThetaParameters shortNegativeR022Q01T (Grid.ofRats (216774059366131/329853488332800) (218062549554931/329853488332800))) := by decide +kernel

def shortNegativeR022Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨534148239228362795808088,538359947378457973482537,true⟩,⟨2714729512193013623202397,2736134896638676073247814,true⟩,⟨⟨613096060278594265243915,620513936203733958563438,true⟩,⟨1036028159324826384397357,1043446035249966077722745,true⟩⟩⟩
  | 1 => ⟨⟨3974062464812326577532,4198665487943976474635,true⟩,⟨534148239228362795808088,538359947378457973482537,true⟩,⟨⟨(-1219291475637224725131502),(-1197037847861943084205313),true⟩,⟨31765929442862399904780,54019557218144040814930,true⟩⟩⟩
  | 2 => ⟨⟨1126824175216176091,1287781482049334501,true⟩,⟨3974062464812326577532,4198665487943976474635,true⟩,⟨⟨522974012098196546335384,560063391723620134866573,true⟩,⟨(-1099405056748065619998756),(-1062315677122642031460149),true⟩⟩⟩
  | 3 => ⟨⟨12142245908669,15567719775436,true⟩,⟨1126824175216176091,1287781482049334501,true⟩,⟨⟨663022909301735517057900,714948040777301053188936,true⟩,⟨967415837749766504267356,1019340969225332040402591,true⟩⟩⟩
  | 4 => ⟨⟨(-34354723669),34367106901,true⟩,⟨12142245908669,15567719775436,true⟩,⟨⟨(-1235461590122313463415259),(-1168700706796605979691585),true⟩,⟨95081809015270666068535,161842692340978149777433,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34354723669),34367106901,true⟩,⟨⟨422707360151545040348368,504303995327394471659971,true⟩,⟨(-1157339460597969701482403),(-1075742825422120270161812),true⟩⟩⟩
theorem shortNegativeR022Q01F_ok : ∀ n : Fin 6, (shortNegativeR022Q01F n).encloses (FactoredFrequency.build shortNegativeR022Q01T (Grid.ofRats (216774059366131/329853488332800) (218062549554931/329853488332800)) n) := by decide +kernel
def shortNegativeR022Q01L : ℕ → ℚ
  | 0 => (-690503/1000000)
  | 1 => (301029/1000000)
  | 2 => (122113/200000)
  | 3 => (112267/250000)
  | 4 => (-55133/1000000)
  | 5 => (-488871/500000)
  | 6 => (-138761/62500)
  | 7 => (-363411/100000)
  | 8 => (-961479/200000)
  | 9 => (-527201/100000)
  | 10 => (-907581/200000)
  | 11 => (-2742189/1000000)
  | _ => 0
def shortNegativeR022Q01U : ℕ → ℚ
  | 0 => (1651/15625)
  | 1 => (116417/100000)
  | 2 => (1511417/1000000)
  | 3 => (1351233/1000000)
  | 4 => (822627/1000000)
  | 5 => (9319/200000)
  | 6 => (-202763/200000)
  | 7 => (-1137487/500000)
  | 8 => (-1703903/500000)
  | 9 => (-3700347/1000000)
  | 10 => (-348611/125000)
  | 11 => (-1183861/1000000)
  | _ => 0
private theorem shortNegativeR022Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR022Q01P shortNegativeR022Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR022Q01L (0:Fin 12)) (shortNegativeR022Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR022Q01P shortNegativeR022Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR022Q01L (1:Fin 12)) (shortNegativeR022Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR022Q01P shortNegativeR022Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR022Q01L (2:Fin 12)) (shortNegativeR022Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR022Q01P shortNegativeR022Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR022Q01L (3:Fin 12)) (shortNegativeR022Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR022Q01P shortNegativeR022Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR022Q01L (4:Fin 12)) (shortNegativeR022Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR022Q01P shortNegativeR022Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR022Q01L (5:Fin 12)) (shortNegativeR022Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR022Q01P shortNegativeR022Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR022Q01L (6:Fin 12)) (shortNegativeR022Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR022Q01P shortNegativeR022Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR022Q01L (7:Fin 12)) (shortNegativeR022Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR022Q01P shortNegativeR022Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR022Q01L (8:Fin 12)) (shortNegativeR022Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR022Q01P shortNegativeR022Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR022Q01L (9:Fin 12)) (shortNegativeR022Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR022Q01P shortNegativeR022Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR022Q01L (10:Fin 12)) (shortNegativeR022Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR022Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR022Q01P shortNegativeR022Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR022Q01L (11:Fin 12)) (shortNegativeR022Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR022Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR022Q01P shortNegativeR022Q01F (shortNegativeNodes12 k)).re (shortNegativeR022Q01L k) (shortNegativeR022Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR022Q01Point00
  · exact shortNegativeR022Q01Point01
  · exact shortNegativeR022Q01Point02
  · exact shortNegativeR022Q01Point03
  · exact shortNegativeR022Q01Point04
  · exact shortNegativeR022Q01Point05
  · exact shortNegativeR022Q01Point06
  · exact shortNegativeR022Q01Point07
  · exact shortNegativeR022Q01Point08
  · exact shortNegativeR022Q01Point09
  · exact shortNegativeR022Q01Point10
  · exact shortNegativeR022Q01Point11

theorem shortNegativeR022Q01Bound {t a : ℝ} (tl : ((103/100):ℝ)≤t) (tu : t≤((26/25):ℝ)) (al : ((216774059366131/329853488332800):ℝ)≤a) (au : a≤((218062549554931/329853488332800):ℝ)) : (((-652095729277753857853708323923001/324518553658426726783156020576256):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-228243316419704562050730014942265/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : shortNegativeR022Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (216774059366131/329853488332800) (218062549554931/329853488332800)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR022Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR022Q01F_ok n) ts asb
  exact factored_negative_12_samples 16770 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip016Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR022Q01L shortNegativeR022Q01U (-652095729277753857853708323923001/324518553658426726783156020576256) (-228243316419704562050730014942265/324518553658426726783156020576256) shortNegativeR022Q01Samples (by decide +kernel)

theorem short_original_negative_022 {t a : ℝ} (tb : RealMem negative_022.t t) (ab : RealMem negative_022.a a) : RealMem negative_022.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((103/100):ℝ) ((26/25):ℝ) := by simpa [negative_022,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((103/100):ℝ)<((26/25):ℝ)) tB
  have aB : a∈Icc ((215485569177331/329853488332800):ℝ) ((218062549554931/329853488332800):ℝ) := by simpa [negative_022,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((215485569177331/329853488332800):ℝ)<((218062549554931/329853488332800):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR022Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_022,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR022Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_022,RealMem] using v

def shortNegativeR023Q00T := Grid.ofRats (26/25) (21/20)
def shortNegativeR023Q00P : PrimalThetaParameters := ⟨⟨⟨44648254144483039692930,46073185999935880155091,true⟩,⟨0,0,true⟩⟩, ⟨⟨1248886090735059065535414,1256303966660198758806748,true⟩,⟨0,0,true⟩⟩, ⟨(-1300180292166186089979739),(-1285344540315975422917669),true⟩, ⟨4911794706833534150994181,5028507088296364804595613,true⟩⟩
theorem shortNegativeR023Q00P_ok : shortNegativeR023Q00P.encloses (primalThetaParameters shortNegativeR023Q00T (Grid.ofRats (1084661897216593/1649267441664000) (1091104348160593/1649267441664000))) := by decide +kernel

def shortNegativeR023Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨529969480196537604126299,534148239228431515304303,true⟩,⟨2736134896638607353671812,2757709060508225571832499,true⟩,⟨⟨612311989267280435094482,619729865192420128414265,true⟩,⟨1036492895599445377434487,1043910771524585070760222,true⟩⟩⟩
  | 1 => ⟨⟨3761474335080210893512,3974062464881046054477,true⟩,⟨529969480196537604126299,534148239228431515304303,true⟩,⟨⟨(-1219385400420615840643928),(-1197131772645334199717709),true⟩,⟨29033183625310215650961,51286811400591856561103,true⟩⟩⟩
  | 2 => ⟨⟨985984661695952795,1126824243935652828,true⟩,⟨3761474335080210893512,3974062464881046054477,true⟩,⟨⟨527044655418514026087974,564134035043937614619296,true⟩,⟨(-1097356028138864725977159),(-1060266648513441137438502),true⟩⟩⟩
  | 3 => ⟨⟨9510885123635,12210965385406,true⟩,⟨985984661695952795,1126824243935652828,true⟩,⟨⟨657770728751171586979072,709695860226737123110840,true⟩,⟨971038146066468522349363,1022963277542034058485442,true⟩⟩⟩
  | 4 => ⟨⟨(-34356325585),34364753068,true⟩,⟨9510885123635,12210965385406,true⟩,⟨⟨(-1236305581859148317022923),(-1169544698533440833298773),true⟩,⟨86922278234195799261233,153683161559903282970483,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34356325585),34364753068,true⟩,⟨⟨431951127154671068959410,513547762330520500270756,true⟩,⟨(-1153457115165362779870700),(-1071860479989513348550550),true⟩⟩⟩
theorem shortNegativeR023Q00F_ok : ∀ n : Fin 6, (shortNegativeR023Q00F n).encloses (FactoredFrequency.build shortNegativeR023Q00T (Grid.ofRats (1084661897216593/1649267441664000) (1091104348160593/1649267441664000)) n) := by decide +kernel
def shortNegativeR023Q00L : ℕ → ℚ
  | 0 => (-399531/500000)
  | 1 => (36457/200000)
  | 2 => (250701/500000)
  | 3 => (88371/250000)
  | 4 => (-141001/1000000)
  | 5 => (-523631/500000)
  | 6 => (-141471/62500)
  | 7 => (-1819349/500000)
  | 8 => (-954129/200000)
  | 9 => (-2606507/500000)
  | 10 => (-4508871/1000000)
  | 11 => (-695813/250000)
  | _ => 0
def shortNegativeR023Q00U : ℕ → ℚ
  | 0 => (-4263/500000)
  | 1 => (207743/200000)
  | 2 => (698639/500000)
  | 3 => (1252443/1000000)
  | 4 => (738501/1000000)
  | 5 => (-22029/1000000)
  | 6 => (-530169/500000)
  | 7 => (-45801/20000)
  | 8 => (-3388477/1000000)
  | 9 => (-918781/250000)
  | 10 => (-2803613/1000000)
  | 11 => (-1263001/1000000)
  | _ => 0
private theorem shortNegativeR023Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR023Q00P shortNegativeR023Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR023Q00L (0:Fin 12)) (shortNegativeR023Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR023Q00P shortNegativeR023Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR023Q00L (1:Fin 12)) (shortNegativeR023Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR023Q00P shortNegativeR023Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR023Q00L (2:Fin 12)) (shortNegativeR023Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR023Q00P shortNegativeR023Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR023Q00L (3:Fin 12)) (shortNegativeR023Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR023Q00P shortNegativeR023Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR023Q00L (4:Fin 12)) (shortNegativeR023Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR023Q00P shortNegativeR023Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR023Q00L (5:Fin 12)) (shortNegativeR023Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR023Q00P shortNegativeR023Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR023Q00L (6:Fin 12)) (shortNegativeR023Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR023Q00P shortNegativeR023Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR023Q00L (7:Fin 12)) (shortNegativeR023Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR023Q00P shortNegativeR023Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR023Q00L (8:Fin 12)) (shortNegativeR023Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR023Q00P shortNegativeR023Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR023Q00L (9:Fin 12)) (shortNegativeR023Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR023Q00P shortNegativeR023Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR023Q00L (10:Fin 12)) (shortNegativeR023Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR023Q00P shortNegativeR023Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR023Q00L (11:Fin 12)) (shortNegativeR023Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR023Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR023Q00P shortNegativeR023Q00F (shortNegativeNodes12 k)).re (shortNegativeR023Q00L k) (shortNegativeR023Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR023Q00Point00
  · exact shortNegativeR023Q00Point01
  · exact shortNegativeR023Q00Point02
  · exact shortNegativeR023Q00Point03
  · exact shortNegativeR023Q00Point04
  · exact shortNegativeR023Q00Point05
  · exact shortNegativeR023Q00Point06
  · exact shortNegativeR023Q00Point07
  · exact shortNegativeR023Q00Point08
  · exact shortNegativeR023Q00Point09
  · exact shortNegativeR023Q00Point10
  · exact shortNegativeR023Q00Point11

theorem shortNegativeR023Q00Bound {t a : ℝ} (tl : ((26/25):ℝ)≤t) (tu : t≤((21/20):ℝ)) (al : ((1084661897216593/1649267441664000):ℝ)≤a) (au : a≤((1091104348160593/1649267441664000):ℝ)) : (((-2674154246917812218110221451643277/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-998696429159596363432948762003853/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR023Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1084661897216593/1649267441664000) (1091104348160593/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR023Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR023Q00F_ok n) ts asb
  exact factored_negative_12_samples 16770 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip016Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR023Q00L shortNegativeR023Q00U (-2674154246917812218110221451643277/1298074214633706907132624082305024) (-998696429159596363432948762003853/1298074214633706907132624082305024) shortNegativeR023Q00Samples (by decide +kernel)

def shortNegativeR023Q01T := Grid.ofRats (26/25) (21/20)
def shortNegativeR023Q01P : PrimalThetaParameters := ⟨⟨⟨44648254144483039692930,46073185999935880155091,true⟩,⟨0,0,true⟩⟩, ⟨⟨1256303966660130039326009,1263721842585269732597367,true⟩,⟨0,0,true⟩⟩, ⟨(-1285344540316044142398501),(-1270508788465833475336478),true⟩, ⟨4884580758396207948439142,5000147702585788574536978,true⟩⟩
theorem shortNegativeR023Q01P_ok : shortNegativeR023Q01P.encloses (primalThetaParameters shortNegativeR023Q01T (Grid.ofRats (1091104348160593/1649267441664000) (1097546799104593/1649267441664000))) := by decide +kernel

def shortNegativeR023Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨529969480196537604126299,534148239228431515304303,true⟩,⟨2736134896638607353671812,2757709060508225571832499,true⟩,⟨⟨605917834384838043343618,613335710309977736663036,true⟩,⟨1040253147444838343748829,1047671023369978037074352,true⟩⟩⟩
  | 1 => ⟨⟨3761474335080210893512,3974062464881046054477,true⟩,⟨529969480196537604126299,534148239228431515304303,true⟩,⟨⟨(-1219919913647943176630977),(-1197666285872661535705362),true⟩,⟨6786290331969862280005,29039918107251503189230,true⟩⟩⟩
  | 2 => ⟨⟨985984661695952795,1126824243935652828,true⟩,⟨3761474335080210893512,3974062464881046054477,true⟩,⟨⟨559880236088936856641206,596969615714360445172573,true⟩,⟨(-1080112512623188273264947),(-1043023132997764684726936),true⟩⟩⟩
  | 3 => ⟨⟨9510885123635,12210965385406,true⟩,⟨985984661695952795,1126824243935652828,true⟩,⟨⟨614330667781302252904468,666255799256867789036908,true⟩,⟨999476955853118942958765,1051402087328684479096513,true⟩⟩⟩
  | 4 => ⟨⟨(-34356325585),34364753068,true⟩,⟨9510885123635,12210965385406,true⟩,⟨⟨(-1241111957427210907001714),(-1174351074101503423279531),true⟩,⟨20343139383379750152205,87104022709087233858504,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34356325585),34364753068,true⟩,⟨⟨505916778620612659161238,587513413796462090472889,true⟩,⟨(-1119039589710538579192354),(-1037442954534689147873397),true⟩⟩⟩
theorem shortNegativeR023Q01F_ok : ∀ n : Fin 6, (shortNegativeR023Q01F n).encloses (FactoredFrequency.build shortNegativeR023Q01T (Grid.ofRats (1091104348160593/1649267441664000) (1097546799104593/1649267441664000)) n) := by decide +kernel
def shortNegativeR023Q01L : ℕ → ℚ
  | 0 => (-854527/1000000)
  | 1 => (136419/1000000)
  | 2 => (235643/500000)
  | 3 => (67899/200000)
  | 4 => (-139271/1000000)
  | 5 => (-1028227/1000000)
  | 6 => (-556761/250000)
  | 7 => (-3589139/1000000)
  | 8 => (-2360767/500000)
  | 9 => (-1296739/250000)
  | 10 => (-4505489/1000000)
  | 11 => (-1407509/500000)
  | _ => 0
def shortNegativeR023Q01U : ℕ → ℚ
  | 0 => (-72081/1000000)
  | 1 => (983537/1000000)
  | 2 => (679937/500000)
  | 3 => (616537/500000)
  | 4 => (736219/1000000)
  | 5 => (-8143/1000000)
  | 6 => (-128841/125000)
  | 7 => (-1124409/500000)
  | 8 => (-837003/250000)
  | 9 => (-3668799/1000000)
  | 10 => (-2837309/1000000)
  | 11 => (-132857/100000)
  | _ => 0
private theorem shortNegativeR023Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR023Q01P shortNegativeR023Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR023Q01L (0:Fin 12)) (shortNegativeR023Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR023Q01P shortNegativeR023Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR023Q01L (1:Fin 12)) (shortNegativeR023Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR023Q01P shortNegativeR023Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR023Q01L (2:Fin 12)) (shortNegativeR023Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR023Q01P shortNegativeR023Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR023Q01L (3:Fin 12)) (shortNegativeR023Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR023Q01P shortNegativeR023Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR023Q01L (4:Fin 12)) (shortNegativeR023Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR023Q01P shortNegativeR023Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR023Q01L (5:Fin 12)) (shortNegativeR023Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR023Q01P shortNegativeR023Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR023Q01L (6:Fin 12)) (shortNegativeR023Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR023Q01P shortNegativeR023Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR023Q01L (7:Fin 12)) (shortNegativeR023Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR023Q01P shortNegativeR023Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR023Q01L (8:Fin 12)) (shortNegativeR023Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR023Q01P shortNegativeR023Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR023Q01L (9:Fin 12)) (shortNegativeR023Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR023Q01P shortNegativeR023Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR023Q01L (10:Fin 12)) (shortNegativeR023Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR023Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR023Q01P shortNegativeR023Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR023Q01L (11:Fin 12)) (shortNegativeR023Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR023Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR023Q01P shortNegativeR023Q01F (shortNegativeNodes12 k)).re (shortNegativeR023Q01L k) (shortNegativeR023Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR023Q01Point00
  · exact shortNegativeR023Q01Point01
  · exact shortNegativeR023Q01Point02
  · exact shortNegativeR023Q01Point03
  · exact shortNegativeR023Q01Point04
  · exact shortNegativeR023Q01Point05
  · exact shortNegativeR023Q01Point06
  · exact shortNegativeR023Q01Point07
  · exact shortNegativeR023Q01Point08
  · exact shortNegativeR023Q01Point09
  · exact shortNegativeR023Q01Point10
  · exact shortNegativeR023Q01Point11

theorem shortNegativeR023Q01Bound {t a : ℝ} (tl : ((26/25):ℝ)≤t) (tu : t≤((21/20):ℝ)) (al : ((1091104348160593/1649267441664000):ℝ)≤a) (au : a≤((1097546799104593/1649267441664000):ℝ)) : (((-2674154246917812218110221451643277/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-998696429159596363432948762003853/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR023Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1091104348160593/1649267441664000) (1097546799104593/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR023Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR023Q01F_ok n) ts asb
  exact factored_negative_12_samples 16770 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip016Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR023Q01L shortNegativeR023Q01U (-2674154246917812218110221451643277/1298074214633706907132624082305024) (-998696429159596363432948762003853/1298074214633706907132624082305024) shortNegativeR023Q01Samples (by decide +kernel)

theorem short_original_negative_023 {t a : ℝ} (tb : RealMem negative_023.t t) (ab : RealMem negative_023.a a) : RealMem negative_023.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((26/25):ℝ) ((21/20):ℝ) := by simpa [negative_023,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((26/25):ℝ)<((21/20):ℝ)) tB
  have aB : a∈Icc ((1084661897216593/1649267441664000):ℝ) ((1097546799104593/1649267441664000):ℝ) := by simpa [negative_023,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((1084661897216593/1649267441664000):ℝ)<((1097546799104593/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR023Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_023,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR023Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_023,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_020
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_021
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_022
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_023
