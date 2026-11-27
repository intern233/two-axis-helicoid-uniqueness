import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip048

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR052Q00T := Grid.ofRats (133/100) (67/50)
def shortNegativeR052Q00P : PrimalThetaParameters := ⟨⟨⟨17952930059193171290920,18525890915829174000671,true⟩,⟨0,0,true⟩⟩, ⟨⟨1591361945115249967158981,1601252446348746651694944,true⟩,⟨0,0,true⟩⟩, ⟨(-615228583405804286730425),(-595447580938879637143473),true⟩, ⟨3514346109426845364783546,3591241704391934560215785,true⟩⟩
theorem shortNegativeR052Q00P_ok : shortNegativeR052Q00P.encloses (primalThetaParameters shortNegativeR052Q00T (Grid.ofRats (460701121143631/549755813888000) (1390693298022893/1649267441664000))) := by decide +kernel

def shortNegativeR052Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨422020526128480821163807,425348117907081845678235,true⟩,⟨3436012940464625129749276,3463105576257814007616406,true⟩,⟨⟨294571746686331624415275,304462247919828309000091,true⟩,⟨1166289655649902210414524,1176180156883398895011347,true⟩⟩⟩
  | 1 => ⟨⟨763725169137542489216,806888804227754958222,true⟩,⟨422020526128480821163807,425348117907081845678235,true⟩,⟨⟨(-839846493279321385768348),(-810174989578968771032891),true⟩,⟨(-898497968909067673185848),(-868826465208715058449574),true⟩⟩⟩
  | 2 => ⟨⟨20524642011849671,23456485886557831,true⟩,⟨763725169137542489216,806888804227754958222,true⟩,⟨⟨1123213779970518496383793,1172666286137727041232762,true⟩,⟨354398156368758004752766,403850662535966549591162,true⟩⟩⟩
  | 3 => ⟨⟨(-26168468800),44809115071,true⟩,⟨20524642011849671,23456485886557831,true⟩,⟨⟨(-1223632967730115009281326),(-1154399459096050534291844),true⟩,⟨183882860263216674914011,253116368897281149890135,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738320),34359738440,true⟩,⟨(-26168468800),44809115071,true⟩,⟨⟨893646614042231010664320,982661125143151415760278,true⟩,⟨(-806982798960976843924357),(-717968287860056438830814),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738320),34359738440,true⟩,⟨⟨(-511344857431947063179223),(-402549343864170727932606),true⟩,⟨1064843497164622993968150,1173639010732399329223883,true⟩⟩⟩
theorem shortNegativeR052Q00F_ok : ∀ n : Fin 6, (shortNegativeR052Q00F n).encloses (FactoredFrequency.build shortNegativeR052Q00T (Grid.ofRats (460701121143631/549755813888000) (1390693298022893/1649267441664000)) n) := by decide +kernel
def shortNegativeR052Q00L : ℕ → ℚ
  | 0 => (-583119/200000)
  | 1 => (-2576993/1000000)
  | 2 => (-1119479/500000)
  | 3 => (-24923/12500)
  | 4 => (-946601/500000)
  | 5 => (-397821/200000)
  | 6 => (-2234953/1000000)
  | 7 => (-2585561/1000000)
  | 8 => (-2961077/1000000)
  | 9 => (-3291841/1000000)
  | 10 => (-171111/50000)
  | 11 => (-412443/125000)
  | _ => 0
def shortNegativeR052Q00U : ℕ → ℚ
  | 0 => (-2388427/1000000)
  | 1 => (-991713/500000)
  | 2 => (-1593459/1000000)
  | 3 => (-1311503/1000000)
  | 4 => (-1187719/1000000)
  | 5 => (-1205599/1000000)
  | 6 => (-692451/500000)
  | 7 => (-846339/500000)
  | 8 => (-2064797/1000000)
  | 9 => (-1187667/500000)
  | 10 => (-2560539/1000000)
  | 11 => (-102047/40000)
  | _ => 0
private theorem shortNegativeR052Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR052Q00P shortNegativeR052Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR052Q00L (0:Fin 12)) (shortNegativeR052Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR052Q00P shortNegativeR052Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR052Q00L (1:Fin 12)) (shortNegativeR052Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR052Q00P shortNegativeR052Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR052Q00L (2:Fin 12)) (shortNegativeR052Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR052Q00P shortNegativeR052Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR052Q00L (3:Fin 12)) (shortNegativeR052Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR052Q00P shortNegativeR052Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR052Q00L (4:Fin 12)) (shortNegativeR052Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR052Q00P shortNegativeR052Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR052Q00L (5:Fin 12)) (shortNegativeR052Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR052Q00P shortNegativeR052Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR052Q00L (6:Fin 12)) (shortNegativeR052Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR052Q00P shortNegativeR052Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR052Q00L (7:Fin 12)) (shortNegativeR052Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR052Q00P shortNegativeR052Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR052Q00L (8:Fin 12)) (shortNegativeR052Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR052Q00P shortNegativeR052Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR052Q00L (9:Fin 12)) (shortNegativeR052Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR052Q00P shortNegativeR052Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR052Q00L (10:Fin 12)) (shortNegativeR052Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR052Q00P shortNegativeR052Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR052Q00L (11:Fin 12)) (shortNegativeR052Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR052Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR052Q00P shortNegativeR052Q00F (shortNegativeNodes12 k)).re (shortNegativeR052Q00L k) (shortNegativeR052Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR052Q00Point00
  · exact shortNegativeR052Q00Point01
  · exact shortNegativeR052Q00Point02
  · exact shortNegativeR052Q00Point03
  · exact shortNegativeR052Q00Point04
  · exact shortNegativeR052Q00Point05
  · exact shortNegativeR052Q00Point06
  · exact shortNegativeR052Q00Point07
  · exact shortNegativeR052Q00Point08
  · exact shortNegativeR052Q00Point09
  · exact shortNegativeR052Q00Point10
  · exact shortNegativeR052Q00Point11

theorem shortNegativeR052Q00Bound {t a : ℝ} (tl : ((133/100):ℝ)≤t) (tu : t≤((67/50):ℝ)) (al : ((460701121143631/549755813888000):ℝ)≤a) (au : a≤((1390693298022893/1649267441664000):ℝ)) : (((-862645709012708184114314042402941/324518553658426726783156020576256):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-574689052829920379644487797827709/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : shortNegativeR052Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (460701121143631/549755813888000) (1390693298022893/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR052Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR052Q00F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR052Q00L shortNegativeR052Q00U (-862645709012708184114314042402941/324518553658426726783156020576256) (-574689052829920379644487797827709/324518553658426726783156020576256) shortNegativeR052Q00Samples (by decide +kernel)

def shortNegativeR052Q01T := Grid.ofRats (133/100) (67/50)
def shortNegativeR052Q01P : PrimalThetaParameters := ⟨⟨⟨17952930059193171290920,18525890915829174000671,true⟩,⟨0,0,true⟩⟩, ⟨⟨1601252446348677932213107,1611142947582174616749102,true⟩,⟨0,0,true⟩⟩, ⟨(-595447580938948356622109),(-575666578472023707035220),true⟩, ⟨3501622571153417738822827,3578142442967397000771436,true⟩⟩
theorem shortNegativeR052Q01P_ok : shortNegativeR052Q01P.encloses (primalThetaParameters shortNegativeR052Q01T (Grid.ofRats (1390693298022893/1649267441664000) (1399283232614893/1649267441664000))) := by decide +kernel

def shortNegativeR052Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨422020526128480821163807,425348117907081845678235,true⟩,⟨3436012940464625129749276,3463105576257814007616406,true⟩,⟨⟨284979686748588419822616,294870187982085104407663,true⟩,⟨1168700849374474937696057,1178591350607971622293287,true⟩⟩⟩
  | 1 => ⟨⟨763725169137542489216,806888804227754958222,true⟩,⟨422020526128480821163807,425348117907081845678235,true⟩,⟨⟨(-817911859062666658613553),(-788240355362314043877764),true⟩,⟨(-918478603509688756505785),(-888807099809336141768608),true⟩⟩⟩
  | 2 => ⟨⟨20524642011849671,23456485886557831,true⟩,⟨763725169137542489216,806888804227754958222,true⟩,⟨⟨1106749285264873518248026,1156201791432082063098606,true⟩,⟨401025721016252700535403,450478227183461245376267,true⟩⟩⟩
  | 3 => ⟨⟨(-26168468800),44809115071,true⟩,⟨20524642011849671,23456485886557831,true⟩,⟨⟨(-1234190027434726559938384),(-1164956518800662084949797),true⟩,⟨115468553933324039732312,184702062567388514706454,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738320),34359738440,true⟩,⟨(-26168468800),44809115071,true⟩,⟨⟨947195826096929135216080,1036210337197849540309548,true⟩,⟨(-735901958438741199428235),(-646887447337820794338897),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738320),34359738440,true⟩,⟨⟨(-610084314410329408122876),(-501288800842553072874060),true⟩,⟨1019247476523734130326832,1128042990091510465582775,true⟩⟩⟩
theorem shortNegativeR052Q01F_ok : ∀ n : Fin 6, (shortNegativeR052Q01F n).encloses (FactoredFrequency.build shortNegativeR052Q01T (Grid.ofRats (1390693298022893/1649267441664000) (1399283232614893/1649267441664000)) n) := by decide +kernel
def shortNegativeR052Q01L : ℕ → ℚ
  | 0 => (-2920617/1000000)
  | 1 => (-2589363/1000000)
  | 2 => (-2252759/1000000)
  | 3 => (-1001851/500000)
  | 4 => (-236929/125000)
  | 5 => (-990681/500000)
  | 6 => (-221693/100000)
  | 7 => (-2558913/1000000)
  | 8 => (-585989/200000)
  | 9 => (-407773/125000)
  | 10 => (-425107/125000)
  | 11 => (-3291301/1000000)
  | _ => 0
def shortNegativeR052Q01U : ℕ → ℚ
  | 0 => (-600041/250000)
  | 1 => (-2002729/1000000)
  | 2 => (-1613991/1000000)
  | 3 => (-331949/250000)
  | 4 => (-1196259/1000000)
  | 5 => (-602531/500000)
  | 6 => (-55013/40000)
  | 7 => (-837893/500000)
  | 8 => (-2044217/1000000)
  | 9 => (-294593/125000)
  | 10 => (-2549931/1000000)
  | 11 => (-510391/200000)
  | _ => 0
private theorem shortNegativeR052Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR052Q01P shortNegativeR052Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR052Q01L (0:Fin 12)) (shortNegativeR052Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR052Q01P shortNegativeR052Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR052Q01L (1:Fin 12)) (shortNegativeR052Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR052Q01P shortNegativeR052Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR052Q01L (2:Fin 12)) (shortNegativeR052Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR052Q01P shortNegativeR052Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR052Q01L (3:Fin 12)) (shortNegativeR052Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR052Q01P shortNegativeR052Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR052Q01L (4:Fin 12)) (shortNegativeR052Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR052Q01P shortNegativeR052Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR052Q01L (5:Fin 12)) (shortNegativeR052Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR052Q01P shortNegativeR052Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR052Q01L (6:Fin 12)) (shortNegativeR052Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR052Q01P shortNegativeR052Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR052Q01L (7:Fin 12)) (shortNegativeR052Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR052Q01P shortNegativeR052Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR052Q01L (8:Fin 12)) (shortNegativeR052Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR052Q01P shortNegativeR052Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR052Q01L (9:Fin 12)) (shortNegativeR052Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR052Q01P shortNegativeR052Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR052Q01L (10:Fin 12)) (shortNegativeR052Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR052Q01P shortNegativeR052Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR052Q01L (11:Fin 12)) (shortNegativeR052Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR052Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR052Q01P shortNegativeR052Q01F (shortNegativeNodes12 k)).re (shortNegativeR052Q01L k) (shortNegativeR052Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR052Q01Point00
  · exact shortNegativeR052Q01Point01
  · exact shortNegativeR052Q01Point02
  · exact shortNegativeR052Q01Point03
  · exact shortNegativeR052Q01Point04
  · exact shortNegativeR052Q01Point05
  · exact shortNegativeR052Q01Point06
  · exact shortNegativeR052Q01Point07
  · exact shortNegativeR052Q01Point08
  · exact shortNegativeR052Q01Point09
  · exact shortNegativeR052Q01Point10
  · exact shortNegativeR052Q01Point11

theorem shortNegativeR052Q01Bound {t a : ℝ} (tl : ((133/100):ℝ)≤t) (tu : t≤((67/50):ℝ)) (al : ((1390693298022893/1649267441664000):ℝ)≤a) (au : a≤((1399283232614893/1649267441664000):ℝ)) : (((-862645709012708184114314042402941/324518553658426726783156020576256):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-574689052829920379644487797827709/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : shortNegativeR052Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1390693298022893/1649267441664000) (1399283232614893/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR052Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR052Q01F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR052Q01L shortNegativeR052Q01U (-862645709012708184114314042402941/324518553658426726783156020576256) (-574689052829920379644487797827709/324518553658426726783156020576256) shortNegativeR052Q01Samples (by decide +kernel)

def shortNegativeR052Q02T := Grid.ofRats (133/100) (67/50)
def shortNegativeR052Q02P : PrimalThetaParameters := ⟨⟨⟨17952930059193171290920,18525890915829174000671,true⟩,⟨0,0,true⟩⟩, ⟨⟨1611142947582105897267234,1621033448815602581803262,true⟩,⟨0,0,true⟩⟩, ⟨(-575666578472092426513793),(-555885576005167776926964),true⟩, ⟨3489389457780239016174521,3565547298990139134399673,true⟩⟩
theorem shortNegativeR052Q02P_ok : shortNegativeR052Q02P.encloses (primalThetaParameters shortNegativeR052Q02T (Grid.ofRats (1399283232614893/1649267441664000) (469291055735631/549755813888000))) := by decide +kernel

def shortNegativeR052Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨422020526128480821163807,425348117907081845678235,true⟩,⟨3436012940464625129749276,3463105576257814007616406,true⟩,⟨⟨275368221507042518697179,285258722740539203282047,true⟩,⟨1171033488424399306840758,1180923989657895991437960,true⟩⟩⟩
  | 1 => ⟨⟨763725169137542489216,806888804227754958222,true⟩,⟨422020526128480821163807,425348117907081845678235,true⟩,⟨⟨(-795493481827976936752262),(-765821978127624322016405),true⟩,⟨(-937914917445852742874167),(-908243413745500128136338),true⟩⟩⟩
  | 2 => ⟨⟨20524642011849671,23456485886557831,true⟩,⟨763725169137542489216,806888804227754958222,true⟩,⟨⟨1088391741301801144559159,1137844247469009689410979,true⟩,⟨446940968489313038133895,496393474656521582976887,true⟩⟩⟩
  | 3 => ⟨⟨(-26168468800),44809115071,true⟩,⟨20524642011849671,23456485886557831,true⟩,⟨⟨(-1240813928547171376102951),(-1171580419913106901116969),true⟩,⟨46562148176967303623297,115795656811031778593797,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738320),34359738440,true⟩,⟨(-26168468800),44809115071,true⟩,⟨⟨995370913228427229626697,1084385424329347634718334,true⟩,⟨(-661074390117305746718008),(-572059879016385341632201),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738320),34359738440,true⟩,⟨⟨(-704326392969624194082172),(-595530879401847858831563),true⟩,⟨964962044854695232866750,1073757558422471568122442,true⟩⟩⟩
theorem shortNegativeR052Q02F_ok : ∀ n : Fin 6, (shortNegativeR052Q02F n).encloses (FactoredFrequency.build shortNegativeR052Q02T (Grid.ofRats (1399283232614893/1649267441664000) (469291055735631/549755813888000)) n) := by decide +kernel
def shortNegativeR052Q02L : ℕ → ℚ
  | 0 => (-117017/40000)
  | 1 => (-260163/100000)
  | 2 => (-35416/15625)
  | 3 => (-2013783/1000000)
  | 4 => (-1897997/1000000)
  | 5 => (-246753/125000)
  | 6 => (-2199341/1000000)
  | 7 => (-39573/15625)
  | 8 => (-1449551/500000)
  | 9 => (-808151/250000)
  | 10 => (-3379733/1000000)
  | 11 => (-656557/200000)
  | _ => 0
def shortNegativeR052Q02U : ℕ → ℚ
  | 0 => (-1205807/500000)
  | 1 => (-1010957/500000)
  | 2 => (-13077/8000)
  | 3 => (-268877/200000)
  | 4 => (-120523/100000)
  | 5 => (-1205041/1000000)
  | 6 => (-683149/500000)
  | 7 => (-1659409/1000000)
  | 8 => (-2024031/1000000)
  | 9 => (-46767/20000)
  | 10 => (-634731/250000)
  | 11 => (-2552511/1000000)
  | _ => 0
private theorem shortNegativeR052Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR052Q02P shortNegativeR052Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR052Q02L (0:Fin 12)) (shortNegativeR052Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR052Q02P shortNegativeR052Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR052Q02L (1:Fin 12)) (shortNegativeR052Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR052Q02P shortNegativeR052Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR052Q02L (2:Fin 12)) (shortNegativeR052Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR052Q02P shortNegativeR052Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR052Q02L (3:Fin 12)) (shortNegativeR052Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR052Q02P shortNegativeR052Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR052Q02L (4:Fin 12)) (shortNegativeR052Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR052Q02P shortNegativeR052Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR052Q02L (5:Fin 12)) (shortNegativeR052Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR052Q02P shortNegativeR052Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR052Q02L (6:Fin 12)) (shortNegativeR052Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR052Q02P shortNegativeR052Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR052Q02L (7:Fin 12)) (shortNegativeR052Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR052Q02P shortNegativeR052Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR052Q02L (8:Fin 12)) (shortNegativeR052Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR052Q02P shortNegativeR052Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR052Q02L (9:Fin 12)) (shortNegativeR052Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR052Q02P shortNegativeR052Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR052Q02L (10:Fin 12)) (shortNegativeR052Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR052Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR052Q02P shortNegativeR052Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR052Q02L (11:Fin 12)) (shortNegativeR052Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR052Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR052Q02P shortNegativeR052Q02F (shortNegativeNodes12 k)).re (shortNegativeR052Q02L k) (shortNegativeR052Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR052Q02Point00
  · exact shortNegativeR052Q02Point01
  · exact shortNegativeR052Q02Point02
  · exact shortNegativeR052Q02Point03
  · exact shortNegativeR052Q02Point04
  · exact shortNegativeR052Q02Point05
  · exact shortNegativeR052Q02Point06
  · exact shortNegativeR052Q02Point07
  · exact shortNegativeR052Q02Point08
  · exact shortNegativeR052Q02Point09
  · exact shortNegativeR052Q02Point10
  · exact shortNegativeR052Q02Point11

theorem shortNegativeR052Q02Bound {t a : ℝ} (tl : ((133/100):ℝ)≤t) (tu : t≤((67/50):ℝ)) (al : ((1399283232614893/1649267441664000):ℝ)≤a) (au : a≤((469291055735631/549755813888000):ℝ)) : (((-862645709012708184114314042402941/324518553658426726783156020576256):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-574689052829920379644487797827709/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : shortNegativeR052Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1399283232614893/1649267441664000) (469291055735631/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR052Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR052Q02F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR052Q02L shortNegativeR052Q02U (-862645709012708184114314042402941/324518553658426726783156020576256) (-574689052829920379644487797827709/324518553658426726783156020576256) shortNegativeR052Q02Samples (by decide +kernel)

theorem short_original_negative_052 {t a : ℝ} (tb : RealMem negative_052.t t) (ab : RealMem negative_052.a a) : RealMem negative_052.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((133/100):ℝ) ((67/50):ℝ) := by simpa [negative_052,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((133/100):ℝ)<((67/50):ℝ)) tB
  have aB : a∈Icc ((460701121143631/549755813888000):ℝ) ((469291055735631/549755813888000):ℝ) := by simpa [negative_052,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((460701121143631/549755813888000):ℝ)<((469291055735631/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR052Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_052,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR052Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_052,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR052Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_052,RealMem] using v

def shortNegativeR053Q00T := Grid.ofRats (67/50) (27/20)
def shortNegativeR053Q00P : PrimalThetaParameters := ⟨⟨⟨17397689491741831531390,17952930059261890767979,true⟩,⟨0,0,true⟩⟩, ⟨⟨1611734125822180251958321,1621624627055676936494349,true⟩,⟨0,0,true⟩⟩, ⟨(-574484221991943717131614),(-554703219525019067544792),true⟩, ⟨3477014813616764665444887,3552382029261755085562026,true⟩⟩
theorem shortNegativeR053Q00P_ok : shortNegativeR053Q00P.encloses (primalThetaParameters shortNegativeR053Q00T (Grid.ofRats (1399796672964841/1649267441664000) (469462202518947/549755813888000))) := by decide +kernel

def shortNegativeR053Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨418718966831528640527536,422020526128549540656351,true⟩,⟨3463105576257745288010151,3490411834911772225947848,true⟩,⟨⟨274793121264644791649162,284683622498141476234444,true⟩,⟨1171170424233327923543549,1181060925466824608141201,true⟩⟩⟩
  | 1 => ⟨⟨722870525613497649001,763725169206261965998,true⟩,⟨418718966831528640527536,422020526128549540656351,true⟩,⟨⟨(-794138454160458178769230),(-764466950460105564033326),true⟩,⟨(-939059174785775312185901),(-909387671085422697447994),true⟩⟩⟩
  | 2 => ⟨⟨17959303593692677,20524710731326408,true⟩,⟨722870525613497649001,763725169206261965998,true⟩,⟨⟨1087235162456817994667110,1136687668624026539519452,true⟩,⟨449661191607170902064052,499113697774379446907624,true⟩⟩⟩
  | 3 => ⟨⟨(-27938599668),42551007937,true⟩,⟨17959303593692677,20524710731326408,true⟩,⟨⟨(-1241084742960569185615708),(-1171851234326504710629455),true⟩,⟨42432773321502444064663,111666281955566919035374,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738335),34359738417,true⟩,⟨(-27938599668),42551007937,true⟩,⟨⟨998074407418705335793454,1087088918519625740885189,true⟩,⟨(-656491825103771928716222),(-567477314002851523630418),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738335),34359738417,true⟩,⟨⟨(-709800225438426672287628),(-601004711870650337036865),true⟩,⟨961451268127018360069857,1070246781694794695325578,true⟩⟩⟩
theorem shortNegativeR053Q00F_ok : ∀ n : Fin 6, (shortNegativeR053Q00F n).encloses (FactoredFrequency.build shortNegativeR053Q00T (Grid.ofRats (1399796672964841/1649267441664000) (469462202518947/549755813888000)) n) := by decide +kernel
def shortNegativeR053Q00L : ℕ → ℚ
  | 0 => (-1461577/500000)
  | 1 => (-2611539/1000000)
  | 2 => (-1143883/500000)
  | 3 => (-1021251/500000)
  | 4 => (-77191/40000)
  | 5 => (-1001897/500000)
  | 6 => (-2222777/1000000)
  | 7 => (-1273009/500000)
  | 8 => (-1450153/500000)
  | 9 => (-1611087/500000)
  | 10 => (-52553/15625)
  | 11 => (-3269283/1000000)
  | _ => 0
def shortNegativeR053Q00U : ℕ → ℚ
  | 0 => (-482447/200000)
  | 1 => (-406889/200000)
  | 2 => (-828911/500000)
  | 3 => (-687241/500000)
  | 4 => (-1237779/1000000)
  | 5 => (-247259/200000)
  | 6 => (-1392421/1000000)
  | 7 => (-419269/250000)
  | 8 => (-1015589/500000)
  | 9 => (-1168081/500000)
  | 10 => (-632859/250000)
  | 11 => (-2546213/1000000)
  | _ => 0
private theorem shortNegativeR053Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR053Q00P shortNegativeR053Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR053Q00L (0:Fin 12)) (shortNegativeR053Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR053Q00P shortNegativeR053Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR053Q00L (1:Fin 12)) (shortNegativeR053Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR053Q00P shortNegativeR053Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR053Q00L (2:Fin 12)) (shortNegativeR053Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR053Q00P shortNegativeR053Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR053Q00L (3:Fin 12)) (shortNegativeR053Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR053Q00P shortNegativeR053Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR053Q00L (4:Fin 12)) (shortNegativeR053Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR053Q00P shortNegativeR053Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR053Q00L (5:Fin 12)) (shortNegativeR053Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR053Q00P shortNegativeR053Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR053Q00L (6:Fin 12)) (shortNegativeR053Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR053Q00P shortNegativeR053Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR053Q00L (7:Fin 12)) (shortNegativeR053Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR053Q00P shortNegativeR053Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR053Q00L (8:Fin 12)) (shortNegativeR053Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR053Q00P shortNegativeR053Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR053Q00L (9:Fin 12)) (shortNegativeR053Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR053Q00P shortNegativeR053Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR053Q00L (10:Fin 12)) (shortNegativeR053Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR053Q00P shortNegativeR053Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR053Q00L (11:Fin 12)) (shortNegativeR053Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR053Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR053Q00P shortNegativeR053Q00F (shortNegativeNodes12 k)).re (shortNegativeR053Q00L k) (shortNegativeR053Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR053Q00Point00
  · exact shortNegativeR053Q00Point01
  · exact shortNegativeR053Q00Point02
  · exact shortNegativeR053Q00Point03
  · exact shortNegativeR053Q00Point04
  · exact shortNegativeR053Q00Point05
  · exact shortNegativeR053Q00Point06
  · exact shortNegativeR053Q00Point07
  · exact shortNegativeR053Q00Point08
  · exact shortNegativeR053Q00Point09
  · exact shortNegativeR053Q00Point10
  · exact shortNegativeR053Q00Point11

theorem shortNegativeR053Q00Bound {t a : ℝ} (tl : ((67/50):ℝ)≤t) (tu : t≤((27/20):ℝ)) (al : ((1399796672964841/1649267441664000):ℝ)≤a) (au : a≤((469462202518947/549755813888000):ℝ)) : (((-855800411564727878072526955160293/324518553658426726783156020576256):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-584609645188274169527150161240805/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : shortNegativeR053Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1399796672964841/1649267441664000) (469462202518947/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR053Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR053Q00F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR053Q00L shortNegativeR053Q00U (-855800411564727878072526955160293/324518553658426726783156020576256) (-584609645188274169527150161240805/324518553658426726783156020576256) shortNegativeR053Q00Samples (by decide +kernel)

def shortNegativeR053Q01T := Grid.ofRats (67/50) (27/20)
def shortNegativeR053Q01P : PrimalThetaParameters := ⟨⟨⟨17397689491741831531390,17952930059261890767979,true⟩,⟨0,0,true⟩⟩, ⟨⟨1621624627055608217012448,1631515128289104901548509,true⟩,⟨0,0,true⟩⟩, ⟨(-554703219525087787023298),(-534922217058163137436536),true⟩, ⟨3465285031845283236608270,3540305558849515314905796,true⟩⟩
theorem shortNegativeR053Q01P_ok : shortNegativeR053Q01P.encloses (primalThetaParameters shortNegativeR053Q01T (Grid.ofRats (469462202518947/549755813888000) (1416976542148841/1649267441664000))) := by decide +kernel

def shortNegativeR053Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨418718966831528640527536,422020526128549540656351,true⟩,⟨3463105576257745288010151,3490411834911772225947848,true⟩,⟨⟨265161792990858125640943,275052294224354810226066,true⟩,⟨1173419642921947291949991,1183310144155443976547624,true⟩⟩⟩
  | 1 => ⟨⟨722870525613497649001,763725169206261965998,true⟩,⟨418718966831528640527536,422020526128549540656351,true⟩,⟨⟨(-771222164528034044316910),(-741550660827681429580893),true⟩,⟨(-957905861676176683269461),(-928234357975824068530867),true⟩⟩⟩
  | 2 => ⟨⟨17959303593692677,20524710731326408,true⟩,⟨722870525613497649001,763725169206261965998,true⟩,⟨⟨1066905007566551115380361,1116357513733759660233719,true⟩,⟨494737728441828756715500,544190234609037301560980,true⟩⟩⟩
  | 3 => ⟨⟨(-27938599668),42551007937,true⟩,⟨17959303593692677,20524710731326408,true⟩,⟨⟨(-1243516968734639416376998),(-1174283460100574941392184),true⟩,⟨(-26748532664949335825118),42484975969115139143534,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738335),34359738417,true⟩,⟨(-27938599668),42551007937,true⟩,⟨⟨1040269865025806877706876,1129284376126727282797232,true⟩,⟨(-578136561347251905073929),(-489122050246331499991170),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738335),34359738417,true⟩,⟨⟨(-798444517499572229346918),(-689649003931795894094768),true⟩,⟨898438039772580686303216,1007233553340357021558239,true⟩⟩⟩
theorem shortNegativeR053Q01F_ok : ∀ n : Fin 6, (shortNegativeR053Q01F n).encloses (FactoredFrequency.build shortNegativeR053Q01T (Grid.ofRats (469462202518947/549755813888000) (1416976542148841/1649267441664000)) n) := by decide +kernel
def shortNegativeR053Q01L : ℕ → ℚ
  | 0 => (-2927129/1000000)
  | 1 => (-655713/250000)
  | 2 => (-460169/200000)
  | 3 => (-205211/100000)
  | 4 => (-1932213/1000000)
  | 5 => (-1996657/1000000)
  | 6 => (-2205689/1000000)
  | 7 => (-315063/125000)
  | 8 => (-11481/4000)
  | 9 => (-798291/250000)
  | 10 => (-417799/125000)
  | 11 => (-326029/100000)
  | _ => 0
def shortNegativeR053Q01U : ℕ → ℚ
  | 0 => (-302847/125000)
  | 1 => (-1026349/500000)
  | 2 => (-83889/50000)
  | 3 => (-1390773/1000000)
  | 4 => (-1246831/1000000)
  | 5 => (-1236693/1000000)
  | 6 => (-173011/125000)
  | 7 => (-830783/500000)
  | 8 => (-125741/62500)
  | 9 => (-2318383/1000000)
  | 10 => (-504103/200000)
  | 11 => (-636577/250000)
  | _ => 0
private theorem shortNegativeR053Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR053Q01P shortNegativeR053Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR053Q01L (0:Fin 12)) (shortNegativeR053Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR053Q01P shortNegativeR053Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR053Q01L (1:Fin 12)) (shortNegativeR053Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR053Q01P shortNegativeR053Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR053Q01L (2:Fin 12)) (shortNegativeR053Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR053Q01P shortNegativeR053Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR053Q01L (3:Fin 12)) (shortNegativeR053Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR053Q01P shortNegativeR053Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR053Q01L (4:Fin 12)) (shortNegativeR053Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR053Q01P shortNegativeR053Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR053Q01L (5:Fin 12)) (shortNegativeR053Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR053Q01P shortNegativeR053Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR053Q01L (6:Fin 12)) (shortNegativeR053Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR053Q01P shortNegativeR053Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR053Q01L (7:Fin 12)) (shortNegativeR053Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR053Q01P shortNegativeR053Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR053Q01L (8:Fin 12)) (shortNegativeR053Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR053Q01P shortNegativeR053Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR053Q01L (9:Fin 12)) (shortNegativeR053Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR053Q01P shortNegativeR053Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR053Q01L (10:Fin 12)) (shortNegativeR053Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR053Q01P shortNegativeR053Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR053Q01L (11:Fin 12)) (shortNegativeR053Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR053Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR053Q01P shortNegativeR053Q01F (shortNegativeNodes12 k)).re (shortNegativeR053Q01L k) (shortNegativeR053Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR053Q01Point00
  · exact shortNegativeR053Q01Point01
  · exact shortNegativeR053Q01Point02
  · exact shortNegativeR053Q01Point03
  · exact shortNegativeR053Q01Point04
  · exact shortNegativeR053Q01Point05
  · exact shortNegativeR053Q01Point06
  · exact shortNegativeR053Q01Point07
  · exact shortNegativeR053Q01Point08
  · exact shortNegativeR053Q01Point09
  · exact shortNegativeR053Q01Point10
  · exact shortNegativeR053Q01Point11

theorem shortNegativeR053Q01Bound {t a : ℝ} (tl : ((67/50):ℝ)≤t) (tu : t≤((27/20):ℝ)) (al : ((469462202518947/549755813888000):ℝ)≤a) (au : a≤((1416976542148841/1649267441664000):ℝ)) : (((-855800411564727878072526955160293/324518553658426726783156020576256):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-584609645188274169527150161240805/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : shortNegativeR053Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (469462202518947/549755813888000) (1416976542148841/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR053Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR053Q01F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR053Q01L shortNegativeR053Q01U (-855800411564727878072526955160293/324518553658426726783156020576256) (-584609645188274169527150161240805/324518553658426726783156020576256) shortNegativeR053Q01Samples (by decide +kernel)

def shortNegativeR053Q02T := Grid.ofRats (67/50) (27/20)
def shortNegativeR053Q02P : PrimalThetaParameters := ⟨⟨⟨17397689491741831531390,17952930059261890767979,true⟩,⟨0,0,true⟩⟩, ⟨⟨1631515128289036182066576,1641405629522532866602667,true⟩,⟨0,0,true⟩⟩, ⟨(-534922217058231856914979),(-515141214591307207328283),true⟩, ⟨3454031418753491256810492,3528718397440019651599074,true⟩⟩
theorem shortNegativeR053Q02P_ok : shortNegativeR053Q02P.encloses (primalThetaParameters shortNegativeR053Q02T (Grid.ofRats (1416976542148841/1649267441664000) (1425566476740841/1649267441664000))) := by decide +kernel

def shortNegativeR053Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨418718966831528640527536,422020526128549540656351,true⟩,⟨3463105576257745288010151,3490411834911772225947848,true⟩,⟨⟨255512385867807627815525,265402887101304312400854,true⟩,⟨1175589991096849048518561,1185480492330345733116584,true⟩⟩⟩
  | 1 => ⟨⟨722870525613497649001,763725169206261965998,true⟩,⟨418718966831528640527536,422020526128549540656351,true⟩,⟨⟨(-747850256003722449856155),(-718178752303369835120081),true⟩,⟨(-976184478396081606113689),(-946512974695728991374462),true⟩⟩⟩
  | 2 => ⟨⟨17959303593692677,20524710731326408,true⟩,⟨722870525613497649001,763725169206261965998,true⟩,⟨⟨1044748466088753915860154,1094200972255962460715076,true⟩,⟨538945160403108309863103,588397666570316854711068,true⟩⟩⟩
  | 3 => ⟨⟨(-27938599668),42551007937,true⟩,⟨17959303593692677,20524710731326408,true⟩,⟨⟨(-1241985454758947558492974),(-1172751946124883083506720),true⟩,⟨(-95955636961758207082565),(-26722128327693732112080),true⟩⟩⟩
  | 4 => ⟨⟨(-34359738335),34359738417,true⟩,⟨(-27938599668),42551007937,true⟩,⟨⟨1076586821428574254446918,1165601332529494659534980,true⟩,⟨(-496889514147578134852826),(-407875003046657729773966),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738335),34359738417,true⟩,⟨⟨(-881066961814880759256880),(-772271448247104424003258),true⟩,⟨827713156188131270497505,936508669755907605751888,true⟩⟩⟩
theorem shortNegativeR053Q02F_ok : ∀ n : Fin 6, (shortNegativeR053Q02F n).encloses (FactoredFrequency.build shortNegativeR053Q02T (Grid.ofRats (1416976542148841/1649267441664000) (1425566476740841/1649267441664000)) n) := by decide +kernel
def shortNegativeR053Q02L : ℕ → ℚ
  | 0 => (-2930909/1000000)
  | 1 => (-2634071/1000000)
  | 2 => (-2313987/1000000)
  | 3 => (-2061931/1000000)
  | 4 => (-967489/500000)
  | 5 => (-397983/200000)
  | 6 => (-68407/31250)
  | 7 => (-499077/200000)
  | 8 => (-1420239/500000)
  | 9 => (-39553/12500)
  | 10 => (-830313/250000)
  | 11 => (-3251049/1000000)
  | _ => 0
def shortNegativeR053Q02U : ℕ → ℚ
  | 0 => (-1216521/500000)
  | 1 => (-1035417/500000)
  | 2 => (-848917/500000)
  | 3 => (-1407349/1000000)
  | 4 => (-628151/500000)
  | 5 => (-1237597/1000000)
  | 6 => (-1376293/1000000)
  | 7 => (-1646561/1000000)
  | 8 => (-996461/500000)
  | 9 => (-2300803/1000000)
  | 10 => (-2509573/1000000)
  | 11 => (-636549/250000)
  | _ => 0
private theorem shortNegativeR053Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR053Q02P shortNegativeR053Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR053Q02L (0:Fin 12)) (shortNegativeR053Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR053Q02P shortNegativeR053Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR053Q02L (1:Fin 12)) (shortNegativeR053Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR053Q02P shortNegativeR053Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR053Q02L (2:Fin 12)) (shortNegativeR053Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR053Q02P shortNegativeR053Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR053Q02L (3:Fin 12)) (shortNegativeR053Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR053Q02P shortNegativeR053Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR053Q02L (4:Fin 12)) (shortNegativeR053Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR053Q02P shortNegativeR053Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR053Q02L (5:Fin 12)) (shortNegativeR053Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR053Q02P shortNegativeR053Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR053Q02L (6:Fin 12)) (shortNegativeR053Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR053Q02P shortNegativeR053Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR053Q02L (7:Fin 12)) (shortNegativeR053Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR053Q02P shortNegativeR053Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR053Q02L (8:Fin 12)) (shortNegativeR053Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR053Q02P shortNegativeR053Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR053Q02L (9:Fin 12)) (shortNegativeR053Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR053Q02P shortNegativeR053Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR053Q02L (10:Fin 12)) (shortNegativeR053Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR053Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR053Q02P shortNegativeR053Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR053Q02L (11:Fin 12)) (shortNegativeR053Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR053Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR053Q02P shortNegativeR053Q02F (shortNegativeNodes12 k)).re (shortNegativeR053Q02L k) (shortNegativeR053Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR053Q02Point00
  · exact shortNegativeR053Q02Point01
  · exact shortNegativeR053Q02Point02
  · exact shortNegativeR053Q02Point03
  · exact shortNegativeR053Q02Point04
  · exact shortNegativeR053Q02Point05
  · exact shortNegativeR053Q02Point06
  · exact shortNegativeR053Q02Point07
  · exact shortNegativeR053Q02Point08
  · exact shortNegativeR053Q02Point09
  · exact shortNegativeR053Q02Point10
  · exact shortNegativeR053Q02Point11

theorem shortNegativeR053Q02Bound {t a : ℝ} (tl : ((67/50):ℝ)≤t) (tu : t≤((27/20):ℝ)) (al : ((1416976542148841/1649267441664000):ℝ)≤a) (au : a≤((1425566476740841/1649267441664000):ℝ)) : (((-855800411564727878072526955160293/324518553658426726783156020576256):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-584609645188274169527150161240805/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : shortNegativeR053Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1416976542148841/1649267441664000) (1425566476740841/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR053Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR053Q02F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR053Q02L shortNegativeR053Q02U (-855800411564727878072526955160293/324518553658426726783156020576256) (-584609645188274169527150161240805/324518553658426726783156020576256) shortNegativeR053Q02Samples (by decide +kernel)

theorem short_original_negative_053 {t a : ℝ} (tb : RealMem negative_053.t t) (ab : RealMem negative_053.a a) : RealMem negative_053.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((67/50):ℝ) ((27/20):ℝ) := by simpa [negative_053,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((67/50):ℝ)<((27/20):ℝ)) tB
  have aB : a∈Icc ((1399796672964841/1649267441664000):ℝ) ((1425566476740841/1649267441664000):ℝ) := by simpa [negative_053,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((1399796672964841/1649267441664000):ℝ)<((1425566476740841/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR053Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_053,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR053Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_053,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR053Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_053,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_052
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_053
