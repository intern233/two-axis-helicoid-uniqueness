import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip048

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR054Q00T := Grid.ofRats (27/20) (34/25)
def shortNegativeR054Q00P : PrimalThetaParameters := ⟨⟨⟨16859621167858901841325,17397689491810551008442,true⟩,⟨0,0,true⟩⟩, ⟨⟨1633755983142269246325100,1643646484375765930861198,true⟩,⟨0,0,true⟩⟩, ⟨(-530440507351765728397916),(-510659504884841078811234),true⟩, ⟨3440257356332936620108018,3514130860037368420104998,true⟩⟩
theorem shortNegativeR054Q00P_ok : shortNegativeR054Q00P.encloses (primalThetaParameters shortNegativeR054Q00T (Grid.ofRats (1418922732353477/1649267441664000) (1427512666945477/1649267441664000))) := by decide +kernel

def shortNegativeR054Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨415443236358333653116656,418718966831597360019923,true⟩,⟨3490411834911703506341341,3517933400822543156094584,true⟩,⟨⟨253323709366578282252042,263214210600074966837268,true⟩,⟨1176070744888830637444181,1185961246122327322042144,true⟩⟩⟩
  | 1 => ⟨⟨684201356609412083642,722870525682217125780,true⟩,⟨415443236358333653116656,418718966831597360019923,true⟩,⟨⟨(-742493106333567268223355),(-712821602633214653486861),true⟩,⟨(-980245722690096536399217),(-950574218989743921659439),true⟩⟩⟩
  | 2 => ⟨⟨15714601714720396,17959372313169414,true⟩,⟨684201356609412083642,722870525682217125780,true⟩,⟨⟨1039478526670020752244525,1088931032837229297099619,true⟩,⟨548832657648712195678870,598285163815920740527213,true⟩⟩⟩
  | 3 => ⟨⟨(-29326205792),40780877069,true⟩,⟨15714601714720396,17959372313169414,true⟩,⟨⟨(-1241087964954657269579172),(-1171854456320592794592487),true⟩,⟨(-111615814268997429148942),(-42382305634932954177802),true⟩⟩⟩
  | 4 => ⟨⟨(-34359738346),34359738402,true⟩,⟨(-29326205792),40780877069,true⟩,⟨⟨1083977262737395587719977,1172991773838315992807931,true⟩,⟨(-478124978107471228431786),(-389110467006550823353400),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738346),34359738402,true⟩,⟨⟨(-898879693173731835734499),(-790084179605955500481182),true⟩,⟨810675590650977005546027,919471104218753340799630,true⟩⟩⟩
theorem shortNegativeR054Q00F_ok : ∀ n : Fin 6, (shortNegativeR054Q00F n).encloses (FactoredFrequency.build shortNegativeR054Q00T (Grid.ofRats (1418922732353477/1649267441664000) (1427512666945477/1649267441664000)) n) := by decide +kernel
def shortNegativeR054Q00L : ℕ → ℚ
  | 0 => (-1463981/500000)
  | 1 => (-2643639/1000000)
  | 2 => (-2334777/1000000)
  | 3 => (-2089909/1000000)
  | 4 => (-1965293/1000000)
  | 5 => (-403451/200000)
  | 6 => (-441821/200000)
  | 7 => (-100191/40000)
  | 8 => (-1418841/500000)
  | 9 => (-3150331/1000000)
  | 10 => (-3302407/1000000)
  | 11 => (-647197/200000)
  | _ => 0
def shortNegativeR054Q00U : ℕ → ℚ
  | 0 => (-1216997/500000)
  | 1 => (-2084211/1000000)
  | 2 => (-1721979/1000000)
  | 3 => (-143807/100000)
  | 4 => (-1288797/1000000)
  | 5 => (-126797/100000)
  | 6 => (-350183/250000)
  | 7 => (-415499/250000)
  | 8 => (-62429/31250)
  | 9 => (-1148343/500000)
  | 10 => (-1250441/500000)
  | 11 => (-1269797/500000)
  | _ => 0
private theorem shortNegativeR054Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR054Q00P shortNegativeR054Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR054Q00L (0:Fin 12)) (shortNegativeR054Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR054Q00P shortNegativeR054Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR054Q00L (1:Fin 12)) (shortNegativeR054Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR054Q00P shortNegativeR054Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR054Q00L (2:Fin 12)) (shortNegativeR054Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR054Q00P shortNegativeR054Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR054Q00L (3:Fin 12)) (shortNegativeR054Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR054Q00P shortNegativeR054Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR054Q00L (4:Fin 12)) (shortNegativeR054Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR054Q00P shortNegativeR054Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR054Q00L (5:Fin 12)) (shortNegativeR054Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR054Q00P shortNegativeR054Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR054Q00L (6:Fin 12)) (shortNegativeR054Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR054Q00P shortNegativeR054Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR054Q00L (7:Fin 12)) (shortNegativeR054Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR054Q00P shortNegativeR054Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR054Q00L (8:Fin 12)) (shortNegativeR054Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR054Q00P shortNegativeR054Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR054Q00L (9:Fin 12)) (shortNegativeR054Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR054Q00P shortNegativeR054Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR054Q00L (10:Fin 12)) (shortNegativeR054Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR054Q00P shortNegativeR054Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR054Q00L (11:Fin 12)) (shortNegativeR054Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR054Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR054Q00P shortNegativeR054Q00F (shortNegativeNodes12 k)).re (shortNegativeR054Q00L k) (shortNegativeR054Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR054Q00Point00
  · exact shortNegativeR054Q00Point01
  · exact shortNegativeR054Q00Point02
  · exact shortNegativeR054Q00Point03
  · exact shortNegativeR054Q00Point04
  · exact shortNegativeR054Q00Point05
  · exact shortNegativeR054Q00Point06
  · exact shortNegativeR054Q00Point07
  · exact shortNegativeR054Q00Point08
  · exact shortNegativeR054Q00Point09
  · exact shortNegativeR054Q00Point10
  · exact shortNegativeR054Q00Point11

theorem shortNegativeR054Q00Bound {t a : ℝ} (tl : ((27/20):ℝ)≤t) (tu : t≤((34/25):ℝ)) (al : ((1418922732353477/1649267441664000):ℝ)≤a) (au : a≤((1427512666945477/1649267441664000):ℝ)) : (((-1712414599567556087977059535881623/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1173262034538827258726881074414999/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR054Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1418922732353477/1649267441664000) (1427512666945477/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR054Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR054Q00F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR054Q00L shortNegativeR054Q00U (-1712414599567556087977059535881623/649037107316853453566312041152512) (-1173262034538827258726881074414999/649037107316853453566312041152512) shortNegativeR054Q00Samples (by decide +kernel)

def shortNegativeR054Q01T := Grid.ofRats (27/20) (34/25)
def shortNegativeR054Q01P : PrimalThetaParameters := ⟨⟨⟨16859621167858901841325,17397689491810551008442,true⟩,⟨0,0,true⟩⟩, ⟨⟨1643646484375697211379227,1653536985609193895915356,true⟩,⟨0,0,true⟩⟩, ⟨(-510659504884909798289600),(-490878502417985148702981),true⟩, ⟨3429571392804716756256599,3503128247938210237852936,true⟩⟩
theorem shortNegativeR054Q01P_ok : shortNegativeR054Q01P.encloses (primalThetaParameters shortNegativeR054Q01T (Grid.ofRats (1427512666945477/1649267441664000) (478700867179159/549755813888000))) := by decide +kernel

def shortNegativeR054Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨415443236358333653116656,418718966831597360019923,true⟩,⟨3490411834911703506341341,3517933400822543156094584,true⟩,⟨⟨243653009382516822262991,253543510616013506848229,true⟩,⟨1178144155326961676783953,1188034656560458361382071,true⟩⟩⟩
  | 1 => ⟨⟨684201356609412083642,722870525682217125780,true⟩,⟨415443236358333653116656,418718966831597360019923,true⟩,⟨⟨(-718581602830146801973640),(-688910099129794187236812),true⟩,⟨(-997812564679136215305301),(-968141060978783600564628),true⟩⟩⟩
  | 2 => ⟨⟨15714601714720396,17959372313169414,true⟩,⟨684201356609412083642,722870525682217125780,true⟩,⟨⟨1015132730089897822118138,1064585236257106366974497,true⟩,⟨591873238032203579413003,641325744199412124263534,true⟩⟩⟩
  | 3 => ⟨⟨(-29326205792),40780877069,true⟩,⟨15714601714720396,17959372313169414,true⟩,⟨⟨(-1234702857560974173695850),(-1165469348926909698706746),true⟩,⟨(-180544757564091209903826),(-111311248930026734929231),true⟩⟩⟩
  | 4 => ⟨⟨(-34359738346),34359738402,true⟩,⟨(-29326205792),40780877069,true⟩,⟨⟨1112818483576655420602879,1201832994677575825687912,true⟩,⟨(-393933600986488297396200),(-304919089885567892322286),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738346),34359738402,true⟩,⟨⟨(-973208310922938135143590),(-864412797355161799889364),true⟩,⟨731279532523620610139189,840075046091396945391581,true⟩⟩⟩
theorem shortNegativeR054Q01F_ok : ∀ n : Fin 6, (shortNegativeR054Q01F n).encloses (FactoredFrequency.build shortNegativeR054Q01T (Grid.ofRats (1427512666945477/1649267441664000) (478700867179159/549755813888000)) n) := by decide +kernel
def shortNegativeR054Q01L : ℕ → ℚ
  | 0 => (-732741/250000)
  | 1 => (-1326979/500000)
  | 2 => (-469437/200000)
  | 3 => (-209931/100000)
  | 4 => (-1967987/1000000)
  | 5 => (-2010771/1000000)
  | 6 => (-2192993/1000000)
  | 7 => (-99217/40000)
  | 8 => (-351091/125000)
  | 9 => (-3122003/1000000)
  | 10 => (-3281377/1000000)
  | 11 => (-1613157/500000)
  | _ => 0
def shortNegativeR054Q01U : ℕ → ℚ
  | 0 => (-2443381/1000000)
  | 1 => (-2101449/1000000)
  | 2 => (-1741397/1000000)
  | 3 => (-727199/500000)
  | 4 => (-1298409/1000000)
  | 5 => (-1269359/1000000)
  | 6 => (-696847/500000)
  | 7 => (-205989/125000)
  | 8 => (-989851/500000)
  | 9 => (-2279759/1000000)
  | 10 => (-311263/125000)
  | 11 => (-507811/200000)
  | _ => 0
private theorem shortNegativeR054Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR054Q01P shortNegativeR054Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR054Q01L (0:Fin 12)) (shortNegativeR054Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR054Q01P shortNegativeR054Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR054Q01L (1:Fin 12)) (shortNegativeR054Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR054Q01P shortNegativeR054Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR054Q01L (2:Fin 12)) (shortNegativeR054Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR054Q01P shortNegativeR054Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR054Q01L (3:Fin 12)) (shortNegativeR054Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR054Q01P shortNegativeR054Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR054Q01L (4:Fin 12)) (shortNegativeR054Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR054Q01P shortNegativeR054Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR054Q01L (5:Fin 12)) (shortNegativeR054Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR054Q01P shortNegativeR054Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR054Q01L (6:Fin 12)) (shortNegativeR054Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR054Q01P shortNegativeR054Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR054Q01L (7:Fin 12)) (shortNegativeR054Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR054Q01P shortNegativeR054Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR054Q01L (8:Fin 12)) (shortNegativeR054Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR054Q01P shortNegativeR054Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR054Q01L (9:Fin 12)) (shortNegativeR054Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR054Q01P shortNegativeR054Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR054Q01L (10:Fin 12)) (shortNegativeR054Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR054Q01P shortNegativeR054Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR054Q01L (11:Fin 12)) (shortNegativeR054Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR054Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR054Q01P shortNegativeR054Q01F (shortNegativeNodes12 k)).re (shortNegativeR054Q01L k) (shortNegativeR054Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR054Q01Point00
  · exact shortNegativeR054Q01Point01
  · exact shortNegativeR054Q01Point02
  · exact shortNegativeR054Q01Point03
  · exact shortNegativeR054Q01Point04
  · exact shortNegativeR054Q01Point05
  · exact shortNegativeR054Q01Point06
  · exact shortNegativeR054Q01Point07
  · exact shortNegativeR054Q01Point08
  · exact shortNegativeR054Q01Point09
  · exact shortNegativeR054Q01Point10
  · exact shortNegativeR054Q01Point11

theorem shortNegativeR054Q01Bound {t a : ℝ} (tl : ((27/20):ℝ)≤t) (tu : t≤((34/25):ℝ)) (al : ((1427512666945477/1649267441664000):ℝ)≤a) (au : a≤((478700867179159/549755813888000):ℝ)) : (((-1712414599567556087977059535881623/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1173262034538827258726881074414999/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR054Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1427512666945477/1649267441664000) (478700867179159/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR054Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR054Q01F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR054Q01L shortNegativeR054Q01U (-1712414599567556087977059535881623/649037107316853453566312041152512) (-1173262034538827258726881074414999/649037107316853453566312041152512) shortNegativeR054Q01Samples (by decide +kernel)

def shortNegativeR054Q02T := Grid.ofRats (27/20) (34/25)
def shortNegativeR054Q02P : PrimalThetaParameters := ⟨⟨⟨16859621167858901841325,17397689491810551008442,true⟩,⟨0,0,true⟩⟩, ⟨⟨1653536985609125176433353,1663427486842621860969516,true⟩,⟨0,0,true⟩⟩, ⟨(-490878502418053868181284),(-471097499951129218594725),true⟩, ⟨3419347656271628880704397,3492600466072510638171532,true⟩⟩
theorem shortNegativeR054Q02P_ok : shortNegativeR054Q02P.encloses (primalThetaParameters shortNegativeR054Q02T (Grid.ofRats (478700867179159/549755813888000) (1444692536129477/1649267441664000))) := by decide +kernel

def shortNegativeR054Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨415443236358333653116656,418718966831597360019923,true⟩,⟨3490411834911703506341341,3517933400822543156094584,true⟩,⟨⟨233965670178649207541361,243856171412145892126761,true⟩,⟨1180138379029530332840602,1190028880263027017439048,true⟩⟩⟩
  | 1 => ⟨⟨684201356609412083642,722870525682217125780,true⟩,⟨415443236358333653116656,418718966831597360019923,true⟩,⟨⟨(-694246189140848299458916),(-664574685440495684722341),true⟩,⟨(-1014787298191998201340020),(-985115794491645586599023),true⟩⟩⟩
  | 2 => ⟨⟨15714601714720396,17959372313169414,true⟩,⟨684201356609412083642,722870525682217125780,true⟩,⟨⟨989047166091736788156441,1038499672258945333014348,true⟩,⟨633882198049875447525132,683334704217083992378151,true⟩⟩⟩
  | 3 => ⟨⟨(-29326205792),40780877069,true⟩,⟨15714601714720396,17959372313169414,true⟩,⟨⟨(-1224382910108670751489322),(-1155149401474606276498989),true⟩,⟨(-248995232396548117532776),(-179761723762483642555865),true⟩⟩⟩
  | 4 => ⟨⟨(-34359738346),34359738402,true⟩,⟨(-29326205792),40780877069,true⟩,⟨⟨1135388055961851682792633,1224402567062772087875666,true⟩,⟨(-307848652224373615559556),(-218834141123453210489160),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738346),34359738402,true⟩,⟨⟨(-1040100652410459640112277),(-931305138842683304857926),true⟩,⟨645524695266548105637858,754320208834324440888274,true⟩⟩⟩
theorem shortNegativeR054Q02F_ok : ∀ n : Fin 6, (shortNegativeR054Q02F n).encloses (FactoredFrequency.build shortNegativeR054Q02T (Grid.ofRats (478700867179159/549755813888000) (1444692536129477/1649267441664000)) n) := by decide +kernel
def shortNegativeR054Q02L : ℕ → ℚ
  | 0 => (-293379/100000)
  | 1 => (-41628/15625)
  | 2 => (-2359657/1000000)
  | 3 => (-2108921/1000000)
  | 4 => (-1971/1000)
  | 5 => (-2004671/1000000)
  | 6 => (-2177289/1000000)
  | 7 => (-1228229/500000)
  | 8 => (-1390027/500000)
  | 9 => (-386721/125000)
  | 10 => (-3260227/1000000)
  | 11 => (-1608209/500000)
  | _ => 0
def shortNegativeR054Q02U : ℕ → ℚ
  | 0 => (-2452503/1000000)
  | 1 => (-2118569/1000000)
  | 2 => (-880451/500000)
  | 3 => (-1471001/1000000)
  | 4 => (-130843/100000)
  | 5 => (-1271241/1000000)
  | 6 => (-1387181/1000000)
  | 7 => (-1634321/1000000)
  | 8 => (-981029/500000)
  | 9 => (-452607/200000)
  | 10 => (-2479319/1000000)
  | 11 => (-2538323/1000000)
  | _ => 0
private theorem shortNegativeR054Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR054Q02P shortNegativeR054Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR054Q02L (0:Fin 12)) (shortNegativeR054Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR054Q02P shortNegativeR054Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR054Q02L (1:Fin 12)) (shortNegativeR054Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR054Q02P shortNegativeR054Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR054Q02L (2:Fin 12)) (shortNegativeR054Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR054Q02P shortNegativeR054Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR054Q02L (3:Fin 12)) (shortNegativeR054Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR054Q02P shortNegativeR054Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR054Q02L (4:Fin 12)) (shortNegativeR054Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR054Q02P shortNegativeR054Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR054Q02L (5:Fin 12)) (shortNegativeR054Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR054Q02P shortNegativeR054Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR054Q02L (6:Fin 12)) (shortNegativeR054Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR054Q02P shortNegativeR054Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR054Q02L (7:Fin 12)) (shortNegativeR054Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR054Q02P shortNegativeR054Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR054Q02L (8:Fin 12)) (shortNegativeR054Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR054Q02P shortNegativeR054Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR054Q02L (9:Fin 12)) (shortNegativeR054Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR054Q02P shortNegativeR054Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR054Q02L (10:Fin 12)) (shortNegativeR054Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR054Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR054Q02P shortNegativeR054Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR054Q02L (11:Fin 12)) (shortNegativeR054Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR054Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR054Q02P shortNegativeR054Q02F (shortNegativeNodes12 k)).re (shortNegativeR054Q02L k) (shortNegativeR054Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR054Q02Point00
  · exact shortNegativeR054Q02Point01
  · exact shortNegativeR054Q02Point02
  · exact shortNegativeR054Q02Point03
  · exact shortNegativeR054Q02Point04
  · exact shortNegativeR054Q02Point05
  · exact shortNegativeR054Q02Point06
  · exact shortNegativeR054Q02Point07
  · exact shortNegativeR054Q02Point08
  · exact shortNegativeR054Q02Point09
  · exact shortNegativeR054Q02Point10
  · exact shortNegativeR054Q02Point11

theorem shortNegativeR054Q02Bound {t a : ℝ} (tl : ((27/20):ℝ)≤t) (tu : t≤((34/25):ℝ)) (al : ((478700867179159/549755813888000):ℝ)≤a) (au : a≤((1444692536129477/1649267441664000):ℝ)) : (((-1712414599567556087977059535881623/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1173262034538827258726881074414999/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR054Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (478700867179159/549755813888000) (1444692536129477/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR054Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR054Q02F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR054Q02L shortNegativeR054Q02U (-1712414599567556087977059535881623/649037107316853453566312041152512) (-1173262034538827258726881074414999/649037107316853453566312041152512) shortNegativeR054Q02Samples (by decide +kernel)

theorem short_original_negative_054 {t a : ℝ} (tb : RealMem negative_054.t t) (ab : RealMem negative_054.a a) : RealMem negative_054.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((27/20):ℝ) ((34/25):ℝ) := by simpa [negative_054,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((27/20):ℝ)<((34/25):ℝ)) tB
  have aB : a∈Icc ((1418922732353477/1649267441664000):ℝ) ((1444692536129477/1649267441664000):ℝ) := by simpa [negative_054,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((1418922732353477/1649267441664000):ℝ)<((1444692536129477/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR054Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_054,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR054Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_054,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR054Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_054,RealMem] using v

def shortNegativeR055Q00T := Grid.ofRats (34/25) (137/100)
def shortNegativeR055Q00P : PrimalThetaParameters := ⟨⟨⟨16338193991715908476779,16859621167927621318368,true⟩,⟨0,0,true⟩⟩, ⟨⟨1657905768187502146492048,1667796269420998831028224,true⟩,⟨0,0,true⟩⟩, ⟨(-482140937261299928063867),(-462359934794375278477336),true⟩, ⟨3404044717226275837879368,3476456292467483583099429,true⟩⟩
theorem shortNegativeR055Q00P_ok : shortNegativeR055Q00P.encloses (primalThetaParameters shortNegativeR055Q00T (Grid.ofRats (1439896904344709/1649267441664000) (1448486838936709/1649267441664000))) := by decide +kernel

def shortNegativeR055Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨412193132644332821700921,415443236358402372608933,true⟩,⟨3517933400822474436487113,3545671971667403779943656,true⟩,⟨⟨229681497157159920571751,239571998390656605157111,true⟩,⟨1180994008603529664017791,1190884509837026348616261,true⟩⟩⟩
  | 1 => ⟨⟨647600752553560362444,684201356678131560419,true⟩,⟨412193132644332821700921,415443236358402372608933,true⟩,⟨⟨(-683365683481047954214466),(-653694179780695339477968),true⟩,⟨(-1022094094007006001668538),(-992422590306653386927363),true⟩⟩⟩
  | 2 => ⟨⟨13750460652551446,15714670434197133,true⟩,⟨647600752553560362444,684201356678131560419,true⟩,⟨⟨976982023134885784059060,1026434529302094328917128,true⟩,⟨652091423020000564963586,701543929187209109817183,true⟩⟩⟩
  | 3 => ⟨⟨(-30413950655),39393270945,true⟩,⟨13750460652551446,15714670434197133,true⟩,⟨⟨(-1218579833269534980296232),(-1149346324635470505304362),true⟩,⟨(-279020242443148545090645),(-209786733809084070111705),true⟩⟩⟩
  | 4 => ⟨⟨(-34359738353),34359738391,true⟩,⟨(-30413950655),39393270945,true⟩,⟨⟨1143327452569825256147785,1232341963670745661229719,true⟩,⟨(-269341291042640898290094),(-180326779941720493221416),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738353),34359738391,true⟩,⟨⟨(-1067137596996659102150072),(-958342083428882766895778),true⟩,⟨605798921015019052678876,714594434582795387928318,true⟩⟩⟩
theorem shortNegativeR055Q00F_ok : ∀ n : Fin 6, (shortNegativeR055Q00F n).encloses (FactoredFrequency.build shortNegativeR055Q00T (Grid.ofRats (1439896904344709/1649267441664000) (1448486838936709/1649267441664000)) n) := by decide +kernel
def shortNegativeR055Q00L : ℕ → ℚ
  | 0 => (-366259/125000)
  | 1 => (-83551/31250)
  | 2 => (-2380481/1000000)
  | 3 => (-106827/50000)
  | 4 => (-2000077/1000000)
  | 5 => (-25369/12500)
  | 6 => (-17549/8000)
  | 7 => (-38456/15625)
  | 8 => (-2772311/1000000)
  | 9 => (-1537663/500000)
  | 10 => (-3237943/1000000)
  | 11 => (-3199199/1000000)
  | _ => 0
def shortNegativeR055Q00U : ℕ → ℚ
  | 0 => (-490783/200000)
  | 1 => (-426663/200000)
  | 2 => (-1786751/1000000)
  | 3 => (-1503139/1000000)
  | 4 => (-335383/250000)
  | 5 => (-1301171/1000000)
  | 6 => (-282019/200000)
  | 7 => (-823701/500000)
  | 8 => (-1964171/1000000)
  | 9 => (-1128269/500000)
  | 10 => (-493807/200000)
  | 11 => (-1265629/500000)
  | _ => 0
private theorem shortNegativeR055Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR055Q00P shortNegativeR055Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR055Q00L (0:Fin 12)) (shortNegativeR055Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR055Q00P shortNegativeR055Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR055Q00L (1:Fin 12)) (shortNegativeR055Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR055Q00P shortNegativeR055Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR055Q00L (2:Fin 12)) (shortNegativeR055Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR055Q00P shortNegativeR055Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR055Q00L (3:Fin 12)) (shortNegativeR055Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR055Q00P shortNegativeR055Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR055Q00L (4:Fin 12)) (shortNegativeR055Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR055Q00P shortNegativeR055Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR055Q00L (5:Fin 12)) (shortNegativeR055Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR055Q00P shortNegativeR055Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR055Q00L (6:Fin 12)) (shortNegativeR055Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR055Q00P shortNegativeR055Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR055Q00L (7:Fin 12)) (shortNegativeR055Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR055Q00P shortNegativeR055Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR055Q00L (8:Fin 12)) (shortNegativeR055Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR055Q00P shortNegativeR055Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR055Q00L (9:Fin 12)) (shortNegativeR055Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR055Q00P shortNegativeR055Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR055Q00L (10:Fin 12)) (shortNegativeR055Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR055Q00P shortNegativeR055Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR055Q00L (11:Fin 12)) (shortNegativeR055Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR055Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR055Q00P shortNegativeR055Q00F (shortNegativeNodes12 k)).re (shortNegativeR055Q00L k) (shortNegativeR055Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR055Q00Point00
  · exact shortNegativeR055Q00Point01
  · exact shortNegativeR055Q00Point02
  · exact shortNegativeR055Q00Point03
  · exact shortNegativeR055Q00Point04
  · exact shortNegativeR055Q00Point05
  · exact shortNegativeR055Q00Point06
  · exact shortNegativeR055Q00Point07
  · exact shortNegativeR055Q00Point08
  · exact shortNegativeR055Q00Point09
  · exact shortNegativeR055Q00Point10
  · exact shortNegativeR055Q00Point11

theorem shortNegativeR055Q00Bound {t a : ℝ} (tl : ((34/25):ℝ)≤t) (tu : t≤((137/100):ℝ)) (al : ((1439896904344709/1649267441664000):ℝ)≤a) (au : a≤((1448486838936709/1649267441664000):ℝ)) : (((-3408582891574724786457560592875703/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2370026506230371989912375340761271/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR055Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1439896904344709/1649267441664000) (1448486838936709/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR055Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR055Q00F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR055Q00L shortNegativeR055Q00U (-3408582891574724786457560592875703/1298074214633706907132624082305024) (-2370026506230371989912375340761271/1298074214633706907132624082305024) shortNegativeR055Q00Samples (by decide +kernel)

def shortNegativeR055Q01T := Grid.ofRats (34/25) (137/100)
def shortNegativeR055Q01P : PrimalThetaParameters := ⟨⟨⟨16338193991715908476779,16859621167927621318368,true⟩,⟨0,0,true⟩⟩, ⟨⟨1667796269420930111546176,1677686770654426796082382,true⟩,⟨0,0,true⟩⟩, ⟨(-462359934794443997955548),(-442578932327519348369083),true⟩, ⟨3394470634975168731503653,3466597055755994545366517,true⟩⟩
theorem shortNegativeR055Q01P_ok : shortNegativeR055Q01P.encloses (primalThetaParameters shortNegativeR055Q01T (Grid.ofRats (1448486838936709/1649267441664000) (485692257842903/549755813888000))) := by decide +kernel

def shortNegativeR055Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨412193132644332821700921,415443236358402372608933,true⟩,⟨3517933400822474436487113,3545671971667403779943656,true⟩,⟨⟨219971310477568130783543,229861811711064815368947,true⟩,⟨1182873834040679412592197,1192764335274176097190876,true⟩⟩⟩
  | 1 => ⟨⟨647600752553560362444,684201356678131560419,true⟩,⟨412193132644332821700921,415443236358402372608933,true⟩,⟨⟨(-658444977608132331083956),(-628773473907779716347186),true⟩,⟨(-1038197272452816181035464),(-1008525768752463566293456),true⟩⟩⟩
  | 2 => ⟨⟨13750460652551446,15714670434197133,true⟩,⟨647600752553560362444,684201356678131560419,true⟩,⟨⟨948465766282275729139616,997918272449484273999284,true⟩,⟨692489844597885000342841,741942350765093545198993,true⟩⟩⟩
  | 3 => ⟨⟨(-30413950655),39393270945,true⟩,⟨13750460652551446,15714670434197133,true⟩,⟨⟨(-1202649845315025942117193),(-1133416336680961467123251),true⟩,⟨(-346386438001279311193731),(-277152929367214836211573),true⟩⟩⟩
  | 4 => ⟨⟨(-34359738353),34359738391,true⟩,⟨(-30413950655),39393270945,true⟩,⟨⟨1156648780672952389779409,1245663291773872794858876,true⟩,⟨(-181349551551962802978623),(-92335040451042397913797),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738353),34359738391,true⟩,⟨⟨(-1122372628188909262751899),(-1013577114621132927498171),true⟩,⟨512110240845740688266398,620905754413517023513226,true⟩⟩⟩
theorem shortNegativeR055Q01F_ok : ∀ n : Fin 6, (shortNegativeR055Q01F n).encloses (FactoredFrequency.build shortNegativeR055Q01T (Grid.ofRats (1448486838936709/1649267441664000) (485692257842903/549755813888000)) n) := by decide +kernel
def shortNegativeR055Q01L : ℕ → ℚ
  | 0 => (-2932173/1000000)
  | 1 => (-134151/50000)
  | 2 => (-95691/40000)
  | 3 => (-2145793/1000000)
  | 4 => (-2003089/1000000)
  | 5 => (-2023749/1000000)
  | 6 => (-1089271/500000)
  | 7 => (-609511/250000)
  | 8 => (-2744499/1000000)
  | 9 => (-3047721/1000000)
  | 10 => (-804233/250000)
  | 11 => (-1594457/500000)
  | _ => 0
def shortNegativeR055Q01U : ℕ → ℚ
  | 0 => (-123109/50000)
  | 1 => (-1074783/500000)
  | 2 => (-902831/500000)
  | 3 => (-1519553/1000000)
  | 4 => (-1351769/1000000)
  | 5 => (-1303621/1000000)
  | 6 => (-1404423/1000000)
  | 7 => (-204351/125000)
  | 8 => (-243437/125000)
  | 9 => (-1120257/500000)
  | 10 => (-1229227/500000)
  | 11 => (-158133/62500)
  | _ => 0
private theorem shortNegativeR055Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR055Q01P shortNegativeR055Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR055Q01L (0:Fin 12)) (shortNegativeR055Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR055Q01P shortNegativeR055Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR055Q01L (1:Fin 12)) (shortNegativeR055Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR055Q01P shortNegativeR055Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR055Q01L (2:Fin 12)) (shortNegativeR055Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR055Q01P shortNegativeR055Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR055Q01L (3:Fin 12)) (shortNegativeR055Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR055Q01P shortNegativeR055Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR055Q01L (4:Fin 12)) (shortNegativeR055Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR055Q01P shortNegativeR055Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR055Q01L (5:Fin 12)) (shortNegativeR055Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR055Q01P shortNegativeR055Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR055Q01L (6:Fin 12)) (shortNegativeR055Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR055Q01P shortNegativeR055Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR055Q01L (7:Fin 12)) (shortNegativeR055Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR055Q01P shortNegativeR055Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR055Q01L (8:Fin 12)) (shortNegativeR055Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR055Q01P shortNegativeR055Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR055Q01L (9:Fin 12)) (shortNegativeR055Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR055Q01P shortNegativeR055Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR055Q01L (10:Fin 12)) (shortNegativeR055Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR055Q01P shortNegativeR055Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR055Q01L (11:Fin 12)) (shortNegativeR055Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR055Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR055Q01P shortNegativeR055Q01F (shortNegativeNodes12 k)).re (shortNegativeR055Q01L k) (shortNegativeR055Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR055Q01Point00
  · exact shortNegativeR055Q01Point01
  · exact shortNegativeR055Q01Point02
  · exact shortNegativeR055Q01Point03
  · exact shortNegativeR055Q01Point04
  · exact shortNegativeR055Q01Point05
  · exact shortNegativeR055Q01Point06
  · exact shortNegativeR055Q01Point07
  · exact shortNegativeR055Q01Point08
  · exact shortNegativeR055Q01Point09
  · exact shortNegativeR055Q01Point10
  · exact shortNegativeR055Q01Point11

theorem shortNegativeR055Q01Bound {t a : ℝ} (tl : ((34/25):ℝ)≤t) (tu : t≤((137/100):ℝ)) (al : ((1448486838936709/1649267441664000):ℝ)≤a) (au : a≤((485692257842903/549755813888000):ℝ)) : (((-3408582891574724786457560592875703/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2370026506230371989912375340761271/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR055Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1448486838936709/1649267441664000) (485692257842903/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR055Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR055Q01F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR055Q01L shortNegativeR055Q01U (-3408582891574724786457560592875703/1298074214633706907132624082305024) (-2370026506230371989912375340761271/1298074214633706907132624082305024) shortNegativeR055Q01Samples (by decide +kernel)

def shortNegativeR055Q02T := Grid.ofRats (34/25) (137/100)
def shortNegativeR055Q02P : PrimalThetaParameters := ⟨⟨⟨16338193991715908476779,16859621167927621318368,true⟩,⟨0,0,true⟩⟩, ⟨⟨1677686770654358076600302,1687577271887854761136540,true⟩,⟨0,0,true⟩⟩, ⟨(-442578932327588067847232),(-422797929860663418260830),true⟩, ⟨3385345146998261616391093,3457198493836812021835597,true⟩⟩
theorem shortNegativeR055Q02P_ok : shortNegativeR055Q02P.encloses (primalThetaParameters shortNegativeR055Q02T (Grid.ofRats (485692257842903/549755813888000) (1465666708120709/1649267441664000))) := by decide +kernel

def shortNegativeR055Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨412193132644332821700921,415443236358402372608933,true⟩,⟨3517933400822474436487113,3545671971667403779943656,true⟩,⟨⟨210246069645553456684999,220136570879050141270548,true⟩,⟨1184674156174629778841963,1194564657408126463440950,true⟩⟩⟩
  | 1 => ⟨⟨647600752553560362444,684201356678131560419,true⟩,⟨412193132644332821700921,415443236358402372608933,true⟩,⟨⟨(-633136585603719160687594),(-603465081903366545950127),true⟩,⟨(-1053684016184567290532463),(-1024012512484214675789195),true⟩⟩⟩
  | 2 => ⟨⟨13750460652551446,15714670434197133,true⟩,⟨647600752553560362444,684201356678131560419,true⟩,⟨⟨918321281185081702217695,967773787352290247077778,true⟩,⟨731688306163277536629544,781140812330486081487059,true⟩⟩⟩
  | 3 => ⟨⟨(-30413950655),39393270945,true⟩,⟨13750460652551446,15714670434197133,true⟩,⟨⟨(-1182890112658174666116066),(-1113656604024110191121088),true⟩,⟨(-412730403706811910328114),(-343496895072747435343736),true⟩⟩⟩
  | 4 => ⟨⟨(-34359738353),34359738391,true⟩,⟨(-30413950655),39393270945,true⟩,⟨⟨1163460940144479362586586,1252475451245399767664163,true⟩,⟨(-92616251802877571843201),(-3601740701957166781596),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738353),34359738391,true⟩,⟨⟨(-1168964140705270173231754),(-1060168627137493837979594),true⟩,⟨413836600310203561585857,522632113877979896829120,true⟩⟩⟩
theorem shortNegativeR055Q02F_ok : ∀ n : Fin 6, (shortNegativeR055Q02F n).encloses (FactoredFrequency.build shortNegativeR055Q02T (Grid.ofRats (485692257842903/549755813888000) (1465666708120709/1649267441664000)) n) := by decide +kernel
def shortNegativeR055Q02L : ℕ → ℚ
  | 0 => (-586823/200000)
  | 1 => (-269233/100000)
  | 2 => (-1202067/500000)
  | 3 => (-538813/250000)
  | 4 => (-501603/250000)
  | 5 => (-2018353/1000000)
  | 6 => (-432771/200000)
  | 7 => (-96611/40000)
  | 8 => (-2716961/1000000)
  | 9 => (-377527/125000)
  | 10 => (-3195821/1000000)
  | 11 => (-317843/100000)
  | _ => 0
def shortNegativeR055Q02U : ℕ → ℚ
  | 0 => (-2470189/1000000)
  | 1 => (-2165697/1000000)
  | 2 => (-456163/250000)
  | 3 => (-1536231/1000000)
  | 4 => (-681201/500000)
  | 5 => (-1306553/1000000)
  | 6 => (-43727/31250)
  | 7 => (-324539/200000)
  | 8 => (-965599/500000)
  | 9 => (-2224697/1000000)
  | 10 => (-1223939/500000)
  | 11 => (-2528821/1000000)
  | _ => 0
private theorem shortNegativeR055Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR055Q02P shortNegativeR055Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR055Q02L (0:Fin 12)) (shortNegativeR055Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR055Q02P shortNegativeR055Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR055Q02L (1:Fin 12)) (shortNegativeR055Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR055Q02P shortNegativeR055Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR055Q02L (2:Fin 12)) (shortNegativeR055Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR055Q02P shortNegativeR055Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR055Q02L (3:Fin 12)) (shortNegativeR055Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR055Q02P shortNegativeR055Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR055Q02L (4:Fin 12)) (shortNegativeR055Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR055Q02P shortNegativeR055Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR055Q02L (5:Fin 12)) (shortNegativeR055Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR055Q02P shortNegativeR055Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR055Q02L (6:Fin 12)) (shortNegativeR055Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR055Q02P shortNegativeR055Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR055Q02L (7:Fin 12)) (shortNegativeR055Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR055Q02P shortNegativeR055Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR055Q02L (8:Fin 12)) (shortNegativeR055Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR055Q02P shortNegativeR055Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR055Q02L (9:Fin 12)) (shortNegativeR055Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR055Q02P shortNegativeR055Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR055Q02L (10:Fin 12)) (shortNegativeR055Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR055Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR055Q02P shortNegativeR055Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR055Q02L (11:Fin 12)) (shortNegativeR055Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR055Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR055Q02P shortNegativeR055Q02F (shortNegativeNodes12 k)).re (shortNegativeR055Q02L k) (shortNegativeR055Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR055Q02Point00
  · exact shortNegativeR055Q02Point01
  · exact shortNegativeR055Q02Point02
  · exact shortNegativeR055Q02Point03
  · exact shortNegativeR055Q02Point04
  · exact shortNegativeR055Q02Point05
  · exact shortNegativeR055Q02Point06
  · exact shortNegativeR055Q02Point07
  · exact shortNegativeR055Q02Point08
  · exact shortNegativeR055Q02Point09
  · exact shortNegativeR055Q02Point10
  · exact shortNegativeR055Q02Point11

theorem shortNegativeR055Q02Bound {t a : ℝ} (tl : ((34/25):ℝ)≤t) (tu : t≤((137/100):ℝ)) (al : ((485692257842903/549755813888000):ℝ)≤a) (au : a≤((1465666708120709/1649267441664000):ℝ)) : (((-3408582891574724786457560592875703/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2370026506230371989912375340761271/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR055Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (485692257842903/549755813888000) (1465666708120709/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR055Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR055Q02F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR055Q02L shortNegativeR055Q02U (-3408582891574724786457560592875703/1298074214633706907132624082305024) (-2370026506230371989912375340761271/1298074214633706907132624082305024) shortNegativeR055Q02Samples (by decide +kernel)

theorem short_original_negative_055 {t a : ℝ} (tb : RealMem negative_055.t t) (ab : RealMem negative_055.a a) : RealMem negative_055.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((34/25):ℝ) ((137/100):ℝ) := by simpa [negative_055,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((34/25):ℝ)<((137/100):ℝ)) tB
  have aB : a∈Icc ((1439896904344709/1649267441664000):ℝ) ((1465666708120709/1649267441664000):ℝ) := by simpa [negative_055,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((1439896904344709/1649267441664000):ℝ)<((1465666708120709/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR055Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_055,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR055Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_055,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR055Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_055,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_054
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_055
