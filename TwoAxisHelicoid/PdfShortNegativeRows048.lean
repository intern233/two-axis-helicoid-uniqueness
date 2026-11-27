import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip048

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR048Q00T := Grid.ofRats (129/100) (13/10)
def shortNegativeR048Q00P : PrimalThetaParameters := ⟨⟨⟨20356841402637285330078,21006522165043968233378,true⟩,⟨0,0,true⟩⟩, ⟨⟨1521153325496760728736050,1531043826730257413271791,true⟩,⟨0,0,true⟩⟩, ⟨(-755645822642782763576733),(-735864820175858113989331),true⟩, ⟨3669836664287291530045757,3753235180620742665947101,true⟩⟩
theorem shortNegativeR048Q00P_ok : shortNegativeR048Q00P.encloses (primalThetaParameters shortNegativeR048Q00T (Grid.ofRats (1321126934018083/1649267441664000) (443238956203361/549755813888000))) := by decide +kernel

def shortNegativeR048Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨435489148873729441907725,438922939463858402281948,true⟩,⟨3329745397030780080138379,3356000123333880309250462,true⟩,⟨⟨362048276710570656680707,371938777944067341265415,true⟩,⟨1146930345196773214976086,1156820846430269899571619,true⟩⟩⟩
  | 1 => ⟨⟨951575930078309493094,1005356370808892242980,true⟩,⟨435489148873729441907725,438922939463858402281948,true⟩,⟨⟨(-980535616000126455850517),(-950864112299773841117340),true⟩,⟨(-742108334663299234584764),(-712436830962946619854854),true⟩⟩⟩
  | 2 => ⟨⟨35012237997258037,40013511528252875,true⟩,⟨951575930078309493094,1005356370808892242980,true⟩,⟨⟨1183704811804466938549710,1233157317971675483387425,true⟩,⟨9856961694451637224185,59309467861660182045747,true⟩⟩⟩
  | 3 => ⟨⟨(-12667324179),62032152952,true⟩,⟨35012237997258037,40013511528252875,true⟩,⟨⟨(-1040328597154840198284020),(-971095088520775723287780),true⟩,⟨636237422465585087913786,705470931099649562905418,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738142),34359738701,true⟩,⟨(-12667324179),62032152952,true⟩,⟨⟨387761061127208454785541,476775572228128859888659,true⟩,⟨(-1173509354630686750529296),(-1084494843529766345416587),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738142),34359738701,true⟩,⟨⟨246119685794787833257855,354915199362564168486890,true⟩,⟨1116580852771758280359529,1225376366339534615600544,true⟩⟩⟩
theorem shortNegativeR048Q00F_ok : ∀ n : Fin 6, (shortNegativeR048Q00F n).encloses (FactoredFrequency.build shortNegativeR048Q00T (Grid.ofRats (1321126934018083/1649267441664000) (443238956203361/549755813888000)) n) := by decide +kernel
def shortNegativeR048Q00L : ℕ → ℚ
  | 0 => (-1427933/500000)
  | 1 => (-1204863/500000)
  | 2 => (-1009919/500000)
  | 3 => (-445303/250000)
  | 4 => (-866407/500000)
  | 5 => (-958833/500000)
  | 6 => (-2272047/1000000)
  | 7 => (-2733801/1000000)
  | 8 => (-639079/200000)
  | 9 => (-1779661/500000)
  | 10 => (-3642619/1000000)
  | 11 => (-848459/250000)
  | _ => 0
def shortNegativeR048Q00U : ℕ → ℚ
  | 0 => (-2269007/1000000)
  | 1 => (-351841/200000)
  | 2 => (-264897/200000)
  | 3 => (-1055961/1000000)
  | 4 => (-979081/1000000)
  | 5 => (-53551/50000)
  | 6 => (-1348933/1000000)
  | 7 => (-55021/31250)
  | 8 => (-2203989/1000000)
  | 9 => (-2532827/1000000)
  | 10 => (-1333619/500000)
  | 11 => (-127697/50000)
  | _ => 0
private theorem shortNegativeR048Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR048Q00P shortNegativeR048Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR048Q00L (0:Fin 12)) (shortNegativeR048Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR048Q00P shortNegativeR048Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR048Q00L (1:Fin 12)) (shortNegativeR048Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR048Q00P shortNegativeR048Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR048Q00L (2:Fin 12)) (shortNegativeR048Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR048Q00P shortNegativeR048Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR048Q00L (3:Fin 12)) (shortNegativeR048Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR048Q00P shortNegativeR048Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR048Q00L (4:Fin 12)) (shortNegativeR048Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR048Q00P shortNegativeR048Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR048Q00L (5:Fin 12)) (shortNegativeR048Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR048Q00P shortNegativeR048Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR048Q00L (6:Fin 12)) (shortNegativeR048Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR048Q00P shortNegativeR048Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR048Q00L (7:Fin 12)) (shortNegativeR048Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR048Q00P shortNegativeR048Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR048Q00L (8:Fin 12)) (shortNegativeR048Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR048Q00P shortNegativeR048Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR048Q00L (9:Fin 12)) (shortNegativeR048Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR048Q00P shortNegativeR048Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR048Q00L (10:Fin 12)) (shortNegativeR048Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR048Q00P shortNegativeR048Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR048Q00L (11:Fin 12)) (shortNegativeR048Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR048Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR048Q00P shortNegativeR048Q00F (shortNegativeNodes12 k)).re (shortNegativeR048Q00L k) (shortNegativeR048Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR048Q00Point00
  · exact shortNegativeR048Q00Point01
  · exact shortNegativeR048Q00Point02
  · exact shortNegativeR048Q00Point03
  · exact shortNegativeR048Q00Point04
  · exact shortNegativeR048Q00Point05
  · exact shortNegativeR048Q00Point06
  · exact shortNegativeR048Q00Point07
  · exact shortNegativeR048Q00Point08
  · exact shortNegativeR048Q00Point09
  · exact shortNegativeR048Q00Point10
  · exact shortNegativeR048Q00Point11

theorem shortNegativeR048Q00Bound {t a : ℝ} (tl : ((129/100):ℝ)≤t) (tu : t≤((13/10):ℝ)) (al : ((1321126934018083/1649267441664000):ℝ)≤a) (au : a≤((443238956203361/549755813888000):ℝ)) : (((-3463798150121927710045496386322433/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2208077883910523880759177241755649/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR048Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1321126934018083/1649267441664000) (443238956203361/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR048Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR048Q00F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR048Q00L shortNegativeR048Q00U (-3463798150121927710045496386322433/1298074214633706907132624082305024) (-2208077883910523880759177241755649/1298074214633706907132624082305024) shortNegativeR048Q00Samples (by decide +kernel)

def shortNegativeR048Q01T := Grid.ofRats (129/100) (13/10)
def shortNegativeR048Q01P : PrimalThetaParameters := ⟨⟨⟨20356841402637285330078,21006522165043968233378,true⟩,⟨0,0,true⟩⟩, ⟨⟨1531043826730188693790178,1540934327963685378325949,true⟩,⟨0,0,true⟩⟩, ⟨(-735864820175926833468414),(-716083817709002183881078),true⟩, ⟨3653444667201295459589753,3736356485481377529332197,true⟩⟩
theorem shortNegativeR048Q01P_ok : shortNegativeR048Q01P.encloses (primalThetaParameters shortNegativeR048Q01T (Grid.ofRats (443238956203361/549755813888000) (1338306803202083/1649267441664000))) := by decide +kernel

def shortNegativeR048Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨435489148873729441907725,438922939463858402281948,true⟩,⟨3329745397030780080138379,3356000123333880309250462,true⟩,⟨⟨352612339819153181659207,362502841052649866244094,true⟩,⟨1149894221713746179083679,1159784722947242863679573,true⟩⟩⟩
  | 1 => ⟨⟨951575930078309493094,1005356370808892242980,true⟩,⟨435489148873729441907725,438922939463858402281948,true⟩,⟨⟨(-962396602602700864901141),(-932725098902348250167745),true⟩,⟨(-765588754809241932221507),(-735917251108889317490812),true⟩⟩⟩
  | 2 => ⟨⟨35012237997258037,40013511528252875,true⟩,⟨951575930078309493094,1005356370808892242980,true⟩,⟨⟨1181279638969630648567584,1230732145136839193406581,true⟩,⟨59246514310259778212225,108699020477468323035777,true⟩⟩⟩
  | 3 => ⟨⟨(-12667324179),62032152952,true⟩,⟨35012237997258037,40013511528252875,true⟩,⟨⟨(-1077077727475482119772673),(-1007844218841417644776394),true⟩,⟨577573376910546889578537,646806885544611364568889,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738142),34359738701,true⟩,⟨(-12667324179),62032152952,true⟩,⟨⟨469644358118686002874015,558658869219606407975127,true⟩,⟨(-1138650644459023661436235),(-1049636133358103256327142),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738142),34359738701,true⟩,⟨⟨139665261818398874010589,248460775386175209241020,true⟩,⟨1138850407740939966773209,1247645921308716302017391,true⟩⟩⟩
theorem shortNegativeR048Q01F_ok : ∀ n : Fin 6, (shortNegativeR048Q01F n).encloses (FactoredFrequency.build shortNegativeR048Q01T (Grid.ofRats (443238956203361/549755813888000) (1338306803202083/1649267441664000)) n) := by decide +kernel
def shortNegativeR048Q01L : ℕ → ℚ
  | 0 => (-22927/8000)
  | 1 => (-2426949/1000000)
  | 2 => (-2036987/1000000)
  | 3 => (-1792457/1000000)
  | 4 => (-1734533/1000000)
  | 5 => (-190777/100000)
  | 6 => (-2250477/1000000)
  | 7 => (-168921/62500)
  | 8 => (-632017/200000)
  | 9 => (-1763681/500000)
  | 10 => (-3621547/1000000)
  | 11 => (-3389391/1000000)
  | _ => 0
def shortNegativeR048Q01U : ℕ → ℚ
  | 0 => (-2286087/1000000)
  | 1 => (-2853/1600)
  | 2 => (-1347619/1000000)
  | 3 => (-536281/500000)
  | 4 => (-247013/250000)
  | 5 => (-213881/200000)
  | 6 => (-20889/15625)
  | 7 => (-69539/40000)
  | 8 => (-2178587/1000000)
  | 9 => (-1255653/500000)
  | 10 => (-531431/200000)
  | 11 => (-1279031/500000)
  | _ => 0
private theorem shortNegativeR048Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR048Q01P shortNegativeR048Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR048Q01L (0:Fin 12)) (shortNegativeR048Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR048Q01P shortNegativeR048Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR048Q01L (1:Fin 12)) (shortNegativeR048Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR048Q01P shortNegativeR048Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR048Q01L (2:Fin 12)) (shortNegativeR048Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR048Q01P shortNegativeR048Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR048Q01L (3:Fin 12)) (shortNegativeR048Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR048Q01P shortNegativeR048Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR048Q01L (4:Fin 12)) (shortNegativeR048Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR048Q01P shortNegativeR048Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR048Q01L (5:Fin 12)) (shortNegativeR048Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR048Q01P shortNegativeR048Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR048Q01L (6:Fin 12)) (shortNegativeR048Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR048Q01P shortNegativeR048Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR048Q01L (7:Fin 12)) (shortNegativeR048Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR048Q01P shortNegativeR048Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR048Q01L (8:Fin 12)) (shortNegativeR048Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR048Q01P shortNegativeR048Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR048Q01L (9:Fin 12)) (shortNegativeR048Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR048Q01P shortNegativeR048Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR048Q01L (10:Fin 12)) (shortNegativeR048Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR048Q01P shortNegativeR048Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR048Q01L (11:Fin 12)) (shortNegativeR048Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR048Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR048Q01P shortNegativeR048Q01F (shortNegativeNodes12 k)).re (shortNegativeR048Q01L k) (shortNegativeR048Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR048Q01Point00
  · exact shortNegativeR048Q01Point01
  · exact shortNegativeR048Q01Point02
  · exact shortNegativeR048Q01Point03
  · exact shortNegativeR048Q01Point04
  · exact shortNegativeR048Q01Point05
  · exact shortNegativeR048Q01Point06
  · exact shortNegativeR048Q01Point07
  · exact shortNegativeR048Q01Point08
  · exact shortNegativeR048Q01Point09
  · exact shortNegativeR048Q01Point10
  · exact shortNegativeR048Q01Point11

theorem shortNegativeR048Q01Bound {t a : ℝ} (tl : ((129/100):ℝ)≤t) (tu : t≤((13/10):ℝ)) (al : ((443238956203361/549755813888000):ℝ)≤a) (au : a≤((1338306803202083/1649267441664000):ℝ)) : (((-3463798150121927710045496386322433/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2208077883910523880759177241755649/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR048Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (443238956203361/549755813888000) (1338306803202083/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR048Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR048Q01F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR048Q01L shortNegativeR048Q01U (-3463798150121927710045496386322433/1298074214633706907132624082305024) (-2208077883910523880759177241755649/1298074214633706907132624082305024) shortNegativeR048Q01Samples (by decide +kernel)

def shortNegativeR048Q02T := Grid.ofRats (129/100) (13/10)
def shortNegativeR048Q02P : PrimalThetaParameters := ⟨⟨⟨20356841402637285330078,21006522165043968233378,true⟩,⟨0,0,true⟩⟩, ⟨⟨1540934327963616658844305,1550824829197113343380107,true⟩,⟨0,0,true⟩⟩, ⟨(-716083817709070903360098),(-696302815242146253772825),true⟩, ⟨3637603335802371627987372,3720044564709150039996534,true⟩⟩
theorem shortNegativeR048Q02P_ok : shortNegativeR048Q02P.encloses (primalThetaParameters shortNegativeR048Q02T (Grid.ofRats (1338306803202083/1649267441664000) (1346896737794083/1649267441664000))) := by decide +kernel

def shortNegativeR048Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨435489148873729441907725,438922939463858402281948,true⟩,⟨3329745397030780080138379,3356000123333880309250462,true⟩,⟨⟨343152470824024926035594,353042972057521610620291,true⟩,⟨1152780802324380186335537,1162671303557876870931401,true⟩⟩⟩
  | 1 => ⟨⟨951575930078309493094,1005356370808892242980,true⟩,⟨435489148873729441907725,438922939463858402281948,true⟩,⟨⟨(-943686813980364306470045),(-914015310280011691736205),true⟩,⟨(-788616949418665013102124),(-758945445718312398370408),true⟩⟩⟩
  | 2 => ⟨⟨35012237997258037,40013511528252875,true⟩,⟨951575930078309493094,1005356370808892242980,true⟩,⟨⟨1176836721622405880437540,1226289227789614425278356,true⟩,⟨108495573756245524855400,157948079923454069681516,true⟩⟩⟩
  | 3 => ⟨⟨(-12667324179),62032152952,true⟩,⟨35012237997258037,40013511528252875,true⟩,⟨⟨(-1110408838717622638793595),(-1041175330083558163798145),true⟩,⟨516902083504429575140923,586135592138494050129156,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738142),34359738701,true⟩,⟨(-12667324179),62032152952,true⟩,⟨⟨548741422968247784404667,637755934069168189505296,true⟩,⟨(-1097862676463415669210780),(-1008848165362495264103818),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738142),34359738701,true⟩,⟨⟨31640213503834662869945,140435727071610998102268,true⟩,⟨1151462560582792508406678,1260258074150568843654413,true⟩⟩⟩
theorem shortNegativeR048Q02F_ok : ∀ n : Fin 6, (shortNegativeR048Q02F n).encloses (FactoredFrequency.build shortNegativeR048Q02T (Grid.ofRats (1338306803202083/1649267441664000) (1346896737794083/1649267441664000)) n) := by decide +kernel
def shortNegativeR048Q02L : ℕ → ℚ
  | 0 => (-2875591/1000000)
  | 1 => (-38188/15625)
  | 2 => (-2054201/1000000)
  | 3 => (-901971/500000)
  | 4 => (-86831/50000)
  | 5 => (-949163/500000)
  | 6 => (-2229399/1000000)
  | 7 => (-2672131/1000000)
  | 8 => (-625017/200000)
  | 9 => (-1747719/500000)
  | 10 => (-1800119/500000)
  | 11 => (-3384559/1000000)
  | _ => 0
def shortNegativeR048Q02U : ℕ → ℚ
  | 0 => (-575707/250000)
  | 1 => (-1806921/1000000)
  | 2 => (-1370881/1000000)
  | 3 => (-1089493/1000000)
  | 4 => (-997429/1000000)
  | 5 => (-106829/100000)
  | 6 => (-662701/500000)
  | 7 => (-1716841/1000000)
  | 8 => (-2153603/1000000)
  | 9 => (-1244979/500000)
  | 10 => (-33087/12500)
  | 11 => (-2561883/1000000)
  | _ => 0
private theorem shortNegativeR048Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR048Q02P shortNegativeR048Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR048Q02L (0:Fin 12)) (shortNegativeR048Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR048Q02P shortNegativeR048Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR048Q02L (1:Fin 12)) (shortNegativeR048Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR048Q02P shortNegativeR048Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR048Q02L (2:Fin 12)) (shortNegativeR048Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR048Q02P shortNegativeR048Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR048Q02L (3:Fin 12)) (shortNegativeR048Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR048Q02P shortNegativeR048Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR048Q02L (4:Fin 12)) (shortNegativeR048Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR048Q02P shortNegativeR048Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR048Q02L (5:Fin 12)) (shortNegativeR048Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR048Q02P shortNegativeR048Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR048Q02L (6:Fin 12)) (shortNegativeR048Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR048Q02P shortNegativeR048Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR048Q02L (7:Fin 12)) (shortNegativeR048Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR048Q02P shortNegativeR048Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR048Q02L (8:Fin 12)) (shortNegativeR048Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR048Q02P shortNegativeR048Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR048Q02L (9:Fin 12)) (shortNegativeR048Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR048Q02P shortNegativeR048Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR048Q02L (10:Fin 12)) (shortNegativeR048Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR048Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR048Q02P shortNegativeR048Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR048Q02L (11:Fin 12)) (shortNegativeR048Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR048Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR048Q02P shortNegativeR048Q02F (shortNegativeNodes12 k)).re (shortNegativeR048Q02L k) (shortNegativeR048Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR048Q02Point00
  · exact shortNegativeR048Q02Point01
  · exact shortNegativeR048Q02Point02
  · exact shortNegativeR048Q02Point03
  · exact shortNegativeR048Q02Point04
  · exact shortNegativeR048Q02Point05
  · exact shortNegativeR048Q02Point06
  · exact shortNegativeR048Q02Point07
  · exact shortNegativeR048Q02Point08
  · exact shortNegativeR048Q02Point09
  · exact shortNegativeR048Q02Point10
  · exact shortNegativeR048Q02Point11

theorem shortNegativeR048Q02Bound {t a : ℝ} (tl : ((129/100):ℝ)≤t) (tu : t≤((13/10):ℝ)) (al : ((1338306803202083/1649267441664000):ℝ)≤a) (au : a≤((1346896737794083/1649267441664000):ℝ)) : (((-3463798150121927710045496386322433/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2208077883910523880759177241755649/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR048Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1338306803202083/1649267441664000) (1346896737794083/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR048Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR048Q02F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR048Q02L shortNegativeR048Q02U (-3463798150121927710045496386322433/1298074214633706907132624082305024) (-2208077883910523880759177241755649/1298074214633706907132624082305024) shortNegativeR048Q02Samples (by decide +kernel)

theorem short_original_negative_048 {t a : ℝ} (tb : RealMem negative_048.t t) (ab : RealMem negative_048.a a) : RealMem negative_048.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((129/100):ℝ) ((13/10):ℝ) := by simpa [negative_048,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((129/100):ℝ)<((13/10):ℝ)) tB
  have aB : a∈Icc ((1321126934018083/1649267441664000):ℝ) ((1346896737794083/1649267441664000):ℝ) := by simpa [negative_048,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((1321126934018083/1649267441664000):ℝ)<((1346896737794083/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR048Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_048,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR048Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_048,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR048Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_048,RealMem] using v

def shortNegativeR049Q00T := Grid.ofRats (13/10) (131/100)
def shortNegativeR049Q00P : PrimalThetaParameters := ⟨⟨⟨19727253689954876072229,20356841402706004807173,true⟩,⟨0,0,true⟩⟩, ⟨⟨1537362717650351386796102,1547253218883848071331894,true⟩,⟨0,0,true⟩⟩, ⟨(-723227038335601447456525),(-703446035868676797869230),true⟩, ⟨3630002383204308490090519,3711713002320080143778515,true⟩⟩
theorem shortNegativeR049Q00P_ok : shortNegativeR049Q00P.encloses (primalThetaParameters shortNegativeR049Q00T (Grid.ofRats (1335204847269317/1649267441664000) (1343794781861317/1649267441664000))) := by decide +kernel

def shortNegativeR049Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨432082221581884577311357,435489148873798161400793,true⟩,⟨3356000123333811589648401,3382461865660978332553422,true⟩,⟨⟨346571294123846110768211,356461795357342795352924,true⟩,⟨1151747342989926644422949,1161637844223423329018763,true⟩⟩⟩
  | 1 => ⟨⟨900672415332334059750,951575930147028969886,true⟩,⟨432082221581884577311357,435489148873798161400793,true⟩,⟨⟨(-950508342149509888243261),(-920836838449157273509627),true⟩,⟨(-780354165145009055720831),(-750682661444656440989533),true⟩⟩⟩
  | 2 => ⟨⟨30636123813615513,35012306716734774,true⟩,⟨900672415332334059750,951575930147028969886,true⟩,⟨⟨1178673488378815893456862,1228125994546024438296928,true⟩,⟨90732395700638916877972,140184901867847461703065,true⟩⟩⟩
  | 3 => ⟨⟨(-17355048302),56052152558,true⟩,⟨30636123813615513,35012306716734774,true⟩,⟨⟨(-1098773886734913361814368),(-1029540378100848886819030),true⟩,⟨539030554449473819135384,608264063083538294123972,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738214),34359738595,true⟩,⟨(-17355048302),56052152558,true⟩,⟨⟨520527040096520987091471,609541551197441392192697,true⟩,⟨(-1113262551244298049958279),(-1024248040143377644850123),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738214),34359738595,true⟩,⟨⟨70775977302669691454099,179571490870446026686143,true⟩,⟨1148030275834168613075954,1256825789401944948322826,true⟩⟩⟩
theorem shortNegativeR049Q00F_ok : ∀ n : Fin 6, (shortNegativeR049Q00F n).encloses (FactoredFrequency.build shortNegativeR049Q00T (Grid.ofRats (1335204847269317/1649267441664000) (1343794781861317/1649267441664000)) n) := by decide +kernel
def shortNegativeR049Q00L : ℕ → ℚ
  | 0 => (-575093/200000)
  | 1 => (-2456251/1000000)
  | 2 => (-2078639/1000000)
  | 3 => (-367489/200000)
  | 4 => (-1775271/1000000)
  | 5 => (-387493/200000)
  | 6 => (-2264299/1000000)
  | 7 => (-2697759/1000000)
  | 8 => (-3137471/1000000)
  | 9 => (-436679/125000)
  | 10 => (-1794681/500000)
  | 11 => (-421767/125000)
  | _ => 0
def shortNegativeR049Q00U : ℕ → ℚ
  | 0 => (-2302841/1000000)
  | 1 => (-909433/500000)
  | 2 => (-1394129/1000000)
  | 3 => (-224211/200000)
  | 4 => (-1034483/1000000)
  | 5 => (-276649/250000)
  | 6 => (-17009/12500)
  | 7 => (-174281/100000)
  | 8 => (-542069/250000)
  | 9 => (-498617/200000)
  | 10 => (-660463/250000)
  | 11 => (-2555933/1000000)
  | _ => 0
private theorem shortNegativeR049Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR049Q00P shortNegativeR049Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR049Q00L (0:Fin 12)) (shortNegativeR049Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR049Q00P shortNegativeR049Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR049Q00L (1:Fin 12)) (shortNegativeR049Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR049Q00P shortNegativeR049Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR049Q00L (2:Fin 12)) (shortNegativeR049Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR049Q00P shortNegativeR049Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR049Q00L (3:Fin 12)) (shortNegativeR049Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR049Q00P shortNegativeR049Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR049Q00L (4:Fin 12)) (shortNegativeR049Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR049Q00P shortNegativeR049Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR049Q00L (5:Fin 12)) (shortNegativeR049Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR049Q00P shortNegativeR049Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR049Q00L (6:Fin 12)) (shortNegativeR049Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR049Q00P shortNegativeR049Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR049Q00L (7:Fin 12)) (shortNegativeR049Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR049Q00P shortNegativeR049Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR049Q00L (8:Fin 12)) (shortNegativeR049Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR049Q00P shortNegativeR049Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR049Q00L (9:Fin 12)) (shortNegativeR049Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR049Q00P shortNegativeR049Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR049Q00L (10:Fin 12)) (shortNegativeR049Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR049Q00P shortNegativeR049Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR049Q00L (11:Fin 12)) (shortNegativeR049Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR049Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR049Q00P shortNegativeR049Q00F (shortNegativeNodes12 k)).re (shortNegativeR049Q00L k) (shortNegativeR049Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR049Q00Point00
  · exact shortNegativeR049Q00Point01
  · exact shortNegativeR049Q00Point02
  · exact shortNegativeR049Q00Point03
  · exact shortNegativeR049Q00Point04
  · exact shortNegativeR049Q00Point05
  · exact shortNegativeR049Q00Point06
  · exact shortNegativeR049Q00Point07
  · exact shortNegativeR049Q00Point08
  · exact shortNegativeR049Q00Point09
  · exact shortNegativeR049Q00Point10
  · exact shortNegativeR049Q00Point11

theorem shortNegativeR049Q00Bound {t a : ℝ} (tl : ((13/10):ℝ)≤t) (tu : t≤((131/100):ℝ)) (al : ((1335204847269317/1649267441664000):ℝ)≤a) (au : a≤((1343794781861317/1649267441664000):ℝ)) : (((-3457624392292609630162860642086803/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2238116936857255897002298761228179/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR049Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1335204847269317/1649267441664000) (1343794781861317/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR049Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR049Q00F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR049Q00L shortNegativeR049Q00U (-3457624392292609630162860642086803/1298074214633706907132624082305024) (-2238116936857255897002298761228179/1298074214633706907132624082305024) shortNegativeR049Q00Samples (by decide +kernel)

def shortNegativeR049Q01T := Grid.ofRats (13/10) (131/100)
def shortNegativeR049Q01P : PrimalThetaParameters := ⟨⟨⟨19727253689954876072229,20356841402706004807173,true⟩,⟨0,0,true⟩⟩, ⟨⟨1547253218883779351850229,1557143720117276036386053,true⟩,⟨0,0,true⟩⟩, ⟨(-703446035868745517348209),(-683665033401820867760973),true⟩, ⟨3614494355713511065404638,3695745594616127575928756,true⟩⟩
theorem shortNegativeR049Q01P_ok : shortNegativeR049Q01P.encloses (primalThetaParameters shortNegativeR049Q01T (Grid.ofRats (1343794781861317/1649267441664000) (450794905484439/549755813888000))) := by decide +kernel

def shortNegativeR049Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨432082221581884577311357,435489148873798161400793,true⟩,⟨3356000123333811589648401,3382461865660978332553422,true⟩,⟨⟨337096466654988619479993,346986967888485304064450,true⟩,⟨1154584438945663886657154,1164474940179160571252887,true⟩⟩⟩
  | 1 => ⟨⟨900672415332334059750,951575930147028969886,true⟩,⟨432082221581884577311357,435489148873798161400793,true⟩,⟨⟨(-931439772739671853644346),(-901768269039319238910047),true⟩,⟨(-803086160172374470014692),(-773414656472021855282147),true⟩⟩⟩
  | 2 => ⟨⟨30636123813615513,35012306716734774,true⟩,⟨900672415332334059750,951575930147028969886,true⟩,⟨⟨1172945144022375763328102,1222397650189584308169671,true⟩,⟨139848538075651932351661,189301044242860477179014,true⟩⟩⟩
  | 3 => ⟨⟨(-17355048302),56052152558,true⟩,⟨30636123813615513,35012306716734774,true⟩,⟨⟨(-1129863341555600320365776),(-1060629832921535845370573),true⟩,⟨477180618158806673090489,546414126792871148077657,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738214),34359738595,true⟩,⟨(-17355048302),56052152558,true⟩,⟨⟨597618572116990428916617,686633083217910834017735,true⟩,⟨(-1068800211092620714650356),(-979785699991700309543980),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738214),34359738595,true⟩,⟨⟨(-37795311844380094633295),71000201723396240600022,true⟩,⟨1154414054935758093122379,1263209568503534428371585,true⟩⟩⟩
theorem shortNegativeR049Q01F_ok : ∀ n : Fin 6, (shortNegativeR049Q01F n).encloses (FactoredFrequency.build shortNegativeR049Q01T (Grid.ofRats (1343794781861317/1649267441664000) (450794905484439/549755813888000)) n) := by decide +kernel
def shortNegativeR049Q01L : ℕ → ℚ
  | 0 => (-2884103/1000000)
  | 1 => (-309021/125000)
  | 2 => (-2094887/1000000)
  | 3 => (-1848299/1000000)
  | 4 => (-44427/25000)
  | 5 => (-964039/500000)
  | 6 => (-1121799/500000)
  | 7 => (-166737/62500)
  | 8 => (-620639/200000)
  | 9 => (-3462007/1000000)
  | 10 => (-3568009/1000000)
  | 11 => (-3368613/1000000)
  | _ => 0
def shortNegativeR049Q01U : ℕ → ℚ
  | 0 => (-2318491/1000000)
  | 1 => (-368313/200000)
  | 2 => (-177071/125000)
  | 3 => (-1137541/1000000)
  | 4 => (-130463/125000)
  | 5 => (-276413/250000)
  | 6 => (-1349683/1000000)
  | 7 => (-1721919/1000000)
  | 8 => (-107203/50000)
  | 9 => (-494451/200000)
  | 10 => (-1315823/500000)
  | 11 => (-2559121/1000000)
  | _ => 0
private theorem shortNegativeR049Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR049Q01P shortNegativeR049Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR049Q01L (0:Fin 12)) (shortNegativeR049Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR049Q01P shortNegativeR049Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR049Q01L (1:Fin 12)) (shortNegativeR049Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR049Q01P shortNegativeR049Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR049Q01L (2:Fin 12)) (shortNegativeR049Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR049Q01P shortNegativeR049Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR049Q01L (3:Fin 12)) (shortNegativeR049Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR049Q01P shortNegativeR049Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR049Q01L (4:Fin 12)) (shortNegativeR049Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR049Q01P shortNegativeR049Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR049Q01L (5:Fin 12)) (shortNegativeR049Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR049Q01P shortNegativeR049Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR049Q01L (6:Fin 12)) (shortNegativeR049Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR049Q01P shortNegativeR049Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR049Q01L (7:Fin 12)) (shortNegativeR049Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR049Q01P shortNegativeR049Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR049Q01L (8:Fin 12)) (shortNegativeR049Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR049Q01P shortNegativeR049Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR049Q01L (9:Fin 12)) (shortNegativeR049Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR049Q01P shortNegativeR049Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR049Q01L (10:Fin 12)) (shortNegativeR049Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR049Q01P shortNegativeR049Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR049Q01L (11:Fin 12)) (shortNegativeR049Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR049Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR049Q01P shortNegativeR049Q01F (shortNegativeNodes12 k)).re (shortNegativeR049Q01L k) (shortNegativeR049Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR049Q01Point00
  · exact shortNegativeR049Q01Point01
  · exact shortNegativeR049Q01Point02
  · exact shortNegativeR049Q01Point03
  · exact shortNegativeR049Q01Point04
  · exact shortNegativeR049Q01Point05
  · exact shortNegativeR049Q01Point06
  · exact shortNegativeR049Q01Point07
  · exact shortNegativeR049Q01Point08
  · exact shortNegativeR049Q01Point09
  · exact shortNegativeR049Q01Point10
  · exact shortNegativeR049Q01Point11

theorem shortNegativeR049Q01Bound {t a : ℝ} (tl : ((13/10):ℝ)≤t) (tu : t≤((131/100):ℝ)) (al : ((1343794781861317/1649267441664000):ℝ)≤a) (au : a≤((450794905484439/549755813888000):ℝ)) : (((-3457624392292609630162860642086803/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2238116936857255897002298761228179/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR049Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1343794781861317/1649267441664000) (450794905484439/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR049Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR049Q01F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR049Q01L shortNegativeR049Q01U (-3457624392292609630162860642086803/1298074214633706907132624082305024) (-2238116936857255897002298761228179/1298074214633706907132624082305024) shortNegativeR049Q01Samples (by decide +kernel)

def shortNegativeR049Q02T := Grid.ofRats (13/10) (131/100)
def shortNegativeR049Q02P : PrimalThetaParameters := ⟨⟨⟨19727253689954876072229,20356841402706004807173,true⟩,⟨0,0,true⟩⟩, ⟨⟨1557143720117207316904357,1567034221350704001440211,true⟩,⟨0,0,true⟩⟩, ⟨(-683665033401889587239890),(-663884030934964937652720),true⟩, ⟨3599521465828908039488770,3680328770936917503594968,true⟩⟩
theorem shortNegativeR049Q02P_ok : shortNegativeR049Q02P.encloses (primalThetaParameters shortNegativeR049Q02T (Grid.ofRats (450794905484439/549755813888000) (1360974651045317/1649267441664000))) := by decide +kernel

def shortNegativeR049Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨432082221581884577311357,435489148873798161400793,true⟩,⟨3356000123333811589648401,3382461865660978332553422,true⟩,⟨⟨327598745593406159456884,337489246826902844041556,true⟩,⟨1157343925068667591783916,1167234426302164276380037,true⟩⟩⟩
  | 1 => ⟨⟨900672415332334059750,951575930147028969886,true⟩,⟨432082221581884577311357,435489148873798161400793,true⟩,⟨⟨(-911819075341681913986633),(-882147571641329299252322),true⟩,⟨(-825343342628347813298892),(-795671838927995198565763),true⟩⟩⟩
  | 2 => ⟨⟨30636123813615513,35012306716734774,true⟩,⟨900672415332334059750,951575930147028969886,true⟩,⟨⟨1165212999431559530401831,1214665505598768075245107,true⟩,⟨188689333635257837883229,238141839802466382713066,true⟩⟩⟩
  | 3 => ⟨⟨(-17355048302),56052152558,true⟩,⟨30636123813615513,35012306716734774,true⟩,⟨⟨(-1157361703925600428877972),(-1088128195291535953883922),true⟩,⟨413652601605672555693222,482886110239737030677991,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738214),34359738595,true⟩,⟨(-17355048302),56052152558,true⟩,⟨⟨671230368641866154567636,760244879742786559666904,true⟩,⟨(-1018787138667435538581776),(-929772627566515133478952),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738214),34359738595,true⟩,⟨⟨(-146500970766171180235798),(-37705457198394845000129),true⟩,⟨1151014469512591996446303,1259809983080368331697294,true⟩⟩⟩
theorem shortNegativeR049Q02F_ok : ∀ n : Fin 6, (shortNegativeR049Q02F n).encloses (FactoredFrequency.build shortNegativeR049Q02T (Grid.ofRats (450794905484439/549755813888000) (1360974651045317/1649267441664000)) n) := by decide +kernel
def shortNegativeR049Q02L : ℕ → ℚ
  | 0 => (-2892467/1000000)
  | 1 => (-1243977/500000)
  | 2 => (-2639/1250)
  | 3 => (-929693/500000)
  | 4 => (-1779249/1000000)
  | 5 => (-191913/100000)
  | 6 => (-1111687/500000)
  | 7 => (-263827/100000)
  | 8 => (-122769/40000)
  | 9 => (-3430631/1000000)
  | 10 => (-1773361/500000)
  | 11 => (-1681367/500000)
  | _ => 0
def shortNegativeR049Q02U : ℕ → ℚ
  | 0 => (-291727/125000)
  | 1 => (-1864141/1000000)
  | 2 => (-1439129/1000000)
  | 3 => (-23087/20000)
  | 4 => (-1053319/1000000)
  | 5 => (-552597/500000)
  | 6 => (-334793/250000)
  | 7 => (-1701581/1000000)
  | 8 => (-33129/15625)
  | 9 => (-2451607/1000000)
  | 10 => (-655273/250000)
  | 11 => (-2562029/1000000)
  | _ => 0
private theorem shortNegativeR049Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR049Q02P shortNegativeR049Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR049Q02L (0:Fin 12)) (shortNegativeR049Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR049Q02P shortNegativeR049Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR049Q02L (1:Fin 12)) (shortNegativeR049Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR049Q02P shortNegativeR049Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR049Q02L (2:Fin 12)) (shortNegativeR049Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR049Q02P shortNegativeR049Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR049Q02L (3:Fin 12)) (shortNegativeR049Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR049Q02P shortNegativeR049Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR049Q02L (4:Fin 12)) (shortNegativeR049Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR049Q02P shortNegativeR049Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR049Q02L (5:Fin 12)) (shortNegativeR049Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR049Q02P shortNegativeR049Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR049Q02L (6:Fin 12)) (shortNegativeR049Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR049Q02P shortNegativeR049Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR049Q02L (7:Fin 12)) (shortNegativeR049Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR049Q02P shortNegativeR049Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR049Q02L (8:Fin 12)) (shortNegativeR049Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR049Q02P shortNegativeR049Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR049Q02L (9:Fin 12)) (shortNegativeR049Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR049Q02P shortNegativeR049Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR049Q02L (10:Fin 12)) (shortNegativeR049Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR049Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR049Q02P shortNegativeR049Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR049Q02L (11:Fin 12)) (shortNegativeR049Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR049Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR049Q02P shortNegativeR049Q02F (shortNegativeNodes12 k)).re (shortNegativeR049Q02L k) (shortNegativeR049Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR049Q02Point00
  · exact shortNegativeR049Q02Point01
  · exact shortNegativeR049Q02Point02
  · exact shortNegativeR049Q02Point03
  · exact shortNegativeR049Q02Point04
  · exact shortNegativeR049Q02Point05
  · exact shortNegativeR049Q02Point06
  · exact shortNegativeR049Q02Point07
  · exact shortNegativeR049Q02Point08
  · exact shortNegativeR049Q02Point09
  · exact shortNegativeR049Q02Point10
  · exact shortNegativeR049Q02Point11

theorem shortNegativeR049Q02Bound {t a : ℝ} (tl : ((13/10):ℝ)≤t) (tu : t≤((131/100):ℝ)) (al : ((450794905484439/549755813888000):ℝ)≤a) (au : a≤((1360974651045317/1649267441664000):ℝ)) : (((-3457624392292609630162860642086803/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2238116936857255897002298761228179/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR049Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (450794905484439/549755813888000) (1360974651045317/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR049Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR049Q02F_ok n) ts asb
  exact factored_negative_12_samples 350 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip048Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR049Q02L shortNegativeR049Q02U (-3457624392292609630162860642086803/1298074214633706907132624082305024) (-2238116936857255897002298761228179/1298074214633706907132624082305024) shortNegativeR049Q02Samples (by decide +kernel)

theorem short_original_negative_049 {t a : ℝ} (tb : RealMem negative_049.t t) (ab : RealMem negative_049.a a) : RealMem negative_049.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((13/10):ℝ) ((131/100):ℝ) := by simpa [negative_049,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((13/10):ℝ)<((131/100):ℝ)) tB
  have aB : a∈Icc ((1335204847269317/1649267441664000):ℝ) ((1360974651045317/1649267441664000):ℝ) := by simpa [negative_049,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((1335204847269317/1649267441664000):ℝ)<((1360974651045317/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR049Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_049,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR049Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_049,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR049Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_049,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_048
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_049
