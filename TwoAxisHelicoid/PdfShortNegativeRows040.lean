import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip040

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR040Q00T := Grid.ofRats (121/100) (61/50)
def shortNegativeR040Q00P : PrimalThetaParameters := ⟨⟨⟨26173421637065243152064,27008736320086306718059,true⟩,⟨0,0,true⟩⟩, ⟨⟨1418851237116628090190338,1423796487733410792198673,true⟩,⟨0,0,true⟩⟩, ⟨(-960249999403048040668810),(-950359498169551356134884),true⟩, ⟨4021966494803245150009937,4080156723194161720920261,true⟩⟩
theorem shortNegativeR040Q00P_ok : shortNegativeR040Q00P.encloses (primalThetaParameters shortNegativeR040Q00T (Grid.ofRats (1232277215781329/1649267441664000) (412190727692443/549755813888000))) := by decide +kernel

def shortNegativeR040Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨463729650472305673072323,467386114736161189905697,true⟩,⟨3126968455526347712036974,3151624304898943865789397,true⟩,⟨⟨462848848372407023484451,467794098989189725541427,true⟩,⟨1113313000814491172924319,1118258251431273874990286,true⟩⟩⟩
  | 1 => ⟨⟨1477257275828043941217,1560747772821603640747,true⟩,⟨463729650472305673072323,467386114736161189905697,true⟩,⟨⟨(-1127629472430542043685983),(-1112793720580331376539297),true⟩,⟨(-461980980879349914771799),(-447145229029139247634267),true⟩⟩⟩
  | 2 => ⟨⟨101884498475068325,116437904682532705,true⟩,⟨1477257275828043941217,1560747772821603640747,true⟩,⟨⟨1098893209999559691505679,1123619463083198323715971,true⟩,⟨(-488399881244159833958965),(-463673628160521201757426),true⟩⟩⟩
  | 3 => ⟨⟨117772490304,228430627228,true⟩,⟨101884498475068325,116437904682532705,true⟩,⟨⟨(-461071021881569212503247),(-426454267564502615199984),true⟩,⟨1107225460695766007891156,1141842215012832605203784,true⟩⟩⟩
  | 4 => ⟨⟨(-34359733450),34359745595,true⟩,⟨117772490304,228430627228,true⟩,⟨⟨(-508961583583584527425865),(-464454328033089965059756),true⟩,⟨(-1128877774938037397580242),(-1084370519387542835205600),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359733450),34359745595,true⟩,⟨⟨1101553071547838246313288,1155950828331760773715714,true⟩,⟨405722214693145019306815,460119971477067546699674,true⟩⟩⟩
theorem shortNegativeR040Q00F_ok : ∀ n : Fin 6, (shortNegativeR040Q00F n).encloses (FactoredFrequency.build shortNegativeR040Q00T (Grid.ofRats (1232277215781329/1649267441664000) (412190727692443/549755813888000)) n) := by decide +kernel
def shortNegativeR040Q00L : ℕ → ℚ
  | 0 => (-2514493/1000000)
  | 1 => (-230733/125000)
  | 2 => (-687813/500000)
  | 3 => (-1191867/1000000)
  | 4 => (-639011/500000)
  | 5 => (-1644367/1000000)
  | 6 => (-55201/25000)
  | 7 => (-179643/62500)
  | 8 => (-140809/40000)
  | 9 => (-983851/250000)
  | 10 => (-3887051/1000000)
  | 11 => (-3344953/1000000)
  | _ => 0
def shortNegativeR040Q00U : ℕ → ℚ
  | 0 => (-973399/500000)
  | 1 => (-621493/500000)
  | 2 => (-371709/500000)
  | 3 => (-65293/125000)
  | 4 => (-9058/15625)
  | 5 => (-426909/500000)
  | 6 => (-1341993/1000000)
  | 7 => (-394943/200000)
  | 8 => (-26009/10000)
  | 9 => (-1479521/500000)
  | 10 => (-2944731/1000000)
  | 11 => (-2552353/1000000)
  | _ => 0
private theorem shortNegativeR040Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR040Q00P shortNegativeR040Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR040Q00L (0:Fin 12)) (shortNegativeR040Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR040Q00P shortNegativeR040Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR040Q00L (1:Fin 12)) (shortNegativeR040Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR040Q00P shortNegativeR040Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR040Q00L (2:Fin 12)) (shortNegativeR040Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR040Q00P shortNegativeR040Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR040Q00L (3:Fin 12)) (shortNegativeR040Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR040Q00P shortNegativeR040Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR040Q00L (4:Fin 12)) (shortNegativeR040Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR040Q00P shortNegativeR040Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR040Q00L (5:Fin 12)) (shortNegativeR040Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR040Q00P shortNegativeR040Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR040Q00L (6:Fin 12)) (shortNegativeR040Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR040Q00P shortNegativeR040Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR040Q00L (7:Fin 12)) (shortNegativeR040Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR040Q00P shortNegativeR040Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR040Q00L (8:Fin 12)) (shortNegativeR040Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR040Q00P shortNegativeR040Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR040Q00L (9:Fin 12)) (shortNegativeR040Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR040Q00P shortNegativeR040Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR040Q00L (10:Fin 12)) (shortNegativeR040Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR040Q00P shortNegativeR040Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR040Q00L (11:Fin 12)) (shortNegativeR040Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR040Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR040Q00P shortNegativeR040Q00F (shortNegativeNodes12 k)).re (shortNegativeR040Q00L k) (shortNegativeR040Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR040Q00Point00
  · exact shortNegativeR040Q00Point01
  · exact shortNegativeR040Q00Point02
  · exact shortNegativeR040Q00Point03
  · exact shortNegativeR040Q00Point04
  · exact shortNegativeR040Q00Point05
  · exact shortNegativeR040Q00Point06
  · exact shortNegativeR040Q00Point07
  · exact shortNegativeR040Q00Point08
  · exact shortNegativeR040Q00Point09
  · exact shortNegativeR040Q00Point10
  · exact shortNegativeR040Q00Point11

theorem shortNegativeR040Q00Bound {t a : ℝ} (tl : ((121/100):ℝ)≤t) (tu : t≤((61/50):ℝ)) (al : ((1232277215781329/1649267441664000):ℝ)≤a) (au : a≤((412190727692443/549755813888000):ℝ)) : (((-3251315034287144084312079227942651/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2104503016930792873644647021803259/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR040Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1232277215781329/1649267441664000) (412190727692443/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR040Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR040Q00F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR040Q00L shortNegativeR040Q00U (-3251315034287144084312079227942651/1298074214633706907132624082305024) (-2104503016930792873644647021803259/1298074214633706907132624082305024) shortNegativeR040Q00Samples (by decide +kernel)

def shortNegativeR040Q01T := Grid.ofRats (121/100) (61/50)
def shortNegativeR040Q01P : PrimalThetaParameters := ⟨⟨⟨26173421637065243152064,27008736320086306718059,true⟩,⟨0,0,true⟩⟩, ⟨⟨1423796487733342072717402,1428741738350124774725753,true⟩,⟨0,0,true⟩⟩, ⟨(-950359498169620075614650),(-940468996936123391080756),true⟩, ⟨4010409229813345496169770,4068431239380992969155139,true⟩⟩
theorem shortNegativeR040Q01P_ok : shortNegativeR040Q01P.encloses (primalThetaParameters shortNegativeR040Q01T (Grid.ofRats (412190727692443/549755813888000) (1240867150373329/1649267441664000))) := by decide +kernel

def shortNegativeR040Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨463729650472305673072323,467386114736161189905697,true⟩,⟨3126968455526347712036974,3151624304898943865789397,true⟩,⟨⟨458280718059769466259018,463225968676552168316017,true⟩,⟨1115207111425689649553285,1120152362042472351619375,true⟩⟩⟩
  | 1 => ⟨⟨1477257275828043941217,1560747772821603640747,true⟩,⟨463729650472305673072323,467386114736161189905697,true⟩,⟨⟨(-1121966934011834489306381),(-1107131182161623822159284),true⟩,⟨(-475693472608178021477898),(-460857720757967354339689),true⟩⟩⟩
  | 2 => ⟨⟨101884498475068325,116437904682532705,true⟩,⟨1477257275828043941217,1560747772821603640747,true⟩,⟨⟨1108396520736881243573809,1133122773820519875783764,true⟩,⟨(-465573287904763193505929),(-440847034821124561305171),true⟩⟩⟩
  | 3 => ⟨⟨117772490304,228430627228,true⟩,⟨101884498475068325,116437904682532705,true⟩,⟨⟨(-493084956784676907502363),(-458468202467610310198592),true⟩,⟨1094059376382188589266545,1128676130699255186579062,true⟩⟩⟩
  | 4 => ⟨⟨(-34359733450),34359745595,true⟩,⟨117772490304,228430627228,true⟩,⟨⟨(-467900021074843987107719),(-423392765524349424741810),true⟩,⟨(-1146042277597785792491836),(-1101535022047291230116593),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359733450),34359745595,true⟩,⟨⟨1080937089207743035154158,1135334845991665562558800,true⟩,⟨456057073090035512951389,510454829873958040347431,true⟩⟩⟩
theorem shortNegativeR040Q01F_ok : ∀ n : Fin 6, (shortNegativeR040Q01F n).encloses (FactoredFrequency.build shortNegativeR040Q01T (Grid.ofRats (412190727692443/549755813888000) (1240867150373329/1649267441664000)) n) := by decide +kernel
def shortNegativeR040Q01L : ℕ → ℚ
  | 0 => (-2526797/1000000)
  | 1 => (-1860959/1000000)
  | 2 => (-86721/62500)
  | 3 => (-1198431/1000000)
  | 4 => (-1277763/1000000)
  | 5 => (-1636549/1000000)
  | 6 => (-548239/250000)
  | 7 => (-2854227/1000000)
  | 8 => (-3498739/1000000)
  | 9 => (-1958901/500000)
  | 10 => (-3879151/1000000)
  | 11 => (-837237/250000)
  | _ => 0
def shortNegativeR040Q01U : ℕ → ℚ
  | 0 => (-1962247/1000000)
  | 1 => (-1260589/1000000)
  | 2 => (-759317/1000000)
  | 3 => (-106529/200000)
  | 4 => (-11663/20000)
  | 5 => (-850189/1000000)
  | 6 => (-1331687/1000000)
  | 7 => (-979687/500000)
  | 8 => (-2583411/1000000)
  | 9 => (-2946077/1000000)
  | 10 => (-2941159/1000000)
  | 11 => (-102383/40000)
  | _ => 0
private theorem shortNegativeR040Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR040Q01P shortNegativeR040Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR040Q01L (0:Fin 12)) (shortNegativeR040Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR040Q01P shortNegativeR040Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR040Q01L (1:Fin 12)) (shortNegativeR040Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR040Q01P shortNegativeR040Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR040Q01L (2:Fin 12)) (shortNegativeR040Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR040Q01P shortNegativeR040Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR040Q01L (3:Fin 12)) (shortNegativeR040Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR040Q01P shortNegativeR040Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR040Q01L (4:Fin 12)) (shortNegativeR040Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR040Q01P shortNegativeR040Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR040Q01L (5:Fin 12)) (shortNegativeR040Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR040Q01P shortNegativeR040Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR040Q01L (6:Fin 12)) (shortNegativeR040Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR040Q01P shortNegativeR040Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR040Q01L (7:Fin 12)) (shortNegativeR040Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR040Q01P shortNegativeR040Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR040Q01L (8:Fin 12)) (shortNegativeR040Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR040Q01P shortNegativeR040Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR040Q01L (9:Fin 12)) (shortNegativeR040Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR040Q01P shortNegativeR040Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR040Q01L (10:Fin 12)) (shortNegativeR040Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR040Q01P shortNegativeR040Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR040Q01L (11:Fin 12)) (shortNegativeR040Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR040Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR040Q01P shortNegativeR040Q01F (shortNegativeNodes12 k)).re (shortNegativeR040Q01L k) (shortNegativeR040Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR040Q01Point00
  · exact shortNegativeR040Q01Point01
  · exact shortNegativeR040Q01Point02
  · exact shortNegativeR040Q01Point03
  · exact shortNegativeR040Q01Point04
  · exact shortNegativeR040Q01Point05
  · exact shortNegativeR040Q01Point06
  · exact shortNegativeR040Q01Point07
  · exact shortNegativeR040Q01Point08
  · exact shortNegativeR040Q01Point09
  · exact shortNegativeR040Q01Point10
  · exact shortNegativeR040Q01Point11

theorem shortNegativeR040Q01Bound {t a : ℝ} (tl : ((121/100):ℝ)≤t) (tu : t≤((61/50):ℝ)) (al : ((412190727692443/549755813888000):ℝ)≤a) (au : a≤((1240867150373329/1649267441664000):ℝ)) : (((-3251315034287144084312079227942651/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2104503016930792873644647021803259/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR040Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (412190727692443/549755813888000) (1240867150373329/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR040Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR040Q01F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR040Q01L shortNegativeR040Q01U (-3251315034287144084312079227942651/1298074214633706907132624082305024) (-2104503016930792873644647021803259/1298074214633706907132624082305024) shortNegativeR040Q01Samples (by decide +kernel)

def shortNegativeR040Q02T := Grid.ofRats (121/100) (61/50)
def shortNegativeR040Q02P : PrimalThetaParameters := ⟨⟨⟨26173421637065243152064,27008736320086306718059,true⟩,⟨0,0,true⟩⟩, ⟨⟨1428741738350056055244466,1433686988966838757252831,true⟩,⟨0,0,true⟩⟩, ⟨(-940468996936192110560490),(-930578495702695426026631),true⟩, ⟨3999025344439958179418355,4056881800116820522917555,true⟩⟩
theorem shortNegativeR040Q02P_ok : shortNegativeR040Q02P.encloses (primalThetaParameters shortNegativeR040Q02T (Grid.ofRats (1240867150373329/1649267441664000) (1245162117669329/1649267441664000))) := by decide +kernel

def shortNegativeR040Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨463729650472305673072323,467386114736161189905697,true⟩,⟨3126968455526347712036974,3151624304898943865789397,true⟩,⟨⟨453704877910156080675572,458650128526938782732376,true⟩,⟨1117082519777457051184565,1122027770394239753250519,true⟩⟩⟩
  | 1 => ⟨⟨1477257275828043941217,1560747772821603640747,true⟩,⟨463729650472305673072323,467386114736161189905697,true⟩,⟨⟨(-1116136548604612705054957),(-1101300796754402037907717),true⟩,⟨(-489335443754598672009641),(-474499691904388004871017),true⟩⟩⟩
  | 2 => ⟨⟨101884498475068325,116437904682532705,true⟩,⟨1477257275828043941217,1560747772821603640747,true⟩,⟨⟨1117431002266561524857807,1142157255350200157067006,true⟩,⟨(-442557110508372106080757),(-417830857424733473881192),true⟩⟩⟩
  | 3 => ⟨⟨117772490304,228430627228,true⟩,⟨101884498475068325,116437904682532705,true⟩,⟨⟨(-524708817896919669665115),(-490092063579853072360661),true⟩,⟨1079982117682916687452517,1114598871999983284765086,true⟩⟩⟩
  | 4 => ⟨⟨(-34359733450),34359745595,true⟩,⟨117772490304,228430627228,true⟩,⟨⟨(-426234504837610913894619),(-381727249287116351529056),true⟩,⟨(-1161683787240418871363852),(-1117176531689924308988166),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359733450),34359745595,true⟩,⟨⟨1058077832215537168568981,1112475588999459695974780,true⟩,⟨505413643751361065100824,559811400535283592499017,true⟩⟩⟩
theorem shortNegativeR040Q02F_ok : ∀ n : Fin 6, (shortNegativeR040Q02F n).encloses (FactoredFrequency.build shortNegativeR040Q02T (Grid.ofRats (1240867150373329/1649267441664000) (1245162117669329/1649267441664000)) n) := by decide +kernel
def shortNegativeR040Q02L : ℕ → ℚ
  | 0 => (-2538981/1000000)
  | 1 => (-469001/250000)
  | 2 => (-56003/40000)
  | 3 => (-602541/500000)
  | 4 => (-10221/8000)
  | 5 => (-1628881/1000000)
  | 6 => (-1089019/500000)
  | 7 => (-283469/100000)
  | 8 => (-3477343/1000000)
  | 9 => (-1950093/500000)
  | 10 => (-3871127/1000000)
  | 11 => (-419097/125000)
  | _ => 0
def shortNegativeR040Q02U : ℕ → ℚ
  | 0 => (-988787/500000)
  | 1 => (-319539/250000)
  | 2 => (-19381/25000)
  | 3 => (-543029/1000000)
  | 4 => (-586709/1000000)
  | 5 => (-846711/1000000)
  | 6 => (-330387/250000)
  | 7 => (-1944189/1000000)
  | 8 => (-2566031/1000000)
  | 9 => (-2933133/1000000)
  | 10 => (-587501/200000)
  | 11 => (-1283331/500000)
  | _ => 0
private theorem shortNegativeR040Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR040Q02P shortNegativeR040Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR040Q02L (0:Fin 12)) (shortNegativeR040Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR040Q02P shortNegativeR040Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR040Q02L (1:Fin 12)) (shortNegativeR040Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR040Q02P shortNegativeR040Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR040Q02L (2:Fin 12)) (shortNegativeR040Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR040Q02P shortNegativeR040Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR040Q02L (3:Fin 12)) (shortNegativeR040Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR040Q02P shortNegativeR040Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR040Q02L (4:Fin 12)) (shortNegativeR040Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR040Q02P shortNegativeR040Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR040Q02L (5:Fin 12)) (shortNegativeR040Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR040Q02P shortNegativeR040Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR040Q02L (6:Fin 12)) (shortNegativeR040Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR040Q02P shortNegativeR040Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR040Q02L (7:Fin 12)) (shortNegativeR040Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR040Q02P shortNegativeR040Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR040Q02L (8:Fin 12)) (shortNegativeR040Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR040Q02P shortNegativeR040Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR040Q02L (9:Fin 12)) (shortNegativeR040Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR040Q02P shortNegativeR040Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR040Q02L (10:Fin 12)) (shortNegativeR040Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR040Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR040Q02P shortNegativeR040Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR040Q02L (11:Fin 12)) (shortNegativeR040Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR040Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR040Q02P shortNegativeR040Q02F (shortNegativeNodes12 k)).re (shortNegativeR040Q02L k) (shortNegativeR040Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR040Q02Point00
  · exact shortNegativeR040Q02Point01
  · exact shortNegativeR040Q02Point02
  · exact shortNegativeR040Q02Point03
  · exact shortNegativeR040Q02Point04
  · exact shortNegativeR040Q02Point05
  · exact shortNegativeR040Q02Point06
  · exact shortNegativeR040Q02Point07
  · exact shortNegativeR040Q02Point08
  · exact shortNegativeR040Q02Point09
  · exact shortNegativeR040Q02Point10
  · exact shortNegativeR040Q02Point11

theorem shortNegativeR040Q02Bound {t a : ℝ} (tl : ((121/100):ℝ)≤t) (tu : t≤((61/50):ℝ)) (al : ((1240867150373329/1649267441664000):ℝ)≤a) (au : a≤((1245162117669329/1649267441664000):ℝ)) : (((-3251315034287144084312079227942651/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2104503016930792873644647021803259/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR040Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1240867150373329/1649267441664000) (1245162117669329/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR040Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR040Q02F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR040Q02L shortNegativeR040Q02U (-3251315034287144084312079227942651/1298074214633706907132624082305024) (-2104503016930792873644647021803259/1298074214633706907132624082305024) shortNegativeR040Q02Samples (by decide +kernel)

theorem short_original_negative_040 {t a : ℝ} (tb : RealMem negative_040.t t) (ab : RealMem negative_040.a a) : RealMem negative_040.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((121/100):ℝ) ((61/50):ℝ) := by simpa [negative_040,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((121/100):ℝ)<((61/50):ℝ)) tB
  have aB : a∈Icc ((1232277215781329/1649267441664000):ℝ) ((1245162117669329/1649267441664000):ℝ) := by simpa [negative_040,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((1232277215781329/1649267441664000):ℝ)<((1245162117669329/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR040Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_040,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR040Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_040,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR040Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_040,RealMem] using v

def shortNegativeR041Q00T := Grid.ofRats (61/50) (123/100)
def shortNegativeR041Q00P : PrimalThetaParameters := ⟨⟨⟨25363941210528581420977,26173421637133962629238,true⟩,⟨0,0,true⟩⟩, ⟨⟨1431081177765396992590618,1436026428382179694598991,true⟩,⟨0,0,true⟩⟩, ⟨(-935790118105510235868170),(-925899616872013551334326),true⟩, ⟨3976407044323345075534023,4033269870577468835627280,true⟩⟩
theorem shortNegativeR041Q00P_ok : shortNegativeR041Q00P.encloses (primalThetaParameters shortNegativeR041Q00T (Grid.ofRats (1242898961611753/1649267441664000) (1247193928907753/1649267441664000))) := by decide +kernel

def shortNegativeR041Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨460101791531806877352917,463729650472374392566223,true⟩,⟨3151624304898875146196183,3176474563302750903325939,true⟩,⟨⟨451537530380363372476140,456482780997146074533338,true⟩,⟨1117963189837829157884652,1122908440454611859951066,true⟩⟩⟩
  | 1 => ⟨⟨1398233011819434810881,1477257275896763418037,true⟩,⟨460101791531806877352917,463729650472374392566223,true⟩,⟨⟨(-1113320148537306811462671),(-1098484396687096144315209),true⟩,⟨(-495763860614312052546370),(-480928108764101385407397),true⟩⟩⟩
  | 2 => ⟨⟨89150153652028143,101884567194545062,true⟩,⟨1398233011819434810881,1477257275896763418037,true⟩,⟨⟨1121540478222505760154237,1146266731306144392363811,true⟩,⟨(-431605601051943569594106),(-406879347968304937394376),true⟩⟩⟩
  | 3 => ⟨⟨84896761856,186491967041,true⟩,⟨89150153652028143,101884567194545062,true⟩,⟨⟨(-539525678602044543348439),(-504908924284977946045029),true⟩,⟨1073008424236345613934251,1107625178553412211245478,true⟩⟩⟩
  | 4 => ⟨⟨(-34359735021),34359743287,true⟩,⟨84896761856,186491967041,true⟩,⟨⟨(-406329639772152924845073),(-361822384221658362479817),true⟩,⟨(-1168546458747968540092203),(-1124039203197473977716457),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359735021),34359743287,true⟩,⟨⟨1046495347924178909975416,1100893104708101437381889,true⟩,⟨528393009333451879714073,582790766117374407113407,true⟩⟩⟩
theorem shortNegativeR041Q00F_ok : ∀ n : Fin 6, (shortNegativeR041Q00F n).encloses (FactoredFrequency.build shortNegativeR041Q00T (Grid.ofRats (1242898961611753/1649267441664000) (1247193928907753/1649267441664000)) n) := by decide +kernel
def shortNegativeR041Q00L : ℕ → ℚ
  | 0 => (-513037/200000)
  | 1 => (-962047/500000)
  | 2 => (-364803/250000)
  | 3 => (-631861/500000)
  | 4 => (-332659/250000)
  | 5 => (-835101/500000)
  | 6 => (-55059/25000)
  | 7 => (-2840867/1000000)
  | 8 => (-432701/125000)
  | 9 => (-1935117/500000)
  | 10 => (-1922571/500000)
  | 11 => (-418667/125000)
  | _ => 0
def shortNegativeR041Q00U : ℕ → ℚ
  | 0 => (-250973/125000)
  | 1 => (-664347/500000)
  | 2 => (-836991/1000000)
  | 3 => (-604947/1000000)
  | 4 => (-2571/4000)
  | 5 => (-446413/500000)
  | 6 => (-270641/200000)
  | 7 => (-978681/500000)
  | 8 => (-2557709/1000000)
  | 9 => (-2914879/1000000)
  | 10 => (-1461861/500000)
  | 11 => (-642997/250000)
  | _ => 0
private theorem shortNegativeR041Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR041Q00P shortNegativeR041Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR041Q00L (0:Fin 12)) (shortNegativeR041Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR041Q00P shortNegativeR041Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR041Q00L (1:Fin 12)) (shortNegativeR041Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR041Q00P shortNegativeR041Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR041Q00L (2:Fin 12)) (shortNegativeR041Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR041Q00P shortNegativeR041Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR041Q00L (3:Fin 12)) (shortNegativeR041Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR041Q00P shortNegativeR041Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR041Q00L (4:Fin 12)) (shortNegativeR041Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR041Q00P shortNegativeR041Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR041Q00L (5:Fin 12)) (shortNegativeR041Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR041Q00P shortNegativeR041Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR041Q00L (6:Fin 12)) (shortNegativeR041Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR041Q00P shortNegativeR041Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR041Q00L (7:Fin 12)) (shortNegativeR041Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR041Q00P shortNegativeR041Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR041Q00L (8:Fin 12)) (shortNegativeR041Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR041Q00P shortNegativeR041Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR041Q00L (9:Fin 12)) (shortNegativeR041Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR041Q00P shortNegativeR041Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR041Q00L (10:Fin 12)) (shortNegativeR041Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR041Q00P shortNegativeR041Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR041Q00L (11:Fin 12)) (shortNegativeR041Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR041Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR041Q00P shortNegativeR041Q00F (shortNegativeNodes12 k)).re (shortNegativeR041Q00L k) (shortNegativeR041Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR041Q00Point00
  · exact shortNegativeR041Q00Point01
  · exact shortNegativeR041Q00Point02
  · exact shortNegativeR041Q00Point03
  · exact shortNegativeR041Q00Point04
  · exact shortNegativeR041Q00Point05
  · exact shortNegativeR041Q00Point06
  · exact shortNegativeR041Q00Point07
  · exact shortNegativeR041Q00Point08
  · exact shortNegativeR041Q00Point09
  · exact shortNegativeR041Q00Point10
  · exact shortNegativeR041Q00Point11

theorem shortNegativeR041Q00Bound {t a : ℝ} (tl : ((61/50):ℝ)≤t) (tu : t≤((123/100):ℝ)) (al : ((1242898961611753/1649267441664000):ℝ)≤a) (au : a≤((1247193928907753/1649267441664000):ℝ)) : (((-3260083281583129841281727374737523/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2149169948926785881109925954240627/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR041Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1242898961611753/1649267441664000) (1247193928907753/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR041Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR041Q00F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR041Q00L shortNegativeR041Q00U (-3260083281583129841281727374737523/1298074214633706907132624082305024) (-2149169948926785881109925954240627/1298074214633706907132624082305024) shortNegativeR041Q00Samples (by decide +kernel)

def shortNegativeR041Q01T := Grid.ofRats (61/50) (123/100)
def shortNegativeR041Q01P : PrimalThetaParameters := ⟨⟨⟨25363941210528581420977,26173421637133962629238,true⟩,⟨0,0,true⟩⟩, ⟨⟨1436026428382110975117681,1440971678998893677126071,true⟩,⟨0,0,true⟩⟩, ⟨(-925899616872082270814014),(-916009115638585586280198),true⟩, ⟨3965261579278807657975978,4021962533937907784110226,true⟩⟩
theorem shortNegativeR041Q01P_ok : shortNegativeR041Q01P.encloses (primalThetaParameters shortNegativeR041Q01T (Grid.ofRats (1247193928907753/1649267441664000) (417162965401251/549755813888000))) := by decide +kernel

def shortNegativeR041Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨460101791531806877352917,463729650472374392566223,true⟩,⟨3151624304898875146196183,3176474563302750903325939,true⟩,⟨⟨446950472622555644002197,451895723239338346059322,true⟩,⟨1119810991420042114980766,1124756242036824817047224,true⟩⟩⟩
  | 1 => ⟨⟨1398233011819434810881,1477257275896763418037,true⟩,⟨460101791531806877352917,463729650472374392566223,true⟩,⟨⟨(-1107244119682302043070500),(-1092408367832091375922505),true⟩,⟨(-509298211138429112384402),(-494462459288218445244638),true⟩⟩⟩
  | 2 => ⟨⟨89150153652028143,101884567194545062,true⟩,⟨1398233011819434810881,1477257275896763418037,true⟩,⟨⟨1129877515319836961427618,1154603768403475593636406,true⟩,⟨(-408327712597661434918164),(-383601459514022802719658),true⟩⟩⟩
  | 3 => ⟨⟨84896761856,186491967041,true⟩,⟨89150153652028143,101884567194545062,true⟩,⟨⟨(-570527805013799357996253),(-535911050696732760691172),true⟩,⟨1057610178814148284629607,1092226933131214881941864,true⟩⟩⟩
  | 4 => ⟨⟨(-34359735021),34359743287,true⟩,⟨84896761856,186491967041,true⟩,⟨⟨(-363877528161484251407718),(-319370272610989689043272),true⟩,⟨(-1181906484459435059104400),(-1137399228908940496728695),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359735021),34359743287,true⟩,⟨⟨1020417167090602319169280,1074814923874524846578311,true⟩,⟨576127118543674014141053,630524875327596541543961,true⟩⟩⟩
theorem shortNegativeR041Q01F_ok : ∀ n : Fin 6, (shortNegativeR041Q01F n).encloses (FactoredFrequency.build shortNegativeR041Q01T (Grid.ofRats (1247193928907753/1649267441664000) (417162965401251/549755813888000)) n) := by decide +kernel
def shortNegativeR041Q01L : ℕ → ℚ
  | 0 => (-2576429/1000000)
  | 1 => (-242287/125000)
  | 2 => (-1471573/1000000)
  | 3 => (-635039/500000)
  | 4 => (-166303/125000)
  | 5 => (-83133/50000)
  | 6 => (-437553/200000)
  | 7 => (-2821777/1000000)
  | 8 => (-430083/125000)
  | 9 => (-385281/100000)
  | 10 => (-1918403/500000)
  | 11 => (-670477/200000)
  | _ => 0
def shortNegativeR041Q01U : ℕ → ℚ
  | 0 => (-2022191/1000000)
  | 1 => (-269097/200000)
  | 2 => (-106547/125000)
  | 3 => (-15377/25000)
  | 4 => (-646287/1000000)
  | 5 => (-11119/12500)
  | 6 => (-167927/125000)
  | 7 => (-38853/20000)
  | 8 => (-2540803/1000000)
  | 9 => (-725539/250000)
  | 10 => (-2919823/1000000)
  | 11 => (-644593/250000)
  | _ => 0
private theorem shortNegativeR041Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR041Q01P shortNegativeR041Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR041Q01L (0:Fin 12)) (shortNegativeR041Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR041Q01P shortNegativeR041Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR041Q01L (1:Fin 12)) (shortNegativeR041Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR041Q01P shortNegativeR041Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR041Q01L (2:Fin 12)) (shortNegativeR041Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR041Q01P shortNegativeR041Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR041Q01L (3:Fin 12)) (shortNegativeR041Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR041Q01P shortNegativeR041Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR041Q01L (4:Fin 12)) (shortNegativeR041Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR041Q01P shortNegativeR041Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR041Q01L (5:Fin 12)) (shortNegativeR041Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR041Q01P shortNegativeR041Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR041Q01L (6:Fin 12)) (shortNegativeR041Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR041Q01P shortNegativeR041Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR041Q01L (7:Fin 12)) (shortNegativeR041Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR041Q01P shortNegativeR041Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR041Q01L (8:Fin 12)) (shortNegativeR041Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR041Q01P shortNegativeR041Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR041Q01L (9:Fin 12)) (shortNegativeR041Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR041Q01P shortNegativeR041Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR041Q01L (10:Fin 12)) (shortNegativeR041Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR041Q01P shortNegativeR041Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR041Q01L (11:Fin 12)) (shortNegativeR041Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR041Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR041Q01P shortNegativeR041Q01F (shortNegativeNodes12 k)).re (shortNegativeR041Q01L k) (shortNegativeR041Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR041Q01Point00
  · exact shortNegativeR041Q01Point01
  · exact shortNegativeR041Q01Point02
  · exact shortNegativeR041Q01Point03
  · exact shortNegativeR041Q01Point04
  · exact shortNegativeR041Q01Point05
  · exact shortNegativeR041Q01Point06
  · exact shortNegativeR041Q01Point07
  · exact shortNegativeR041Q01Point08
  · exact shortNegativeR041Q01Point09
  · exact shortNegativeR041Q01Point10
  · exact shortNegativeR041Q01Point11

theorem shortNegativeR041Q01Bound {t a : ℝ} (tl : ((61/50):ℝ)≤t) (tu : t≤((123/100):ℝ)) (al : ((1247193928907753/1649267441664000):ℝ)≤a) (au : a≤((417162965401251/549755813888000):ℝ)) : (((-3260083281583129841281727374737523/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2149169948926785881109925954240627/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR041Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1247193928907753/1649267441664000) (417162965401251/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR041Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR041Q01F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR041Q01L shortNegativeR041Q01U (-3260083281583129841281727374737523/1298074214633706907132624082305024) (-2149169948926785881109925954240627/1298074214633706907132624082305024) shortNegativeR041Q01Samples (by decide +kernel)

def shortNegativeR041Q02T := Grid.ofRats (61/50) (123/100)
def shortNegativeR041Q02P : PrimalThetaParameters := ⟨⟨⟨25363941210528581420977,26173421637133962629238,true⟩,⟨0,0,true⟩⟩, ⟨⟨1440971678998824957644745,1445916929615607659653151,true⟩,⟨0,0,true⟩⟩, ⟨(-916009115638654305759854),(-906118614405157621226070),true⟩, ⟨3954284826077325588511204,4010826478338851144571893,true⟩⟩
theorem shortNegativeR041Q02P_ok : shortNegativeR041Q02P.encloses (primalThetaParameters shortNegativeR041Q02T (Grid.ofRats (417162965401251/549755813888000) (1255783863499753/1649267441664000))) := by decide +kernel

def shortNegativeR041Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨460101791531806877352917,463729650472374392566223,true⟩,⟨3151624304898875146196183,3176474563302750903325939,true⟩,⟨⟨442355894618030029676003,447301145234812731732943,true⟩,⟨1121640013705587645714076,1126585264322370347780377,true⟩⟩⟩
  | 1 => ⟨⟨1398233011819434810881,1477257275896763418037,true⟩,⟨460101791531806877352917,463729650472374392566223,true⟩,⟨⟨(-1101002461040466305190967),(-1086166709190255638042720),true⟩,⟨(-522756980330124003068277),(-507921228479913335927974),true⟩⟩⟩
  | 2 => ⟨⟨89150153652028143,101884567194545062,true⟩,⟨1398233011819434810881,1477257275896763418037,true⟩,⟨⟨1137736737413425001023788,1162462990497063633232336,true⟩,⟨(-384884186699539032328607),(-360157933615900400130768),true⟩⟩⟩
  | 3 => ⟨⟨84896761856,186491967041,true⟩,⟨89150153652028143,101884567194545062,true⟩,⟨⟨(-601076364754464137797803),(-566459610437397540492810),true⟩,⟨1041330642521499115050785,1075947396838565712362316,true⟩⟩⟩
  | 4 => ⟨⟨(-34359735021),34359743287,true⟩,⟨84896761856,186491967041,true⟩,⟨⟨(-320962437311035839841570),(-276455181760541277477590),true⟩,⟨(-1193694912875194111831446),(-1149187657324699549455453),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359735021),34359743287,true⟩,⟨⟨992218226180023724999434,1046615982963946252409523,true⟩,⟨622639874097434016470276,677037630881356543875277,true⟩⟩⟩
theorem shortNegativeR041Q02F_ok : ∀ n : Fin 6, (shortNegativeR041Q02F n).encloses (FactoredFrequency.build shortNegativeR041Q02T (Grid.ofRats (417162965401251/549755813888000) (1255783863499753/1649267441664000)) n) := by decide +kernel
def shortNegativeR041Q02L : ℕ → ℚ
  | 0 => (-2587559/1000000)
  | 1 => (-30507/15625)
  | 2 => (-1483953/1000000)
  | 3 => (-31913/25000)
  | 4 => (-665167/500000)
  | 5 => (-827633/500000)
  | 6 => (-543333/250000)
  | 7 => (-2802831/1000000)
  | 8 => (-341981/100000)
  | 9 => (-1917689/500000)
  | 10 => (-1914179/500000)
  | 11 => (-3355277/1000000)
  | _ => 0
def shortNegativeR041Q02U : ℕ → ℚ
  | 0 => (-2036481/1000000)
  | 1 => (-1362241/1000000)
  | 2 => (-108473/125000)
  | 3 => (-312647/500000)
  | 4 => (-324971/500000)
  | 5 => (-443181/500000)
  | 6 => (-133379/100000)
  | 7 => (-482023/250000)
  | 8 => (-1262003/500000)
  | 9 => (-2889457/1000000)
  | 10 => (-58317/20000)
  | 11 => (-258463/100000)
  | _ => 0
private theorem shortNegativeR041Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR041Q02P shortNegativeR041Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR041Q02L (0:Fin 12)) (shortNegativeR041Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR041Q02P shortNegativeR041Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR041Q02L (1:Fin 12)) (shortNegativeR041Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR041Q02P shortNegativeR041Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR041Q02L (2:Fin 12)) (shortNegativeR041Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR041Q02P shortNegativeR041Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR041Q02L (3:Fin 12)) (shortNegativeR041Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR041Q02P shortNegativeR041Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR041Q02L (4:Fin 12)) (shortNegativeR041Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR041Q02P shortNegativeR041Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR041Q02L (5:Fin 12)) (shortNegativeR041Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR041Q02P shortNegativeR041Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR041Q02L (6:Fin 12)) (shortNegativeR041Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR041Q02P shortNegativeR041Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR041Q02L (7:Fin 12)) (shortNegativeR041Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR041Q02P shortNegativeR041Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR041Q02L (8:Fin 12)) (shortNegativeR041Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR041Q02P shortNegativeR041Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR041Q02L (9:Fin 12)) (shortNegativeR041Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR041Q02P shortNegativeR041Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR041Q02L (10:Fin 12)) (shortNegativeR041Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR041Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR041Q02P shortNegativeR041Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR041Q02L (11:Fin 12)) (shortNegativeR041Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR041Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR041Q02P shortNegativeR041Q02F (shortNegativeNodes12 k)).re (shortNegativeR041Q02L k) (shortNegativeR041Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR041Q02Point00
  · exact shortNegativeR041Q02Point01
  · exact shortNegativeR041Q02Point02
  · exact shortNegativeR041Q02Point03
  · exact shortNegativeR041Q02Point04
  · exact shortNegativeR041Q02Point05
  · exact shortNegativeR041Q02Point06
  · exact shortNegativeR041Q02Point07
  · exact shortNegativeR041Q02Point08
  · exact shortNegativeR041Q02Point09
  · exact shortNegativeR041Q02Point10
  · exact shortNegativeR041Q02Point11

theorem shortNegativeR041Q02Bound {t a : ℝ} (tl : ((61/50):ℝ)≤t) (tu : t≤((123/100):ℝ)) (al : ((417162965401251/549755813888000):ℝ)≤a) (au : a≤((1255783863499753/1649267441664000):ℝ)) : (((-3260083281583129841281727374737523/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2149169948926785881109925954240627/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR041Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (417162965401251/549755813888000) (1255783863499753/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR041Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR041Q02F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR041Q02L shortNegativeR041Q02U (-3260083281583129841281727374737523/1298074214633706907132624082305024) (-2149169948926785881109925954240627/1298074214633706907132624082305024) shortNegativeR041Q02Samples (by decide +kernel)

theorem short_original_negative_041 {t a : ℝ} (tb : RealMem negative_041.t t) (ab : RealMem negative_041.a a) : RealMem negative_041.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((61/50):ℝ) ((123/100):ℝ) := by simpa [negative_041,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((61/50):ℝ)<((123/100):ℝ)) tB
  have aB : a∈Icc ((1242898961611753/1649267441664000):ℝ) ((1255783863499753/1649267441664000):ℝ) := by simpa [negative_041,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((1242898961611753/1649267441664000):ℝ)<((1255783863499753/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR041Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_041,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR041Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_041,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR041Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_041,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_040
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_041
