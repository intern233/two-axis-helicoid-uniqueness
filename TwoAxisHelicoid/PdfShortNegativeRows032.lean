import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip032

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR032Q00T := Grid.ofRats (113/100) (57/50)
def shortNegativeR032Q00P : PrimalThetaParameters := ⟨⟨⟨33651979039478494786283,34725969005087868206856,true⟩,⟨0,0,true⟩⟩, ⟨⟨1331274277187556343034383,1338692153112696036305979,true⟩,⟨0,0,true⟩⟩, ⟨(-1135403919261191534981277),(-1120568167410980867919731),true⟩, ⟨4401190729044027496820957,4494824014323024102193468,true⟩⟩
theorem shortNegativeR032Q00P_ok : shortNegativeR032Q00P.encloses (primalThetaParameters shortNegativeR032Q00T (Grid.ofRats (1156216322627161/1649267441664000) (1162658773571161/1649267441664000))) := by decide +kernel

def shortNegativeR032Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨493801485716282027088701,497695063545776673607287,true⟩,⟨2936540352477419473222130,2959694694338236094079962,true⟩,⟨⟨540047214679938168005637,547465090605077861325500,true⟩,⟨1076027550165121632447922,1083445426090261325775187,true⟩⟩⟩
  | 1 => ⟨⟨2293342012967188927293,2422955363000513354224,true⟩,⟨493801485716282027088701,497695063545776673607287,true⟩,⟨⟨(-1202374440403500115668939),(-1180120812628218474737776),true⟩,⟨(-217114021381782845433323),(-194860393606501204515714),true⟩⟩⟩
  | 2 => ⟨⟨296480523232305643,338830313673132017,true⟩,⟨2293342012967188927293,2422955363000513354224,true⟩,⟨⟨856207578447174328333416,893296958072597916865468,true⟩,⟨(-852996669560550336000639),(-815907289935126747469151),true⟩⟩⟩
  | 3 => ⟨⟨1032566920793,1395408655473,true⟩,⟨296480523232305643,338830313673132017,true⟩,⟨⟨123651540500419161247925,175576671975984697384557,true⟩,⟨1173669568103857431235165,1225594699579422967386251,true⟩⟩⟩
  | 4 => ⟨⟨(-34359631492),34359895412,true⟩,⟨1032566920793,1395408655473,true⟩,⟨⟨(-1086289513647418188831115),(-1019528630321710705094941),true⟩,⟨(-627420948247637235998064),(-560660064921929752268200),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359631492),34359895412,true⟩,⟨⟨1063365843437221150692691,1144962478613070581990825,true⟩,⟨(-533061603684438994765478),(-451464968508589563475769),true⟩⟩⟩
theorem shortNegativeR032Q00F_ok : ∀ n : Fin 6, (shortNegativeR032Q00F n).encloses (FactoredFrequency.build shortNegativeR032Q00T (Grid.ofRats (1156216322627161/1649267441664000) (1162658773571161/1649267441664000)) n) := by decide +kernel
def shortNegativeR032Q00L : ℕ → ℚ
  | 0 => (-244901/125000)
  | 1 => (-1093273/1000000)
  | 2 => (-12747/20000)
  | 3 => (-56733/100000)
  | 4 => (-415489/500000)
  | 5 => (-287697/200000)
  | 6 => (-228617/100000)
  | 7 => (-405961/125000)
  | 8 => (-4084911/1000000)
  | 9 => (-4548621/1000000)
  | 10 => (-423951/100000)
  | 11 => (-3227937/1000000)
  | _ => 0
def shortNegativeR032Q00U : ℕ → ℚ
  | 0 => (-629763/500000)
  | 1 => (-351091/1000000)
  | 2 => (38591/250000)
  | 3 => (50787/200000)
  | 4 => (10031/1000000)
  | 5 => (-5829/12500)
  | 6 => (-59479/50000)
  | 7 => (-2070797/1000000)
  | 8 => (-2905671/1000000)
  | 9 => (-3272183/1000000)
  | 10 => (-3014179/1000000)
  | 11 => (-2220871/1000000)
  | _ => 0
private theorem shortNegativeR032Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR032Q00P shortNegativeR032Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR032Q00L (0:Fin 12)) (shortNegativeR032Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR032Q00P shortNegativeR032Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR032Q00L (1:Fin 12)) (shortNegativeR032Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR032Q00P shortNegativeR032Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR032Q00L (2:Fin 12)) (shortNegativeR032Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR032Q00P shortNegativeR032Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR032Q00L (3:Fin 12)) (shortNegativeR032Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR032Q00P shortNegativeR032Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR032Q00L (4:Fin 12)) (shortNegativeR032Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR032Q00P shortNegativeR032Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR032Q00L (5:Fin 12)) (shortNegativeR032Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR032Q00P shortNegativeR032Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR032Q00L (6:Fin 12)) (shortNegativeR032Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR032Q00P shortNegativeR032Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR032Q00L (7:Fin 12)) (shortNegativeR032Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR032Q00P shortNegativeR032Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR032Q00L (8:Fin 12)) (shortNegativeR032Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR032Q00P shortNegativeR032Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR032Q00L (9:Fin 12)) (shortNegativeR032Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR032Q00P shortNegativeR032Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR032Q00L (10:Fin 12)) (shortNegativeR032Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR032Q00P shortNegativeR032Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR032Q00L (11:Fin 12)) (shortNegativeR032Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR032Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR032Q00P shortNegativeR032Q00F (shortNegativeNodes12 k)).re (shortNegativeR032Q00L k) (shortNegativeR032Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR032Q00Point00
  · exact shortNegativeR032Q00Point01
  · exact shortNegativeR032Q00Point02
  · exact shortNegativeR032Q00Point03
  · exact shortNegativeR032Q00Point04
  · exact shortNegativeR032Q00Point05
  · exact shortNegativeR032Q00Point06
  · exact shortNegativeR032Q00Point07
  · exact shortNegativeR032Q00Point08
  · exact shortNegativeR032Q00Point09
  · exact shortNegativeR032Q00Point10
  · exact shortNegativeR032Q00Point11

theorem shortNegativeR032Q00Bound {t a : ℝ} (tl : ((113/100):ℝ)≤t) (tu : t≤((57/50):ℝ)) (al : ((1156216322627161/1649267441664000):ℝ)≤a) (au : a≤((1162658773571161/1649267441664000):ℝ)) : (((-3056354289655537749546383376791133/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1704079418817348214715601420957277/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR032Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1156216322627161/1649267441664000) (1162658773571161/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR032Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR032Q00F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR032Q00L shortNegativeR032Q00U (-3056354289655537749546383376791133/1298074214633706907132624082305024) (-1704079418817348214715601420957277/1298074214633706907132624082305024) shortNegativeR032Q00Samples (by decide +kernel)

def shortNegativeR032Q01T := Grid.ofRats (113/100) (57/50)
def shortNegativeR032Q01P : PrimalThetaParameters := ⟨⟨⟨33651979039478494786283,34725969005087868206856,true⟩,⟨0,0,true⟩⟩, ⟨⟨1338692153112627316824978,1346110029037767010096598,true⟩,⟨0,0,true⟩⟩, ⟨(-1120568167411049587400039),(-1105732415560838920338541),true⟩, ⟨4379192741418177691692852,4472317223537017570538266,true⟩⟩
theorem shortNegativeR032Q01P_ok : shortNegativeR032Q01P.encloses (primalThetaParameters shortNegativeR032Q01T (Grid.ofRats (1162658773571161/1649267441664000) (1169101224515161/1649267441664000))) := by decide +kernel

def shortNegativeR032Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨493801485716282027088701,497695063545776673607287,true⟩,⟨2936540352477419473222130,2959694694338236094079962,true⟩,⟨⟨533411840081396117274707,540829716006535810594654,true⟩,⟨1079343649460749856608498,1086761525385889549935984,true⟩⟩⟩
  | 1 => ⟨⟨2293342012967188927293,2422955363000513354224,true⟩,⟨493801485716282027088701,497695063545776673607287,true⟩,⟨⟨(-1198381070477490540966760),(-1176127442702208900034769),true⟩,⟨(-239006096711214319011210),(-216752468935932678092421),true⟩⟩⟩
  | 2 => ⟨⟨296480523232305643,338830313673132017,true⟩,⟨2293342012967188927293,2422955363000513354224,true⟩,⟨⟨881392585577971886506153,918481965203395475037856,true⟩,⟨(-825771137405514392059183),(-788681757780090803528764),true⟩⟩⟩
  | 3 => ⟨⟨1032566920793,1395408655473,true⟩,⟨296480523232305643,338830313673132017,true⟩,⟨⟨72003442772119237373867,123928574247684773510609,true⟩,⟨1178987349614527933955121,1230912481090093470107100,true⟩⟩⟩
  | 4 => ⟨⟨(-34359631492),34359895412,true⟩,⟨1032566920793,1395408655473,true⟩,⟨⟨(-1051896227688970003981046),(-985135344363262520243780),true⟩,⟨(-684630954865342874260580),(-617870071539635390528369),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359631492),34359895412,true⟩,⟨⟨1094051900700333066261889,1175648535876182497558433,true⟩,⟨(-457471594127225446498215),(-375874958951376015211562),true⟩⟩⟩
theorem shortNegativeR032Q01F_ok : ∀ n : Fin 6, (shortNegativeR032Q01F n).encloses (FactoredFrequency.build shortNegativeR032Q01T (Grid.ofRats (1162658773571161/1649267441664000) (1169101224515161/1649267441664000)) n) := by decide +kernel
def shortNegativeR032Q01L : ℕ → ℚ
  | 0 => (-498271/250000)
  | 1 => (-112593/100000)
  | 2 => (-82703/125000)
  | 3 => (-579697/1000000)
  | 4 => (-830103/1000000)
  | 5 => (-1423457/1000000)
  | 6 => (-1128717/500000)
  | 7 => (-80219/25000)
  | 8 => (-4045797/1000000)
  | 9 => (-4520767/1000000)
  | 10 => (-4235777/1000000)
  | 11 => (-812271/250000)
  | _ => 0
def shortNegativeR032Q01U : ℕ → ℚ
  | 0 => (-20278/15625)
  | 1 => (-195303/500000)
  | 2 => (123409/1000000)
  | 3 => (235977/1000000)
  | 4 => (731/125000)
  | 5 => (-22857/50000)
  | 6 => (-583941/500000)
  | 7 => (-509981/250000)
  | 8 => (-143681/50000)
  | 9 => (-812717/250000)
  | 10 => (-602969/200000)
  | 11 => (-35123/15625)
  | _ => 0
private theorem shortNegativeR032Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR032Q01P shortNegativeR032Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR032Q01L (0:Fin 12)) (shortNegativeR032Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR032Q01P shortNegativeR032Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR032Q01L (1:Fin 12)) (shortNegativeR032Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR032Q01P shortNegativeR032Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR032Q01L (2:Fin 12)) (shortNegativeR032Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR032Q01P shortNegativeR032Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR032Q01L (3:Fin 12)) (shortNegativeR032Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR032Q01P shortNegativeR032Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR032Q01L (4:Fin 12)) (shortNegativeR032Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR032Q01P shortNegativeR032Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR032Q01L (5:Fin 12)) (shortNegativeR032Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR032Q01P shortNegativeR032Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR032Q01L (6:Fin 12)) (shortNegativeR032Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR032Q01P shortNegativeR032Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR032Q01L (7:Fin 12)) (shortNegativeR032Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR032Q01P shortNegativeR032Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR032Q01L (8:Fin 12)) (shortNegativeR032Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR032Q01P shortNegativeR032Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR032Q01L (9:Fin 12)) (shortNegativeR032Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR032Q01P shortNegativeR032Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR032Q01L (10:Fin 12)) (shortNegativeR032Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR032Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR032Q01P shortNegativeR032Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR032Q01L (11:Fin 12)) (shortNegativeR032Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR032Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR032Q01P shortNegativeR032Q01F (shortNegativeNodes12 k)).re (shortNegativeR032Q01L k) (shortNegativeR032Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR032Q01Point00
  · exact shortNegativeR032Q01Point01
  · exact shortNegativeR032Q01Point02
  · exact shortNegativeR032Q01Point03
  · exact shortNegativeR032Q01Point04
  · exact shortNegativeR032Q01Point05
  · exact shortNegativeR032Q01Point06
  · exact shortNegativeR032Q01Point07
  · exact shortNegativeR032Q01Point08
  · exact shortNegativeR032Q01Point09
  · exact shortNegativeR032Q01Point10
  · exact shortNegativeR032Q01Point11

theorem shortNegativeR032Q01Bound {t a : ℝ} (tl : ((113/100):ℝ)≤t) (tu : t≤((57/50):ℝ)) (al : ((1162658773571161/1649267441664000):ℝ)≤a) (au : a≤((1169101224515161/1649267441664000):ℝ)) : (((-3056354289655537749546383376791133/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1704079418817348214715601420957277/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR032Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1162658773571161/1649267441664000) (1169101224515161/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR032Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR032Q01F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR032Q01L shortNegativeR032Q01U (-3056354289655537749546383376791133/1298074214633706907132624082305024) (-1704079418817348214715601420957277/1298074214633706907132624082305024) shortNegativeR032Q01Samples (by decide +kernel)

theorem short_original_negative_032 {t a : ℝ} (tb : RealMem negative_032.t t) (ab : RealMem negative_032.a a) : RealMem negative_032.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((113/100):ℝ) ((57/50):ℝ) := by simpa [negative_032,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((113/100):ℝ)<((57/50):ℝ)) tB
  have aB : a∈Icc ((1156216322627161/1649267441664000):ℝ) ((1169101224515161/1649267441664000):ℝ) := by simpa [negative_032,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((1156216322627161/1649267441664000):ℝ)<((1169101224515161/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR032Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_032,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR032Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_032,RealMem] using v

def shortNegativeR033Q00T := Grid.ofRats (57/50) (229/200)
def shortNegativeR033Q00P : PrimalThetaParameters := ⟨⟨⟨33127504982464519258536,33651979039547214263556,true⟩,⟨0,0,true⟩⟩, ⟨⟨1341368757365259753566329,1356204509215470420628576,true⟩,⟨0,0,true⟩⟩, ⟨(-1115214958905784713917320),(-1085543455205432099274648),true⟩, ⟨4315807192362080072048078,4464625901790061233265656,true⟩⟩
theorem shortNegativeR033Q00P_ok : shortNegativeR033Q00P.encloses (primalThetaParameters shortNegativeR033Q00T (Grid.ofRats (232996682727811/329853488332800) (235573663105411/329853488332800))) := by decide +kernel

def shortNegativeR033Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨491866134357095546136274,493801485716350746583704,true⟩,⟨2959694694338167374494605,2971340239232175636305978,true⟩,⟨⟨523974755823735054433751,538810507673945721544518,true⟩,⟨1078456660222576982418608,1093292412072787649537074,true⟩⟩⟩
  | 1 => ⟨⟨2231159068885547695078,2293342013035908404155,true⟩,⟨491866134357095546136274,493801485716350746583704,true⟩,⟨⟨(-1205748008680840658956459),(-1161240753130346096652109),true⟩,⟨(-268916733439205811851167),(-224409477888711249559705),true⟩⟩⟩
  | 2 => ⟨⟨277334033131507927,296480591951782380,true⟩,⟨2231159068885547695078,2293342013035908404155,true⟩,⟨⟨883850425689920681063034,958029184940699138547754,true⟩,⟨(-820269762625820362116695),(-746091003375041904633879),true⟩⟩⟩
  | 3 => ⟨⟨910277329025,1101286397530,true⟩,⟨277334033131507927,296480591951782380,true⟩,⟨⟨1432280955802439612590,105282543906864792284017,true⟩,⟨1155822616967634203465146,1259672879918696556152461,true⟩⟩⟩
  | 4 => ⟨⟨(-34359650200),34359845245,true⟩,⟨910277329025,1101286397530,true⟩,⟨⟨(-1053178566763682194066808),(-919656800112335946212652),true⟩,⟨(-765675607116562111384122),(-632153840465215863533916),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359650200),34359845245,true⟩,⟨⟨1075534503301294852267762,1238727773652924995258878,true⟩,⟨(-431666864840621581593597),(-268473594488991438613586),true⟩⟩⟩
theorem shortNegativeR033Q00F_ok : ∀ n : Fin 6, (shortNegativeR033Q00F n).encloses (FactoredFrequency.build shortNegativeR033Q00T (Grid.ofRats (232996682727811/329853488332800) (235573663105411/329853488332800)) n) := by decide +kernel
def shortNegativeR033Q00L : ℕ → ℚ
  | 0 => (-2019289/1000000)
  | 1 => (-1171181/1000000)
  | 2 => (-706693/1000000)
  | 3 => (-309199/500000)
  | 4 => (-856853/1000000)
  | 5 => (-358343/250000)
  | 6 => (-1121661/500000)
  | 7 => (-3168127/1000000)
  | 8 => (-796567/200000)
  | 9 => (-4447379/1000000)
  | 10 => (-83753/20000)
  | 11 => (-3255983/1000000)
  | _ => 0
def shortNegativeR033Q00U : ℕ → ℚ
  | 0 => (-1402229/1000000)
  | 1 => (-514999/1000000)
  | 2 => (-507/1000000)
  | 3 => (26281/200000)
  | 4 => (-19271/250000)
  | 5 => (-517171/1000000)
  | 6 => (-24059/20000)
  | 7 => (-81861/40000)
  | 8 => (-178559/62500)
  | 9 => (-404103/125000)
  | 10 => (-1511767/500000)
  | 11 => (-1146563/500000)
  | _ => 0
private theorem shortNegativeR033Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR033Q00P shortNegativeR033Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR033Q00L (0:Fin 12)) (shortNegativeR033Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR033Q00P shortNegativeR033Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR033Q00L (1:Fin 12)) (shortNegativeR033Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR033Q00P shortNegativeR033Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR033Q00L (2:Fin 12)) (shortNegativeR033Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR033Q00P shortNegativeR033Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR033Q00L (3:Fin 12)) (shortNegativeR033Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR033Q00P shortNegativeR033Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR033Q00L (4:Fin 12)) (shortNegativeR033Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR033Q00P shortNegativeR033Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR033Q00L (5:Fin 12)) (shortNegativeR033Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR033Q00P shortNegativeR033Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR033Q00L (6:Fin 12)) (shortNegativeR033Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR033Q00P shortNegativeR033Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR033Q00L (7:Fin 12)) (shortNegativeR033Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR033Q00P shortNegativeR033Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR033Q00L (8:Fin 12)) (shortNegativeR033Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR033Q00P shortNegativeR033Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR033Q00L (9:Fin 12)) (shortNegativeR033Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR033Q00P shortNegativeR033Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR033Q00L (10:Fin 12)) (shortNegativeR033Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR033Q00P shortNegativeR033Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR033Q00L (11:Fin 12)) (shortNegativeR033Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR033Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR033Q00P shortNegativeR033Q00F (shortNegativeNodes12 k)).re (shortNegativeR033Q00L k) (shortNegativeR033Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR033Q00Point00
  · exact shortNegativeR033Q00Point01
  · exact shortNegativeR033Q00Point02
  · exact shortNegativeR033Q00Point03
  · exact shortNegativeR033Q00Point04
  · exact shortNegativeR033Q00Point05
  · exact shortNegativeR033Q00Point06
  · exact shortNegativeR033Q00Point07
  · exact shortNegativeR033Q00Point08
  · exact shortNegativeR033Q00Point09
  · exact shortNegativeR033Q00Point10
  · exact shortNegativeR033Q00Point11

theorem shortNegativeR033Q00Bound {t a : ℝ} (tl : ((57/50):ℝ)≤t) (tu : t≤((229/200):ℝ)) (al : ((232996682727811/329853488332800):ℝ)≤a) (au : a≤((235573663105411/329853488332800):ℝ)) : (((-1542904884372351464395090963914867/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-883317851359021944097645584900211/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR033Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (232996682727811/329853488332800) (235573663105411/329853488332800)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR033Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR033Q00F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR033Q00L shortNegativeR033Q00U (-1542904884372351464395090963914867/649037107316853453566312041152512) (-883317851359021944097645584900211/649037107316853453566312041152512) shortNegativeR033Q00Samples (by decide +kernel)

def shortNegativeR033Q10T := Grid.ofRats (229/200) (23/20)
def shortNegativeR033Q10P : PrimalThetaParameters := ⟨⟨⟨32611204977744993299805,33127504982533238735803,true⟩,⟨0,0,true⟩⟩, ⟨⟨1341368757365259753566329,1356204509215470420628576,true⟩,⟨0,0,true⟩⟩, ⟨(-1115214958905784713917320),(-1085543455205432099274648),true⟩, ⟨4304930704797142315129484,4452926630709160344501775,true⟩⟩
theorem shortNegativeR033Q10P_ok : shortNegativeR033Q10P.encloses (primalThetaParameters shortNegativeR033Q10T (Grid.ofRats (232996682727811/329853488332800) (235573663105411/329853488332800))) := by decide +kernel

def shortNegativeR033Q10F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨489938368201663710745394,491866134357164265631195,true⟩,⟨2971340239232106916719916,2983031605986098302962471,true⟩,⟨⟨523974755823735054433751,538810507673945721544518,true⟩,⟨1078456660222576982418608,1093292412072787649537074,true⟩⟩⟩
  | 1 => ⟨⟨2170662187551084639290,2231159068954267171937,true⟩,⟨489938368201663710745394,491866134357164265631195,true⟩,⟨⟨(-1205748008680840658956459),(-1161240753130346096652109),true⟩,⟨(-268916733439205811851167),(-224409477888711249559705),true⟩⟩⟩
  | 2 => ⟨⟨259424008875746729,277334101850984664,true⟩,⟨2170662187551084639290,2231159068954267171937,true⟩,⟨⟨883850425689920681063034,958029184940699138547754,true⟩,⟨(-820269762625820362116695),(-746091003375041904633879),true⟩⟩⟩
  | 3 => ⟨⟨802004393534,978996805762,true⟩,⟨259424008875746729,277334101850984664,true⟩,⟨⟨1432280955802439612590,105282543906864792284017,true⟩,⟨1155822616967634203465146,1259672879918696556152461,true⟩⟩⟩
  | 4 => ⟨⟨(-34359665633),34359826537,true⟩,⟨802004393534,978996805762,true⟩,⟨⟨(-1053178566763682194066808),(-919656800112335946212652),true⟩,⟨(-765675607116562111384122),(-632153840465215863533916),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359665633),34359826537,true⟩,⟨⟨1075534503301294852267762,1238727773652924995258878,true⟩,⟨(-431666864840621581593597),(-268473594488991438613586),true⟩⟩⟩
theorem shortNegativeR033Q10F_ok : ∀ n : Fin 6, (shortNegativeR033Q10F n).encloses (FactoredFrequency.build shortNegativeR033Q10T (Grid.ofRats (232996682727811/329853488332800) (235573663105411/329853488332800)) n) := by decide +kernel
def shortNegativeR033Q10L : ℕ → ℚ
  | 0 => (-1021379/500000)
  | 1 => (-150701/125000)
  | 2 => (-744863/1000000)
  | 3 => (-655633/1000000)
  | 4 => (-222721/250000)
  | 5 => (-73069/50000)
  | 6 => (-1131013/500000)
  | 7 => (-793487/250000)
  | 8 => (-3976001/1000000)
  | 9 => (-1107863/250000)
  | 10 => (-4175589/1000000)
  | 11 => (-652047/200000)
  | _ => 0
def shortNegativeR033Q10U : ℕ → ℚ
  | 0 => (-1426193/1000000)
  | 1 => (-274919/500000)
  | 2 => (-7731/200000)
  | 3 => (46539/500000)
  | 4 => (-27653/250000)
  | 5 => (-272899/500000)
  | 6 => (-122399/100000)
  | 7 => (-411363/200000)
  | 8 => (-2855163/1000000)
  | 9 => (-1611633/500000)
  | 10 => (-377243/125000)
  | 11 => (-2301503/1000000)
  | _ => 0
private theorem shortNegativeR033Q10Point00 : containedInReported (sampledFactoredPrimal shortNegativeR033Q10P shortNegativeR033Q10F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR033Q10L (0:Fin 12)) (shortNegativeR033Q10U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q10Point01 : containedInReported (sampledFactoredPrimal shortNegativeR033Q10P shortNegativeR033Q10F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR033Q10L (1:Fin 12)) (shortNegativeR033Q10U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q10Point02 : containedInReported (sampledFactoredPrimal shortNegativeR033Q10P shortNegativeR033Q10F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR033Q10L (2:Fin 12)) (shortNegativeR033Q10U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q10Point03 : containedInReported (sampledFactoredPrimal shortNegativeR033Q10P shortNegativeR033Q10F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR033Q10L (3:Fin 12)) (shortNegativeR033Q10U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q10Point04 : containedInReported (sampledFactoredPrimal shortNegativeR033Q10P shortNegativeR033Q10F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR033Q10L (4:Fin 12)) (shortNegativeR033Q10U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q10Point05 : containedInReported (sampledFactoredPrimal shortNegativeR033Q10P shortNegativeR033Q10F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR033Q10L (5:Fin 12)) (shortNegativeR033Q10U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q10Point06 : containedInReported (sampledFactoredPrimal shortNegativeR033Q10P shortNegativeR033Q10F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR033Q10L (6:Fin 12)) (shortNegativeR033Q10U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q10Point07 : containedInReported (sampledFactoredPrimal shortNegativeR033Q10P shortNegativeR033Q10F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR033Q10L (7:Fin 12)) (shortNegativeR033Q10U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q10Point08 : containedInReported (sampledFactoredPrimal shortNegativeR033Q10P shortNegativeR033Q10F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR033Q10L (8:Fin 12)) (shortNegativeR033Q10U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q10Point09 : containedInReported (sampledFactoredPrimal shortNegativeR033Q10P shortNegativeR033Q10F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR033Q10L (9:Fin 12)) (shortNegativeR033Q10U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q10Point10 : containedInReported (sampledFactoredPrimal shortNegativeR033Q10P shortNegativeR033Q10F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR033Q10L (10:Fin 12)) (shortNegativeR033Q10U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR033Q10Point11 : containedInReported (sampledFactoredPrimal shortNegativeR033Q10P shortNegativeR033Q10F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR033Q10L (11:Fin 12)) (shortNegativeR033Q10U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR033Q10Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR033Q10P shortNegativeR033Q10F (shortNegativeNodes12 k)).re (shortNegativeR033Q10L k) (shortNegativeR033Q10U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR033Q10Point00
  · exact shortNegativeR033Q10Point01
  · exact shortNegativeR033Q10Point02
  · exact shortNegativeR033Q10Point03
  · exact shortNegativeR033Q10Point04
  · exact shortNegativeR033Q10Point05
  · exact shortNegativeR033Q10Point06
  · exact shortNegativeR033Q10Point07
  · exact shortNegativeR033Q10Point08
  · exact shortNegativeR033Q10Point09
  · exact shortNegativeR033Q10Point10
  · exact shortNegativeR033Q10Point11

theorem shortNegativeR033Q10Bound {t a : ℝ} (tl : ((229/200):ℝ)≤t) (tu : t≤((23/20):ℝ)) (al : ((232996682727811/329853488332800):ℝ)≤a) (au : a≤((235573663105411/329853488332800):ℝ)) : (((-1542904884372351464395090963914867/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-883317851359021944097645584900211/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR033Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (232996682727811/329853488332800) (235573663105411/329853488332800)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR033Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR033Q10F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR033Q10L shortNegativeR033Q10U (-1542904884372351464395090963914867/649037107316853453566312041152512) (-883317851359021944097645584900211/649037107316853453566312041152512) shortNegativeR033Q10Samples (by decide +kernel)

theorem short_original_negative_033 {t a : ℝ} (tb : RealMem negative_033.t t) (ab : RealMem negative_033.a a) : RealMem negative_033.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((57/50):ℝ) ((23/20):ℝ) := by simpa [negative_033,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((57/50):ℝ)<((23/20):ℝ)) tB
  have aB : a∈Icc ((232996682727811/329853488332800):ℝ) ((235573663105411/329853488332800):ℝ) := by simpa [negative_033,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((232996682727811/329853488332800):ℝ)<((235573663105411/329853488332800):ℝ)) aB
  fin_cases ti <;> fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR033Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_033,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR033Q10Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_033,RealMem] using v

def shortNegativeR034Q00T := Grid.ofRats (23/20) (231/200)
def shortNegativeR034Q00P : PrimalThetaParameters := ⟨⟨⟨32102951630780532446590,32611204977813712777066,true⟩,⟨0,0,true⟩⟩, ⟨⟨1351681575816802985191780,1366517327667013652254060,true⟩,⟨0,0,true⟩⟩, ⟨(-1094589322002698250666352),(-1064917818302345636023745),true⟩, ⟨4265273038219776104060073,4411041937768158712508332,true⟩⟩
theorem shortNegativeR034Q00P_ok : shortNegativeR034Q00P.encloses (primalThetaParameters shortNegativeR034Q00T (Grid.ofRats (46957605287933/65970697666560) (47473001363453/65970697666560))) := by decide +kernel

def shortNegativeR034Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨488018157521371235432597,489938368201732430239939,true⟩,⟨2983031605986029583376584,2994768974895805744841706,true⟩,⟨⟨514692411764140714348850,529528163614351381459674,true⟩,⟨1082950174239588204981057,1097785926089798872099779,true⟩⟩⟩
  | 1 => ⟨⟨2111805652125695574317,2170662187619804116145,true⟩,⟨488018157521371235432597,489938368201732430239939,true⟩,⟨⟨(-1199048637290983683701009),(-1154541381740489121395910),true⟩,⟨(-299120279630902854934864),(-254613024080408292642143),true⟩⟩⟩
  | 2 => ⟨⟨242670600436223395,259424077595223466,true⟩,⟨2111805652125695574317,2170662187619804116145,true⟩,⟨⟨916407559007943400238628,990586318258721857722463,true⟩,⟨(-780288697001129038337987),(-706109937750350580857045),true⟩⟩⟩
  | 3 => ⟨⟨706141545434,870723870271,true⟩,⟨242670600436223395,259424077595223466,true⟩,⟨⟨(-70739350029849216485610),33110912921213136187025,true⟩,⟨1156854278719353501978327,1260704541670415854666886,true⟩⟩⟩
  | 4 => ⟨⟨(-34359678365),34359811104,true⟩,⟨706141545434,870723870271,true⟩,⟨⟨(-996666290186799683373737),(-863144523535453435520089),true⟩,⟨(-839274683604571439804427),(-705752916953225191952945),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359678365),34359811104,true⟩,⟨⟨1103244909348707900943394,1266438179700338043931790,true⟩,⟨(-321705259968107288882675),(-158511989616477145907292),true⟩⟩⟩
theorem shortNegativeR034Q00F_ok : ∀ n : Fin 6, (shortNegativeR034Q00F n).encloses (FactoredFrequency.build shortNegativeR034Q00T (Grid.ofRats (46957605287933/65970697666560) (47473001363453/65970697666560)) n) := by decide +kernel
def shortNegativeR034Q00L : ℕ → ℚ
  | 0 => (-421727/200000)
  | 1 => (-1282533/1000000)
  | 2 => (-815369/1000000)
  | 3 => (-709687/1000000)
  | 4 => (-924099/1000000)
  | 5 => (-1469821/1000000)
  | 6 => (-1121641/500000)
  | 7 => (-1564653/500000)
  | 8 => (-1959237/500000)
  | 9 => (-2189833/500000)
  | 10 => (-831593/200000)
  | 11 => (-3290451/1000000)
  | _ => 0
def shortNegativeR034Q00U : ℕ → ℚ
  | 0 => (-1496981/1000000)
  | 1 => (-633979/1000000)
  | 2 => (-115303/1000000)
  | 3 => (31533/1000000)
  | 4 => (-14897/100000)
  | 5 => (-280779/500000)
  | 6 => (-607711/500000)
  | 7 => (-2025173/1000000)
  | 8 => (-702371/250000)
  | 9 => (-397851/125000)
  | 10 => (-94037/31250)
  | 11 => (-1168299/500000)
  | _ => 0
private theorem shortNegativeR034Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR034Q00P shortNegativeR034Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR034Q00L (0:Fin 12)) (shortNegativeR034Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR034Q00P shortNegativeR034Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR034Q00L (1:Fin 12)) (shortNegativeR034Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR034Q00P shortNegativeR034Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR034Q00L (2:Fin 12)) (shortNegativeR034Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR034Q00P shortNegativeR034Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR034Q00L (3:Fin 12)) (shortNegativeR034Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR034Q00P shortNegativeR034Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR034Q00L (4:Fin 12)) (shortNegativeR034Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR034Q00P shortNegativeR034Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR034Q00L (5:Fin 12)) (shortNegativeR034Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR034Q00P shortNegativeR034Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR034Q00L (6:Fin 12)) (shortNegativeR034Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR034Q00P shortNegativeR034Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR034Q00L (7:Fin 12)) (shortNegativeR034Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR034Q00P shortNegativeR034Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR034Q00L (8:Fin 12)) (shortNegativeR034Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR034Q00P shortNegativeR034Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR034Q00L (9:Fin 12)) (shortNegativeR034Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR034Q00P shortNegativeR034Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR034Q00L (10:Fin 12)) (shortNegativeR034Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR034Q00P shortNegativeR034Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR034Q00L (11:Fin 12)) (shortNegativeR034Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR034Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR034Q00P shortNegativeR034Q00F (shortNegativeNodes12 k)).re (shortNegativeR034Q00L k) (shortNegativeR034Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR034Q00Point00
  · exact shortNegativeR034Q00Point01
  · exact shortNegativeR034Q00Point02
  · exact shortNegativeR034Q00Point03
  · exact shortNegativeR034Q00Point04
  · exact shortNegativeR034Q00Point05
  · exact shortNegativeR034Q00Point06
  · exact shortNegativeR034Q00Point07
  · exact shortNegativeR034Q00Point08
  · exact shortNegativeR034Q00Point09
  · exact shortNegativeR034Q00Point10
  · exact shortNegativeR034Q00Point11

theorem shortNegativeR034Q00Bound {t a : ℝ} (tl : ((23/20):ℝ)≤t) (tu : t≤((231/200):ℝ)) (al : ((46957605287933/65970697666560):ℝ)≤a) (au : a≤((47473001363453/65970697666560):ℝ)) : (((-3113905861951936045011501029235111/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-3650584569824102556735382762763085/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : shortNegativeR034Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (46957605287933/65970697666560) (47473001363453/65970697666560)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR034Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR034Q00F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR034Q00L shortNegativeR034Q00U (-3113905861951936045011501029235111/1298074214633706907132624082305024) (-3650584569824102556735382762763085/2596148429267413814265248164610048) shortNegativeR034Q00Samples (by decide +kernel)

def shortNegativeR034Q10T := Grid.ofRats (231/200) (29/25)
def shortNegativeR034Q10P : PrimalThetaParameters := ⟨⟨⟨31602619532505796241673,32102951630849251923844,true⟩,⟨0,0,true⟩⟩, ⟨⟨1351681575816802985191780,1366517327667013652254060,true⟩,⟨0,0,true⟩⟩, ⟨(-1094589322002698250666352),(-1064917818302345636023745),true⟩, ⟨4254734776184169631746871,4399713131668812295769394,true⟩⟩
theorem shortNegativeR034Q10P_ok : shortNegativeR034Q10P.encloses (primalThetaParameters shortNegativeR034Q10T (Grid.ofRats (46957605287933/65970697666560) (47473001363453/65970697666560))) := by decide +kernel

def shortNegativeR034Q10F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨486105472704117907400556,488018157521439954927220,true⟩,⟨2994768974895737025254499,3006552526966511585630127,true⟩,⟨⟨514692411764140714348850,529528163614351381459674,true⟩,⟨1082950174239588204981057,1097785926089798872099779,true⟩⟩⟩
  | 1 => ⟨⟨2054544985362916508377,2111805652194415051170,true⟩,⟨486105472704117907400556,488018157521439954927220,true⟩,⟨⟨(-1199048637290983683701009),(-1154541381740489121395910),true⟩,⟨(-299120279630902854934864),(-254613024080408292642143),true⟩⟩⟩
  | 2 => ⟨⟨226999114438586895,242670669155700132,true⟩,⟨2054544985362916508377,2111805652194415051170,true⟩,⟨⟨916407559007943400238628,990586318258721857722463,true⟩,⟨(-780288697001129038337987),(-706109937750350580857045),true⟩⟩⟩
  | 3 => ⟨⟨621266358445,774861022171,true⟩,⟨226999114438586895,242670669155700132,true⟩,⟨⟨(-70739350029849216485610),33110912921213136187025,true⟩,⟨1156854278719353501978327,1260704541670415854666886,true⟩⟩⟩
  | 4 => ⟨⟨(-34359688868),34359798372,true⟩,⟨621266358445,774861022171,true⟩,⟨⟨(-996666290186799683373737),(-863144523535453435520089),true⟩,⟨(-839274683604571439804427),(-705752916953225191952945),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359688868),34359798372,true⟩,⟨⟨1103244909348707900943394,1266438179700338043931790,true⟩,⟨(-321705259968107288882675),(-158511989616477145907292),true⟩⟩⟩
theorem shortNegativeR034Q10F_ok : ∀ n : Fin 6, (shortNegativeR034Q10F n).encloses (FactoredFrequency.build shortNegativeR034Q10T (Grid.ofRats (46957605287933/65970697666560) (47473001363453/65970697666560)) n) := by decide +kernel
def shortNegativeR034Q10L : ℕ → ℚ
  | 0 => (-426013/200000)
  | 1 => (-1314897/1000000)
  | 2 => (-851887/1000000)
  | 3 => (-372841/500000)
  | 4 => (-29911/31250)
  | 5 => (-149707/100000)
  | 6 => (-2261539/1000000)
  | 7 => (-3135167/1000000)
  | 8 => (-1956089/500000)
  | 9 => (-4364413/1000000)
  | 10 => (-4145881/1000000)
  | 11 => (-1646733/500000)
  | _ => 0
def shortNegativeR034Q10U : ℕ → ℚ
  | 0 => (-1518977/1000000)
  | 1 => (-666873/1000000)
  | 2 => (-151931/1000000)
  | 3 => (-5443/1000000)
  | 4 => (-181673/1000000)
  | 5 => (-294777/500000)
  | 6 => (-1236079/1000000)
  | 7 => (-2035467/1000000)
  | 8 => (-1404067/500000)
  | 9 => (-3173777/1000000)
  | 10 => (-187717/62500)
  | 11 => (-1171883/500000)
  | _ => 0
private theorem shortNegativeR034Q10Point00 : containedInReported (sampledFactoredPrimal shortNegativeR034Q10P shortNegativeR034Q10F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR034Q10L (0:Fin 12)) (shortNegativeR034Q10U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q10Point01 : containedInReported (sampledFactoredPrimal shortNegativeR034Q10P shortNegativeR034Q10F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR034Q10L (1:Fin 12)) (shortNegativeR034Q10U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q10Point02 : containedInReported (sampledFactoredPrimal shortNegativeR034Q10P shortNegativeR034Q10F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR034Q10L (2:Fin 12)) (shortNegativeR034Q10U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q10Point03 : containedInReported (sampledFactoredPrimal shortNegativeR034Q10P shortNegativeR034Q10F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR034Q10L (3:Fin 12)) (shortNegativeR034Q10U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q10Point04 : containedInReported (sampledFactoredPrimal shortNegativeR034Q10P shortNegativeR034Q10F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR034Q10L (4:Fin 12)) (shortNegativeR034Q10U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q10Point05 : containedInReported (sampledFactoredPrimal shortNegativeR034Q10P shortNegativeR034Q10F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR034Q10L (5:Fin 12)) (shortNegativeR034Q10U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q10Point06 : containedInReported (sampledFactoredPrimal shortNegativeR034Q10P shortNegativeR034Q10F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR034Q10L (6:Fin 12)) (shortNegativeR034Q10U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q10Point07 : containedInReported (sampledFactoredPrimal shortNegativeR034Q10P shortNegativeR034Q10F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR034Q10L (7:Fin 12)) (shortNegativeR034Q10U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q10Point08 : containedInReported (sampledFactoredPrimal shortNegativeR034Q10P shortNegativeR034Q10F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR034Q10L (8:Fin 12)) (shortNegativeR034Q10U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q10Point09 : containedInReported (sampledFactoredPrimal shortNegativeR034Q10P shortNegativeR034Q10F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR034Q10L (9:Fin 12)) (shortNegativeR034Q10U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q10Point10 : containedInReported (sampledFactoredPrimal shortNegativeR034Q10P shortNegativeR034Q10F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR034Q10L (10:Fin 12)) (shortNegativeR034Q10U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR034Q10Point11 : containedInReported (sampledFactoredPrimal shortNegativeR034Q10P shortNegativeR034Q10F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR034Q10L (11:Fin 12)) (shortNegativeR034Q10U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR034Q10Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR034Q10P shortNegativeR034Q10F (shortNegativeNodes12 k)).re (shortNegativeR034Q10L k) (shortNegativeR034Q10U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR034Q10Point00
  · exact shortNegativeR034Q10Point01
  · exact shortNegativeR034Q10Point02
  · exact shortNegativeR034Q10Point03
  · exact shortNegativeR034Q10Point04
  · exact shortNegativeR034Q10Point05
  · exact shortNegativeR034Q10Point06
  · exact shortNegativeR034Q10Point07
  · exact shortNegativeR034Q10Point08
  · exact shortNegativeR034Q10Point09
  · exact shortNegativeR034Q10Point10
  · exact shortNegativeR034Q10Point11

theorem shortNegativeR034Q10Bound {t a : ℝ} (tl : ((231/200):ℝ)≤t) (tu : t≤((29/25):ℝ)) (al : ((46957605287933/65970697666560):ℝ)≤a) (au : a≤((47473001363453/65970697666560):ℝ)) : (((-3113905861951936045011501029235111/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-3650584569824102556735382762763085/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : shortNegativeR034Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (46957605287933/65970697666560) (47473001363453/65970697666560)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR034Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR034Q10F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR034Q10L shortNegativeR034Q10U (-3113905861951936045011501029235111/1298074214633706907132624082305024) (-3650584569824102556735382762763085/2596148429267413814265248164610048) shortNegativeR034Q10Samples (by decide +kernel)

theorem short_original_negative_034 {t a : ℝ} (tb : RealMem negative_034.t t) (ab : RealMem negative_034.a a) : RealMem negative_034.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((23/20):ℝ) ((29/25):ℝ) := by simpa [negative_034,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((23/20):ℝ)<((29/25):ℝ)) tB
  have aB : a∈Icc ((46957605287933/65970697666560):ℝ) ((47473001363453/65970697666560):ℝ) := by simpa [negative_034,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((46957605287933/65970697666560):ℝ)<((47473001363453/65970697666560):ℝ)) aB
  fin_cases ti <;> fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR034Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_034,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR034Q10Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_034,RealMem] using v

def shortNegativeR035Q00T := Grid.ofRats (29/25) (233/200)
def shortNegativeR035Q00P : PrimalThetaParameters := ⟨⟨⟨31110085228385405399241,31602619532574515718919,true⟩,⟨0,0,true⟩⟩, ⟨⟨1362223651138088012974177,1377059402988298680036490,true⟩,⟨0,0,true⟩⟩, ⟨(-1073505171360128195101491),(-1043833667659775580458952),true⟩, ⟨4215615417204092467794381,4358416404815361926434902,true⟩⟩
theorem shortNegativeR035Q00P_ok : shortNegativeR035Q00P.encloses (primalThetaParameters shortNegativeR035Q00T (Grid.ofRats (78873064076223/109951162777600) (79732057535423/109951162777600))) := by decide +kernel

def shortNegativeR035Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨484200284253861930143975,486105472704186626895275,true⟩,⟨3006552526966442866043072,3018382443915632753418450,true⟩,⟨⟨505164453443960024839290,520000205294170691950048,true⟩,⟨1087461566273662920922860,1102297318123873588041643,true⟩⟩⟩
  | 1 => ⟨⟨1998836915996950134447,2054544985431635985226,true⟩,⟨484200284253861930143975,486105472704186626895275,true⟩,⟨⟨(-1191403802640656966072756),(-1146896547090162403767244),true⟩,⟨(-329807697725694976476452),(-285300442175200414182801),true⟩⟩⟩
  | 2 => ⟨⟨212339681150090972,226999183158063632,true⟩,⟨1998836915996950134447,2054544985431635985226,true⟩,⟨⟨947895349780129377802213,1022074109030907835285587,true⟩,⟨(-738022129729734265754621),(-663843370478955808275153),true⟩⟩⟩
  | 3 => ⟨⟨546119442728,689985835182,true⟩,⟨212339681150090972,226999183158063632,true⟩,⟨⟨(-144444086774268634814180),(-40593823823206282139942),true⟩,⟨1153455256717894317700383,1257305519668956670389936,true⟩⟩⟩
  | 4 => ⟨⟨(-34359697532),34359787869,true⟩,⟨546119442728,689985835182,true⟩,⟨⟨(-933237877158575954655476),(-799716110507229706801070),true⟩,⟨(-909802552811350793801814),(-776280786160004545947726),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359697532),34359787869,true⟩,⟨⟨1120794628271498496872286,1283987898623128639857523,true⟩,⟨(-207123074289158425172021),(-43929803937528282201609),true⟩⟩⟩
theorem shortNegativeR035Q00F_ok : ∀ n : Fin 6, (shortNegativeR035Q00F n).encloses (FactoredFrequency.build shortNegativeR035Q00T (Grid.ofRats (78873064076223/109951162777600) (79732057535423/109951162777600)) n) := by decide +kernel
def shortNegativeR035Q00L : ℕ → ℚ
  | 0 => (-438379/200000)
  | 1 => (-69501/50000)
  | 2 => (-920263/1000000)
  | 3 => (-159681/200000)
  | 4 => (-19789/20000)
  | 5 => (-15049/10000)
  | 6 => (-2242597/1000000)
  | 7 => (-1545427/500000)
  | 8 => (-1927611/500000)
  | 9 => (-1078119/250000)
  | 10 => (-412631/100000)
  | 11 => (-66399/20000)
  | _ => 0
def shortNegativeR035Q00U : ℕ → ℚ
  | 0 => (-198253/125000)
  | 1 => (-46757/62500)
  | 2 => (-113421/500000)
  | 3 => (-8001/125000)
  | 4 => (-219549/1000000)
  | 5 => (-1891/3125)
  | 6 => (-1227669/1000000)
  | 7 => (-100221/50000)
  | 8 => (-2763237/1000000)
  | 9 => (-3133523/1000000)
  | 10 => (-2993317/1000000)
  | 11 => (-1187887/500000)
  | _ => 0
private theorem shortNegativeR035Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR035Q00P shortNegativeR035Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR035Q00L (0:Fin 12)) (shortNegativeR035Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR035Q00P shortNegativeR035Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR035Q00L (1:Fin 12)) (shortNegativeR035Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR035Q00P shortNegativeR035Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR035Q00L (2:Fin 12)) (shortNegativeR035Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR035Q00P shortNegativeR035Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR035Q00L (3:Fin 12)) (shortNegativeR035Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR035Q00P shortNegativeR035Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR035Q00L (4:Fin 12)) (shortNegativeR035Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR035Q00P shortNegativeR035Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR035Q00L (5:Fin 12)) (shortNegativeR035Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR035Q00P shortNegativeR035Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR035Q00L (6:Fin 12)) (shortNegativeR035Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR035Q00P shortNegativeR035Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR035Q00L (7:Fin 12)) (shortNegativeR035Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR035Q00P shortNegativeR035Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR035Q00L (8:Fin 12)) (shortNegativeR035Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR035Q00P shortNegativeR035Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR035Q00L (9:Fin 12)) (shortNegativeR035Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR035Q00P shortNegativeR035Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR035Q00L (10:Fin 12)) (shortNegativeR035Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR035Q00P shortNegativeR035Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR035Q00L (11:Fin 12)) (shortNegativeR035Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR035Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR035Q00P shortNegativeR035Q00F (shortNegativeNodes12 k)).re (shortNegativeR035Q00L k) (shortNegativeR035Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR035Q00Point00
  · exact shortNegativeR035Q00Point01
  · exact shortNegativeR035Q00Point02
  · exact shortNegativeR035Q00Point03
  · exact shortNegativeR035Q00Point04
  · exact shortNegativeR035Q00Point05
  · exact shortNegativeR035Q00Point06
  · exact shortNegativeR035Q00Point07
  · exact shortNegativeR035Q00Point08
  · exact shortNegativeR035Q00Point09
  · exact shortNegativeR035Q00Point10
  · exact shortNegativeR035Q00Point11

theorem shortNegativeR035Q00Bound {t a : ℝ} (tl : ((29/25):ℝ)≤t) (tu : t≤((233/200):ℝ)) (al : ((78873064076223/109951162777600):ℝ)≤a) (au : a≤((79732057535423/109951162777600):ℝ)) : (((-1570102002051349837454900731894085/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-940284627715098395094925258316101/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR035Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (78873064076223/109951162777600) (79732057535423/109951162777600)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR035Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR035Q00F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR035Q00L shortNegativeR035Q00U (-1570102002051349837454900731894085/649037107316853453566312041152512) (-940284627715098395094925258316101/649037107316853453566312041152512) shortNegativeR035Q00Samples (by decide +kernel)

def shortNegativeR035Q10T := Grid.ofRats (233/200) (117/100)
def shortNegativeR035Q10P : PrimalThetaParameters := ⟨⟨⟨30625227187952129823872,31110085228454124876479,true⟩,⟨0,0,true⟩⟩, ⟨⟨1362223651138088012974177,1377059402988298680036490,true⟩,⟨0,0,true⟩⟩, ⟨(-1073505171360128195101491),(-1043833667659775580458952),true⟩, ⟨4205405433491733423356484,4347446885166560291497013,true⟩⟩
theorem shortNegativeR035Q10P_ok : shortNegativeR035Q10P.encloses (primalThetaParameters shortNegativeR035Q10T (Grid.ofRats (78873064076223/109951162777600) (79732057535423/109951162777600))) := by decide +kernel

def shortNegativeR035Q10F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨482302562790165056827103,484200284253930649638662,true⟩,⟨3018382443915564033830998,3030258908175591795244134,true⟩,⟨⟨505164453443960024839290,520000205294170691950048,true⟩,⟨1087461566273662920922860,1102297318123873588041643,true⟩⟩⟩
  | 1 => ⟨⟨1944639346043038851448,1998836916065669611292,true⟩,⟨482302562790165056827103,484200284253930649638662,true⟩,⟨⟨(-1191403802640656966072756),(-1146896547090162403767244),true⟩,⟨(-329807697725694976476452),(-285300442175200414182801),true⟩⟩⟩
  | 2 => ⟨⟨198626942972468734,212339749869567709,true⟩,⟨1944639346043038851448,1998836916065669611292,true⟩,⟨⟨947895349780129377802213,1022074109030907835285587,true⟩,⟨(-738022129729734265754621),(-663843370478955808275153),true⟩⟩⟩
  | 3 => ⟨⟨479585757889,614838919465,true⟩,⟨198626942972468734,212339749869567709,true⟩,⟨⟨(-144444086774268634814180),(-40593823823206282139942),true⟩,⟨1153455256717894317700383,1257305519668956670389936,true⟩⟩⟩
  | 4 => ⟨⟨(-34359704680),34359779205,true⟩,⟨479585757889,614838919465,true⟩,⟨⟨(-933237877158575954655476),(-799716110507229706801070),true⟩,⟨(-909802552811350793801814),(-776280786160004545947726),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359704680),34359779205,true⟩,⟨⟨1120794628271498496872286,1283987898623128639857523,true⟩,⟨(-207123074289158425172021),(-43929803937528282201609),true⟩⟩⟩
theorem shortNegativeR035Q10F_ok : ∀ n : Fin 6, (shortNegativeR035Q10F n).encloses (FactoredFrequency.build shortNegativeR035Q10T (Grid.ofRats (78873064076223/109951162777600) (79732057535423/109951162777600)) n) := by decide +kernel
def shortNegativeR035Q10L : ℕ → ℚ
  | 0 => (-552847/250000)
  | 1 => (-177607/125000)
  | 2 => (-955137/1000000)
  | 3 => (-833149/1000000)
  | 4 => (-1021517/1000000)
  | 5 => (-1531393/1000000)
  | 6 => (-2260413/1000000)
  | 7 => (-1548377/500000)
  | 8 => (-1924723/500000)
  | 9 => (-4297883/1000000)
  | 10 => (-822849/200000)
  | 11 => (-3321829/1000000)
  | _ => 0
def shortNegativeR035Q10U : ℕ → ℚ
  | 0 => (-1606147/1000000)
  | 1 => (-779107/1000000)
  | 2 => (-261951/1000000)
  | 3 => (-49409/500000)
  | 4 => (-62853/250000)
  | 5 => (-3953/6250)
  | 6 => (-249589/200000)
  | 7 => (-402943/200000)
  | 8 => (-2762301/1000000)
  | 9 => (-3125009/1000000)
  | 10 => (-2987519/1000000)
  | 11 => (-119091/50000)
  | _ => 0
private theorem shortNegativeR035Q10Point00 : containedInReported (sampledFactoredPrimal shortNegativeR035Q10P shortNegativeR035Q10F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR035Q10L (0:Fin 12)) (shortNegativeR035Q10U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q10Point01 : containedInReported (sampledFactoredPrimal shortNegativeR035Q10P shortNegativeR035Q10F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR035Q10L (1:Fin 12)) (shortNegativeR035Q10U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q10Point02 : containedInReported (sampledFactoredPrimal shortNegativeR035Q10P shortNegativeR035Q10F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR035Q10L (2:Fin 12)) (shortNegativeR035Q10U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q10Point03 : containedInReported (sampledFactoredPrimal shortNegativeR035Q10P shortNegativeR035Q10F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR035Q10L (3:Fin 12)) (shortNegativeR035Q10U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q10Point04 : containedInReported (sampledFactoredPrimal shortNegativeR035Q10P shortNegativeR035Q10F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR035Q10L (4:Fin 12)) (shortNegativeR035Q10U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q10Point05 : containedInReported (sampledFactoredPrimal shortNegativeR035Q10P shortNegativeR035Q10F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR035Q10L (5:Fin 12)) (shortNegativeR035Q10U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q10Point06 : containedInReported (sampledFactoredPrimal shortNegativeR035Q10P shortNegativeR035Q10F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR035Q10L (6:Fin 12)) (shortNegativeR035Q10U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q10Point07 : containedInReported (sampledFactoredPrimal shortNegativeR035Q10P shortNegativeR035Q10F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR035Q10L (7:Fin 12)) (shortNegativeR035Q10U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q10Point08 : containedInReported (sampledFactoredPrimal shortNegativeR035Q10P shortNegativeR035Q10F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR035Q10L (8:Fin 12)) (shortNegativeR035Q10U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q10Point09 : containedInReported (sampledFactoredPrimal shortNegativeR035Q10P shortNegativeR035Q10F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR035Q10L (9:Fin 12)) (shortNegativeR035Q10U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q10Point10 : containedInReported (sampledFactoredPrimal shortNegativeR035Q10P shortNegativeR035Q10F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR035Q10L (10:Fin 12)) (shortNegativeR035Q10U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR035Q10Point11 : containedInReported (sampledFactoredPrimal shortNegativeR035Q10P shortNegativeR035Q10F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR035Q10L (11:Fin 12)) (shortNegativeR035Q10U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR035Q10Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR035Q10P shortNegativeR035Q10F (shortNegativeNodes12 k)).re (shortNegativeR035Q10L k) (shortNegativeR035Q10U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR035Q10Point00
  · exact shortNegativeR035Q10Point01
  · exact shortNegativeR035Q10Point02
  · exact shortNegativeR035Q10Point03
  · exact shortNegativeR035Q10Point04
  · exact shortNegativeR035Q10Point05
  · exact shortNegativeR035Q10Point06
  · exact shortNegativeR035Q10Point07
  · exact shortNegativeR035Q10Point08
  · exact shortNegativeR035Q10Point09
  · exact shortNegativeR035Q10Point10
  · exact shortNegativeR035Q10Point11

theorem shortNegativeR035Q10Bound {t a : ℝ} (tl : ((233/200):ℝ)≤t) (tu : t≤((117/100):ℝ)) (al : ((78873064076223/109951162777600):ℝ)≤a) (au : a≤((79732057535423/109951162777600):ℝ)) : (((-1570102002051349837454900731894085/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-940284627715098395094925258316101/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR035Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (78873064076223/109951162777600) (79732057535423/109951162777600)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR035Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR035Q10F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR035Q10L shortNegativeR035Q10U (-1570102002051349837454900731894085/649037107316853453566312041152512) (-940284627715098395094925258316101/649037107316853453566312041152512) shortNegativeR035Q10Samples (by decide +kernel)

theorem short_original_negative_035 {t a : ℝ} (tb : RealMem negative_035.t t) (ab : RealMem negative_035.a a) : RealMem negative_035.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((29/25):ℝ) ((117/100):ℝ) := by simpa [negative_035,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((29/25):ℝ)<((117/100):ℝ)) tB
  have aB : a∈Icc ((78873064076223/109951162777600):ℝ) ((79732057535423/109951162777600):ℝ) := by simpa [negative_035,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((78873064076223/109951162777600):ℝ)<((79732057535423/109951162777600):ℝ)) aB
  fin_cases ti <;> fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR035Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_035,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR035Q10Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_035,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_032
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_033
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_034
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_035
