import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip032

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR039Q00T := Grid.ofRats (6/5) (121/100)
def shortNegativeR039Q00P : PrimalThetaParameters := ⟨⟨⟨27008736320017587240873,27870709749809716696314,true⟩,⟨0,0,true⟩⟩, ⟨⟨1406949430228214414176120,1411894680844997116184417,true⟩,⟨0,0,true⟩⟩, ⟨(-984053613179875392697320),(-974163111946378708163322),true⟩, ⟨4068324643860835685261817,4127880727206538172388754,true⟩⟩
theorem shortNegativeR039Q00P_ok : shortNegativeR039Q00P.encloses (primalThetaParameters shortNegativeR039Q00T (Grid.ofRats (1221940455258763/1649267441664000) (1226235422554763/1649267441664000))) := by decide +kernel

def shortNegativeR039Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨467386114736092470411650,471071409873494097462913,true⟩,⟨3102505494280535070626756,3126968455526416431629189,true⟩,⟨⟨473810967857521559300617,478756218474304261357490,true⟩,⟨1108677938842061697308695,1113623189458844399374358,true⟩⟩⟩
  | 1 => ⟨⟨1560747772752884163923,1648956921798901937691,true⟩,⟨467386114736092470411650,471071409873494097462913,true⟩,⟨⟨(-1140564417191204219810516),(-1125728665340993552664525),true⟩,⟨(-428702285021359656518304),(-413866533171148989382105),true⟩⟩⟩
  | 2 => ⟨⟨116437835963055968,133070062440351428,true⟩,⟨1560747772752884163923,1648956921798901937691,true⟩,⟨⟨1074123840533453631780372,1098850093617092263991138,true⟩,⟨(-542502455121087876961686),(-517776202037449244758572),true⟩⟩⟩
  | 3 => ⟨⟨159711150491,281930619512,true⟩,⟨116437835963055968,133070062440351428,true⟩,⟨⟨(-382582194069429606617742),(-347965439752363009316351),true⟩,⟨1135113713921921441422373,1169730468238988038734599,true⟩⟩⟩
  | 4 => ⟨⟨(-34359731142),34359748987,true⟩,⟨159711150491,281930619512,true⟩,⟨⟨(-604975947731303050261150),(-560468692180808487893930),true⟩,⟨(-1081468589506781305022593),(-1036961333956286742648815),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359731142),34359748987,true⟩,⟨⟨1141732058987448717115588,1196129815771371244513359,true⟩,⟨281187406919491619501718,335585163703414146887645,true⟩⟩⟩
theorem shortNegativeR039Q00F_ok : ∀ n : Fin 6, (shortNegativeR039Q00F n).encloses (FactoredFrequency.build shortNegativeR039Q00T (Grid.ofRats (1221940455258763/1649267441664000) (1226235422554763/1649267441664000)) n) := by decide +kernel
def shortNegativeR039Q00L : ℕ → ℚ
  | 0 => (-1229543/500000)
  | 1 => (-352603/200000)
  | 2 => (-1290927/1000000)
  | 3 => (-55871/50000)
  | 4 => (-152941/125000)
  | 5 => (-323447/200000)
  | 6 => (-1106563/500000)
  | 7 => (-2912443/1000000)
  | 8 => (-357963/100000)
  | 9 => (-2000519/500000)
  | 10 => (-3927681/1000000)
  | 11 => (-1668533/500000)
  | _ => 0
def shortNegativeR039Q00U : ℕ → ℚ
  | 0 => (-1881377/1000000)
  | 1 => (-1153181/1000000)
  | 2 => (-646679/1000000)
  | 3 => (-218849/500000)
  | 4 => (-25769/50000)
  | 5 => (-407041/500000)
  | 6 => (-665319/500000)
  | 7 => (-1992581/1000000)
  | 8 => (-2645119/1000000)
  | 9 => (-1501911/500000)
  | 10 => (-741183/250000)
  | 11 => (-2529593/1000000)
  | _ => 0
private theorem shortNegativeR039Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR039Q00P shortNegativeR039Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR039Q00L (0:Fin 12)) (shortNegativeR039Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR039Q00P shortNegativeR039Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR039Q00L (1:Fin 12)) (shortNegativeR039Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR039Q00P shortNegativeR039Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR039Q00L (2:Fin 12)) (shortNegativeR039Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR039Q00P shortNegativeR039Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR039Q00L (3:Fin 12)) (shortNegativeR039Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR039Q00P shortNegativeR039Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR039Q00L (4:Fin 12)) (shortNegativeR039Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR039Q00P shortNegativeR039Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR039Q00L (5:Fin 12)) (shortNegativeR039Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR039Q00P shortNegativeR039Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR039Q00L (6:Fin 12)) (shortNegativeR039Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR039Q00P shortNegativeR039Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR039Q00L (7:Fin 12)) (shortNegativeR039Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR039Q00P shortNegativeR039Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR039Q00L (8:Fin 12)) (shortNegativeR039Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR039Q00P shortNegativeR039Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR039Q00L (9:Fin 12)) (shortNegativeR039Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR039Q00P shortNegativeR039Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR039Q00L (10:Fin 12)) (shortNegativeR039Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR039Q00P shortNegativeR039Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR039Q00L (11:Fin 12)) (shortNegativeR039Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR039Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR039Q00P shortNegativeR039Q00F (shortNegativeNodes12 k)).re (shortNegativeR039Q00L k) (shortNegativeR039Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR039Q00Point00
  · exact shortNegativeR039Q00Point01
  · exact shortNegativeR039Q00Point02
  · exact shortNegativeR039Q00Point03
  · exact shortNegativeR039Q00Point04
  · exact shortNegativeR039Q00Point05
  · exact shortNegativeR039Q00Point06
  · exact shortNegativeR039Q00Point07
  · exact shortNegativeR039Q00Point08
  · exact shortNegativeR039Q00Point09
  · exact shortNegativeR039Q00Point10
  · exact shortNegativeR039Q00Point11

theorem shortNegativeR039Q00Bound {t a : ℝ} (tl : ((6/5):ℝ)≤t) (tu : t≤((121/100):ℝ)) (al : ((1221940455258763/1649267441664000):ℝ)≤a) (au : a≤((1226235422554763/1649267441664000):ℝ)) : (((-3224606882459938529796398247433057/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2073439929862924787389596838777697/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR039Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1221940455258763/1649267441664000) (1226235422554763/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR039Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR039Q00F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR039Q00L shortNegativeR039Q00U (-3224606882459938529796398247433057/1298074214633706907132624082305024) (-2073439929862924787389596838777697/1298074214633706907132624082305024) shortNegativeR039Q00Samples (by decide +kernel)

def shortNegativeR039Q01T := Grid.ofRats (6/5) (121/100)
def shortNegativeR039Q01P : PrimalThetaParameters := ⟨⟨⟨27008736320017587240873,27870709749809716696314,true⟩,⟨0,0,true⟩⟩, ⟨⟨1411894680844928396703183,1416839931461711098711496,true⟩,⟨0,0,true⟩⟩, ⟨(-974163111946447427643163),(-964272610712950743109194),true⟩, ⟨4056356692632419417989412,4115738198065961900293062,true⟩⟩
theorem shortNegativeR039Q01P_ok : shortNegativeR039Q01P.encloses (primalThetaParameters shortNegativeR039Q01T (Grid.ofRats (1226235422554763/1649267441664000) (410176796616921/549755813888000))) := by decide +kernel

def shortNegativeR039Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨467386114736092470411650,471071409873494097462913,true⟩,⟨3102505494280535070626756,3126968455526416431629189,true⟩,⟨⟨469261706032867562809231,474206956649650264865917,true⟩,⟨1110616929922865980817557,1115562180539648682883102,true⟩⟩⟩
  | 1 => ⟨⟨1560747772752884163923,1648956921798901937691,true⟩,⟨467386114736092470411650,471071409873494097462913,true⟩,⟨⟨(-1135309285585265577191392),(-1120473533735054910045122),true⟩,⟨(-442576014244635676334934),(-427740262394425009198192),true⟩⟩⟩
  | 2 => ⟨⟨116437835963055968,133070062440351428,true⟩,⟨1560747772752884163923,1648956921798901937691,true⟩,⟨⟨1084738818924213171201199,1109465072007851803411759,true⟩,⟨(-520171120359905638350449),(-495444867276267006148012),true⟩⟩⟩
  | 3 => ⟨⟨159711150491,281930619512,true⟩,⟨116437835963055968,133070062440351428,true⟩,⟨⟨(-415426755906607543991629),(-380810001589540946689263),true⟩,⟨1124183363430906018241616,1158800117747972615554213,true⟩⟩⟩
  | 4 => ⟨⟨(-34359731142),34359748987,true⟩,⟨159711150491,281930619512,true⟩,⟨⟨(-565594324867312656909924),(-521087069316818094543251),true⟩,⟨(-1102199239467989601560495),(-1057691983917495039186435),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359731142),34359748987,true⟩,⟨⟨1126677181426341765523361,1181074938210264292922692,true⟩,⟨333455632059649319901737,387853388843571847290144,true⟩⟩⟩
theorem shortNegativeR039Q01F_ok : ∀ n : Fin 6, (shortNegativeR039Q01F n).encloses (FactoredFrequency.build shortNegativeR039Q01T (Grid.ofRats (1226235422554763/1649267441664000) (410176796616921/549755813888000)) n) := by decide +kernel
def shortNegativeR039Q01L : ℕ → ℚ
  | 0 => (-2472503/1000000)
  | 1 => (-889517/500000)
  | 2 => (-260671/200000)
  | 3 => (-562099/500000)
  | 4 => (-48929/40000)
  | 5 => (-201143/125000)
  | 6 => (-137347/62500)
  | 7 => (-2891241/1000000)
  | 8 => (-3557597/1000000)
  | 9 => (-1991637/500000)
  | 10 => (-784053/200000)
  | 11 => (-417759/125000)
  | _ => 0
def shortNegativeR039Q01U : ℕ → ℚ
  | 0 => (-948957/500000)
  | 1 => (-1171619/1000000)
  | 2 => (-331549/500000)
  | 3 => (-448167/1000000)
  | 4 => (-259359/500000)
  | 5 => (-810127/1000000)
  | 6 => (-1319809/1000000)
  | 7 => (-1976599/1000000)
  | 8 => (-2627043/1000000)
  | 9 => (-2990629/1000000)
  | 10 => (-118461/40000)
  | 11 => (-634427/250000)
  | _ => 0
private theorem shortNegativeR039Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR039Q01P shortNegativeR039Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR039Q01L (0:Fin 12)) (shortNegativeR039Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR039Q01P shortNegativeR039Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR039Q01L (1:Fin 12)) (shortNegativeR039Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR039Q01P shortNegativeR039Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR039Q01L (2:Fin 12)) (shortNegativeR039Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR039Q01P shortNegativeR039Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR039Q01L (3:Fin 12)) (shortNegativeR039Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR039Q01P shortNegativeR039Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR039Q01L (4:Fin 12)) (shortNegativeR039Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR039Q01P shortNegativeR039Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR039Q01L (5:Fin 12)) (shortNegativeR039Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR039Q01P shortNegativeR039Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR039Q01L (6:Fin 12)) (shortNegativeR039Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR039Q01P shortNegativeR039Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR039Q01L (7:Fin 12)) (shortNegativeR039Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR039Q01P shortNegativeR039Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR039Q01L (8:Fin 12)) (shortNegativeR039Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR039Q01P shortNegativeR039Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR039Q01L (9:Fin 12)) (shortNegativeR039Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR039Q01P shortNegativeR039Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR039Q01L (10:Fin 12)) (shortNegativeR039Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR039Q01P shortNegativeR039Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR039Q01L (11:Fin 12)) (shortNegativeR039Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR039Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR039Q01P shortNegativeR039Q01F (shortNegativeNodes12 k)).re (shortNegativeR039Q01L k) (shortNegativeR039Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR039Q01Point00
  · exact shortNegativeR039Q01Point01
  · exact shortNegativeR039Q01Point02
  · exact shortNegativeR039Q01Point03
  · exact shortNegativeR039Q01Point04
  · exact shortNegativeR039Q01Point05
  · exact shortNegativeR039Q01Point06
  · exact shortNegativeR039Q01Point07
  · exact shortNegativeR039Q01Point08
  · exact shortNegativeR039Q01Point09
  · exact shortNegativeR039Q01Point10
  · exact shortNegativeR039Q01Point11

theorem shortNegativeR039Q01Bound {t a : ℝ} (tl : ((6/5):ℝ)≤t) (tu : t≤((121/100):ℝ)) (al : ((1226235422554763/1649267441664000):ℝ)≤a) (au : a≤((410176796616921/549755813888000):ℝ)) : (((-3224606882459938529796398247433057/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2073439929862924787389596838777697/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR039Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1226235422554763/1649267441664000) (410176796616921/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR039Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR039Q01F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR039Q01L shortNegativeR039Q01U (-3224606882459938529796398247433057/1298074214633706907132624082305024) (-2073439929862924787389596838777697/1298074214633706907132624082305024) shortNegativeR039Q01Samples (by decide +kernel)

def shortNegativeR039Q02T := Grid.ofRats (6/5) (121/100)
def shortNegativeR039Q02P : PrimalThetaParameters := ⟨⟨⟨27008736320017587240873,27870709749809716696314,true⟩,⟨0,0,true⟩⟩, ⟨⟨1416839931461642379230247,1421785182078425081238576,true⟩,⟨0,0,true⟩⟩, ⟨(-964272610713019462589004),(-954382109479522778055066),true⟩, ⟨4044566887456289415836228,4103776578449508629959332,true⟩⟩
theorem shortNegativeR039Q02P_ok : shortNegativeR039Q02P.encloses (primalThetaParameters shortNegativeR039Q02T (Grid.ofRats (410176796616921/549755813888000) (1234825357146763/1649267441664000))) := by decide +kernel

def shortNegativeR039Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨467386114736092470411650,471071409873494097462913,true⟩,⟨3102505494280535070626756,3126968455526416431629189,true⟩,⟨⟨464704550625143814404058,469649801241926516461129,true⟩,⟨1112537295552257157318772,1117482546169039859384780,true⟩⟩⟩
  | 1 => ⟨⟨1560747772752884163923,1648956921798901937691,true⟩,⟨467386114736092470411650,471071409873494097462913,true⟩,⟨⟨(-1129884297681742772097100),(-1115048545831532104950462),true⟩,⟨(-456384210252918203937452),(-441548458402707536800074),true⟩⟩⟩
  | 2 => ⟨⟨116437835963055968,133070062440351428,true⟩,⟨1560747772752884163923,1648956921798901937691,true⟩,⟨⟨1094894864450068598102271,1119621117533707230312639,true⟩,⟨(-497627362515903007730958),(-472901109432264375529167),true⟩⟩⟩
  | 3 => ⟨⟨159711150491,281930619512,true⟩,⟨116437835963055968,133070062440351428,true⟩,⟨⟨(-447944913393799841494345),(-413328159076733244191730),true⟩,⟨1112317140873967100318774,1146933895191033697631008,true⟩⟩⟩
  | 4 => ⟨⟨(-34359731142),34359748987,true⟩,⟨159711150491,281930619512,true⟩,⟨⟨(-525476349943069245517382),(-480969094392574683150726),true⟩,⟨(-1121466313848743242806913),(-1076959058298248680432055),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359731142),34359748987,true⟩,⟨⟨1109286434448168156597798,1163684191232090683998960,true⟩,⟨384993759860562699067022,439391516644485226458216,true⟩⟩⟩
theorem shortNegativeR039Q02F_ok : ∀ n : Fin 6, (shortNegativeR039Q02F n).encloses (FactoredFrequency.build shortNegativeR039Q02T (Grid.ofRats (410176796616921/549755813888000) (1234825357146763/1649267441664000)) n) := by decide +kernel
def shortNegativeR039Q02L : ℕ → ℚ
  | 0 => (-2485793/1000000)
  | 1 => (-359/200)
  | 2 => (-657911/500000)
  | 3 => (-141383/125000)
  | 4 => (-611523/500000)
  | 5 => (-800603/500000)
  | 6 => (-545537/250000)
  | 7 => (-2870199/1000000)
  | 8 => (-441957/125000)
  | 9 => (-991373/250000)
  | 10 => (-782543/200000)
  | 11 => (-3346901/1000000)
  | _ => 0
def shortNegativeR039Q02U : ℕ → ℚ
  | 0 => (-76573/40000)
  | 1 => (-59501/50000)
  | 2 => (-679543/1000000)
  | 3 => (-458721/1000000)
  | 4 => (-26109/50000)
  | 5 => (-806327/1000000)
  | 6 => (-40911/31250)
  | 7 => (-980389/500000)
  | 8 => (-2609079/1000000)
  | 9 => (-744363/250000)
  | 10 => (-2958229/1000000)
  | 11 => (-2545679/1000000)
  | _ => 0
private theorem shortNegativeR039Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR039Q02P shortNegativeR039Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR039Q02L (0:Fin 12)) (shortNegativeR039Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR039Q02P shortNegativeR039Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR039Q02L (1:Fin 12)) (shortNegativeR039Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR039Q02P shortNegativeR039Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR039Q02L (2:Fin 12)) (shortNegativeR039Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR039Q02P shortNegativeR039Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR039Q02L (3:Fin 12)) (shortNegativeR039Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR039Q02P shortNegativeR039Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR039Q02L (4:Fin 12)) (shortNegativeR039Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR039Q02P shortNegativeR039Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR039Q02L (5:Fin 12)) (shortNegativeR039Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR039Q02P shortNegativeR039Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR039Q02L (6:Fin 12)) (shortNegativeR039Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR039Q02P shortNegativeR039Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR039Q02L (7:Fin 12)) (shortNegativeR039Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR039Q02P shortNegativeR039Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR039Q02L (8:Fin 12)) (shortNegativeR039Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR039Q02P shortNegativeR039Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR039Q02L (9:Fin 12)) (shortNegativeR039Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR039Q02P shortNegativeR039Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR039Q02L (10:Fin 12)) (shortNegativeR039Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR039Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR039Q02P shortNegativeR039Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR039Q02L (11:Fin 12)) (shortNegativeR039Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR039Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR039Q02P shortNegativeR039Q02F (shortNegativeNodes12 k)).re (shortNegativeR039Q02L k) (shortNegativeR039Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR039Q02Point00
  · exact shortNegativeR039Q02Point01
  · exact shortNegativeR039Q02Point02
  · exact shortNegativeR039Q02Point03
  · exact shortNegativeR039Q02Point04
  · exact shortNegativeR039Q02Point05
  · exact shortNegativeR039Q02Point06
  · exact shortNegativeR039Q02Point07
  · exact shortNegativeR039Q02Point08
  · exact shortNegativeR039Q02Point09
  · exact shortNegativeR039Q02Point10
  · exact shortNegativeR039Q02Point11

theorem shortNegativeR039Q02Bound {t a : ℝ} (tl : ((6/5):ℝ)≤t) (tu : t≤((121/100):ℝ)) (al : ((410176796616921/549755813888000):ℝ)≤a) (au : a≤((1234825357146763/1649267441664000):ℝ)) : (((-3224606882459938529796398247433057/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2073439929862924787389596838777697/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR039Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (410176796616921/549755813888000) (1234825357146763/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR039Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR039Q02F_ok n) ts asb
  exact factored_negative_12_samples 1440 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip032Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR039Q02L shortNegativeR039Q02U (-3224606882459938529796398247433057/1298074214633706907132624082305024) (-2073439929862924787389596838777697/1298074214633706907132624082305024) shortNegativeR039Q02Samples (by decide +kernel)

theorem short_original_negative_039 {t a : ℝ} (tb : RealMem negative_039.t t) (ab : RealMem negative_039.a a) : RealMem negative_039.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((6/5):ℝ) ((121/100):ℝ) := by simpa [negative_039,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((6/5):ℝ)<((121/100):ℝ)) tB
  have aB : a∈Icc ((1221940455258763/1649267441664000):ℝ) ((1234825357146763/1649267441664000):ℝ) := by simpa [negative_039,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((1221940455258763/1649267441664000):ℝ)<((1234825357146763/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR039Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_039,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR039Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_039,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR039Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_039,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_039
