import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip040

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR042Q00T := Grid.ofRats (123/100) (31/25)
def shortNegativeR042Q00P : PrimalThetaParameters := ⟨⟨⟨24579496049538445612959,25363941210597300898142,true⟩,⟨0,0,true⟩⟩, ⟨⟨1443664194450952388636831,1448609445067735090645246,true⟩,⟨0,0,true⟩⟩, ⟨(-910624084734399443775664),(-900733583500902759241897),true⟩, ⟨3931631665284123563780142,3987204350956534534162099,true⟩⟩
theorem shortNegativeR042Q00P_ok : shortNegativeR042Q00P.encloses (primalThetaParameters shortNegativeR042Q00T (Grid.ofRats (1253827355203541/1649267441664000) (419374107499847/549755813888000))) := by decide +kernel

def shortNegativeR042Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨456502314128867198908792,460101791531875596846659,true⟩,⟨3176474563302682183732068,3201520763634590441598791,true⟩,⟨⟨439851173597322924081492,444796424214105626138304,true⟩,⟨1122627945419630347824407,1127573196036413049890648,true⟩⟩⟩
  | 1 => ⟨⟨1323436064476744081880,1398233011888154287696,true⟩,⟨456502314128867198908792,460101791531875596846659,true⟩,⟨⟨(-1097534791478112115094666),(-1082699039627901447946281),true⟩,⟨(-530052306245287740521509),(-515216554395077073380919),true⟩⟩⟩
  | 2 => ⟨⟨78007449223855537,89150222371504880,true⟩,⟨1323436064476744081880,1398233011888154287696,true⟩,⟨⟨1141813728559877975100239,1166539981643516607308713,true⟩,⟨(-372053861032518386352335),(-347327607948879754154801),true⟩⟩⟩
  | 3 => ⟨⟨59125468349,153616238593,true⟩,⟨78007449223855537,89150222371504880,true⟩,⟨⟨(-617509332762786722146956),(-582892578445720124840920),true⟩,⟨1032101195040350319451887,1066717949357416916764105,true⟩⟩⟩
  | 4 => ⟨⟨(-34359736091),34359741716,true⟩,⟨59125468349,153616238593,true⟩,⟨⟨(-297422731977155316553785),(-252915476426660754190165),true⟩,⟨(-1199446730636295476089328),(-1154939475085800913713290),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359736091),34359741716,true⟩,⟨⟨975993397274620362166485,1030391154058542889578013,true⟩,⟨647417231239144578965525,701814988023067106372525,true⟩⟩⟩
theorem shortNegativeR042Q00F_ok : ∀ n : Fin 6, (shortNegativeR042Q00F n).encloses (FactoredFrequency.build shortNegativeR042Q00T (Grid.ofRats (1253827355203541/1649267441664000) (419374107499847/549755813888000)) n) := by decide +kernel
def shortNegativeR042Q00L : ℕ → ℚ
  | 0 => (-2611369/1000000)
  | 1 => (-249731/125000)
  | 2 => (-1540627/1000000)
  | 3 => (-1333021/1000000)
  | 4 => (-345349/250000)
  | 5 => (-338953/200000)
  | 6 => (-34314/15625)
  | 7 => (-2807931/1000000)
  | 8 => (-1701857/500000)
  | 9 => (-3805487/1000000)
  | 10 => (-190101/50000)
  | 11 => (-3350399/1000000)
  | _ => 0
def shortNegativeR042Q00U : ℕ → ℚ
  | 0 => (-258067/125000)
  | 1 => (-1410443/1000000)
  | 2 => (-927461/1000000)
  | 3 => (-21423/31250)
  | 4 => (-704519/1000000)
  | 5 => (-116391/125000)
  | 6 => (-682143/500000)
  | 7 => (-1940501/1000000)
  | 8 => (-2515511/1000000)
  | 9 => (-2871323/1000000)
  | 10 => (-2901783/1000000)
  | 11 => (-1294339/500000)
  | _ => 0
private theorem shortNegativeR042Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR042Q00P shortNegativeR042Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR042Q00L (0:Fin 12)) (shortNegativeR042Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR042Q00P shortNegativeR042Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR042Q00L (1:Fin 12)) (shortNegativeR042Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR042Q00P shortNegativeR042Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR042Q00L (2:Fin 12)) (shortNegativeR042Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR042Q00P shortNegativeR042Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR042Q00L (3:Fin 12)) (shortNegativeR042Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR042Q00P shortNegativeR042Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR042Q00L (4:Fin 12)) (shortNegativeR042Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR042Q00P shortNegativeR042Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR042Q00L (5:Fin 12)) (shortNegativeR042Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR042Q00P shortNegativeR042Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR042Q00L (6:Fin 12)) (shortNegativeR042Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR042Q00P shortNegativeR042Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR042Q00L (7:Fin 12)) (shortNegativeR042Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR042Q00P shortNegativeR042Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR042Q00L (8:Fin 12)) (shortNegativeR042Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR042Q00P shortNegativeR042Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR042Q00L (9:Fin 12)) (shortNegativeR042Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR042Q00P shortNegativeR042Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR042Q00L (10:Fin 12)) (shortNegativeR042Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR042Q00P shortNegativeR042Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR042Q00L (11:Fin 12)) (shortNegativeR042Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR042Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR042Q00P shortNegativeR042Q00F (shortNegativeNodes12 k)).re (shortNegativeR042Q00L k) (shortNegativeR042Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR042Q00Point00
  · exact shortNegativeR042Q00Point01
  · exact shortNegativeR042Q00Point02
  · exact shortNegativeR042Q00Point03
  · exact shortNegativeR042Q00Point04
  · exact shortNegativeR042Q00Point05
  · exact shortNegativeR042Q00Point06
  · exact shortNegativeR042Q00Point07
  · exact shortNegativeR042Q00Point08
  · exact shortNegativeR042Q00Point09
  · exact shortNegativeR042Q00Point10
  · exact shortNegativeR042Q00Point11

theorem shortNegativeR042Q00Bound {t a : ℝ} (tl : ((123/100):ℝ)≤t) (tu : t≤((31/25):ℝ)) (al : ((1253827355203541/1649267441664000):ℝ)≤a) (au : a≤((419374107499847/549755813888000):ℝ)) : (((-817263273760904473433960377051765/324518553658426726783156020576256):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-547361408784967635145370565175925/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : shortNegativeR042Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1253827355203541/1649267441664000) (419374107499847/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR042Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR042Q00F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR042Q00L shortNegativeR042Q00U (-817263273760904473433960377051765/324518553658426726783156020576256) (-547361408784967635145370565175925/324518553658426726783156020576256) shortNegativeR042Q00Samples (by decide +kernel)

def shortNegativeR042Q01T := Grid.ofRats (123/100) (31/25)
def shortNegativeR042Q01P : PrimalThetaParameters := ⟨⟨⟨24579496049538445612959,25363941210597300898142,true⟩,⟨0,0,true⟩⟩, ⟨⟨1448609445067666371163895,1453554695684449073172326,true⟩,⟨0,0,true⟩⟩, ⟨(-900733583500971478721504),(-890843082267474794187769),true⟩, ⟨3920899500687689735397196,3976316652487816047824429,true⟩⟩
theorem shortNegativeR042Q01P_ok : shortNegativeR042Q01P.encloses (primalThetaParameters shortNegativeR042Q01T (Grid.ofRats (419374107499847/549755813888000) (1262417289795541/1649267441664000))) := by decide +kernel

def shortNegativeR042Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨456502314128867198908792,460101791531875596846659,true⟩,⟨3176474563302682183732068,3201520763634590441598791,true⟩,⟨⟨435245131946105241927839,440190382562887943985325,true⟩,⟨1124427903715797417659531,1129373154332580119726561,true⟩⟩⟩
  | 1 => ⟨⟨1323436064476744081880,1398233011888154287696,true⟩,⟨456502314128867198908792,460101791531875596846659,true⟩,⟨⟨(-1091039179258144006517994),(-1076203427407933339369583),true⟩,⟨(-543390364299004528470840),(-528554612448793861329957),true⟩⟩⟩
  | 2 => ⟨⟨78007449223855537,89150222371504880,true⟩,⟨1323436064476744081880,1398233011888154287696,true⟩,⟨⟨1148928593952878315881786,1173654847036516948089142,true⟩,⟨(-348373806790778054614619),(-323647553707139422418626),true⟩⟩⟩
  | 3 => ⟨⟨59125468349,153616238593,true⟩,⟨78007449223855537,89150222371504880,true⟩,⟨⟨(-647308300900971890360111),(-612691546583905293054449),true⟩,⟨1014487016035012840002169,1049103770352079437313363,true⟩⟩⟩
  | 4 => ⟨⟨(-34359736091),34359741716,true⟩,⟨59125468349,153616238593,true⟩,⟨⟨(-253907064169301480765327),(-209399808618806918402459),true⟩,⟨(-1208777257012241787087479),(-1164270001461747224711467),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359736091),34359741716,true⟩,⟨⟨944632678973704126716064,999030435757626654128553,true⟩,⟨691859576421782190994936,746257333205704718403942,true⟩⟩⟩
theorem shortNegativeR042Q01F_ok : ∀ n : Fin 6, (shortNegativeR042Q01F n).encloses (FactoredFrequency.build shortNegativeR042Q01T (Grid.ofRats (419374107499847/549755813888000) (1262417289795541/1649267441664000)) n) := by decide +kernel
def shortNegativeR042Q01L : ℕ → ℚ
  | 0 => (-655401/250000)
  | 1 => (-402237/200000)
  | 2 => (-1552429/1000000)
  | 3 => (-1339177/1000000)
  | 4 => (-690619/500000)
  | 5 => (-105469/62500)
  | 6 => (-2181989/1000000)
  | 7 => (-697357/250000)
  | 8 => (-845827/250000)
  | 9 => (-3788469/1000000)
  | 10 => (-237081/62500)
  | 11 => (-3352563/1000000)
  | _ => 0
def shortNegativeR042Q01U : ℕ → ℚ
  | 0 => (-2077947/1000000)
  | 1 => (-1426447/1000000)
  | 2 => (-47117/50000)
  | 3 => (-347751/500000)
  | 4 => (-354077/500000)
  | 5 => (-58009/62500)
  | 6 => (-21172/15625)
  | 7 => (-1926411/1000000)
  | 8 => (-499837/200000)
  | 9 => (-2858643/1000000)
  | 10 => (-579519/200000)
  | 11 => (-2594277/1000000)
  | _ => 0
private theorem shortNegativeR042Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR042Q01P shortNegativeR042Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR042Q01L (0:Fin 12)) (shortNegativeR042Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR042Q01P shortNegativeR042Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR042Q01L (1:Fin 12)) (shortNegativeR042Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR042Q01P shortNegativeR042Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR042Q01L (2:Fin 12)) (shortNegativeR042Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR042Q01P shortNegativeR042Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR042Q01L (3:Fin 12)) (shortNegativeR042Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR042Q01P shortNegativeR042Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR042Q01L (4:Fin 12)) (shortNegativeR042Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR042Q01P shortNegativeR042Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR042Q01L (5:Fin 12)) (shortNegativeR042Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR042Q01P shortNegativeR042Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR042Q01L (6:Fin 12)) (shortNegativeR042Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR042Q01P shortNegativeR042Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR042Q01L (7:Fin 12)) (shortNegativeR042Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR042Q01P shortNegativeR042Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR042Q01L (8:Fin 12)) (shortNegativeR042Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR042Q01P shortNegativeR042Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR042Q01L (9:Fin 12)) (shortNegativeR042Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR042Q01P shortNegativeR042Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR042Q01L (10:Fin 12)) (shortNegativeR042Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR042Q01P shortNegativeR042Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR042Q01L (11:Fin 12)) (shortNegativeR042Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR042Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR042Q01P shortNegativeR042Q01F (shortNegativeNodes12 k)).re (shortNegativeR042Q01L k) (shortNegativeR042Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR042Q01Point00
  · exact shortNegativeR042Q01Point01
  · exact shortNegativeR042Q01Point02
  · exact shortNegativeR042Q01Point03
  · exact shortNegativeR042Q01Point04
  · exact shortNegativeR042Q01Point05
  · exact shortNegativeR042Q01Point06
  · exact shortNegativeR042Q01Point07
  · exact shortNegativeR042Q01Point08
  · exact shortNegativeR042Q01Point09
  · exact shortNegativeR042Q01Point10
  · exact shortNegativeR042Q01Point11

theorem shortNegativeR042Q01Bound {t a : ℝ} (tl : ((123/100):ℝ)≤t) (tu : t≤((31/25):ℝ)) (al : ((419374107499847/549755813888000):ℝ)≤a) (au : a≤((1262417289795541/1649267441664000):ℝ)) : (((-817263273760904473433960377051765/324518553658426726783156020576256):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-547361408784967635145370565175925/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : shortNegativeR042Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (419374107499847/549755813888000) (1262417289795541/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR042Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR042Q01F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR042Q01L shortNegativeR042Q01U (-817263273760904473433960377051765/324518553658426726783156020576256) (-547361408784967635145370565175925/324518553658426726783156020576256) shortNegativeR042Q01Samples (by decide +kernel)

def shortNegativeR042Q02T := Grid.ofRats (123/100) (31/25)
def shortNegativeR042Q02P : PrimalThetaParameters := ⟨⟨⟨24579496049538445612959,25363941210597300898142,true⟩,⟨0,0,true⟩⟩, ⟨⟨1453554695684380353690960,1458499946301163055699404,true⟩,⟨0,0,true⟩⟩, ⟨(-890843082267543513667345),(-880952581034046829133644),true⟩, ⟨3910331477377697072882719,3965595571495244110106191,true⟩⟩
theorem shortNegativeR042Q02P_ok : shortNegativeR042Q02P.encloses (primalThetaParameters shortNegativeR042Q02T (Grid.ofRats (1262417289795541/1649267441664000) (1266712257091541/1649267441664000))) := by decide +kernel

def shortNegativeR042Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨456502314128867198908792,460101791531875596846659,true⟩,⟨3176474563302682183732068,3201520763634590441598791,true⟩,⟨⟨430631765914938002187758,435577016531720704245037,true⟩,⟨1126209005459989759913350,1131154256076772461980246,true⟩⟩⟩
  | 1 => ⟨⟨1323436064476744081880,1398233011888154287696,true⟩,⟨456502314128867198908792,460101791531875596846659,true⟩,⟨⟨(-1084380377655766351219964),(-1069544625805555684071255),true⟩,⟨(-556647706867433959355796),(-541811955017223292214338),true⟩⟩⟩
  | 2 => ⟨⟨78007449223855537,89150222371504880,true⟩,⟨1323436064476744081880,1398233011888154287696,true⟩,⟨⟨1155557675013366452263092,1180283928097005084470433,true⟩,⟨(-324553194650328018390610),(-299826941566689386195042),true⟩⟩⟩
  | 3 => ⟨⟨59125468349,153616238593,true⟩,⟨78007449223855537,89150222371504880,true⟩,⟨⟨(-676590752529050708604074),(-641973998211984111298102),true⟩,⟨996026901442143416699280,1030643655759210014010118,true⟩⟩⟩
  | 4 => ⟨⟨(-34359736091),34359741716,true⟩,⟨59125468349,153616238593,true⟩,⟨⟨(-210077452484122825482233),(-165570196933628263121039),true⟩,⟨(-1216499769993271157672734),(-1171992514442776595297690),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359736091),34359741716,true⟩,⟨⟨911304616265150056148526,965702373049072583563388,true⟩,⟨734846282899213356995798,789244039683135884408229,true⟩⟩⟩
theorem shortNegativeR042Q02F_ok : ∀ n : Fin 6, (shortNegativeR042Q02F n).encloses (FactoredFrequency.build shortNegativeR042Q02T (Grid.ofRats (1262417289795541/1649267441664000) (1266712257091541/1649267441664000)) n) := by decide +kernel
def shortNegativeR042Q02L : ℕ → ℚ
  | 0 => (-2631731/1000000)
  | 1 => (-80979/40000)
  | 2 => (-6257/4000)
  | 3 => (-672709/500000)
  | 4 => (-3453/2500)
  | 5 => (-420097/250000)
  | 6 => (-2168041/1000000)
  | 7 => (-1385533/500000)
  | 8 => (-3362991/1000000)
  | 9 => (-1885727/500000)
  | 10 => (-946117/250000)
  | 11 => (-1677291/500000)
  | _ => 0
def shortNegativeR042Q02U : ℕ → ℚ
  | 0 => (-1045623/500000)
  | 1 => (-90151/62500)
  | 2 => (-23931/25000)
  | 3 => (-352773/500000)
  | 4 => (-142381/200000)
  | 5 => (-185061/200000)
  | 6 => (-1345889/1000000)
  | 7 => (-1912469/1000000)
  | 8 => (-2482967/1000000)
  | 9 => (-355747/125000)
  | 10 => (-2893339/1000000)
  | 11 => (-2599757/1000000)
  | _ => 0
private theorem shortNegativeR042Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR042Q02P shortNegativeR042Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR042Q02L (0:Fin 12)) (shortNegativeR042Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR042Q02P shortNegativeR042Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR042Q02L (1:Fin 12)) (shortNegativeR042Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR042Q02P shortNegativeR042Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR042Q02L (2:Fin 12)) (shortNegativeR042Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR042Q02P shortNegativeR042Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR042Q02L (3:Fin 12)) (shortNegativeR042Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR042Q02P shortNegativeR042Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR042Q02L (4:Fin 12)) (shortNegativeR042Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR042Q02P shortNegativeR042Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR042Q02L (5:Fin 12)) (shortNegativeR042Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR042Q02P shortNegativeR042Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR042Q02L (6:Fin 12)) (shortNegativeR042Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR042Q02P shortNegativeR042Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR042Q02L (7:Fin 12)) (shortNegativeR042Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR042Q02P shortNegativeR042Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR042Q02L (8:Fin 12)) (shortNegativeR042Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR042Q02P shortNegativeR042Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR042Q02L (9:Fin 12)) (shortNegativeR042Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR042Q02P shortNegativeR042Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR042Q02L (10:Fin 12)) (shortNegativeR042Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR042Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR042Q02P shortNegativeR042Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR042Q02L (11:Fin 12)) (shortNegativeR042Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR042Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR042Q02P shortNegativeR042Q02F (shortNegativeNodes12 k)).re (shortNegativeR042Q02L k) (shortNegativeR042Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR042Q02Point00
  · exact shortNegativeR042Q02Point01
  · exact shortNegativeR042Q02Point02
  · exact shortNegativeR042Q02Point03
  · exact shortNegativeR042Q02Point04
  · exact shortNegativeR042Q02Point05
  · exact shortNegativeR042Q02Point06
  · exact shortNegativeR042Q02Point07
  · exact shortNegativeR042Q02Point08
  · exact shortNegativeR042Q02Point09
  · exact shortNegativeR042Q02Point10
  · exact shortNegativeR042Q02Point11

theorem shortNegativeR042Q02Bound {t a : ℝ} (tl : ((123/100):ℝ)≤t) (tu : t≤((31/25):ℝ)) (al : ((1262417289795541/1649267441664000):ℝ)≤a) (au : a≤((1266712257091541/1649267441664000):ℝ)) : (((-817263273760904473433960377051765/324518553658426726783156020576256):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-547361408784967635145370565175925/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : shortNegativeR042Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1262417289795541/1649267441664000) (1266712257091541/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR042Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR042Q02F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR042Q02L shortNegativeR042Q02U (-817263273760904473433960377051765/324518553658426726783156020576256) (-547361408784967635145370565175925/324518553658426726783156020576256) shortNegativeR042Q02Samples (by decide +kernel)

theorem short_original_negative_042 {t a : ℝ} (tb : RealMem negative_042.t t) (ab : RealMem negative_042.a a) : RealMem negative_042.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((123/100):ℝ) ((31/25):ℝ) := by simpa [negative_042,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((123/100):ℝ)<((31/25):ℝ)) tB
  have aB : a∈Icc ((1253827355203541/1649267441664000):ℝ) ((1266712257091541/1649267441664000):ℝ) := by simpa [negative_042,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((1253827355203541/1649267441664000):ℝ)<((1266712257091541/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR042Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_042,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR042Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_042,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR042Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_042,RealMem] using v

def shortNegativeR043Q00T := Grid.ofRats (31/25) (5/4)
def shortNegativeR043Q00P : PrimalThetaParameters := ⟨⟨⟨23819311874074666912372,24579496049607165090113,true⟩,⟨0,0,true⟩⟩, ⟨⟨1456628971635744264008098,1461574222252526966016554,true⟩,⟨0,0,true⟩⟩, ⟨(-884694530364815693033048),(-874804029131319008499363),true⟩, ⟨3887625825405036300165603,3941944470046384531006517,true⟩⟩
theorem shortNegativeR043Q00P_ok : shortNegativeR043Q00P.encloses (primalThetaParameters shortNegativeR043Q00T (Grid.ofRats (1265087309111723/1649267441664000) (423127425469241/549755813888000))) := by decide +kernel

def shortNegativeR043Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨452930996228482677845999,456502314128935918402447,true⟩,⟨3201520763634521722004378,3226764450877960729143013,true⟩,⟨⟨427760152152768660777557,432705402769551362834614,true⟩,⟨1127306731260385260435351,1132251981877167962502068,true⟩⟩⟩
  | 1 => ⟨⟨1252640298113443821008,1323436064545463558692,true⟩,⟨452930996228482677845999,456502314128935918402447,true⟩,⟨⟨(-1080159034576361060019513),(-1065323282726150392870556),true⟩,⟨(-564847731482254613086523),(-550011979632043945944654),true⟩⟩⟩
  | 2 => ⟨⟨68257449227862369,78007517943332274,true⟩,⟨1252640298113443821008,1323436064545463558692,true⟩,⟨⟨1159432628895653033723771,1184158881979291665930594,true⟩,⟨(-309678354657747491973755),(-284952101574108859778972),true⟩⟩⟩
  | 3 => ⟨⟨38923343548,127844945086,true⟩,⟨68257449227862369,78007517943332274,true⟩,⟨⟨(-694523598758951778760802),(-659906844441885181454709),true⟩,⟨984131177164941089166958,1018747931482007686477512,true⟩⟩⟩
  | 4 => ⟨⟨(-34359736818),34359740646,true⟩,⟨38923343548,127844945086,true⟩,⟨⟨(-182698136765538631267758),(-138190881215044068906301),true⟩,⟨(-1220485323594452038858066),(-1175978068043957476482327),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359736818),34359740646,true⟩,⟨⟨889623707274292950755999,944021464058215478171676,true⟩,⟨760797304176930925477030,815195060960853452890938,true⟩⟩⟩
theorem shortNegativeR043Q00F_ok : ∀ n : Fin 6, (shortNegativeR043Q00F n).encloses (FactoredFrequency.build shortNegativeR043Q00T (Grid.ofRats (1265087309111723/1649267441664000) (423127425469241/549755813888000)) n) := by decide +kernel
def shortNegativeR043Q00L : ℕ → ℚ
  | 0 => (-1326621/500000)
  | 1 => (-206727/100000)
  | 2 => (-101157/62500)
  | 3 => (-1399811/1000000)
  | 4 => (-22349/15625)
  | 5 => (-429521/250000)
  | 6 => (-437851/200000)
  | 7 => (-346883/125000)
  | 8 => (-3346471/1000000)
  | 9 => (-374171/100000)
  | 10 => (-1878869/500000)
  | 11 => (-3348311/1000000)
  | _ => 0
def shortNegativeR043Q00U : ℕ → ℚ
  | 0 => (-529313/250000)
  | 1 => (-744189/500000)
  | 2 => (-507453/500000)
  | 3 => (-95519/125000)
  | 4 => (-765051/1000000)
  | 5 => (-484377/500000)
  | 6 => (-1375247/1000000)
  | 7 => (-962057/500000)
  | 8 => (-247427/100000)
  | 9 => (-2827747/1000000)
  | 10 => (-575797/200000)
  | 11 => (-1301297/500000)
  | _ => 0
private theorem shortNegativeR043Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR043Q00P shortNegativeR043Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR043Q00L (0:Fin 12)) (shortNegativeR043Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR043Q00P shortNegativeR043Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR043Q00L (1:Fin 12)) (shortNegativeR043Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR043Q00P shortNegativeR043Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR043Q00L (2:Fin 12)) (shortNegativeR043Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR043Q00P shortNegativeR043Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR043Q00L (3:Fin 12)) (shortNegativeR043Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR043Q00P shortNegativeR043Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR043Q00L (4:Fin 12)) (shortNegativeR043Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR043Q00P shortNegativeR043Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR043Q00L (5:Fin 12)) (shortNegativeR043Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR043Q00P shortNegativeR043Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR043Q00L (6:Fin 12)) (shortNegativeR043Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR043Q00P shortNegativeR043Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR043Q00L (7:Fin 12)) (shortNegativeR043Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR043Q00P shortNegativeR043Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR043Q00L (8:Fin 12)) (shortNegativeR043Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR043Q00P shortNegativeR043Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR043Q00L (9:Fin 12)) (shortNegativeR043Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR043Q00P shortNegativeR043Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR043Q00L (10:Fin 12)) (shortNegativeR043Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR043Q00P shortNegativeR043Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR043Q00L (11:Fin 12)) (shortNegativeR043Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR043Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR043Q00P shortNegativeR043Q00F (shortNegativeNodes12 k)).re (shortNegativeR043Q00L k) (shortNegativeR043Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR043Q00Point00
  · exact shortNegativeR043Q00Point01
  · exact shortNegativeR043Q00Point02
  · exact shortNegativeR043Q00Point03
  · exact shortNegativeR043Q00Point04
  · exact shortNegativeR043Q00Point05
  · exact shortNegativeR043Q00Point06
  · exact shortNegativeR043Q00Point07
  · exact shortNegativeR043Q00Point08
  · exact shortNegativeR043Q00Point09
  · exact shortNegativeR043Q00Point10
  · exact shortNegativeR043Q00Point11

theorem shortNegativeR043Q00Bound {t a : ℝ} (tl : ((31/25):ℝ)≤t) (tu : t≤((5/4):ℝ)) (al : ((1265087309111723/1649267441664000):ℝ)≤a) (au : a≤((423127425469241/549755813888000):ℝ)) : (((-3294781676011462877878681915072555/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2208916761663728321457730638815275/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR043Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1265087309111723/1649267441664000) (423127425469241/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR043Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR043Q00F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR043Q00L shortNegativeR043Q00U (-3294781676011462877878681915072555/1298074214633706907132624082305024) (-2208916761663728321457730638815275/1298074214633706907132624082305024) shortNegativeR043Q00Samples (by decide +kernel)

def shortNegativeR043Q01T := Grid.ofRats (31/25) (5/4)
def shortNegativeR043Q01P : PrimalThetaParameters := ⟨⟨⟨23819311874074666912372,24579496049607165090113,true⟩,⟨0,0,true⟩⟩, ⟨⟨1461574222252458246535162,1466519472869240948543632,true⟩,⟨0,0,true⟩⟩, ⟨(-874804029131387727978889),(-864913527897891043445238),true⟩, ⟨3877308923247545418474179,3931478365741805886146239,true⟩⟩
theorem shortNegativeR043Q01P_ok : shortNegativeR043Q01P.encloses (primalThetaParameters shortNegativeR043Q01T (Grid.ofRats (423127425469241/549755813888000) (1273677243703723/1649267441664000))) := by decide +kernel

def shortNegativeR043Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨452930996228482677845999,456502314128935918402447,true⟩,⟨3201520763634521722004378,3226764450877960729143013,true⟩,⟨⟨423135072601556669610673,428080323218339371667900,true⟩,⟨1129057190830227837348666,1134002441447010539415627,true⟩⟩⟩
  | 1 => ⟨⟨1252640298113443821008,1323436064545463558692,true⟩,⟨452930996228482677845999,456502314128935918402447,true⟩,⟨⟨(-1073237737325967780539341),(-1058401985475757113390331),true⟩,⟨(-577969942238381673487454),(-563134190388171006345251),true⟩⟩⟩
  | 2 => ⟨⟨68257449227862369,78007517943332274,true⟩,⟨1252640298113443821008,1323436064545463558692,true⟩,⟨⟨1165268127075391234612484,1189994380159029866819281,true⟩,⟨(-285651011079096307354768),(-260924757995457675160423),true⟩⟩⟩
  | 3 => ⟨⟨38923343548,127844945086,true⟩,⟨68257449227862369,78007517943332274,true⟩,⟨⟨(-722917595577352136981116),(-688300841260285539674961),true⟩,⟨964331713818443113892311,998948468135509711202262,true⟩⟩⟩
  | 4 => ⟨⟨(-34359736818),34359740646,true⟩,⟨38923343548,127844945086,true⟩,⟨⟨(-138485835930112181380680),(-93978580379617619019970),true⟩,⟨(-1225578900142759338003205),(-1181071644592264775627531),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359736818),34359740646,true⟩,⟨⟨853250395353810466271481,907648152137732993688644,true⟩,⟨801239842148940321254663,855637598932862848671118,true⟩⟩⟩
theorem shortNegativeR043Q01F_ok : ∀ n : Fin 6, (shortNegativeR043Q01F n).encloses (FactoredFrequency.build shortNegativeR043Q01T (Grid.ofRats (423127425469241/549755813888000) (1273677243703723/1649267441664000)) n) := by decide +kernel
def shortNegativeR043Q01L : ℕ → ℚ
  | 0 => (-2662519/1000000)
  | 1 => (-2079773/1000000)
  | 2 => (-1629769/1000000)
  | 3 => (-56231/40000)
  | 4 => (-1430239/1000000)
  | 5 => (-427777/250000)
  | 6 => (-543909/250000)
  | 7 => (-2757141/1000000)
  | 8 => (-16633/5000)
  | 9 => (-3724907/1000000)
  | 10 => (-374867/100000)
  | 11 => (-66993/20000)
  | _ => 0
def shortNegativeR043Q01U : ℕ → ℚ
  | 0 => (-2129711/1000000)
  | 1 => (-1503619/1000000)
  | 2 => (-1029287/1000000)
  | 3 => (-12093/15625)
  | 4 => (-48049/62500)
  | 5 => (-96609/100000)
  | 6 => (-683237/500000)
  | 7 => (-382127/200000)
  | 8 => (-1229261/500000)
  | 9 => (-2815313/1000000)
  | 10 => (-2874543/1000000)
  | 11 => (-1303729/500000)
  | _ => 0
private theorem shortNegativeR043Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR043Q01P shortNegativeR043Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR043Q01L (0:Fin 12)) (shortNegativeR043Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR043Q01P shortNegativeR043Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR043Q01L (1:Fin 12)) (shortNegativeR043Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR043Q01P shortNegativeR043Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR043Q01L (2:Fin 12)) (shortNegativeR043Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR043Q01P shortNegativeR043Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR043Q01L (3:Fin 12)) (shortNegativeR043Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR043Q01P shortNegativeR043Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR043Q01L (4:Fin 12)) (shortNegativeR043Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR043Q01P shortNegativeR043Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR043Q01L (5:Fin 12)) (shortNegativeR043Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR043Q01P shortNegativeR043Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR043Q01L (6:Fin 12)) (shortNegativeR043Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR043Q01P shortNegativeR043Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR043Q01L (7:Fin 12)) (shortNegativeR043Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR043Q01P shortNegativeR043Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR043Q01L (8:Fin 12)) (shortNegativeR043Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR043Q01P shortNegativeR043Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR043Q01L (9:Fin 12)) (shortNegativeR043Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR043Q01P shortNegativeR043Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR043Q01L (10:Fin 12)) (shortNegativeR043Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR043Q01P shortNegativeR043Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR043Q01L (11:Fin 12)) (shortNegativeR043Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR043Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR043Q01P shortNegativeR043Q01F (shortNegativeNodes12 k)).re (shortNegativeR043Q01L k) (shortNegativeR043Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR043Q01Point00
  · exact shortNegativeR043Q01Point01
  · exact shortNegativeR043Q01Point02
  · exact shortNegativeR043Q01Point03
  · exact shortNegativeR043Q01Point04
  · exact shortNegativeR043Q01Point05
  · exact shortNegativeR043Q01Point06
  · exact shortNegativeR043Q01Point07
  · exact shortNegativeR043Q01Point08
  · exact shortNegativeR043Q01Point09
  · exact shortNegativeR043Q01Point10
  · exact shortNegativeR043Q01Point11

theorem shortNegativeR043Q01Bound {t a : ℝ} (tl : ((31/25):ℝ)≤t) (tu : t≤((5/4):ℝ)) (al : ((423127425469241/549755813888000):ℝ)≤a) (au : a≤((1273677243703723/1649267441664000):ℝ)) : (((-3294781676011462877878681915072555/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2208916761663728321457730638815275/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR043Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (423127425469241/549755813888000) (1273677243703723/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR043Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR043Q01F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR043Q01L shortNegativeR043Q01U (-3294781676011462877878681915072555/1298074214633706907132624082305024) (-2208916761663728321457730638815275/1298074214633706907132624082305024) shortNegativeR043Q01Samples (by decide +kernel)

def shortNegativeR043Q02T := Grid.ofRats (31/25) (5/4)
def shortNegativeR043Q02P : PrimalThetaParameters := ⟨⟨⟨23819311874074666912372,24579496049607165090113,true⟩,⟨0,0,true⟩⟩, ⟨⟨1466519472869172229062225,1471464723485954931070712,true⟩,⟨0,0,true⟩⟩, ⟨(-864913527897959762924732),(-855023026664463078391110),true⟩, ⟨3867151687581267104538666,3921174313762424432149369,true⟩⟩
theorem shortNegativeR043Q02P_ok : shortNegativeR043Q02P.encloses (primalThetaParameters shortNegativeR043Q02T (Grid.ofRats (1273677243703723/1649267441664000) (1277972210999723/1649267441664000))) := by decide +kernel

def shortNegativeR043Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨452930996228482677845999,456502314128935918402447,true⟩,⟨3201520763634521722004378,3226764450877960729143013,true⟩,⟨⟨418502871309365967071569,423448121926148669128724,true⟩,⟨1130788716385719167270611,1135733967002501869337574,true⟩⟩⟩
  | 1 => ⟨⟨1252640298113443821008,1323436064545463558692,true⟩,⟨452930996228482677845999,456502314128935918402447,true⟩,⟨⟨(-1066155931524841090577201),(-1051320179674630423427888),true⟩,⟨(-591006229951977390615315),(-576170478101766723472538),true⟩⟩⟩
  | 2 => ⟨⟨68257449227862369,78007517943332274,true⟩,⟨1252640298113443821008,1323436064545463558692,true⟩,⟨⟨1170611005870707879928060,1195337258954346512134243,true⟩,⟨(-261509347411676161554952),(-236783094328037529361623),true⟩⟩⟩
  | 3 => ⟨⟨38923343548,127844945086,true⟩,⟨68257449227862369,78007517943332274,true⟩,⟨⟨(-750733086276527061146741),(-716116331959460463839939),true⟩,⟨943727435590444935461334,978344189907511532771265,true⟩⟩⟩
  | 4 => ⟨⟨(-34359736818),34359740646,true⟩,⟨38923343548,127844945086,true⟩,⟨⟨(-94116013623533920936952),(-49608758073039358577004),true⟩,⟨(-1229041693191497115874898),(-1184534437641002553499327),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359736818),34359740646,true⟩,⟨⟨815094730368350495582095,869492487152273023001240,true⟩,⟨840005315539568211656334,894403072323490739075819,true⟩⟩⟩
theorem shortNegativeR043Q02F_ok : ∀ n : Fin 6, (shortNegativeR043Q02F n).encloses (FactoredFrequency.build shortNegativeR043Q02T (Grid.ofRats (1273677243703723/1649267441664000) (1277972210999723/1649267441664000)) n) := by decide +kernel
def shortNegativeR043Q02L : ℕ → ℚ
  | 0 => (-1335847/500000)
  | 1 => (-2092231/1000000)
  | 2 => (-328209/200000)
  | 3 => (-1411823/1000000)
  | 4 => (-1430259/1000000)
  | 5 => (-1704273/1000000)
  | 6 => (-1081087/500000)
  | 7 => (-1369677/500000)
  | 8 => (-661363/200000)
  | 9 => (-37081/10000)
  | 10 => (-3739507/1000000)
  | 11 => (-1675427/500000)
  | _ => 0
def shortNegativeR043Q02U : ℕ → ℚ
  | 0 => (-2142063/1000000)
  | 1 => (-759413/500000)
  | 2 => (-1043687/1000000)
  | 3 => (-195957/250000)
  | 4 => (-772633/1000000)
  | 5 => (-60223/62500)
  | 6 => (-42433/31250)
  | 7 => (-18973/10000)
  | 8 => (-2442881/1000000)
  | 9 => (-1401453/500000)
  | 10 => (-71751/25000)
  | 11 => (-2612209/1000000)
  | _ => 0
private theorem shortNegativeR043Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR043Q02P shortNegativeR043Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR043Q02L (0:Fin 12)) (shortNegativeR043Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR043Q02P shortNegativeR043Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR043Q02L (1:Fin 12)) (shortNegativeR043Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR043Q02P shortNegativeR043Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR043Q02L (2:Fin 12)) (shortNegativeR043Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR043Q02P shortNegativeR043Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR043Q02L (3:Fin 12)) (shortNegativeR043Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR043Q02P shortNegativeR043Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR043Q02L (4:Fin 12)) (shortNegativeR043Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR043Q02P shortNegativeR043Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR043Q02L (5:Fin 12)) (shortNegativeR043Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR043Q02P shortNegativeR043Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR043Q02L (6:Fin 12)) (shortNegativeR043Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR043Q02P shortNegativeR043Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR043Q02L (7:Fin 12)) (shortNegativeR043Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR043Q02P shortNegativeR043Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR043Q02L (8:Fin 12)) (shortNegativeR043Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR043Q02P shortNegativeR043Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR043Q02L (9:Fin 12)) (shortNegativeR043Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR043Q02P shortNegativeR043Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR043Q02L (10:Fin 12)) (shortNegativeR043Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR043Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR043Q02P shortNegativeR043Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR043Q02L (11:Fin 12)) (shortNegativeR043Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR043Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR043Q02P shortNegativeR043Q02F (shortNegativeNodes12 k)).re (shortNegativeR043Q02L k) (shortNegativeR043Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR043Q02Point00
  · exact shortNegativeR043Q02Point01
  · exact shortNegativeR043Q02Point02
  · exact shortNegativeR043Q02Point03
  · exact shortNegativeR043Q02Point04
  · exact shortNegativeR043Q02Point05
  · exact shortNegativeR043Q02Point06
  · exact shortNegativeR043Q02Point07
  · exact shortNegativeR043Q02Point08
  · exact shortNegativeR043Q02Point09
  · exact shortNegativeR043Q02Point10
  · exact shortNegativeR043Q02Point11

theorem shortNegativeR043Q02Bound {t a : ℝ} (tl : ((31/25):ℝ)≤t) (tu : t≤((5/4):ℝ)) (al : ((1273677243703723/1649267441664000):ℝ)≤a) (au : a≤((1277972210999723/1649267441664000):ℝ)) : (((-3294781676011462877878681915072555/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2208916761663728321457730638815275/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR043Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1273677243703723/1649267441664000) (1277972210999723/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR043Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR043Q02F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR043Q02L shortNegativeR043Q02U (-3294781676011462877878681915072555/1298074214633706907132624082305024) (-2208916761663728321457730638815275/1298074214633706907132624082305024) shortNegativeR043Q02Samples (by decide +kernel)

theorem short_original_negative_043 {t a : ℝ} (tb : RealMem negative_043.t t) (ab : RealMem negative_043.a a) : RealMem negative_043.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((31/25):ℝ) ((5/4):ℝ) := by simpa [negative_043,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((31/25):ℝ)<((5/4):ℝ)) tB
  have aB : a∈Icc ((1265087309111723/1649267441664000):ℝ) ((1277972210999723/1649267441664000):ℝ) := by simpa [negative_043,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((1265087309111723/1649267441664000):ℝ)<((1277972210999723/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR043Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_043,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR043Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_043,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR043Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_043,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_042
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_043
