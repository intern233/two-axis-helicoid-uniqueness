import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip040

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR044Q00T := Grid.ofRats (5/4) (63/50)
def shortNegativeR044Q00P : PrimalThetaParameters := ⟨⟨⟨23082638350719460987329,23819311874143386389515,true⟩,⟨0,0,true⟩⟩, ⟨⟨1470008745599627174763975,1474953996216409876772474,true⟩,⟨0,0,true⟩⟩, ⟨(-857934982437049871521209),(-848044481203553186987610),true⟩, ⟨3844375078764671442191215,3897474647021471597959710,true⟩⟩
theorem shortNegativeR044Q00P_ok : shortNegativeR044Q00P.encloses (primalThetaParameters shortNegativeR044Q00T (Grid.ofRats (1276707689160517/1649267441664000) (1281002656456517/1649267441664000))) := by decide +kernel

def shortNegativeR044Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨449387617532677972991660,452930996228551397339462,true⟩,⟨3226764450877892009548012,3252207182198408205130605,true⟩,⟨⟨415230236917280767104220,420175487534063469161446,true⟩,⟨1131999038603662511824933,1136944289220445213892033,true⟩⟩⟩
  | 1 => ⟨⟨1185631673924494472952,1252640298182163297815,true⟩,⟨449387617532677972991660,452930996228551397339462,true⟩,⟨⟨(-1061063144799339639666688),(-1046227392949128972516618),true⟩,⟨(-600151614386014452392522),(-585315862535803785248787),true⟩⟩⟩
  | 2 => ⟨⟨59726082311091613,68257517947339106,true⟩,⟨1185631673924494472952,1252640298182163297815,true⟩,⟨⟨1174083201093075552877162,1198809454176714185083173,true⟩,⟨(-244412149320573155295020),(-219685896236934523102139),true⟩⟩⟩
  | 3 => ⟨⟨23086891785,107642820285,true⟩,⟨59726082311091613,68257517947339106,true⟩,⟨⟨(-769998666856181574301835),(-735381912539114976994881),true⟩,⟨928714331409169759039430,963331085726236356349041,true⟩⟩⟩
  | 4 => ⟨⟨(-34359737314),34359739919,true⟩,⟨23086891785,107642820285,true⟩,⟨⟨(-62747371458930508237547),(-18240115908435945877657),true⟩,⟨(-1230501075135837852262732),(-1185993819585343289886771),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359737314),34359739919,true⟩,⟨⟨787142147130663651004586,841539903914586178423674,true⟩,⟨866305643970215969525539,920703400754138496945720,true⟩⟩⟩
theorem shortNegativeR044Q00F_ok : ∀ n : Fin 6, (shortNegativeR044Q00F n).encloses (FactoredFrequency.build shortNegativeR044Q00T (Grid.ofRats (1276707689160517/1649267441664000) (1281002656456517/1649267441664000)) n) := by decide +kernel
def shortNegativeR044Q00L : ℕ → ℚ
  | 0 => (-2691/1000)
  | 1 => (-533127/250000)
  | 2 => (-211619/125000)
  | 3 => (-1464147/1000000)
  | 4 => (-1477497/1000000)
  | 5 => (-1740187/1000000)
  | 6 => (-2181843/1000000)
  | 7 => (-137111/50000)
  | 8 => (-3289801/1000000)
  | 9 => (-919567/250000)
  | 10 => (-3712339/1000000)
  | 11 => (-133729/40000)
  | _ => 0
def shortNegativeR044Q00U : ℕ → ℚ
  | 0 => (-17329/8000)
  | 1 => (-31253/20000)
  | 2 => (-548919/500000)
  | 3 => (-52553/62500)
  | 4 => (-824387/1000000)
  | 5 => (-201147/200000)
  | 6 => (-1386099/1000000)
  | 7 => (-1908177/1000000)
  | 8 => (-608487/250000)
  | 9 => (-69617/25000)
  | 10 => (-2855391/1000000)
  | 11 => (-1306947/500000)
  | _ => 0
private theorem shortNegativeR044Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR044Q00P shortNegativeR044Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR044Q00L (0:Fin 12)) (shortNegativeR044Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR044Q00P shortNegativeR044Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR044Q00L (1:Fin 12)) (shortNegativeR044Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR044Q00P shortNegativeR044Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR044Q00L (2:Fin 12)) (shortNegativeR044Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR044Q00P shortNegativeR044Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR044Q00L (3:Fin 12)) (shortNegativeR044Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR044Q00P shortNegativeR044Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR044Q00L (4:Fin 12)) (shortNegativeR044Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR044Q00P shortNegativeR044Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR044Q00L (5:Fin 12)) (shortNegativeR044Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR044Q00P shortNegativeR044Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR044Q00L (6:Fin 12)) (shortNegativeR044Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR044Q00P shortNegativeR044Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR044Q00L (7:Fin 12)) (shortNegativeR044Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR044Q00P shortNegativeR044Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR044Q00L (8:Fin 12)) (shortNegativeR044Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR044Q00P shortNegativeR044Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR044Q00L (9:Fin 12)) (shortNegativeR044Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR044Q00P shortNegativeR044Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR044Q00L (10:Fin 12)) (shortNegativeR044Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR044Q00P shortNegativeR044Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR044Q00L (11:Fin 12)) (shortNegativeR044Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR044Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR044Q00P shortNegativeR044Q00F (shortNegativeNodes12 k)).re (shortNegativeR044Q00L k) (shortNegativeR044Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR044Q00Point00
  · exact shortNegativeR044Q00Point01
  · exact shortNegativeR044Q00Point02
  · exact shortNegativeR044Q00Point03
  · exact shortNegativeR044Q00Point04
  · exact shortNegativeR044Q00Point05
  · exact shortNegativeR044Q00Point06
  · exact shortNegativeR044Q00Point07
  · exact shortNegativeR044Q00Point08
  · exact shortNegativeR044Q00Point09
  · exact shortNegativeR044Q00Point10
  · exact shortNegativeR044Q00Point11

theorem shortNegativeR044Q00Bound {t a : ℝ} (tl : ((5/4):ℝ)≤t) (tu : t≤((63/50):ℝ)) (al : ((1276707689160517/1649267441664000):ℝ)≤a) (au : a≤((1281002656456517/1649267441664000):ℝ)) : (((-3302633445369412862405870823218415/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2242354841530912125152988408913135/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR044Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1276707689160517/1649267441664000) (1281002656456517/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR044Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR044Q00F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR044Q00L shortNegativeR044Q00U (-3302633445369412862405870823218415/1298074214633706907132624082305024) (-2242354841530912125152988408913135/1298074214633706907132624082305024) shortNegativeR044Q00Samples (by decide +kernel)

def shortNegativeR044Q01T := Grid.ofRats (5/4) (63/50)
def shortNegativeR044Q01P : PrimalThetaParameters := ⟨⟨⟨23082638350719460987329,23819311874143386389515,true⟩,⟨0,0,true⟩⟩, ⟨⟨1474953996216341157291039,1479899246833123859299553,true⟩,⟨0,0,true⟩⟩, ⟨(-848044481203621906467050),(-838153979970125221933482),true⟩, ⟨3834475951795030607238236,3887432648448774573905916,true⟩⟩
theorem shortNegativeR044Q01P_ok : shortNegativeR044Q01P.encloses (primalThetaParameters shortNegativeR044Q01T (Grid.ofRats (1281002656456517/1649267441664000) (428432541250839/549755813888000))) := by decide +kernel

def shortNegativeR044Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨449387617532677972991660,452930996228551397339462,true⟩,⟨3226764450877892009548012,3252207182198408205130605,true⟩,⟨⟨410586067826991134303016,415531318443773836360640,true⟩,⟨1133698203993343909941570,1138643454610126612009193,true⟩⟩⟩
  | 1 => ⟨⟨1185631673924494472952,1252640298182163297815,true⟩,⟨449387617532677972991660,452930996228551397339462,true⟩,⟨⟨(-1053710052483638406437208),(-1038874300633427739287513),true⟩,⟨(-613036830882189197091149),(-598201079031978529947511),true⟩⟩⟩
  | 2 => ⟨⟨59726082311091613,68257517947339106,true⟩,⟨1185631673924494472952,1252640298182163297815,true⟩,⟨⟨1178580833338978963691994,1203307086422617595897525,true⟩,⟨(-220098828226306991428834),(-195372575142668359236846),true⟩⟩⟩
  | 3 => ⟨⟨23086891785,107642820285,true⟩,⟨59726082311091613,68257517947339106,true⟩,⟨⟨(-796775117698745357541655),(-762158363381678760234505),true⟩,⟨906776704272024508298963,941393458589091105608102,true⟩⟩⟩
  | 4 => ⟨⟨(-34359737314),34359739919,true⟩,⟨23086891785,107642820285,true⟩,⟨⟨(-18247699110806042021952),26259556439688520337038,true⟩,⟨(-1231172810295914510522474),(-1186665554745419948147151),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359737314),34359739919,true⟩,⟨⟨746126632815262613039547,800524389599185140460647,true⟩,⟨902031604882769008630836,956429361666691536054076,true⟩⟩⟩
theorem shortNegativeR044Q01F_ok : ∀ n : Fin 6, (shortNegativeR044Q01F n).encloses (FactoredFrequency.build shortNegativeR044Q01T (Grid.ofRats (1281002656456517/1649267441664000) (428432541250839/549755813888000)) n) := by decide +kernel
def shortNegativeR044Q01L : ℕ → ℚ
  | 0 => (-337421/125000)
  | 1 => (-134013/62500)
  | 2 => (-5324/3125)
  | 3 => (-1470409/1000000)
  | 4 => (-369367/250000)
  | 5 => (-1733501/1000000)
  | 6 => (-1084357/500000)
  | 7 => (-272487/100000)
  | 8 => (-3270461/1000000)
  | 9 => (-1830841/500000)
  | 10 => (-3702967/1000000)
  | 11 => (-835949/250000)
  | _ => 0
def shortNegativeR044Q01U : ℕ → ℚ
  | 0 => (-87107/40000)
  | 1 => (-788577/500000)
  | 2 => (-138857/125000)
  | 3 => (-212621/250000)
  | 4 => (-828221/1000000)
  | 5 => (-1003391/1000000)
  | 6 => (-344457/250000)
  | 7 => (-1895301/1000000)
  | 8 => (-302347/125000)
  | 9 => (-554503/200000)
  | 10 => (-356341/125000)
  | 11 => (-261807/100000)
  | _ => 0
private theorem shortNegativeR044Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR044Q01P shortNegativeR044Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR044Q01L (0:Fin 12)) (shortNegativeR044Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR044Q01P shortNegativeR044Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR044Q01L (1:Fin 12)) (shortNegativeR044Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR044Q01P shortNegativeR044Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR044Q01L (2:Fin 12)) (shortNegativeR044Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR044Q01P shortNegativeR044Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR044Q01L (3:Fin 12)) (shortNegativeR044Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR044Q01P shortNegativeR044Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR044Q01L (4:Fin 12)) (shortNegativeR044Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR044Q01P shortNegativeR044Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR044Q01L (5:Fin 12)) (shortNegativeR044Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR044Q01P shortNegativeR044Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR044Q01L (6:Fin 12)) (shortNegativeR044Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR044Q01P shortNegativeR044Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR044Q01L (7:Fin 12)) (shortNegativeR044Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR044Q01P shortNegativeR044Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR044Q01L (8:Fin 12)) (shortNegativeR044Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR044Q01P shortNegativeR044Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR044Q01L (9:Fin 12)) (shortNegativeR044Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR044Q01P shortNegativeR044Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR044Q01L (10:Fin 12)) (shortNegativeR044Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR044Q01P shortNegativeR044Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR044Q01L (11:Fin 12)) (shortNegativeR044Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR044Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR044Q01P shortNegativeR044Q01F (shortNegativeNodes12 k)).re (shortNegativeR044Q01L k) (shortNegativeR044Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR044Q01Point00
  · exact shortNegativeR044Q01Point01
  · exact shortNegativeR044Q01Point02
  · exact shortNegativeR044Q01Point03
  · exact shortNegativeR044Q01Point04
  · exact shortNegativeR044Q01Point05
  · exact shortNegativeR044Q01Point06
  · exact shortNegativeR044Q01Point07
  · exact shortNegativeR044Q01Point08
  · exact shortNegativeR044Q01Point09
  · exact shortNegativeR044Q01Point10
  · exact shortNegativeR044Q01Point11

theorem shortNegativeR044Q01Bound {t a : ℝ} (tl : ((5/4):ℝ)≤t) (tu : t≤((63/50):ℝ)) (al : ((1281002656456517/1649267441664000):ℝ)≤a) (au : a≤((428432541250839/549755813888000):ℝ)) : (((-3302633445369412862405870823218415/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2242354841530912125152988408913135/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR044Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1281002656456517/1649267441664000) (428432541250839/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR044Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR044Q01F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR044Q01L shortNegativeR044Q01U (-3302633445369412862405870823218415/1298074214633706907132624082305024) (-2242354841530912125152988408913135/1298074214633706907132624082305024) shortNegativeR044Q01Samples (by decide +kernel)

def shortNegativeR044Q02T := Grid.ofRats (5/4) (63/50)
def shortNegativeR044Q02P : PrimalThetaParameters := ⟨⟨⟨23082638350719460987329,23819311874143386389515,true⟩,⟨0,0,true⟩⟩, ⟨⟨1479899246833055139818103,1484844497449837841826632,true⟩,⟨0,0,true⟩⟩, ⟨(-838153979970193941412890),(-828263478736697256879357),true⟩, ⟨3824732110818957328851300,3877548233926261290827433,true⟩⟩
theorem shortNegativeR044Q02P_ok : shortNegativeR044Q02P.encloses (primalThetaParameters shortNegativeR044Q02T (Grid.ofRats (428432541250839/549755813888000) (1289592591048517/1649267441664000))) := by decide +kernel

def shortNegativeR044Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨449387617532677972991660,452930996228551397339462,true⟩,⟨3226764450877892009548012,3252207182198408205130605,true⟩,⟨⟨405934986979616370873015,410880237596399072930121,true⟩,⟨1135378357710084263906273,1140323608326866965973447,true⟩⟩⟩
  | 1 => ⟨⟨1185631673924494472952,1252640298182163297815,true⟩,⟨449387617532677972991660,452930996228551397339462,true⟩,⟨⟨(-1046199392414712547580647),(-1031363640564501880430832),true⟩,⟨(-625830843391388994735776),(-610995091541178327591734),true⟩⟩⟩
  | 2 => ⟨⟨59726082311091613,68257517947339106,true⟩,⟨1185631673924494472952,1252640298182163297815,true⟩,⟨⟨1182580277311944647396199,1207306530395583279601341,true⟩,⟨(-195698608424850557854957),(-170972355341211925663744),true⟩⟩⟩
  | 3 => ⟨⟨23086891785,107642820285,true⟩,⟨59726082311091613,68257517947339106,true⟩,⟨⟨(-822912509034482280945428),(-788295754717415683638840),true⟩,⟨884081449739519461413064,918698204056586058720971,true⟩⟩⟩
  | 4 => ⟨⟨(-34359737314),34359739919,true⟩,⟨23086891785,107642820285,true⟩,⟨⟨26246544279316428423941,70753799829810990782775,true⟩,⟨(-1230206180916959315211063),(-1185698925366464752836272),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359737314),34359739919,true⟩,⟨⟨703545623318905278476669,757943380102827805898707,true⟩,⟨935876461625755254395921,990274218409677781821151,true⟩⟩⟩
theorem shortNegativeR044Q02F_ok : ∀ n : Fin 6, (shortNegativeR044Q02F n).encloses (FactoredFrequency.build shortNegativeR044Q02T (Grid.ofRats (428432541250839/549755813888000) (1289592591048517/1649267441664000)) n) := by decide +kernel
def shortNegativeR044Q02L : ℕ → ℚ
  | 0 => (-67691/25000)
  | 1 => (-269483/125000)
  | 2 => (-68577/40000)
  | 3 => (-73859/50000)
  | 4 => (-738777/500000)
  | 5 => (-345391/200000)
  | 6 => (-1077869/500000)
  | 7 => (-676913/250000)
  | 8 => (-1625603/500000)
  | 9 => (-3645097/1000000)
  | 10 => (-3693511/1000000)
  | 11 => (-3344241/1000000)
  | _ => 0
def shortNegativeR044Q02U : ℕ → ℚ
  | 0 => (-2189123/1000000)
  | 1 => (-1591623/1000000)
  | 2 => (-1123911/1000000)
  | 3 => (-430097/500000)
  | 4 => (-832167/1000000)
  | 5 => (-200237/200000)
  | 6 => (-684853/500000)
  | 7 => (-376513/200000)
  | 8 => (-240371/100000)
  | 9 => (-2760381/1000000)
  | 10 => (-2846011/1000000)
  | 11 => (-2622141/1000000)
  | _ => 0
private theorem shortNegativeR044Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR044Q02P shortNegativeR044Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR044Q02L (0:Fin 12)) (shortNegativeR044Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR044Q02P shortNegativeR044Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR044Q02L (1:Fin 12)) (shortNegativeR044Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR044Q02P shortNegativeR044Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR044Q02L (2:Fin 12)) (shortNegativeR044Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR044Q02P shortNegativeR044Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR044Q02L (3:Fin 12)) (shortNegativeR044Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR044Q02P shortNegativeR044Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR044Q02L (4:Fin 12)) (shortNegativeR044Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR044Q02P shortNegativeR044Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR044Q02L (5:Fin 12)) (shortNegativeR044Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR044Q02P shortNegativeR044Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR044Q02L (6:Fin 12)) (shortNegativeR044Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR044Q02P shortNegativeR044Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR044Q02L (7:Fin 12)) (shortNegativeR044Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR044Q02P shortNegativeR044Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR044Q02L (8:Fin 12)) (shortNegativeR044Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR044Q02P shortNegativeR044Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR044Q02L (9:Fin 12)) (shortNegativeR044Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR044Q02P shortNegativeR044Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR044Q02L (10:Fin 12)) (shortNegativeR044Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR044Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR044Q02P shortNegativeR044Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR044Q02L (11:Fin 12)) (shortNegativeR044Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR044Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR044Q02P shortNegativeR044Q02F (shortNegativeNodes12 k)).re (shortNegativeR044Q02L k) (shortNegativeR044Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR044Q02Point00
  · exact shortNegativeR044Q02Point01
  · exact shortNegativeR044Q02Point02
  · exact shortNegativeR044Q02Point03
  · exact shortNegativeR044Q02Point04
  · exact shortNegativeR044Q02Point05
  · exact shortNegativeR044Q02Point06
  · exact shortNegativeR044Q02Point07
  · exact shortNegativeR044Q02Point08
  · exact shortNegativeR044Q02Point09
  · exact shortNegativeR044Q02Point10
  · exact shortNegativeR044Q02Point11

theorem shortNegativeR044Q02Bound {t a : ℝ} (tl : ((5/4):ℝ)≤t) (tu : t≤((63/50):ℝ)) (al : ((428432541250839/549755813888000):ℝ)≤a) (au : a≤((1289592591048517/1649267441664000):ℝ)) : (((-3302633445369412862405870823218415/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2242354841530912125152988408913135/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR044Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (428432541250839/549755813888000) (1289592591048517/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR044Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR044Q02F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR044Q02L shortNegativeR044Q02U (-3302633445369412862405870823218415/1298074214633706907132624082305024) (-2242354841530912125152988408913135/1298074214633706907132624082305024) shortNegativeR044Q02Samples (by decide +kernel)

theorem short_original_negative_044 {t a : ℝ} (tb : RealMem negative_044.t t) (ab : RealMem negative_044.a a) : RealMem negative_044.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((5/4):ℝ) ((63/50):ℝ) := by simpa [negative_044,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((5/4):ℝ)<((63/50):ℝ)) tB
  have aB : a∈Icc ((1276707689160517/1649267441664000):ℝ) ((1289592591048517/1649267441664000):ℝ) := by simpa [negative_044,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((1276707689160517/1649267441664000):ℝ)<((1289592591048517/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR044Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_044,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR044Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_044,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR044Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_044,RealMem] using v

def shortNegativeR045Q00T := Grid.ofRats (63/50) (127/100)
def shortNegativeR045Q00P : PrimalThetaParameters := ⟨⟨⟨22368748352047117994193,23082638350788180464463,true⟩,⟨0,0,true⟩⟩, ⟨⟨1476424478654376201716501,1486314979887872886252098,true⟩,⟨0,0,true⟩⟩, ⟨(-845103516327551817616117),(-825322513860627168028433),true⟩, ⟨3793413215570113267350003,3882149122610822156671533,true⟩⟩
theorem shortNegativeR045Q00P_ok : shortNegativeR045Q00P.encloses (primalThetaParameters shortNegativeR045Q00T (Grid.ofRats (427426591849733/549755813888000) (1290869710141199/1649267441664000))) := by decide +kernel

def shortNegativeR045Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨445871959466917205370697,449387617532746692485042,true⟩,⟨3252207182198339485534595,3277850527039581792704777,true⟩,⟨⟨404405446402277487799025,414295947635774172383389,true⟩,⟨1132566790717733811318484,1142457291951230495912876,true⟩⟩⟩
  | 1 => ⟨⟨1122207602876885974494,1185631673993213949756,true⟩,⟨445871959466917205370697,449387617532746692485042,true⟩,⟨⟨(-1055151960738041233795932),(-1025480457037688619064738),true⟩,⟨(-630663506060786001978422),(-600992002360433387253066),true⟩⟩⟩
  | 2 => ⟨⟨52261033952272971,59726151030568350,true⟩,⟨1122207602876885974494,1185631673993213949756,true⟩,⟨⟨1169447006315290582009577,1218899512482499126850117,true⟩,⟨(-213012906533929052515270),(-163560400366720507688576),true⟩⟩⟩
  | 3 => ⟨⟨10672692443,91806368522,true⟩,⟨52261033952272971,59726151030568350,true⟩,⟨⟨(-834976883258105379232815),(-765743374624040904236055),true⟩,⟨871432527638608237786543,940666036272672712784752,true⟩⟩⟩
  | 4 => ⟨⟨(-34359737651),34359739423,true⟩,⟨10672692443,91806368522,true⟩,⟨⟨(-5020374355425967585005),83994136745494437517086,true⟩,⟨(-1252788027368166556773657),(-1163773516267246151655548),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359737651),34359739423,true⟩,⟨⟨685098031661947419169632,793893545229723754389086,true⟩,⟨901974355001987203477134,1010769868569763538699576,true⟩⟩⟩
theorem shortNegativeR045Q00F_ok : ∀ n : Fin 6, (shortNegativeR045Q00F n).encloses (FactoredFrequency.build shortNegativeR045Q00T (Grid.ofRats (427426591849733/549755813888000) (1290869710141199/1649267441664000)) n) := by decide +kernel
def shortNegativeR045Q00L : ℕ → ℚ
  | 0 => (-2776391/1000000)
  | 1 => (-2248653/1000000)
  | 2 => (-1825171/1000000)
  | 3 => (-319701/200000)
  | 4 => (-800231/500000)
  | 5 => (-928951/500000)
  | 6 => (-2290077/1000000)
  | 7 => (-2839897/1000000)
  | 8 => (-3369449/1000000)
  | 9 => (-939/250)
  | 10 => (-3794929/1000000)
  | 11 => (-3437127/1000000)
  | _ => 0
def shortNegativeR045Q00U : ℕ → ℚ
  | 0 => (-2149139/1000000)
  | 1 => (-1562817/1000000)
  | 2 => (-1102731/1000000)
  | 3 => (-419737/500000)
  | 4 => (-404027/500000)
  | 5 => (-120277/125000)
  | 6 => (-656907/500000)
  | 7 => (-904979/500000)
  | 8 => (-1157851/500000)
  | 9 => (-1327247/500000)
  | 10 => (-1369883/500000)
  | 11 => (-1267931/500000)
  | _ => 0
private theorem shortNegativeR045Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR045Q00P shortNegativeR045Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR045Q00L (0:Fin 12)) (shortNegativeR045Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR045Q00P shortNegativeR045Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR045Q00L (1:Fin 12)) (shortNegativeR045Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR045Q00P shortNegativeR045Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR045Q00L (2:Fin 12)) (shortNegativeR045Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR045Q00P shortNegativeR045Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR045Q00L (3:Fin 12)) (shortNegativeR045Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR045Q00P shortNegativeR045Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR045Q00L (4:Fin 12)) (shortNegativeR045Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR045Q00P shortNegativeR045Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR045Q00L (5:Fin 12)) (shortNegativeR045Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR045Q00P shortNegativeR045Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR045Q00L (6:Fin 12)) (shortNegativeR045Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR045Q00P shortNegativeR045Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR045Q00L (7:Fin 12)) (shortNegativeR045Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR045Q00P shortNegativeR045Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR045Q00L (8:Fin 12)) (shortNegativeR045Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR045Q00P shortNegativeR045Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR045Q00L (9:Fin 12)) (shortNegativeR045Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR045Q00P shortNegativeR045Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR045Q00L (10:Fin 12)) (shortNegativeR045Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR045Q00P shortNegativeR045Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR045Q00L (11:Fin 12)) (shortNegativeR045Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR045Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR045Q00P shortNegativeR045Q00F (shortNegativeNodes12 k)).re (shortNegativeR045Q00L k) (shortNegativeR045Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR045Q00Point00
  · exact shortNegativeR045Q00Point01
  · exact shortNegativeR045Q00Point02
  · exact shortNegativeR045Q00Point03
  · exact shortNegativeR045Q00Point04
  · exact shortNegativeR045Q00Point05
  · exact shortNegativeR045Q00Point06
  · exact shortNegativeR045Q00Point07
  · exact shortNegativeR045Q00Point08
  · exact shortNegativeR045Q00Point09
  · exact shortNegativeR045Q00Point10
  · exact shortNegativeR045Q00Point11

theorem shortNegativeR045Q00Bound {t a : ℝ} (tl : ((63/50):ℝ)≤t) (tu : t≤((127/100):ℝ)) (al : ((427426591849733/549755813888000):ℝ)≤a) (au : a≤((1290869710141199/1649267441664000):ℝ)) : (((-3409811168853793739306950456715/1267650600228229401496703205376):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2039862451083761617327559275915/1267650600228229401496703205376):ℚ):ℝ) := by
  have ts : shortNegativeR045Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (427426591849733/549755813888000) (1290869710141199/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR045Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR045Q00F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR045Q00L shortNegativeR045Q00U (-3409811168853793739306950456715/1267650600228229401496703205376) (-2039862451083761617327559275915/1267650600228229401496703205376) shortNegativeR045Q00Samples (by decide +kernel)

def shortNegativeR045Q01T := Grid.ofRats (63/50) (127/100)
def shortNegativeR045Q01P : PrimalThetaParameters := ⟨⟨⟨22368748352047117994193,23082638350788180464463,true⟩,⟨0,0,true⟩⟩, ⟨⟨1486314979887804166770627,1496205481121300851306258,true⟩,⟨0,0,true⟩⟩, ⟨(-825322513860695887507801),(-805541511393771237920177),true⟩, ⟨3774448462866593699760802,3862615951796125687756774,true⟩⟩
theorem shortNegativeR045Q01P_ok : shortNegativeR045Q01P.encloses (primalThetaParameters shortNegativeR045Q01T (Grid.ofRats (1290869710141199/1649267441664000) (1299459644733199/1649267441664000))) := by decide +kernel

def shortNegativeR045Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨445871959466917205370697,449387617532746692485042,true⟩,⟨3252207182198339485534595,3277850527039581792704777,true⟩,⟨⟨395085602226722232445160,404976103460218917029433,true⟩,⟨1135877677845082892909589,1145768179078579577504067,true⟩⟩⟩
  | 1 => ⟨⟨1122207602876885974494,1185631673993213949756,true⟩,⟨445871959466917205370697,449387617532746692485042,true⟩,⟨⟨(-1039725467299054071222213),(-1010053963598701456490702),true⟩,⟨(-656008668073266072133827),(-626337164372913457407588),true⟩⟩⟩
  | 2 => ⟨⟨52261033952272971,59726151030568350,true⟩,⟨1122207602876885974494,1185631673993213949756,true⟩,⟨⟨1176147967617224826021018,1225600473784433370860172,true⟩,⟨(-164019983692987133563609),(-114567477525778588739075),true⟩⟩⟩
  | 3 => ⟨⟨10672692443,91806368522,true⟩,⟨52261033952272971,59726151030568350,true⟩,⟨⟨(-885524603844704705138720),(-816291095210640230141257),true⟩,⟨824136684653138541109279,893370193287203016106843,true⟩⟩⟩
  | 4 => ⟨⟨(-34359737651),34359739423,true⟩,⟨10672692443,91806368522,true⟩,⟨⟨83759281913991575452655,172773793014911980555108,true⟩,⟨(-1246609303089596252030164),(-1157594791988675846912930),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359737651),34359739423,true⟩,⟨⟨596154339829564060588084,704949853397340395810720,true⟩,⟨964564267495105478202716,1073359781062881813430425,true⟩⟩⟩
theorem shortNegativeR045Q01F_ok : ∀ n : Fin 6, (shortNegativeR045Q01F n).encloses (FactoredFrequency.build shortNegativeR045Q01T (Grid.ofRats (1290869710141199/1649267441664000) (1299459644733199/1649267441664000)) n) := by decide +kernel
def shortNegativeR045Q01L : ℕ → ℚ
  | 0 => (-697761/250000)
  | 1 => (-2270167/1000000)
  | 2 => (-922621/500000)
  | 3 => (-1611059/1000000)
  | 4 => (-399953/250000)
  | 5 => (-461063/250000)
  | 6 => (-1132953/500000)
  | 7 => (-2805503/1000000)
  | 8 => (-133241/40000)
  | 9 => (-1861289/500000)
  | 10 => (-3775111/1000000)
  | 11 => (-1718241/500000)
  | _ => 0
def shortNegativeR045Q01U : ℕ → ℚ
  | 0 => (-1085473/500000)
  | 1 => (-795347/500000)
  | 2 => (-564061/500000)
  | 3 => (-858867/1000000)
  | 4 => (-408169/500000)
  | 5 => (-958627/1000000)
  | 6 => (-1298777/1000000)
  | 7 => (-1785951/1000000)
  | 8 => (-2286779/1000000)
  | 9 => (-2631049/1000000)
  | 10 => (-2730369/1000000)
  | 11 => (-2543241/1000000)
  | _ => 0
private theorem shortNegativeR045Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR045Q01P shortNegativeR045Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR045Q01L (0:Fin 12)) (shortNegativeR045Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR045Q01P shortNegativeR045Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR045Q01L (1:Fin 12)) (shortNegativeR045Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR045Q01P shortNegativeR045Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR045Q01L (2:Fin 12)) (shortNegativeR045Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR045Q01P shortNegativeR045Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR045Q01L (3:Fin 12)) (shortNegativeR045Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR045Q01P shortNegativeR045Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR045Q01L (4:Fin 12)) (shortNegativeR045Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR045Q01P shortNegativeR045Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR045Q01L (5:Fin 12)) (shortNegativeR045Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR045Q01P shortNegativeR045Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR045Q01L (6:Fin 12)) (shortNegativeR045Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR045Q01P shortNegativeR045Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR045Q01L (7:Fin 12)) (shortNegativeR045Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR045Q01P shortNegativeR045Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR045Q01L (8:Fin 12)) (shortNegativeR045Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR045Q01P shortNegativeR045Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR045Q01L (9:Fin 12)) (shortNegativeR045Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR045Q01P shortNegativeR045Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR045Q01L (10:Fin 12)) (shortNegativeR045Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR045Q01P shortNegativeR045Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR045Q01L (11:Fin 12)) (shortNegativeR045Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR045Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR045Q01P shortNegativeR045Q01F (shortNegativeNodes12 k)).re (shortNegativeR045Q01L k) (shortNegativeR045Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR045Q01Point00
  · exact shortNegativeR045Q01Point01
  · exact shortNegativeR045Q01Point02
  · exact shortNegativeR045Q01Point03
  · exact shortNegativeR045Q01Point04
  · exact shortNegativeR045Q01Point05
  · exact shortNegativeR045Q01Point06
  · exact shortNegativeR045Q01Point07
  · exact shortNegativeR045Q01Point08
  · exact shortNegativeR045Q01Point09
  · exact shortNegativeR045Q01Point10
  · exact shortNegativeR045Q01Point11

theorem shortNegativeR045Q01Bound {t a : ℝ} (tl : ((63/50):ℝ)≤t) (tu : t≤((127/100):ℝ)) (al : ((1290869710141199/1649267441664000):ℝ)≤a) (au : a≤((1299459644733199/1649267441664000):ℝ)) : (((-3409811168853793739306950456715/1267650600228229401496703205376):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2039862451083761617327559275915/1267650600228229401496703205376):ℚ):ℝ) := by
  have ts : shortNegativeR045Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1290869710141199/1649267441664000) (1299459644733199/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR045Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR045Q01F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR045Q01L shortNegativeR045Q01U (-3409811168853793739306950456715/1267650600228229401496703205376) (-2039862451083761617327559275915/1267650600228229401496703205376) shortNegativeR045Q01Samples (by decide +kernel)

def shortNegativeR045Q02T := Grid.ofRats (63/50) (127/100)
def shortNegativeR045Q02P : PrimalThetaParameters := ⟨⟨⟨22368748352047117994193,23082638350788180464463,true⟩,⟨0,0,true⟩⟩, ⟨⟨1496205481121232131824755,1506095982354728816360416,true⟩,⟨0,0,true⟩⟩, ⟨(-805541511393839957399482),(-785760508926915307811924),true⟩, ⟨3756083213752504536966278,3843700321809035513738145,true⟩⟩
theorem shortNegativeR045Q02P_ok : shortNegativeR045Q02P.encloses (primalThetaParameters shortNegativeR045Q02T (Grid.ofRats (1299459644733199/1649267441664000) (436016526441733/549755813888000))) := by decide +kernel

def shortNegativeR045Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨445871959466917205370697,449387617532746692485042,true⟩,⟨3252207182198339485534595,3277850527039581792704777,true⟩,⟨⟨385738983120040243863199,395629484353536928447686,true⟩,⟨1139112207223722737130275,1149002708457219421725153,true⟩⟩⟩
  | 1 => ⟨⟨1122207602876885974494,1185631673993213949756,true⟩,⟨445871959466917205370697,449387617532746692485042,true⟩,⟨⟨(-1023681618618575350940274),(-994010114918222736208250),true⟩,⟨(-680967611496012917243955),(-651296107795660302516640),true⟩⟩⟩
  | 2 => ⟨⟨52261033952272971,59726151030568350,true⟩,⟨1122207602876885974494,1185631673993213949756,true⟩,⟨⟨1180839770104219440625088,1230292276271427985463350,true⟩,⟨(-114794011277081119097814),(-65341505109872574274904),true⟩⟩⟩
  | 3 => ⟨⟨10672692443,91806368522,true⟩,⟨52261033952272971,59726151030568350,true⟩,⟨⟨(-933282369374358108303428),(-864048860740293633306833),true⟩,⟨774025162506812057656502,843258671140876532651858,true⟩⟩⟩
  | 4 => ⟨⟨(-34359737651),34359739423,true⟩,⟨10672692443,91806368522,true⟩,⟨⟨171843850703540445503337,260858361804460850605666,true⟩,⟨(-1233916283662140982512862),(-1144901772561220577397141),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359737651),34359739423,true⟩,⟨⟨501945487414029882706080,610741000981806217931068,true⟩,⟨1018907340551551976451833,1127702854119328311683940,true⟩⟩⟩
theorem shortNegativeR045Q02F_ok : ∀ n : Fin 6, (shortNegativeR045Q02F n).encloses (FactoredFrequency.build shortNegativeR045Q02T (Grid.ofRats (1299459644733199/1649267441664000) (436016526441733/549755813888000)) n) := by decide +kernel
def shortNegativeR045Q02L : ℕ → ℚ
  | 0 => (-350667/125000)
  | 1 => (-458303/200000)
  | 2 => (-93269/50000)
  | 3 => (-162387/100000)
  | 4 => (-1599617/1000000)
  | 5 => (-1831147/1000000)
  | 6 => (-89691/40000)
  | 7 => (-692903/250000)
  | 8 => (-1646463/500000)
  | 9 => (-1844577/500000)
  | 10 => (-938741/250000)
  | 11 => (-3435347/1000000)
  | _ => 0
def shortNegativeR045Q02U : ℕ → ℚ
  | 0 => (-438473/200000)
  | 1 => (-40461/25000)
  | 2 => (-1153657/1000000)
  | 3 => (-878549/1000000)
  | 4 => (-825061/1000000)
  | 5 => (-955579/1000000)
  | 6 => (-321083/250000)
  | 7 => (-141/80)
  | 8 => (-225829/100000)
  | 9 => (-521551/200000)
  | 10 => (-2720803/1000000)
  | 11 => (-10201/4000)
  | _ => 0
private theorem shortNegativeR045Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR045Q02P shortNegativeR045Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR045Q02L (0:Fin 12)) (shortNegativeR045Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR045Q02P shortNegativeR045Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR045Q02L (1:Fin 12)) (shortNegativeR045Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR045Q02P shortNegativeR045Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR045Q02L (2:Fin 12)) (shortNegativeR045Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR045Q02P shortNegativeR045Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR045Q02L (3:Fin 12)) (shortNegativeR045Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR045Q02P shortNegativeR045Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR045Q02L (4:Fin 12)) (shortNegativeR045Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR045Q02P shortNegativeR045Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR045Q02L (5:Fin 12)) (shortNegativeR045Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR045Q02P shortNegativeR045Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR045Q02L (6:Fin 12)) (shortNegativeR045Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR045Q02P shortNegativeR045Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR045Q02L (7:Fin 12)) (shortNegativeR045Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR045Q02P shortNegativeR045Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR045Q02L (8:Fin 12)) (shortNegativeR045Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR045Q02P shortNegativeR045Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR045Q02L (9:Fin 12)) (shortNegativeR045Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR045Q02P shortNegativeR045Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR045Q02L (10:Fin 12)) (shortNegativeR045Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR045Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR045Q02P shortNegativeR045Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR045Q02L (11:Fin 12)) (shortNegativeR045Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR045Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR045Q02P shortNegativeR045Q02F (shortNegativeNodes12 k)).re (shortNegativeR045Q02L k) (shortNegativeR045Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR045Q02Point00
  · exact shortNegativeR045Q02Point01
  · exact shortNegativeR045Q02Point02
  · exact shortNegativeR045Q02Point03
  · exact shortNegativeR045Q02Point04
  · exact shortNegativeR045Q02Point05
  · exact shortNegativeR045Q02Point06
  · exact shortNegativeR045Q02Point07
  · exact shortNegativeR045Q02Point08
  · exact shortNegativeR045Q02Point09
  · exact shortNegativeR045Q02Point10
  · exact shortNegativeR045Q02Point11

theorem shortNegativeR045Q02Bound {t a : ℝ} (tl : ((63/50):ℝ)≤t) (tu : t≤((127/100):ℝ)) (al : ((1299459644733199/1649267441664000):ℝ)≤a) (au : a≤((436016526441733/549755813888000):ℝ)) : (((-3409811168853793739306950456715/1267650600228229401496703205376):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2039862451083761617327559275915/1267650600228229401496703205376):ℚ):ℝ) := by
  have ts : shortNegativeR045Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1299459644733199/1649267441664000) (436016526441733/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR045Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR045Q02F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR045Q02L shortNegativeR045Q02U (-3409811168853793739306950456715/1267650600228229401496703205376) (-2039862451083761617327559275915/1267650600228229401496703205376) shortNegativeR045Q02Samples (by decide +kernel)

theorem short_original_negative_045 {t a : ℝ} (tb : RealMem negative_045.t t) (ab : RealMem negative_045.a a) : RealMem negative_045.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((63/50):ℝ) ((127/100):ℝ) := by simpa [negative_045,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((63/50):ℝ)<((127/100):ℝ)) tB
  have aB : a∈Icc ((427426591849733/549755813888000):ℝ) ((436016526441733/549755813888000):ℝ) := by simpa [negative_045,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((427426591849733/549755813888000):ℝ)<((436016526441733/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR045Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_045,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR045Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_045,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR045Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_045,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_044
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_045
