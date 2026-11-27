import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip056

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR056Q00T := Grid.ofRats (137/100) (69/50)
def shortNegativeR056Q00P : PrimalThetaParameters := ⟨⟨⟨15832893292989752023175,16338193991784627953815,true⟩,⟨0,0,true⟩⟩, ⟨⟨1670116902198393495049754,1689897904665318144640128,true⟩,⟨0,0,true⟩⟩, ⟨(-457718669239517230948377),(-418156664305736651253670),true⟩, ⟨3347567138629026032779819,3479315532680509902488267,true⟩⟩
theorem shortNegativeR056Q00P_ok : shortNegativeR056Q00P.encloses (primalThetaParameters shortNegativeR056Q00T (Grid.ofRats (483500772181657/549755813888000) (1467682185728971/1649267441664000))) := by decide +kernel

def shortNegativeR056Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨408968455205758580776327,412193132644401541192970,true⟩,⟨3545671971667335060334838,3573629258509655217383487,true⟩,⟨⟨207883012840524839883007,227664015307449489522239,true⟩,⟨1179258914903454353642620,1199039917370379003295229,true⟩⟩⟩
  | 1 => ⟨⟨612958057824028045105,647600752622279839218,true⟩,⟨408968455205758580776327,412193132644401541192970,true⟩,⟨⟨(-654725296927588451582978),(-595382289526951941683735),true⟩,⟨(-1064470707847240602337859),(-1005127700446604092432967),true⟩⟩⟩
  | 2 => ⟨⟨12031813669521140,13750529372028183,true⟩,⟨612958057824028045105,647600752622279839218,true⟩,⟨⟨901750310392562144863010,1000655322726910514993947,true⟩,⟨696680752104917259040303,795585764439265629168425,true⟩⟩⟩
  | 3 => ⟨⟨(-31266634182),38305526082,true⟩,⟨12031813669521140,13750529372028183,true⟩,⟨⟨(-1223120328580773872240056),(-1084653311312713641866462),true⟩,⟨(-429853591386078010388702),(-291386574118017780026023),true⟩⟩⟩
  | 4 => ⟨⟨(-34359738358),34359738384,true⟩,⟨(-31266634182),38305526082,true⟩,⟨⟨1117783144240379766108024,1295812166442151856673001,true⟩,⟨(-160715671438263649339922),17313350763508441209654,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738358),34359738384,true⟩,⟨⟨(-1211863071378490473097944),(-994272044243006522249008),true⟩,⟨385920162590123411468439,603511189725607362309002,true⟩⟩⟩
theorem shortNegativeR056Q00F_ok : ∀ n : Fin 6, (shortNegativeR056Q00F n).encloses (FactoredFrequency.build shortNegativeR056Q00T (Grid.ofRats (483500772181657/549755813888000) (1467682185728971/1649267441664000)) n) := by decide +kernel
def shortNegativeR056Q00L : ℕ → ℚ
  | 0 => (-3025411/1000000)
  | 1 => (-2807013/1000000)
  | 2 => (-2541541/1000000)
  | 3 => (-288921/125000)
  | 4 => (-2175283/1000000)
  | 5 => (-2208801/1000000)
  | 6 => (-1184701/500000)
  | 7 => (-2626099/1000000)
  | 8 => (-2920253/1000000)
  | 9 => (-128809/40000)
  | 10 => (-675533/200000)
  | 11 => (-666231/200000)
  | _ => 0
def shortNegativeR056Q00U : ℕ → ℚ
  | 0 => (-476403/200000)
  | 1 => (-2071287/1000000)
  | 2 => (-432163/250000)
  | 3 => (-1441023/1000000)
  | 4 => (-634289/500000)
  | 5 => (-600853/500000)
  | 6 => (-1282527/1000000)
  | 7 => (-1494933/1000000)
  | 8 => (-359047/200000)
  | 9 => (-1037219/500000)
  | 10 => (-2296079/1000000)
  | 11 => (-149463/62500)
  | _ => 0
private theorem shortNegativeR056Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR056Q00P shortNegativeR056Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR056Q00L (0:Fin 12)) (shortNegativeR056Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR056Q00P shortNegativeR056Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR056Q00L (1:Fin 12)) (shortNegativeR056Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR056Q00P shortNegativeR056Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR056Q00L (2:Fin 12)) (shortNegativeR056Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR056Q00P shortNegativeR056Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR056Q00L (3:Fin 12)) (shortNegativeR056Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR056Q00P shortNegativeR056Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR056Q00L (4:Fin 12)) (shortNegativeR056Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR056Q00P shortNegativeR056Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR056Q00L (5:Fin 12)) (shortNegativeR056Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR056Q00P shortNegativeR056Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR056Q00L (6:Fin 12)) (shortNegativeR056Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR056Q00P shortNegativeR056Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR056Q00L (7:Fin 12)) (shortNegativeR056Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR056Q00P shortNegativeR056Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR056Q00L (8:Fin 12)) (shortNegativeR056Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR056Q00P shortNegativeR056Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR056Q00L (9:Fin 12)) (shortNegativeR056Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR056Q00P shortNegativeR056Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR056Q00L (10:Fin 12)) (shortNegativeR056Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR056Q00P shortNegativeR056Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR056Q00L (11:Fin 12)) (shortNegativeR056Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR056Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR056Q00P shortNegativeR056Q00F (shortNegativeNodes12 k)).re (shortNegativeR056Q00L k) (shortNegativeR056Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR056Q00Point00
  · exact shortNegativeR056Q00Point01
  · exact shortNegativeR056Q00Point02
  · exact shortNegativeR056Q00Point03
  · exact shortNegativeR056Q00Point04
  · exact shortNegativeR056Q00Point05
  · exact shortNegativeR056Q00Point06
  · exact shortNegativeR056Q00Point07
  · exact shortNegativeR056Q00Point08
  · exact shortNegativeR056Q00Point09
  · exact shortNegativeR056Q00Point10
  · exact shortNegativeR056Q00Point11

theorem shortNegativeR056Q00Bound {t a : ℝ} (tl : ((137/100):ℝ)≤t) (tu : t≤((69/50):ℝ)) (al : ((483500772181657/549755813888000):ℝ)≤a) (au : a≤((1467682185728971/1649267441664000):ℝ)) : (((-1821309028325545181763278582559079/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1067394113570429780627520047264103/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR056Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (483500772181657/549755813888000) (1467682185728971/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR056Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR056Q00F_ok n) ts asb
  exact factored_negative_12_samples 80 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip056Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR056Q00L shortNegativeR056Q00U (-1821309028325545181763278582559079/649037107316853453566312041152512) (-1067394113570429780627520047264103/649037107316853453566312041152512) shortNegativeR056Q00Samples (by decide +kernel)

def shortNegativeR056Q01T := Grid.ofRats (137/100) (69/50)
def shortNegativeR056Q01P : PrimalThetaParameters := ⟨⟨⟨15832893292989752023175,16338193991784627953815,true⟩,⟨0,0,true⟩⟩, ⟨⟨1689897904665249425158009,1709678907132174074748444,true⟩,⟨0,0,true⟩⟩, ⟨(-418156664305805370731741),(-378594659372024791037164),true⟩, ⟨3330651648767307057711198,3461360686643194015052683,true⟩⟩
theorem shortNegativeR056Q01P_ok : shortNegativeR056Q01P.encloses (primalThetaParameters shortNegativeR056Q01T (Grid.ofRats (1467682185728971/1649267441664000) (1484862054912971/1649267441664000))) := by decide +kernel

def shortNegativeR056Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨408968455205758580776327,412193132644401541192970,true⟩,⟨3545671971667335060334838,3573629258509655217383487,true⟩,⟨⟨188397317612063138990131,208178320078987788629707,true⟩,⟨1182662884669402400641907,1202443887136327050295180,true⟩⟩⟩
  | 1 => ⟨⟨612958057824028045105,647600752622279839218,true⟩,⟨408968455205758580776327,412193132644401541192970,true⟩,⟨⟨(-603197201916170550543658),(-543854194515534040644447),true⟩,⟨(-1093894182850185854299928),(-1034551175449549344393957),true⟩⟩⟩
  | 2 => ⟨⟨12031813669521140,13750529372028183,true⟩,⟨612958057824028045105,647600752622279839218,true⟩,⟨⟨837593953289887176165295,936498965624235546297848,true⟩,⟨771918430800767792374309,870823443135116162505961,true⟩⟩⟩
  | 3 => ⟨⟨(-31266634182),38305526082,true⟩,⟨12031813669521140,13750529372028183,true⟩,⟨⟨(-1174345632386107683796491),(-1035878615118047453420232),true⟩,⟨(-559364951480819645278821),(-420897934212759414911025),true⟩⟩⟩
  | 4 => ⟨⟨(-34359738358),34359738384,true⟩,⟨(-31266634182),38305526082,true⟩,⟨⟨1115242127118571272076759,1293271149320343362643702,true⟩,⟨17134377896003657352747,195163400097775747904578,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738358),34359738384,true⟩,⟨⟨(-1282606572157710578547285),(-1065015545022226627702540),true⟩,⟨180460836514326600449581,398051863649810551282150,true⟩⟩⟩
theorem shortNegativeR056Q01F_ok : ∀ n : Fin 6, (shortNegativeR056Q01F n).encloses (FactoredFrequency.build shortNegativeR056Q01T (Grid.ofRats (1467682185728971/1649267441664000) (1484862054912971/1649267441664000)) n) := by decide +kernel
def shortNegativeR056Q01L : ℕ → ℚ
  | 0 => (-605201/200000)
  | 1 => (-2822107/1000000)
  | 2 => (-1281009/500000)
  | 3 => (-93103/40000)
  | 4 => (-272471/125000)
  | 5 => (-2195939/1000000)
  | 6 => (-2337963/1000000)
  | 7 => (-322309/125000)
  | 8 => (-2863049/1000000)
  | 9 => (-3162483/1000000)
  | 10 => (-3332113/1000000)
  | 11 => (-826613/250000)
  | _ => 0
def shortNegativeR056Q01U : ℕ → ℚ
  | 0 => (-2398237/1000000)
  | 1 => (-2103471/1000000)
  | 2 => (-883407/500000)
  | 3 => (-1475173/1000000)
  | 4 => (-645691/500000)
  | 5 => (-1210073/1000000)
  | 6 => (-318893/250000)
  | 7 => (-36867/25000)
  | 8 => (-1766777/1000000)
  | 9 => (-1023373/500000)
  | 10 => (-2277987/1000000)
  | 11 => (-239043/100000)
  | _ => 0
private theorem shortNegativeR056Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR056Q01P shortNegativeR056Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR056Q01L (0:Fin 12)) (shortNegativeR056Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR056Q01P shortNegativeR056Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR056Q01L (1:Fin 12)) (shortNegativeR056Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR056Q01P shortNegativeR056Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR056Q01L (2:Fin 12)) (shortNegativeR056Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR056Q01P shortNegativeR056Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR056Q01L (3:Fin 12)) (shortNegativeR056Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR056Q01P shortNegativeR056Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR056Q01L (4:Fin 12)) (shortNegativeR056Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR056Q01P shortNegativeR056Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR056Q01L (5:Fin 12)) (shortNegativeR056Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR056Q01P shortNegativeR056Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR056Q01L (6:Fin 12)) (shortNegativeR056Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR056Q01P shortNegativeR056Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR056Q01L (7:Fin 12)) (shortNegativeR056Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR056Q01P shortNegativeR056Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR056Q01L (8:Fin 12)) (shortNegativeR056Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR056Q01P shortNegativeR056Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR056Q01L (9:Fin 12)) (shortNegativeR056Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR056Q01P shortNegativeR056Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR056Q01L (10:Fin 12)) (shortNegativeR056Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR056Q01P shortNegativeR056Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR056Q01L (11:Fin 12)) (shortNegativeR056Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR056Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR056Q01P shortNegativeR056Q01F (shortNegativeNodes12 k)).re (shortNegativeR056Q01L k) (shortNegativeR056Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR056Q01Point00
  · exact shortNegativeR056Q01Point01
  · exact shortNegativeR056Q01Point02
  · exact shortNegativeR056Q01Point03
  · exact shortNegativeR056Q01Point04
  · exact shortNegativeR056Q01Point05
  · exact shortNegativeR056Q01Point06
  · exact shortNegativeR056Q01Point07
  · exact shortNegativeR056Q01Point08
  · exact shortNegativeR056Q01Point09
  · exact shortNegativeR056Q01Point10
  · exact shortNegativeR056Q01Point11

theorem shortNegativeR056Q01Bound {t a : ℝ} (tl : ((137/100):ℝ)≤t) (tu : t≤((69/50):ℝ)) (al : ((1467682185728971/1649267441664000):ℝ)≤a) (au : a≤((1484862054912971/1649267441664000):ℝ)) : (((-1821309028325545181763278582559079/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1067394113570429780627520047264103/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR056Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1467682185728971/1649267441664000) (1484862054912971/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR056Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR056Q01F_ok n) ts asb
  exact factored_negative_12_samples 80 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip056Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR056Q01L shortNegativeR056Q01U (-1821309028325545181763278582559079/649037107316853453566312041152512) (-1067394113570429780627520047264103/649037107316853453566312041152512) shortNegativeR056Q01Samples (by decide +kernel)

def shortNegativeR056Q02T := Grid.ofRats (137/100) (69/50)
def shortNegativeR056Q02P : PrimalThetaParameters := ⟨⟨⟨15832893292989752023175,16338193991784627953815,true⟩,⟨0,0,true⟩⟩, ⟨⟨1709678907132105355266262,1729459909599030004856761,true⟩,⟨0,0,true⟩⟩, ⟨(-378594659372093510515109),(-339032654438312930820654),true⟩, ⟨3315454536901572309881731,3445217701161153199457860,true⟩⟩
theorem shortNegativeR056Q02P_ok : shortNegativeR056Q02P.encloses (primalThetaParameters shortNegativeR056Q02T (Grid.ofRats (1484862054912971/1649267441664000) (500680641365657/549755813888000))) := by decide +kernel

def shortNegativeR056Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨408968455205758580776327,412193132644401541192970,true⟩,⟨3545671971667335060334838,3573629258509655217383487,true⟩,⟨⟨168858535939723245004568,188639538406647894643988,true⟩,⟨1185747579056958184962031,1205528581523882834615454,true⟩⟩⟩
  | 1 => ⟨⟨612958057824028045105,647600752622279839218,true⟩,⟨408968455205758580776327,412193132644401541192970,true⟩,⟨⟨(-550287433262832497902252),(-490944425862195988003094),true⟩,⟨(-1120753852204161536951865),(-1061410844803525027044843),true⟩⟩⟩
  | 2 => ⟨⟨12031813669521140,13750529372028183,true⟩,⟨612958057824028045105,647600752622279839218,true⟩,⟨⟨767503679930166712563878,866408692264515082699243,true⟩,⟨841661531051514130917719,940566543385862501054111,true⟩⟩⟩
  | 3 => ⟨⟨(-31266634182),38305526082,true⟩,⟨12031813669521140,13750529372028183,true⟩,⟨⟨(-1111089058505212046918463),(-972622041237151816539586),true⟩,⟨(-682453412529459831142602),(-543986395261399600769624),true⟩⟩⟩
  | 4 => ⟨⟨(-34359738358),34359738384,true⟩,⟨(-31266634182),38305526082,true⟩,⟨⟨1086632590549533456858635,1264661612751305547432361,true⟩,⟨192686624345656151506380,370715646547428242067807,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738358),34359738384,true⟩,⟨⟨(-1315426599170544010610362),(-1097835572035060059770171),true⟩,⟨(-34343780291032122056214),183247246844451828768865,true⟩⟩⟩
theorem shortNegativeR056Q02F_ok : ∀ n : Fin 6, (shortNegativeR056Q02F n).encloses (FactoredFrequency.build shortNegativeR056Q02T (Grid.ofRats (1484862054912971/1649267441664000) (500680641365657/549755813888000)) n) := by decide +kernel
def shortNegativeR056Q02L : ℕ → ℚ
  | 0 => (-3026027/1000000)
  | 1 => (-2836913/1000000)
  | 2 => (-2582743/1000000)
  | 3 => (-2344571/1000000)
  | 4 => (-43709/20000)
  | 5 => (-1092251/500000)
  | 6 => (-1154011/500000)
  | 7 => (-253223/100000)
  | 8 => (-140343/50000)
  | 9 => (-1552543/500000)
  | 10 => (-3286143/1000000)
  | 11 => (-1640663/500000)
  | _ => 0
def shortNegativeR056Q02U : ℕ → ℚ
  | 0 => (-241349/100000)
  | 1 => (-1067597/500000)
  | 2 => (-902639/500000)
  | 3 => (-1510357/1000000)
  | 4 => (-328939/250000)
  | 5 => (-305089/250000)
  | 6 => (-1270671/1000000)
  | 7 => (-72819/50000)
  | 8 => (-869941/500000)
  | 9 => (-2019989/1000000)
  | 10 => (-70627/31250)
  | 11 => (-477707/200000)
  | _ => 0
private theorem shortNegativeR056Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR056Q02P shortNegativeR056Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR056Q02L (0:Fin 12)) (shortNegativeR056Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR056Q02P shortNegativeR056Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR056Q02L (1:Fin 12)) (shortNegativeR056Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR056Q02P shortNegativeR056Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR056Q02L (2:Fin 12)) (shortNegativeR056Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR056Q02P shortNegativeR056Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR056Q02L (3:Fin 12)) (shortNegativeR056Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR056Q02P shortNegativeR056Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR056Q02L (4:Fin 12)) (shortNegativeR056Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR056Q02P shortNegativeR056Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR056Q02L (5:Fin 12)) (shortNegativeR056Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR056Q02P shortNegativeR056Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR056Q02L (6:Fin 12)) (shortNegativeR056Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR056Q02P shortNegativeR056Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR056Q02L (7:Fin 12)) (shortNegativeR056Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR056Q02P shortNegativeR056Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR056Q02L (8:Fin 12)) (shortNegativeR056Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR056Q02P shortNegativeR056Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR056Q02L (9:Fin 12)) (shortNegativeR056Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR056Q02P shortNegativeR056Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR056Q02L (10:Fin 12)) (shortNegativeR056Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR056Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR056Q02P shortNegativeR056Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR056Q02L (11:Fin 12)) (shortNegativeR056Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR056Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR056Q02P shortNegativeR056Q02F (shortNegativeNodes12 k)).re (shortNegativeR056Q02L k) (shortNegativeR056Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR056Q02Point00
  · exact shortNegativeR056Q02Point01
  · exact shortNegativeR056Q02Point02
  · exact shortNegativeR056Q02Point03
  · exact shortNegativeR056Q02Point04
  · exact shortNegativeR056Q02Point05
  · exact shortNegativeR056Q02Point06
  · exact shortNegativeR056Q02Point07
  · exact shortNegativeR056Q02Point08
  · exact shortNegativeR056Q02Point09
  · exact shortNegativeR056Q02Point10
  · exact shortNegativeR056Q02Point11

theorem shortNegativeR056Q02Bound {t a : ℝ} (tl : ((137/100):ℝ)≤t) (tu : t≤((69/50):ℝ)) (al : ((1484862054912971/1649267441664000):ℝ)≤a) (au : a≤((500680641365657/549755813888000):ℝ)) : (((-1821309028325545181763278582559079/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1067394113570429780627520047264103/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR056Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1484862054912971/1649267441664000) (500680641365657/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR056Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR056Q02F_ok n) ts asb
  exact factored_negative_12_samples 80 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip056Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR056Q02L shortNegativeR056Q02U (-1821309028325545181763278582559079/649037107316853453566312041152512) (-1067394113570429780627520047264103/649037107316853453566312041152512) shortNegativeR056Q02Samples (by decide +kernel)

theorem short_original_negative_056 {t a : ℝ} (tb : RealMem negative_056.t t) (ab : RealMem negative_056.a a) : RealMem negative_056.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((137/100):ℝ) ((69/50):ℝ) := by simpa [negative_056,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((137/100):ℝ)<((69/50):ℝ)) tB
  have aB : a∈Icc ((483500772181657/549755813888000):ℝ) ((500680641365657/549755813888000):ℝ) := by simpa [negative_056,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((483500772181657/549755813888000):ℝ)<((500680641365657/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR056Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_056,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR056Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_056,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR056Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_056,RealMem] using v

def shortNegativeR057Q00T := Grid.ofRats (69/50) (139/100)
def shortNegativeR057Q00P : PrimalThetaParameters := ⟨⟨⟨15343220318861679449988,15832893293058471500202,true⟩,⟨0,0,true⟩⟩, ⟨⟨1701451738664403953995255,1721232741131328603585728,true⟩,⟨0,0,true⟩⟩, ⟨(-395048996307496313057176),(-355486991373715733362669),true⟩, ⟨3311464227564350531305986,3440653918818865397880783,true⟩⟩
theorem shortNegativeR057Q00P_ok : shortNegativeR057Q00P.encloses (primalThetaParameters shortNegativeR057Q00T (Grid.ofRats (1477716730591483/1649267441664000) (1494896599775483/1649267441664000))) := by decide +kernel

def shortNegativeR057Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨405769005127271926280730,408968455205827300268397,true⟩,⟨3573629258509586497773989,3601806985904170255656748,true⟩,⟨⟨176991074655928352959379,196772077122853002598904,true⟩,⟨1184503451331603550015324,1204284453798528199668740,true⟩⟩⟩
  | 1 => ⟨⟨580168536200499237283,612958057892747521878,true⟩,⟨405769005127271926280730,408968455205827300268397,true⟩,⟨⟨(-572452994869617445606124),(-513109987468980935706655),true⟩,⟨(-1109898280898020803609121),(-1050555273497384293702252),true⟩⟩⟩
  | 2 => ⟨⟨10527976949658756,12031882388997877,true⟩,⟨580168536200499237283,612958057892747521878,true⟩,⟨⟨797346663641934165485394,896251675976282535619996,true⟩,⟨813352688150470033178056,912257700484818403312881,true⟩⟩⟩
  | 3 => ⟨⟨(-31935053058),37452842555,true⟩,⟨10527976949658756,12031882388997877,true⟩,⟨⟨(-1139108328606570535650523),(-1000641311338510305271929),true⟩,⟨(-632145141947490020658811),(-493678124679429790287192),true⟩⟩⟩
  | 4 => ⟨⟨(-34359738361),34359738379,true⟩,⟨(-31935053058),37452842555,true⟩,⟨⟨1101671052275792271395615,1279700074477564361966220,true⟩,⟨120197167581889888153532,298226189783661978710611,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738361),34359738379,true⟩,⟨⟨(-1306479114557913530789687),(-1088888087422429579947010),true⟩,⟨55690441000173795679789,273281468135657746508245,true⟩⟩⟩
theorem shortNegativeR057Q00F_ok : ∀ n : Fin 6, (shortNegativeR057Q00F n).encloses (FactoredFrequency.build shortNegativeR057Q00T (Grid.ofRats (1477716730591483/1649267441664000) (1494896599775483/1649267441664000)) n) := by decide +kernel
def shortNegativeR057Q00L : ℕ → ℚ
  | 0 => (-3019191/1000000)
  | 1 => (-2831813/1000000)
  | 2 => (-2584519/1000000)
  | 3 => (-2355919/1000000)
  | 4 => (-551639/250000)
  | 5 => (-442677/200000)
  | 6 => (-292679/125000)
  | 7 => (-2565719/1000000)
  | 8 => (-177211/62500)
  | 9 => (-1561909/500000)
  | 10 => (-3292927/1000000)
  | 11 => (-327821/100000)
  | _ => 0
def shortNegativeR057Q00U : ℕ → ℚ
  | 0 => (-75099/31250)
  | 1 => (-1063027/500000)
  | 2 => (-45061/25000)
  | 3 => (-758207/500000)
  | 4 => (-665391/500000)
  | 5 => (-310703/250000)
  | 6 => (-1297509/1000000)
  | 7 => (-1483589/1000000)
  | 8 => (-1762877/1000000)
  | 9 => (-508731/250000)
  | 10 => (-1132387/500000)
  | 11 => (-2383973/1000000)
  | _ => 0
private theorem shortNegativeR057Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR057Q00P shortNegativeR057Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR057Q00L (0:Fin 12)) (shortNegativeR057Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR057Q00P shortNegativeR057Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR057Q00L (1:Fin 12)) (shortNegativeR057Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR057Q00P shortNegativeR057Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR057Q00L (2:Fin 12)) (shortNegativeR057Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR057Q00P shortNegativeR057Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR057Q00L (3:Fin 12)) (shortNegativeR057Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR057Q00P shortNegativeR057Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR057Q00L (4:Fin 12)) (shortNegativeR057Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR057Q00P shortNegativeR057Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR057Q00L (5:Fin 12)) (shortNegativeR057Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR057Q00P shortNegativeR057Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR057Q00L (6:Fin 12)) (shortNegativeR057Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR057Q00P shortNegativeR057Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR057Q00L (7:Fin 12)) (shortNegativeR057Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR057Q00P shortNegativeR057Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR057Q00L (8:Fin 12)) (shortNegativeR057Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR057Q00P shortNegativeR057Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR057Q00L (9:Fin 12)) (shortNegativeR057Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR057Q00P shortNegativeR057Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR057Q00L (10:Fin 12)) (shortNegativeR057Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR057Q00P shortNegativeR057Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR057Q00L (11:Fin 12)) (shortNegativeR057Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR057Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR057Q00P shortNegativeR057Q00F (shortNegativeNodes12 k)).re (shortNegativeR057Q00L k) (shortNegativeR057Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR057Q00Point00
  · exact shortNegativeR057Q00Point01
  · exact shortNegativeR057Q00Point02
  · exact shortNegativeR057Q00Point03
  · exact shortNegativeR057Q00Point04
  · exact shortNegativeR057Q00Point05
  · exact shortNegativeR057Q00Point06
  · exact shortNegativeR057Q00Point07
  · exact shortNegativeR057Q00Point08
  · exact shortNegativeR057Q00Point09
  · exact shortNegativeR057Q00Point10
  · exact shortNegativeR057Q00Point11

theorem shortNegativeR057Q00Bound {t a : ℝ} (tl : ((69/50):ℝ)≤t) (tu : t≤((139/100):ℝ)) (al : ((1477716730591483/1649267441664000):ℝ)≤a) (au : a≤((1494896599775483/1649267441664000):ℝ)) : (((-3591970051913485948126215331887889/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2188191369992842068838368196410129/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR057Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1477716730591483/1649267441664000) (1494896599775483/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR057Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR057Q00F_ok n) ts asb
  exact factored_negative_12_samples 80 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip056Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR057Q00L shortNegativeR057Q00U (-3591970051913485948126215331887889/1298074214633706907132624082305024) (-2188191369992842068838368196410129/1298074214633706907132624082305024) shortNegativeR057Q00Samples (by decide +kernel)

def shortNegativeR057Q01T := Grid.ofRats (69/50) (139/100)
def shortNegativeR057Q01P : PrimalThetaParameters := ⟨⟨⟨15343220318861679449988,15832893293058471500202,true⟩,⟨0,0,true⟩⟩, ⟨⟨1721232741131259884103509,1741013743598184533694044,true⟩,⟨0,0,true⟩⟩, ⟨(-355486991373784452840541),(-315924986440003873146163),true⟩, ⟨3297244394921068725209568,3425546462034721262152461,true⟩⟩
theorem shortNegativeR057Q01P_ok : shortNegativeR057Q01P.encloses (primalThetaParameters shortNegativeR057Q01T (Grid.ofRats (1494896599775483/1649267441664000) (504025489653161/549755813888000))) := by decide +kernel

def shortNegativeR057Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨405769005127271926280730,408968455205827300268397,true⟩,⟨3573629258509586497773989,3601806985904170255656748,true⟩,⟨⟨157423704989347019607436,177204707456271669246961,true⟩,⟨1187401273450943558588808,1207182275917868208242518,true⟩⟩⟩
  | 1 => ⟨⟨580168536200499237283,612958057892747521878,true⟩,⟨405769005127271926280730,408968455205827300268397,true⟩,⟨⟨(-518794975089188982004651),(-459451967688552472105158),true⟩,⟨(-1135230125876186176251478),(-1075887118475549666343494),true⟩⟩⟩
  | 2 => ⟨⟨10527976949658756,12031882388997877,true⟩,⟨580168536200499237283,612958057892747521878,true⟩,⟨⟨724004955817991704472594,822909968152340074609259,true⟩,⟨879668148984980195803795,978573161319328565942610,true⟩⟩⟩
  | 3 => ⟨⟨(-31935053058),37452842555,true⟩,⟨10527976949658756,12031882388997877,true⟩,⟨⟨(-1067764810248652627974940),(-929297792980592397594986),true⟩,⟨(-750729566602607569671584),(-612262549334547339295993),true⟩⟩⟩
  | 4 => ⟨⟨(-34359738361),34359738379,true⟩,⟨(-31935053058),37452842555,true⟩,⟨⟨1058085950070779236110568,1236114972272551326688072,true⟩,⟨292642624703825131761355,470671646905597222328336,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738361),34359738379,true⟩,⟨⟨(-1316577500077120805953963),(-1098986472941636855113598),true⟩,⟨(-161372223186750759573707),56218803948733191251530,true⟩⟩⟩
theorem shortNegativeR057Q01F_ok : ∀ n : Fin 6, (shortNegativeR057Q01F n).encloses (FactoredFrequency.build shortNegativeR057Q01T (Grid.ofRats (1494896599775483/1649267441664000) (504025489653161/549755813888000)) n) := by decide +kernel
def shortNegativeR057Q01L : ℕ → ℚ
  | 0 => (-3018209/1000000)
  | 1 => (-569049/200000)
  | 2 => (-651/250)
  | 3 => (-2372127/1000000)
  | 4 => (-2212033/1000000)
  | 5 => (-2202329/1000000)
  | 6 => (-2312409/1000000)
  | 7 => (-2520813/1000000)
  | 8 => (-556137/200000)
  | 9 => (-766917/250000)
  | 10 => (-3247491/1000000)
  | 11 => (-1626451/500000)
  | _ => 0
def shortNegativeR057Q01U : ℕ → ℚ
  | 0 => (-2417171/1000000)
  | 1 => (-33693/15625)
  | 2 => (-28747/15625)
  | 3 => (-1551121/1000000)
  | 4 => (-1355361/1000000)
  | 5 => (-1253923/1000000)
  | 6 => (-80871/62500)
  | 7 => (-183367/125000)
  | 8 => (-347533/200000)
  | 9 => (-2009507/1000000)
  | 10 => (-2247453/1000000)
  | 11 => (-476317/200000)
  | _ => 0
private theorem shortNegativeR057Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR057Q01P shortNegativeR057Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR057Q01L (0:Fin 12)) (shortNegativeR057Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR057Q01P shortNegativeR057Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR057Q01L (1:Fin 12)) (shortNegativeR057Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR057Q01P shortNegativeR057Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR057Q01L (2:Fin 12)) (shortNegativeR057Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR057Q01P shortNegativeR057Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR057Q01L (3:Fin 12)) (shortNegativeR057Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR057Q01P shortNegativeR057Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR057Q01L (4:Fin 12)) (shortNegativeR057Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR057Q01P shortNegativeR057Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR057Q01L (5:Fin 12)) (shortNegativeR057Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR057Q01P shortNegativeR057Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR057Q01L (6:Fin 12)) (shortNegativeR057Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR057Q01P shortNegativeR057Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR057Q01L (7:Fin 12)) (shortNegativeR057Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR057Q01P shortNegativeR057Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR057Q01L (8:Fin 12)) (shortNegativeR057Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR057Q01P shortNegativeR057Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR057Q01L (9:Fin 12)) (shortNegativeR057Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR057Q01P shortNegativeR057Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR057Q01L (10:Fin 12)) (shortNegativeR057Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR057Q01P shortNegativeR057Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR057Q01L (11:Fin 12)) (shortNegativeR057Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR057Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR057Q01P shortNegativeR057Q01F (shortNegativeNodes12 k)).re (shortNegativeR057Q01L k) (shortNegativeR057Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR057Q01Point00
  · exact shortNegativeR057Q01Point01
  · exact shortNegativeR057Q01Point02
  · exact shortNegativeR057Q01Point03
  · exact shortNegativeR057Q01Point04
  · exact shortNegativeR057Q01Point05
  · exact shortNegativeR057Q01Point06
  · exact shortNegativeR057Q01Point07
  · exact shortNegativeR057Q01Point08
  · exact shortNegativeR057Q01Point09
  · exact shortNegativeR057Q01Point10
  · exact shortNegativeR057Q01Point11

theorem shortNegativeR057Q01Bound {t a : ℝ} (tl : ((69/50):ℝ)≤t) (tu : t≤((139/100):ℝ)) (al : ((1494896599775483/1649267441664000):ℝ)≤a) (au : a≤((504025489653161/549755813888000):ℝ)) : (((-3591970051913485948126215331887889/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2188191369992842068838368196410129/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR057Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1494896599775483/1649267441664000) (504025489653161/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR057Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR057Q01F_ok n) ts asb
  exact factored_negative_12_samples 80 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip056Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR057Q01L shortNegativeR057Q01U (-3591970051913485948126215331887889/1298074214633706907132624082305024) (-2188191369992842068838368196410129/1298074214633706907132624082305024) shortNegativeR057Q01Samples (by decide +kernel)

def shortNegativeR057Q02T := Grid.ofRats (69/50) (139/100)
def shortNegativeR057Q02P : PrimalThetaParameters := ⟨⟨⟨15343220318861679449988,15832893293058471500202,true⟩,⟨0,0,true⟩⟩, ⟨⟨1741013743598115814211762,1760794746065040463802362,true⟩,⟨0,0,true⟩⟩, ⟨(-315924986440072592623909),(-276362981506292012929654),true⟩, ⟨3284691779218539267840195,3412195684944800240565005,true⟩⟩
theorem shortNegativeR057Q02P_ok : shortNegativeR057Q02P.encloses (primalThetaParameters shortNegativeR057Q02T (Grid.ofRats (504025489653161/549755813888000) (1529256338143483/1649267441664000))) := by decide +kernel

def shortNegativeR057Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨405769005127271926280730,408968455205827300268397,true⟩,⟨3573629258509586497773989,3601806985904170255656748,true⟩,⟨⟨137811541263955693821408,157592543730880343460987,true⟩,⟨1189978551610636092290196,1209759554077560741944261,true⟩⟩⟩
  | 1 => ⟨⟨580168536200499237283,612958057892747521878,true⟩,⟨405769005127271926280730,408968455205827300268397,true⟩,⟨⟨(-463958614024028512516692),(-404615606623392002617420),true⟩,⟨(-1157898583298031347191709),(-1098555575897394837282879),true⟩⟩⟩
  | 2 => ⟨⟨10527976949658756,12031882388997877,true⟩,⟨580168536200499237283,612958057892747521878,true⟩,⟨⟨645489187764310971402750,744394200098659341540865,true⟩,⟨939768237330727260472818,1038673249665075630614987,true⟩⟩⟩
  | 3 => ⟨⟨(-31935053058),37452842555,true⟩,⟨10527976949658756,12031882388997877,true⟩,⟨⟨(-983336096402373068352357),(-844869079134312837970099),true⟩,⟨(-860383365719349815395185),(-721916348451289585014613),true⟩⟩⟩
  | 4 => ⟨⟨(-34359738361),34359738379,true⟩,⟨(-31935053058),37452842555,true⟩,⟨⟨989669587043992862721476,1167698609245764953304584,true⟩,⟨456826357413255323017994,634855379615027413593768,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738361),34359738379,true⟩,⟨⟨(-1287654879493417741460005),(-1070063852357933790610293),true⟩,⟨(-376736239662556835425455),(-159145212527072884588279),true⟩⟩⟩
theorem shortNegativeR057Q02F_ok : ∀ n : Fin 6, (shortNegativeR057Q02F n).encloses (FactoredFrequency.build shortNegativeR057Q02T (Grid.ofRats (504025489653161/549755813888000) (1529256338143483/1649267441664000)) n) := by decide +kernel
def shortNegativeR057Q02L : ℕ → ℚ
  | 0 => (-120669/40000)
  | 1 => (-1429213/500000)
  | 2 => (-327967/125000)
  | 3 => (-298639/125000)
  | 4 => (-2218681/1000000)
  | 5 => (-274083/125000)
  | 6 => (-1142421/500000)
  | 7 => (-495451/200000)
  | 8 => (-2726999/1000000)
  | 9 => (-3011899/1000000)
  | 10 => (-80043/25000)
  | 11 => (-3226893/1000000)
  | _ => 0
def shortNegativeR057Q02U : ℕ → ℚ
  | 0 => (-2430237/1000000)
  | 1 => (-87447/40000)
  | 2 => (-375487/200000)
  | 3 => (-793403/500000)
  | 4 => (-690729/500000)
  | 5 => (-1266897/1000000)
  | 6 => (-1292363/1000000)
  | 7 => (-1452187/1000000)
  | 8 => (-1713987/1000000)
  | 9 => (-496257/250000)
  | 10 => (-1115169/500000)
  | 11 => (-475757/200000)
  | _ => 0
private theorem shortNegativeR057Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR057Q02P shortNegativeR057Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR057Q02L (0:Fin 12)) (shortNegativeR057Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR057Q02P shortNegativeR057Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR057Q02L (1:Fin 12)) (shortNegativeR057Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR057Q02P shortNegativeR057Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR057Q02L (2:Fin 12)) (shortNegativeR057Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR057Q02P shortNegativeR057Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR057Q02L (3:Fin 12)) (shortNegativeR057Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR057Q02P shortNegativeR057Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR057Q02L (4:Fin 12)) (shortNegativeR057Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR057Q02P shortNegativeR057Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR057Q02L (5:Fin 12)) (shortNegativeR057Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR057Q02P shortNegativeR057Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR057Q02L (6:Fin 12)) (shortNegativeR057Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR057Q02P shortNegativeR057Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR057Q02L (7:Fin 12)) (shortNegativeR057Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR057Q02P shortNegativeR057Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR057Q02L (8:Fin 12)) (shortNegativeR057Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR057Q02P shortNegativeR057Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR057Q02L (9:Fin 12)) (shortNegativeR057Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR057Q02P shortNegativeR057Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR057Q02L (10:Fin 12)) (shortNegativeR057Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR057Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR057Q02P shortNegativeR057Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR057Q02L (11:Fin 12)) (shortNegativeR057Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR057Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR057Q02P shortNegativeR057Q02F (shortNegativeNodes12 k)).re (shortNegativeR057Q02L k) (shortNegativeR057Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR057Q02Point00
  · exact shortNegativeR057Q02Point01
  · exact shortNegativeR057Q02Point02
  · exact shortNegativeR057Q02Point03
  · exact shortNegativeR057Q02Point04
  · exact shortNegativeR057Q02Point05
  · exact shortNegativeR057Q02Point06
  · exact shortNegativeR057Q02Point07
  · exact shortNegativeR057Q02Point08
  · exact shortNegativeR057Q02Point09
  · exact shortNegativeR057Q02Point10
  · exact shortNegativeR057Q02Point11

theorem shortNegativeR057Q02Bound {t a : ℝ} (tl : ((69/50):ℝ)≤t) (tu : t≤((139/100):ℝ)) (al : ((504025489653161/549755813888000):ℝ)≤a) (au : a≤((1529256338143483/1649267441664000):ℝ)) : (((-3591970051913485948126215331887889/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2188191369992842068838368196410129/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR057Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (504025489653161/549755813888000) (1529256338143483/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR057Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR057Q02F_ok n) ts asb
  exact factored_negative_12_samples 80 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip056Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR057Q02L shortNegativeR057Q02U (-3591970051913485948126215331887889/1298074214633706907132624082305024) (-2188191369992842068838368196410129/1298074214633706907132624082305024) shortNegativeR057Q02Samples (by decide +kernel)

theorem short_original_negative_057 {t a : ℝ} (tb : RealMem negative_057.t t) (ab : RealMem negative_057.a a) : RealMem negative_057.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((69/50):ℝ) ((139/100):ℝ) := by simpa [negative_057,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((69/50):ℝ)<((139/100):ℝ)) tB
  have aB : a∈Icc ((1477716730591483/1649267441664000):ℝ) ((1529256338143483/1649267441664000):ℝ) := by simpa [negative_057,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((1477716730591483/1649267441664000):ℝ)<((1529256338143483/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR057Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_057,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR057Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_057,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR057Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_057,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_056
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_057
