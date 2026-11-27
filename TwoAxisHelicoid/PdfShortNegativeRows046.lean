import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip040

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR046Q00T := Grid.ofRats (127/100) (32/25)
def shortNegativeR046Q00P : PrimalThetaParameters := ⟨⟨⟨21676937238918972523817,22368748352115837471314,true⟩,⟨0,0,true⟩⟩, ⟨⟨1490757747002031717190796,1500648248235528401726438,true⟩,⟨0,0,true⟩⟩, ⟨(-816436979632240786667436),(-796655977165316137079843),true⟩, ⟨3751526591187412819353960,3838436153208122816753098,true⟩⟩
theorem shortNegativeR046Q00P_ok : shortNegativeR046Q00P.encloses (primalThetaParameters shortNegativeR046Q00T (Grid.ofRats (51789130750967/65970697666560) (52132728134647/65970697666560))) := by decide +kernel

def shortNegativeR046Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨442383805166621112640338,445871959466985924863858,true⟩,⟨3277850527039513073107606,3303696067220044571293690,true⟩,⟨⟨390890419399910606446893,400780920633407291031196,true⟩,⟨1137340072616184387451966,1147230573849681072046549,true⟩⟩⟩
  | 1 => ⟨⟨1062176333216592378408,1122207602945605451294,true⟩,⟨442383805166621112640338,445871959466985924863858,true⟩,⟨⟨(-1032594448848685852299161),(-1002922945148333237567325),true⟩,⟨(-667268792103962777430176),(-637597288403610162703364),true⟩⟩⟩
  | 2 => ⟨⟨45729027118766116,52261102671749708,true⟩,⟨1062176333216592378408,1122207602945605451294,true⟩,⟨⟨1178504602530886669458517,1227957108698095214297601,true⟩,⟨(-141931822183894767332745),(-92479316016686222508614),true⟩⟩⟩
  | 3 => ⟨⟨941197810,79392169180,true⟩,⟨45729027118766116,52261102671749708,true⟩,⟨⟨(-907331889174638444610583),(-838098380540573969613688),true⟩,⟨801965537344327953852726,871199045978392428849123,true⟩⟩⟩
  | 4 => ⟨⟨(-34359737880),34359739086,true⟩,⟨941197810,79392169180,true⟩,⟨⟨123441091408364198432589,212455602509284603534947,true⟩,⟨(-1241710241716424147438870),(-1152695730615503742322346),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359737880),34359739086,true⟩,⟨⟨554442865923677894099166,663238379491454229322390,true⟩,⟨990023007789454711242728,1098818521357231046471947,true⟩⟩⟩
theorem shortNegativeR046Q00F_ok : ∀ n : Fin 6, (shortNegativeR046Q00F n).encloses (FactoredFrequency.build shortNegativeR046Q00T (Grid.ofRats (51789130750967/65970697666560) (52132728134647/65970697666560)) n) := by decide +kernel
def shortNegativeR046Q00L : ℕ → ℚ
  | 0 => (-2806491/1000000)
  | 1 => (-2306093/1000000)
  | 2 => (-946617/500000)
  | 3 => (-415459/250000)
  | 4 => (-410759/250000)
  | 5 => (-937959/500000)
  | 6 => (-2284899/1000000)
  | 7 => (-280477/100000)
  | 8 => (-1655619/500000)
  | 9 => (-3690467/1000000)
  | 10 => (-3745353/1000000)
  | 11 => (-53522/15625)
  | _ => 0
def shortNegativeR046Q00U : ℕ → ℚ
  | 0 => (-2192333/1000000)
  | 1 => (-1631369/1000000)
  | 2 => (-58949/50000)
  | 3 => (-456791/500000)
  | 4 => (-865971/1000000)
  | 5 => (-499451/500000)
  | 6 => (-662753/500000)
  | 7 => (-359209/200000)
  | 8 => (-2277647/1000000)
  | 9 => (-1306741/500000)
  | 10 => (-2716211/1000000)
  | 11 => (-1272009/500000)
  | _ => 0
private theorem shortNegativeR046Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR046Q00P shortNegativeR046Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR046Q00L (0:Fin 12)) (shortNegativeR046Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR046Q00P shortNegativeR046Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR046Q00L (1:Fin 12)) (shortNegativeR046Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR046Q00P shortNegativeR046Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR046Q00L (2:Fin 12)) (shortNegativeR046Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR046Q00P shortNegativeR046Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR046Q00L (3:Fin 12)) (shortNegativeR046Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR046Q00P shortNegativeR046Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR046Q00L (4:Fin 12)) (shortNegativeR046Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR046Q00P shortNegativeR046Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR046Q00L (5:Fin 12)) (shortNegativeR046Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR046Q00P shortNegativeR046Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR046Q00L (6:Fin 12)) (shortNegativeR046Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR046Q00P shortNegativeR046Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR046Q00L (7:Fin 12)) (shortNegativeR046Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR046Q00P shortNegativeR046Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR046Q00L (8:Fin 12)) (shortNegativeR046Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR046Q00P shortNegativeR046Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR046Q00L (9:Fin 12)) (shortNegativeR046Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR046Q00P shortNegativeR046Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR046Q00L (10:Fin 12)) (shortNegativeR046Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR046Q00P shortNegativeR046Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR046Q00L (11:Fin 12)) (shortNegativeR046Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR046Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR046Q00P shortNegativeR046Q00F (shortNegativeNodes12 k)).re (shortNegativeR046Q00L k) (shortNegativeR046Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR046Q00Point00
  · exact shortNegativeR046Q00Point01
  · exact shortNegativeR046Q00Point02
  · exact shortNegativeR046Q00Point03
  · exact shortNegativeR046Q00Point04
  · exact shortNegativeR046Q00Point05
  · exact shortNegativeR046Q00Point06
  · exact shortNegativeR046Q00Point07
  · exact shortNegativeR046Q00Point08
  · exact shortNegativeR046Q00Point09
  · exact shortNegativeR046Q00Point10
  · exact shortNegativeR046Q00Point11

theorem shortNegativeR046Q00Bound {t a : ℝ} (tl : ((127/100):ℝ)≤t) (tu : t≤((32/25):ℝ)) (al : ((51789130750967/65970697666560):ℝ)≤a) (au : a≤((52132728134647/65970697666560):ℝ)) : (((-1742127138103950150461796938672017/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1065063012687087985198826688604049/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR046Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (51789130750967/65970697666560) (52132728134647/65970697666560)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR046Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR046Q00F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR046Q00L shortNegativeR046Q00U (-1742127138103950150461796938672017/649037107316853453566312041152512) (-1065063012687087985198826688604049/649037107316853453566312041152512) shortNegativeR046Q00Samples (by decide +kernel)

def shortNegativeR046Q01T := Grid.ofRats (127/100) (32/25)
def shortNegativeR046Q01P : PrimalThetaParameters := ⟨⟨⟨21676937238918972523817,22368748352115837471314,true⟩,⟨0,0,true⟩⟩, ⟨⟨1500648248235459682244922,1510538749468956366780598,true⟩,⟨0,0,true⟩⟩, ⟨(-796655977165384856559120),(-776874974698460206971587),true⟩, ⟨3733408892863887931598572,3819777180319865306294955,true⟩⟩
theorem shortNegativeR046Q01P_ok : shortNegativeR046Q01P.encloses (primalThetaParameters shortNegativeR046Q01T (Grid.ofRats (52132728134647/65970697666560) (17492108506109/21990232555520))) := by decide +kernel

def shortNegativeR046Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨442383805166621112640338,445871959466985924863858,true⟩,⟨3277850527039513073107606,3303696067220044571293690,true⟩,⟨⟨381531976633785168405552,391422477867281852989936,true⟩,⟨1140540231677829844283505,1150430732911326528878333,true⟩⟩⟩
  | 1 => ⟨⟨1062176333216592378408,1122207602945605451294,true⟩,⟨442383805166621112640338,445871959466985924863858,true⟩,⟨⟨(-1016276410620607741616106),(-986604906920255126883540),true⟩,⟨(-692049340234481564795778),(-662377836534128950067665),true⟩⟩⟩
  | 2 => ⟨⟨45729027118766116,52261102671749708,true⟩,⟨1062176333216592378408,1122207602945605451294,true⟩,⟨⟨1182291143818161552089174,1231743649985370096926834,true⟩,⟨(-92627953411269313818747),(-43175447244060768996770),true⟩⟩⟩
  | 3 => ⟨⟨941197810,79392169180,true⟩,⟨45729027118766116,52261102671749708,true⟩,⟨⟨(-953784886868081839882752),(-884551378234017364886198),true⟩,⟨750642172046443764839498,819875680680508239834208,true⟩⟩⟩
  | 4 => ⟨⟨(-34359737880),34359739086,true⟩,⟨941197810,79392169180,true⟩,⟨⟨211057743304054710661083,300072254404975115763872,true⟩,⟨(-1226111321509694581707228),(-1137096810408774176591696),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359737880),34359739086,true⟩,⟨⟨458114775927457508221487,566910289495233843447316,true⟩,⟨1040514358933489738684689,1149309872501266073918535,true⟩⟩⟩
theorem shortNegativeR046Q01F_ok : ∀ n : Fin 6, (shortNegativeR046Q01F n).encloses (FactoredFrequency.build shortNegativeR046Q01T (Grid.ofRats (52132728134647/65970697666560) (17492108506109/21990232555520)) n) := by decide +kernel
def shortNegativeR046Q01L : ℕ → ℚ
  | 0 => (-176219/62500)
  | 1 => (-2326111/1000000)
  | 2 => (-1912293/1000000)
  | 3 => (-167393/100000)
  | 4 => (-1644287/1000000)
  | 5 => (-93161/50000)
  | 6 => (-2261593/1000000)
  | 7 => (-277149/100000)
  | 8 => (-65477/20000)
  | 9 => (-1828751/500000)
  | 10 => (-3725041/1000000)
  | 11 => (-3423393/1000000)
  | _ => 0
def shortNegativeR046Q01U : ℕ → ℚ
  | 0 => (-2212489/1000000)
  | 1 => (-1657881/1000000)
  | 2 => (-1203593/1000000)
  | 3 => (-466339/500000)
  | 4 => (-10931/12500)
  | 5 => (-99597/100000)
  | 6 => (-52459/40000)
  | 7 => (-886619/500000)
  | 8 => (-1124949/500000)
  | 9 => (-40479/15625)
  | 10 => (-2706533/1000000)
  | 11 => (-1275117/500000)
  | _ => 0
private theorem shortNegativeR046Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR046Q01P shortNegativeR046Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR046Q01L (0:Fin 12)) (shortNegativeR046Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR046Q01P shortNegativeR046Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR046Q01L (1:Fin 12)) (shortNegativeR046Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR046Q01P shortNegativeR046Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR046Q01L (2:Fin 12)) (shortNegativeR046Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR046Q01P shortNegativeR046Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR046Q01L (3:Fin 12)) (shortNegativeR046Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR046Q01P shortNegativeR046Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR046Q01L (4:Fin 12)) (shortNegativeR046Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR046Q01P shortNegativeR046Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR046Q01L (5:Fin 12)) (shortNegativeR046Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR046Q01P shortNegativeR046Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR046Q01L (6:Fin 12)) (shortNegativeR046Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR046Q01P shortNegativeR046Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR046Q01L (7:Fin 12)) (shortNegativeR046Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR046Q01P shortNegativeR046Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR046Q01L (8:Fin 12)) (shortNegativeR046Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR046Q01P shortNegativeR046Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR046Q01L (9:Fin 12)) (shortNegativeR046Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR046Q01P shortNegativeR046Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR046Q01L (10:Fin 12)) (shortNegativeR046Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR046Q01P shortNegativeR046Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR046Q01L (11:Fin 12)) (shortNegativeR046Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR046Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR046Q01P shortNegativeR046Q01F (shortNegativeNodes12 k)).re (shortNegativeR046Q01L k) (shortNegativeR046Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR046Q01Point00
  · exact shortNegativeR046Q01Point01
  · exact shortNegativeR046Q01Point02
  · exact shortNegativeR046Q01Point03
  · exact shortNegativeR046Q01Point04
  · exact shortNegativeR046Q01Point05
  · exact shortNegativeR046Q01Point06
  · exact shortNegativeR046Q01Point07
  · exact shortNegativeR046Q01Point08
  · exact shortNegativeR046Q01Point09
  · exact shortNegativeR046Q01Point10
  · exact shortNegativeR046Q01Point11

theorem shortNegativeR046Q01Bound {t a : ℝ} (tl : ((127/100):ℝ)≤t) (tu : t≤((32/25):ℝ)) (al : ((52132728134647/65970697666560):ℝ)≤a) (au : a≤((17492108506109/21990232555520):ℝ)) : (((-1742127138103950150461796938672017/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1065063012687087985198826688604049/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR046Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (52132728134647/65970697666560) (17492108506109/21990232555520)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR046Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR046Q01F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR046Q01L shortNegativeR046Q01U (-1742127138103950150461796938672017/649037107316853453566312041152512) (-1065063012687087985198826688604049/649037107316853453566312041152512) shortNegativeR046Q01Samples (by decide +kernel)

def shortNegativeR046Q02T := Grid.ofRats (127/100) (32/25)
def shortNegativeR046Q02P : PrimalThetaParameters := ⟨⟨⟨21676937238918972523817,22368748352115837471314,true⟩,⟨0,0,true⟩⟩, ⟨⟨1510538749468887647299050,1520429250702384331834756,true⟩,⟨0,0,true⟩⟩, ⟨(-776874974698528926450801),(-757093972231604276863334),true⟩, ⟨3715874079582858767555448,3801718571969897072370368,true⟩⟩
theorem shortNegativeR046Q02P_ok : shortNegativeR046Q02P.encloses (primalThetaParameters shortNegativeR046Q02T (Grid.ofRats (17492108506109/21990232555520) (52819922902007/65970697666560))) := by decide +kernel

def shortNegativeR046Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨442383805166621112640338,445871959466985924863858,true⟩,⟨3277850527039513073107606,3303696067220044571293690,true⟩,⟨⟨372147666110040212635811,382038167343536897220472,true⟩,⟨1143663720915942686721471,1153554222149439371316796,true⟩⟩⟩
  | 1 => ⟨⟨1062176333216592378408,1122207602945605451294,true⟩,⟨442383805166621112640338,445871959466985924863858,true⟩,⟨⟨(-999355141985964464434450),(-969683638285611849701720),true⟩,⟨(-716421960222004744815206),(-686750456521652130086360),true⟩⟩⟩
  | 2 => ⟨⟨45729027118766116,52261102671749708,true⟩,⟨1062176333216592378408,1122207602945605451294,true⟩,⟨⟨1184058248264369609221204,1233510754431578154057887,true⟩,⟨(-43210479652034105571065),6242026515174439249331,true⟩⟩⟩
  | 3 => ⟨⟨941197810,79392169180,true⟩,⟨45729027118766116,52261102671749708,true⟩,⟨⟨(-997224117816961971265286),(-927990609182897496269098),true⟩,⟨696744101257435231240958,765977609891499706233963,true⟩⟩⟩
  | 4 => ⟨⟨(-34359737880),34359739086,true⟩,⟨941197810,79392169180,true⟩,⟨⟨297289466328131635997012,386303977429052041100213,true⟩,⟨(-1204109186492260358287905),(-1115094675391339953173450),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359737880),34359739086,true⟩,⟨⟨357638730987044613050456,466434244554820948278346,true⟩,⟨1082144178243718668680385,1190939691811495003918250,true⟩⟩⟩
theorem shortNegativeR046Q02F_ok : ∀ n : Fin 6, (shortNegativeR046Q02F n).encloses (FactoredFrequency.build shortNegativeR046Q02T (Grid.ofRats (17492108506109/21990232555520) (52819922902007/65970697666560)) n) := by decide +kernel
def shortNegativeR046Q02L : ℕ → ℚ
  | 0 => (-1416089/500000)
  | 1 => (-2345973/1000000)
  | 2 => (-1931419/1000000)
  | 3 => (-1686277/1000000)
  | 4 => (-823129/500000)
  | 5 => (-926407/500000)
  | 6 => (-223881/100000)
  | 7 => (-27387/10000)
  | 8 => (-647357/200000)
  | 9 => (-3624551/1000000)
  | 10 => (-3704433/1000000)
  | 11 => (-1710463/500000)
  | _ => 0
def shortNegativeR046Q02U : ℕ → ℚ
  | 0 => (-89291/40000)
  | 1 => (-1684263/1000000)
  | 2 => (-245669/200000)
  | 3 => (-238013/250000)
  | 4 => (-176683/200000)
  | 5 => (-198713/200000)
  | 6 => (-64901/50000)
  | 7 => (-437291/250000)
  | 8 => (-138911/62500)
  | 9 => (-256799/100000)
  | 10 => (-2696707/1000000)
  | 11 => (-319513/125000)
  | _ => 0
private theorem shortNegativeR046Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR046Q02P shortNegativeR046Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR046Q02L (0:Fin 12)) (shortNegativeR046Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR046Q02P shortNegativeR046Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR046Q02L (1:Fin 12)) (shortNegativeR046Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR046Q02P shortNegativeR046Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR046Q02L (2:Fin 12)) (shortNegativeR046Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR046Q02P shortNegativeR046Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR046Q02L (3:Fin 12)) (shortNegativeR046Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR046Q02P shortNegativeR046Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR046Q02L (4:Fin 12)) (shortNegativeR046Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR046Q02P shortNegativeR046Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR046Q02L (5:Fin 12)) (shortNegativeR046Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR046Q02P shortNegativeR046Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR046Q02L (6:Fin 12)) (shortNegativeR046Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR046Q02P shortNegativeR046Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR046Q02L (7:Fin 12)) (shortNegativeR046Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR046Q02P shortNegativeR046Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR046Q02L (8:Fin 12)) (shortNegativeR046Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR046Q02P shortNegativeR046Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR046Q02L (9:Fin 12)) (shortNegativeR046Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR046Q02P shortNegativeR046Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR046Q02L (10:Fin 12)) (shortNegativeR046Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR046Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR046Q02P shortNegativeR046Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR046Q02L (11:Fin 12)) (shortNegativeR046Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR046Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR046Q02P shortNegativeR046Q02F (shortNegativeNodes12 k)).re (shortNegativeR046Q02L k) (shortNegativeR046Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR046Q02Point00
  · exact shortNegativeR046Q02Point01
  · exact shortNegativeR046Q02Point02
  · exact shortNegativeR046Q02Point03
  · exact shortNegativeR046Q02Point04
  · exact shortNegativeR046Q02Point05
  · exact shortNegativeR046Q02Point06
  · exact shortNegativeR046Q02Point07
  · exact shortNegativeR046Q02Point08
  · exact shortNegativeR046Q02Point09
  · exact shortNegativeR046Q02Point10
  · exact shortNegativeR046Q02Point11

theorem shortNegativeR046Q02Bound {t a : ℝ} (tl : ((127/100):ℝ)≤t) (tu : t≤((32/25):ℝ)) (al : ((17492108506109/21990232555520):ℝ)≤a) (au : a≤((52819922902007/65970697666560):ℝ)) : (((-1742127138103950150461796938672017/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1065063012687087985198826688604049/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR046Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (17492108506109/21990232555520) (52819922902007/65970697666560)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR046Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR046Q02F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR046Q02L shortNegativeR046Q02U (-1742127138103950150461796938672017/649037107316853453566312041152512) (-1065063012687087985198826688604049/649037107316853453566312041152512) shortNegativeR046Q02Samples (by decide +kernel)

theorem short_original_negative_046 {t a : ℝ} (tb : RealMem negative_046.t t) (ab : RealMem negative_046.a a) : RealMem negative_046.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((127/100):ℝ) ((32/25):ℝ) := by simpa [negative_046,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((127/100):ℝ)<((32/25):ℝ)) tB
  have aB : a∈Icc ((51789130750967/65970697666560):ℝ) ((52819922902007/65970697666560):ℝ) := by simpa [negative_046,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((51789130750967/65970697666560):ℝ)<((52819922902007/65970697666560):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR046Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_046,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR046Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_046,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR046Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_046,RealMem] using v

def shortNegativeR047Q00T := Grid.ofRats (32/25) (129/100)
def shortNegativeR047Q00P : PrimalThetaParameters := ⟨⟨⟨21006522164975248756275,21676937238987692000930,true⟩,⟨0,0,true⟩⟩, ⟨⟨1505645343069973130924747,1515535844303469815460438,true⟩,⟨0,0,true⟩⟩, ⟨(-786661787496357959199437),(-766880785029433309611940),true⟩, ⟨3710339480089466021858868,3795470398067444504104890,true⟩⟩
theorem shortNegativeR047Q00P_ok : shortNegativeR047Q00P.encloses (primalThetaParameters shortNegativeR047Q00T (Grid.ofRats (17435442633933/21990232555520) (52649925285479/65970697666560))) := by decide +kernel

def shortNegativeR047Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨438922939463789682788788,442383805166689832133599,true⟩,⟨3303696067219975851694355,3329745397030848799738575,true⟩,⟨⟨376793824278753411329551,386684325512250095914271,true⟩,⟨1142127944967922889460325,1152018446201419574055615,true⟩⟩⟩
  | 1 => ⟨⟨1005356370740172766186,1062176333285311855205,true⟩,⟨438922939463789682788788,442383805166689832133599,true⟩,⟨⟨(-1007801842830525429433471),(-978130339130172814701095),true⟩,⟨(-704415319046093118118293),(-674743815345740503390080),true⟩⟩⟩
  | 2 => ⟨⟨40013442808776138,45729095838242853,true⟩,⟨1005356370740172766186,1062176333285311855205,true⟩,⟨⟨1183436625415358070511044,1232889131582566615347852,true⟩,⟨(-67669196019603354462683),(-18216689852394809641914),true⟩⟩⟩
  | 3 => ⟨⟨(-6687323785),69660674547,true⟩,⟨40013442808776138,45729095838242853,true⟩,⟨⟨(-976118051490618372379405),(-906884542856553897382749),true⟩,⟨723721524257482004932915,792955032891546479927045,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738036),34359738857,true⟩,⟨(-6687323785),69660674547,true⟩,⟨⟨254828223746292052254761,343842734847212457356775,true⟩,⟨(-1215788565981513960367646),(-1126774054880593555253633),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738036),34359738857,true⟩,⟨⟨407818227852683092456489,516613741420459427682860,true⟩,⟨1062677899059236827962996,1171473412627013163198381,true⟩⟩⟩
theorem shortNegativeR047Q00F_ok : ∀ n : Fin 6, (shortNegativeR047Q00F n).encloses (FactoredFrequency.build shortNegativeR047Q00T (Grid.ofRats (17435442633933/21990232555520) (52649925285479/65970697666560)) n) := by decide +kernel
def shortNegativeR047Q00L : ℕ → ℚ
  | 0 => (-88529/31250)
  | 1 => (-235973/100000)
  | 2 => (-979041/500000)
  | 3 => (-430677/250000)
  | 4 => (-337729/200000)
  | 5 => (-1896549/1000000)
  | 6 => (-1139449/500000)
  | 7 => (-2769433/1000000)
  | 8 => (-1626631/500000)
  | 9 => (-906237/250000)
  | 10 => (-1847297/500000)
  | 11 => (-852737/250000)
  | _ => 0
def shortNegativeR047Q00U : ℕ → ℚ
  | 0 => (-2232231/1000000)
  | 1 => (-424193/250000)
  | 2 => (-1252831/1000000)
  | 3 => (-493037/500000)
  | 4 => (-230737/250000)
  | 5 => (-258787/250000)
  | 6 => (-334301/250000)
  | 7 => (-22239/12500)
  | 8 => (-1120213/500000)
  | 9 => (-1286471/500000)
  | 10 => (-673007/250000)
  | 11 => (-510001/200000)
  | _ => 0
private theorem shortNegativeR047Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR047Q00P shortNegativeR047Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR047Q00L (0:Fin 12)) (shortNegativeR047Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR047Q00P shortNegativeR047Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR047Q00L (1:Fin 12)) (shortNegativeR047Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR047Q00P shortNegativeR047Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR047Q00L (2:Fin 12)) (shortNegativeR047Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR047Q00P shortNegativeR047Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR047Q00L (3:Fin 12)) (shortNegativeR047Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR047Q00P shortNegativeR047Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR047Q00L (4:Fin 12)) (shortNegativeR047Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR047Q00P shortNegativeR047Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR047Q00L (5:Fin 12)) (shortNegativeR047Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR047Q00P shortNegativeR047Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR047Q00L (6:Fin 12)) (shortNegativeR047Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR047Q00P shortNegativeR047Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR047Q00L (7:Fin 12)) (shortNegativeR047Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR047Q00P shortNegativeR047Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR047Q00L (8:Fin 12)) (shortNegativeR047Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR047Q00P shortNegativeR047Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR047Q00L (9:Fin 12)) (shortNegativeR047Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR047Q00P shortNegativeR047Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR047Q00L (10:Fin 12)) (shortNegativeR047Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR047Q00P shortNegativeR047Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR047Q00L (11:Fin 12)) (shortNegativeR047Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR047Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR047Q00P shortNegativeR047Q00F (shortNegativeNodes12 k)).re (shortNegativeR047Q00L k) (shortNegativeR047Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR047Q00Point00
  · exact shortNegativeR047Q00Point01
  · exact shortNegativeR047Q00Point02
  · exact shortNegativeR047Q00Point03
  · exact shortNegativeR047Q00Point04
  · exact shortNegativeR047Q00Point05
  · exact shortNegativeR047Q00Point06
  · exact shortNegativeR047Q00Point07
  · exact shortNegativeR047Q00Point08
  · exact shortNegativeR047Q00Point09
  · exact shortNegativeR047Q00Point10
  · exact shortNegativeR047Q00Point11

theorem shortNegativeR047Q00Bound {t a : ℝ} (tl : ((32/25):ℝ)≤t) (tu : t≤((129/100):ℝ)) (al : ((17435442633933/21990232555520):ℝ)≤a) (au : a≤((52649925285479/65970697666560):ℝ)) : (((-1735739144536741584078414378591807/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1086662614148910497454715169039935/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR047Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (17435442633933/21990232555520) (52649925285479/65970697666560)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR047Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR047Q00F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR047Q00L shortNegativeR047Q00U (-1735739144536741584078414378591807/649037107316853453566312041152512) (-1086662614148910497454715169039935/649037107316853453566312041152512) shortNegativeR047Q00Samples (by decide +kernel)

def shortNegativeR047Q01T := Grid.ofRats (32/25) (129/100)
def shortNegativeR047Q01P : PrimalThetaParameters := ⟨⟨⟨21006522164975248756275,21676937238987692000930,true⟩,⟨0,0,true⟩⟩, ⟨⟨1515535844303401095978874,1525426345536897780514597,true⟩,⟨0,0,true⟩⟩, ⟨(-766880785029502029091121),(-747099782562577379503684),true⟩, ⟨3693078622521867224044712,3777695570385350066091447,true⟩⟩
theorem shortNegativeR047Q01P_ok : shortNegativeR047Q01P.encloses (primalThetaParameters shortNegativeR047Q01T (Grid.ofRats (52649925285479/65970697666560) (52993522669159/65970697666560))) := by decide +kernel

def shortNegativeR047Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨438922939463789682788788,442383805166689832133599,true⟩,⟨3303696067219975851694355,3329745397030848799738575,true⟩,⟨⟨367396683018329257676509,377287184251825942261149,true⟩,⟨1145212617585610383993575,1155103118819107068588943,true⟩⟩⟩
  | 1 => ⟨⟨1005356370740172766186,1062176333285311855205,true⟩,⟨438922939463789682788788,442383805166689832133599,true⟩,⟨⟨(-990579650265333024512867),(-960908146564980409780128),true⟩,⟨(-728576238327225784185869),(-698904734626873169456730),true⟩⟩⟩
  | 2 => ⟨⟨40013442808776138,45729095838242853,true⟩,⟨1005356370740172766186,1062176333285311855205,true⟩,⟨⟨1184182089547308450438008,1233634595714516995274298,true⟩,⟨(-18225757080786769193129),31226749086421775626862,true⟩⟩⟩
  | 3 => ⟨⟨(-6687323785),69660674547,true⟩,⟨40013442808776138,45729095838242853,true⟩,⟨⟨(-1017979803811330774190887),(-948746295177266299194525),true⟩,⟨668589296723611670189908,737822805357676145182415,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738036),34359738857,true⟩,⟨(-6687323785),69660674547,true⟩,⟨⟨340181959751839531081138,429196470852759936183287,true⟩,⟨(-1190594444625097664390771),(-1101579933524177259278143),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738036),34359738857,true⟩,⟨⟨305553833042235195126450,414349346610011530354716,true⟩,⟨1099697772326483684125588,1208493285894260019364786,true⟩⟩⟩
theorem shortNegativeR047Q01F_ok : ∀ n : Fin 6, (shortNegativeR047Q01F n).encloses (FactoredFrequency.build shortNegativeR047Q01T (Grid.ofRats (52649925285479/65970697666560) (52993522669159/65970697666560)) n) := by decide +kernel
def shortNegativeR047Q01L : ℕ → ℚ
  | 0 => (-355549/125000)
  | 1 => (-2378317/1000000)
  | 2 => (-1976167/1000000)
  | 3 => (-1734367/1000000)
  | 4 => (-105643/62500)
  | 5 => (-377231/200000)
  | 6 => (-2256459/1000000)
  | 7 => (-171079/62500)
  | 8 => (-1608457/500000)
  | 9 => (-3592471/1000000)
  | 10 => (-734773/200000)
  | 11 => (-851917/250000)
  | _ => 0
def shortNegativeR047Q01U : ℕ → ℚ
  | 0 => (-562703/250000)
  | 1 => (-430491/250000)
  | 2 => (-319173/250000)
  | 3 => (-12561/12500)
  | 4 => (-931687/1000000)
  | 5 => (-8263/8000)
  | 6 => (-662087/500000)
  | 7 => (-877813/500000)
  | 8 => (-2213851/1000000)
  | 9 => (-2550757/1000000)
  | 10 => (-1341061/500000)
  | 11 => (-2555137/1000000)
  | _ => 0
private theorem shortNegativeR047Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR047Q01P shortNegativeR047Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR047Q01L (0:Fin 12)) (shortNegativeR047Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR047Q01P shortNegativeR047Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR047Q01L (1:Fin 12)) (shortNegativeR047Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR047Q01P shortNegativeR047Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR047Q01L (2:Fin 12)) (shortNegativeR047Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR047Q01P shortNegativeR047Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR047Q01L (3:Fin 12)) (shortNegativeR047Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR047Q01P shortNegativeR047Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR047Q01L (4:Fin 12)) (shortNegativeR047Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR047Q01P shortNegativeR047Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR047Q01L (5:Fin 12)) (shortNegativeR047Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR047Q01P shortNegativeR047Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR047Q01L (6:Fin 12)) (shortNegativeR047Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR047Q01P shortNegativeR047Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR047Q01L (7:Fin 12)) (shortNegativeR047Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR047Q01P shortNegativeR047Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR047Q01L (8:Fin 12)) (shortNegativeR047Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR047Q01P shortNegativeR047Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR047Q01L (9:Fin 12)) (shortNegativeR047Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR047Q01P shortNegativeR047Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR047Q01L (10:Fin 12)) (shortNegativeR047Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR047Q01P shortNegativeR047Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR047Q01L (11:Fin 12)) (shortNegativeR047Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR047Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR047Q01P shortNegativeR047Q01F (shortNegativeNodes12 k)).re (shortNegativeR047Q01L k) (shortNegativeR047Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR047Q01Point00
  · exact shortNegativeR047Q01Point01
  · exact shortNegativeR047Q01Point02
  · exact shortNegativeR047Q01Point03
  · exact shortNegativeR047Q01Point04
  · exact shortNegativeR047Q01Point05
  · exact shortNegativeR047Q01Point06
  · exact shortNegativeR047Q01Point07
  · exact shortNegativeR047Q01Point08
  · exact shortNegativeR047Q01Point09
  · exact shortNegativeR047Q01Point10
  · exact shortNegativeR047Q01Point11

theorem shortNegativeR047Q01Bound {t a : ℝ} (tl : ((32/25):ℝ)≤t) (tu : t≤((129/100):ℝ)) (al : ((52649925285479/65970697666560):ℝ)≤a) (au : a≤((52993522669159/65970697666560):ℝ)) : (((-1735739144536741584078414378591807/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1086662614148910497454715169039935/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR047Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (52649925285479/65970697666560) (52993522669159/65970697666560)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR047Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR047Q01F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR047Q01L shortNegativeR047Q01U (-1735739144536741584078414378591807/649037107316853453566312041152512) (-1086662614148910497454715169039935/649037107316853453566312041152512) shortNegativeR047Q01Samples (by decide +kernel)

def shortNegativeR047Q02T := Grid.ofRats (32/25) (129/100)
def shortNegativeR047Q02P : PrimalThetaParameters := ⟨⟨⟨21006522164975248756275,21676937238987692000930,true⟩,⟨0,0,true⟩⟩, ⟨⟨1525426345536829061033002,1535316846770325745568755,true⟩,⟨0,0,true⟩⟩, ⟨(-747099782562646098982802),(-727318780095721449395431),true⟩, ⟨3676384362461223192730961,3760504068703068861459446,true⟩⟩
theorem shortNegativeR047Q02P_ok : shortNegativeR047Q02P.encloses (primalThetaParameters shortNegativeR047Q02T (Grid.ofRats (52993522669159/65970697666560) (17779040017613/21990232555520))) := by decide +kernel

def shortNegativeR047Q02F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨438922939463789682788788,442383805166689832133599,true⟩,⟨3303696067219975851694355,3329745397030848799738575,true⟩,⟨⟨357974620106092975299927,367865121339589659884853,true⟩,⟨1148220307646859816725994,1158110808880356501321843,true⟩⟩⟩
  | 1 => ⟨⟨1005356370740172766186,1062176333285311855205,true⟩,⟨438922939463789682788788,442383805166689832133599,true⟩,⟨⟨(-972769706061149711789292),(-943098202360797097056032),true⟩,⟨(-752307227027780466328402),(-722635723327427851598168),true⟩⟩⟩
  | 2 => ⟨⟨40013442808776138,45729095838242853,true⟩,⟨1005356370740172766186,1062176333285311855205,true⟩,⟨⟨1182904953134437859222942,1232357459301646404060876,true⟩,⟨31206806007236784228786,80659312174445329050862,true⟩⟩⟩
  | 3 => ⟨⟨(-6687323785),69660674547,true⟩,⟨40013442808776138,45729095838242853,true⟩,⟨⟨(-1056617307214521397996363),(-987383798580456923000104),true⟩,⟨611151398511929573729008,680384907145994048720090,true⟩⟩⟩
  | 4 => ⟨⟨(-34359738036),34359738857,true⟩,⟨(-6687323785),69660674547,true⟩,⟨⟨423451031569182514406022,512465542670102919508288,true⟩,⟨(-1159189577491089593567207),(-1070175066390169188456043),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359738036),34359738857,true⟩,⟨⟨200376215858881664356633,309171729426657999586355,true⟩,⟨1127377120337268138882011,1236172633905044474124493,true⟩⟩⟩
theorem shortNegativeR047Q02F_ok : ∀ n : Fin 6, (shortNegativeR047Q02F n).encloses (FactoredFrequency.build shortNegativeR047Q02T (Grid.ofRats (52993522669159/65970697666560) (17779040017613/21990232555520)) n) := by decide +kernel
def shortNegativeR047Q02L : ℕ → ℚ
  | 0 => (-2855543/1000000)
  | 1 => (-2396759/1000000)
  | 2 => (-24929/12500)
  | 3 => (-1746273/1000000)
  | 4 => (-211539/125000)
  | 5 => (-469057/250000)
  | 6 => (-2234531/1000000)
  | 7 => (-2705571/1000000)
  | 8 => (-636177/200000)
  | 9 => (-445003/125000)
  | 10 => (-1826437/500000)
  | 11 => (-850993/250000)
  | _ => 0
def shortNegativeR047Q02U : ℕ → ℚ
  | 0 => (-2269037/1000000)
  | 1 => (-1747027/1000000)
  | 2 => (-1300683/1000000)
  | 3 => (-255873/250000)
  | 4 => (-940837/1000000)
  | 5 => (-1031111/1000000)
  | 6 => (-1311699/1000000)
  | 7 => (-1732703/1000000)
  | 8 => (-1093847/500000)
  | 9 => (-2528737/1000000)
  | 10 => (-668021/250000)
  | 11 => (-2559943/1000000)
  | _ => 0
private theorem shortNegativeR047Q02Point00 : containedInReported (sampledFactoredPrimal shortNegativeR047Q02P shortNegativeR047Q02F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR047Q02L (0:Fin 12)) (shortNegativeR047Q02U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q02Point01 : containedInReported (sampledFactoredPrimal shortNegativeR047Q02P shortNegativeR047Q02F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR047Q02L (1:Fin 12)) (shortNegativeR047Q02U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q02Point02 : containedInReported (sampledFactoredPrimal shortNegativeR047Q02P shortNegativeR047Q02F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR047Q02L (2:Fin 12)) (shortNegativeR047Q02U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q02Point03 : containedInReported (sampledFactoredPrimal shortNegativeR047Q02P shortNegativeR047Q02F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR047Q02L (3:Fin 12)) (shortNegativeR047Q02U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q02Point04 : containedInReported (sampledFactoredPrimal shortNegativeR047Q02P shortNegativeR047Q02F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR047Q02L (4:Fin 12)) (shortNegativeR047Q02U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q02Point05 : containedInReported (sampledFactoredPrimal shortNegativeR047Q02P shortNegativeR047Q02F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR047Q02L (5:Fin 12)) (shortNegativeR047Q02U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q02Point06 : containedInReported (sampledFactoredPrimal shortNegativeR047Q02P shortNegativeR047Q02F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR047Q02L (6:Fin 12)) (shortNegativeR047Q02U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q02Point07 : containedInReported (sampledFactoredPrimal shortNegativeR047Q02P shortNegativeR047Q02F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR047Q02L (7:Fin 12)) (shortNegativeR047Q02U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q02Point08 : containedInReported (sampledFactoredPrimal shortNegativeR047Q02P shortNegativeR047Q02F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR047Q02L (8:Fin 12)) (shortNegativeR047Q02U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q02Point09 : containedInReported (sampledFactoredPrimal shortNegativeR047Q02P shortNegativeR047Q02F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR047Q02L (9:Fin 12)) (shortNegativeR047Q02U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q02Point10 : containedInReported (sampledFactoredPrimal shortNegativeR047Q02P shortNegativeR047Q02F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR047Q02L (10:Fin 12)) (shortNegativeR047Q02U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR047Q02Point11 : containedInReported (sampledFactoredPrimal shortNegativeR047Q02P shortNegativeR047Q02F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR047Q02L (11:Fin 12)) (shortNegativeR047Q02U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR047Q02Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR047Q02P shortNegativeR047Q02F (shortNegativeNodes12 k)).re (shortNegativeR047Q02L k) (shortNegativeR047Q02U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR047Q02Point00
  · exact shortNegativeR047Q02Point01
  · exact shortNegativeR047Q02Point02
  · exact shortNegativeR047Q02Point03
  · exact shortNegativeR047Q02Point04
  · exact shortNegativeR047Q02Point05
  · exact shortNegativeR047Q02Point06
  · exact shortNegativeR047Q02Point07
  · exact shortNegativeR047Q02Point08
  · exact shortNegativeR047Q02Point09
  · exact shortNegativeR047Q02Point10
  · exact shortNegativeR047Q02Point11

theorem shortNegativeR047Q02Bound {t a : ℝ} (tl : ((32/25):ℝ)≤t) (tu : t≤((129/100):ℝ)) (al : ((52993522669159/65970697666560):ℝ)≤a) (au : a≤((17779040017613/21990232555520):ℝ)) : (((-1735739144536741584078414378591807/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1086662614148910497454715169039935/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR047Q02T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (52993522669159/65970697666560) (17779040017613/21990232555520)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR047Q02P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR047Q02F_ok n) ts asb
  exact factored_negative_12_samples 600 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip040Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR047Q02L shortNegativeR047Q02U (-1735739144536741584078414378591807/649037107316853453566312041152512) (-1086662614148910497454715169039935/649037107316853453566312041152512) shortNegativeR047Q02Samples (by decide +kernel)

theorem short_original_negative_047 {t a : ℝ} (tb : RealMem negative_047.t t) (ab : RealMem negative_047.a a) : RealMem negative_047.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((32/25):ℝ) ((129/100):ℝ) := by simpa [negative_047,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((32/25):ℝ)<((129/100):ℝ)) tB
  have aB : a∈Icc ((17435442633933/21990232555520):ℝ) ((17779040017613/21990232555520):ℝ) := by simpa [negative_047,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=3) (by decide) (by norm_num : ((17435442633933/21990232555520):ℝ)<((17779040017613/21990232555520):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR047Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_047,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR047Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_047,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR047Q02Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_047,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_046
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_047
