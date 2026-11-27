import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip000

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR002Q00T := Grid.ofRats (181/200) (363/400)
def shortNegativeR002Q00P : PrimalThetaParameters := ⟨⟨⟨69859924509936081219309,70410763381708102516357,true⟩,⟨0,0,true⟩⟩, ⟨⟨1150982260614026743925119,1152836729595363206853177,true⟩,⟨0,0,true⟩⟩, ⟨(-1495987952408250733200952),(-1492279014445646526824151),true⟩, ⟨5915258185810610667820322,5959725406337144180982907,true⟩⟩
theorem shortNegativeR002Q00P_ok : shortNegativeR002Q00P.encloses (primalThetaParameters shortNegativeR002Q00T (Grid.ofRats (999632081517913/1649267441664000) (1001242694253913/1649267441664000))) := by decide +kernel

def shortNegativeR002Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨592729807539821833844779,593894773123483913605543,true⟩,⟨2460876410217350771622523,2465713076581945554588493,true⟩,⟨⟨699491656705662500605049,701346125686998963580701,true⟩,⟨984422964264173208808100,986277433245509671787691,true⟩⟩⟩
  | 1 => ⟨⟨8233783741659112419761,8347734016813665519157,true⟩,⟨592729807539821833844779,593894773123483913605543,true⟩,⟨⟨(-1163591565803714479661396),(-1158028158859842529762335),true⟩,⟨334889883790274100324380,340453290734146050212101,true⟩⟩⟩
  | 2 => ⟨⟨6609530349921007283,6833876157887762492,true⟩,⟨8233783741659112419761,8347734016813665519157,true⟩,⟨⟨57954596055275960083461,67226940961683396894440,true⟩,⟨(-1211940621640905845290942),(-1202668276734498408464207),true⟩⟩⟩
  | 3 => ⟨⟨306564269962182,325874813116209,true⟩,⟨6609530349921007283,6833876157887762492,true⟩,⟨⟨1113177805295974215796548,1126159088164917139511064,true⟩,⟨449408696936548822410624,462389979805491746116005,true⟩⟩⟩
  | 4 => ⟨⟨(-33537877553),35264600265,true⟩,⟨306564269962182,325874813116209,true⟩,⟨⟨(-806902955225499431502518),(-790212734394021020855976),true⟩,⟨899293036547957897745055,915983257379436308393094,true⟩⟩⟩
  | _ => ⟨⟨(-34359738241),34359738515,true⟩,⟨(-33537877553),35264600265,true⟩,⟨⟨(-604969531382624282774283),(-584570372588610385226500),true⟩,⟨(-1062696772526722316255248),(-1042297613732708418701167),true⟩⟩⟩
theorem shortNegativeR002Q00F_ok : ∀ n : Fin 6, (shortNegativeR002Q00F n).encloses (FactoredFrequency.build shortNegativeR002Q00T (Grid.ofRats (999632081517913/1649267441664000) (1001242694253913/1649267441664000)) n) := by decide +kernel
def shortNegativeR002Q00L : ℕ → ℚ
  | 0 => (2658511/1000000)
  | 1 => (3212459/1000000)
  | 2 => (3135461/1000000)
  | 3 => (691509/250000)
  | 4 => (564161/250000)
  | 5 => (1625357/1000000)
  | 6 => (407767/500000)
  | 7 => (-48213/200000)
  | 8 => (-1580521/1000000)
  | 9 => (-313661/100000)
  | 10 => (-934603/200000)
  | 11 => (-1431489/250000)
  | 12 => (-2827537/500000)
  | 13 => (-2074859/500000)
  | 14 => (-803747/500000)
  | 15 => (113827/125000)
  | _ => 0
def shortNegativeR002Q00U : ℕ → ℚ
  | 0 => (2918699/1000000)
  | 1 => (3477077/1000000)
  | 2 => (424769/125000)
  | 3 => (3019843/1000000)
  | 4 => (2499479/1000000)
  | 5 => (927963/500000)
  | 6 => (262961/250000)
  | 7 => (6269/250000)
  | 8 => (-25191/20000)
  | 9 => (-2758047/1000000)
  | 10 => (-2116371/500000)
  | 11 => (-1292979/250000)
  | 12 => (-1247999/250000)
  | 13 => (-3387011/1000000)
  | 14 => (-849623/1000000)
  | 15 => (1564603/1000000)
  | _ => 0
private theorem shortNegativeR002Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR002Q00P shortNegativeR002Q00F (shortNegativeNodes16 (0:Fin 16))).re (shortNegativeR002Q00L (0:Fin 16)) (shortNegativeR002Q00U (0:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR002Q00P shortNegativeR002Q00F (shortNegativeNodes16 (1:Fin 16))).re (shortNegativeR002Q00L (1:Fin 16)) (shortNegativeR002Q00U (1:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR002Q00P shortNegativeR002Q00F (shortNegativeNodes16 (2:Fin 16))).re (shortNegativeR002Q00L (2:Fin 16)) (shortNegativeR002Q00U (2:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR002Q00P shortNegativeR002Q00F (shortNegativeNodes16 (3:Fin 16))).re (shortNegativeR002Q00L (3:Fin 16)) (shortNegativeR002Q00U (3:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR002Q00P shortNegativeR002Q00F (shortNegativeNodes16 (4:Fin 16))).re (shortNegativeR002Q00L (4:Fin 16)) (shortNegativeR002Q00U (4:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR002Q00P shortNegativeR002Q00F (shortNegativeNodes16 (5:Fin 16))).re (shortNegativeR002Q00L (5:Fin 16)) (shortNegativeR002Q00U (5:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR002Q00P shortNegativeR002Q00F (shortNegativeNodes16 (6:Fin 16))).re (shortNegativeR002Q00L (6:Fin 16)) (shortNegativeR002Q00U (6:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR002Q00P shortNegativeR002Q00F (shortNegativeNodes16 (7:Fin 16))).re (shortNegativeR002Q00L (7:Fin 16)) (shortNegativeR002Q00U (7:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR002Q00P shortNegativeR002Q00F (shortNegativeNodes16 (8:Fin 16))).re (shortNegativeR002Q00L (8:Fin 16)) (shortNegativeR002Q00U (8:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR002Q00P shortNegativeR002Q00F (shortNegativeNodes16 (9:Fin 16))).re (shortNegativeR002Q00L (9:Fin 16)) (shortNegativeR002Q00U (9:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR002Q00P shortNegativeR002Q00F (shortNegativeNodes16 (10:Fin 16))).re (shortNegativeR002Q00L (10:Fin 16)) (shortNegativeR002Q00U (10:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR002Q00P shortNegativeR002Q00F (shortNegativeNodes16 (11:Fin 16))).re (shortNegativeR002Q00L (11:Fin 16)) (shortNegativeR002Q00U (11:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q00Point12 : containedInReported (sampledFactoredPrimal shortNegativeR002Q00P shortNegativeR002Q00F (shortNegativeNodes16 (12:Fin 16))).re (shortNegativeR002Q00L (12:Fin 16)) (shortNegativeR002Q00U (12:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q00Point13 : containedInReported (sampledFactoredPrimal shortNegativeR002Q00P shortNegativeR002Q00F (shortNegativeNodes16 (13:Fin 16))).re (shortNegativeR002Q00L (13:Fin 16)) (shortNegativeR002Q00U (13:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q00Point14 : containedInReported (sampledFactoredPrimal shortNegativeR002Q00P shortNegativeR002Q00F (shortNegativeNodes16 (14:Fin 16))).re (shortNegativeR002Q00L (14:Fin 16)) (shortNegativeR002Q00U (14:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q00Point15 : containedInReported (sampledFactoredPrimal shortNegativeR002Q00P shortNegativeR002Q00F (shortNegativeNodes16 (15:Fin 16))).re (shortNegativeR002Q00L (15:Fin 16)) (shortNegativeR002Q00U (15:Fin 16))=true := by decide +kernel
theorem shortNegativeR002Q00Samples : ∀ k : Fin 16, containedInReported (sampledFactoredPrimal shortNegativeR002Q00P shortNegativeR002Q00F (shortNegativeNodes16 k)).re (shortNegativeR002Q00L k) (shortNegativeR002Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR002Q00Point00
  · exact shortNegativeR002Q00Point01
  · exact shortNegativeR002Q00Point02
  · exact shortNegativeR002Q00Point03
  · exact shortNegativeR002Q00Point04
  · exact shortNegativeR002Q00Point05
  · exact shortNegativeR002Q00Point06
  · exact shortNegativeR002Q00Point07
  · exact shortNegativeR002Q00Point08
  · exact shortNegativeR002Q00Point09
  · exact shortNegativeR002Q00Point10
  · exact shortNegativeR002Q00Point11
  · exact shortNegativeR002Q00Point12
  · exact shortNegativeR002Q00Point13
  · exact shortNegativeR002Q00Point14
  · exact shortNegativeR002Q00Point15

theorem shortNegativeR002Q00Bound {t a : ℝ} (tl : ((181/200):ℝ)≤t) (tu : t≤((363/400):ℝ)) (al : ((999632081517913/1649267441664000):ℝ)≤a) (au : a≤((1001242694253913/1649267441664000):ℝ)) : (((-49158166072484769395849313940771/81129638414606681695789005144064):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-12993856946970429837095321498915/81129638414606681695789005144064):ℚ):ℝ) := by
  have ts : shortNegativeR002Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (999632081517913/1649267441664000) (1001242694253913/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR002Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR002Q00F_ok n) ts asb
  exact factored_negative_16_samples 17310 ps fs shortNegativeNodes16Sound (by linarith) (by linarith) (shortNegativeStrip000Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR002Q00L shortNegativeR002Q00U (-49158166072484769395849313940771/81129638414606681695789005144064) (-12993856946970429837095321498915/81129638414606681695789005144064) shortNegativeR002Q00Samples (by decide +kernel)

def shortNegativeR002Q01T := Grid.ofRats (181/200) (363/400)
def shortNegativeR002Q01P : PrimalThetaParameters := ⟨⟨⟨69859924509936081219309,70410763381708102516357,true⟩,⟨0,0,true⟩⟩, ⟨⟨1152836729595294487372768,1154691198576630950300832,true⟩,⟨0,0,true⟩⟩, ⟨(-1492279014445715246305642),(-1488570076483111039928854),true⟩, ⟨5906313471269243927074675,5950661316825439383872222,true⟩⟩
theorem shortNegativeR002Q01P_ok : shortNegativeR002Q01P.encloses (primalThetaParameters shortNegativeR002Q01T (Grid.ofRats (1001242694253913/1649267441664000) (1002853306989913/1649267441664000))) := by decide +kernel

def shortNegativeR002Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨592729807539821833844779,593894773123483913605543,true⟩,⟨2460876410217350771622523,2465713076581945554588493,true⟩,⟨⟨697979324947566430933975,699833793928902893909682,true⟩,⟨985496233653268557479626,987350702634605020459329,true⟩⟩⟩
  | 1 => ⟨⟨8233783741659112419761,8347734016813665519157,true⟩,⟨592729807539821833844779,593894773123483913605543,true⟩,⟨⟨(-1165133213780740805997885),(-1159569806836868856098753),true⟩,⟨329544346987162543769003,335107753931034493656699,true⟩⟩⟩
  | 2 => ⟨⟨6609530349921007283,6833876157887762492,true⟩,⟨8233783741659112419761,8347734016813665519157,true⟩,⟨⟨67212573399129651735816,76484918305537088547333,true⟩,⟨(-1211425050033018723291623),(-1202152705126611286464487),true⟩⟩⟩
  | 3 => ⟨⟨306564269962182,325874813116209,true⟩,⟨6609530349921007283,6833876157887762492,true⟩,⟨⟨1108217964337264990191107,1121199247206207913905913,true⟩,⟨461405032353323208783132,474386315222266132489042,true⟩⟩⟩
  | 4 => ⟨⟨(-33537877553),35264600265,true⟩,⟨306564269962182,325874813116209,true⟩,⟨⟨(-819357150789332310101887),(-802666929957853899455219),true⟩,⟨888182138305661513034999,904872359137139923682839,true⟩⟩⟩
  | _ => ⟨⟨(-34359738241),34359738515,true⟩,⟨(-33537877553),35264600265,true⟩,⟨⟨(-587126088076267880450636),(-566726929282253982902878),true⟩,⟨(-1072582486316193774545192),(-1052183327522179876990751),true⟩⟩⟩
theorem shortNegativeR002Q01F_ok : ∀ n : Fin 6, (shortNegativeR002Q01F n).encloses (FactoredFrequency.build shortNegativeR002Q01T (Grid.ofRats (1001242694253913/1649267441664000) (1002853306989913/1649267441664000)) n) := by decide +kernel
def shortNegativeR002Q01L : ℕ → ℚ
  | 0 => (2633321/1000000)
  | 1 => (638893/200000)
  | 2 => (3123967/1000000)
  | 3 => (275933/100000)
  | 4 => (281693/125000)
  | 5 => (812733/500000)
  | 6 => (409529/500000)
  | 7 => (-5839/25000)
  | 8 => (-1568689/1000000)
  | 9 => (-1560491/500000)
  | 10 => (-2327557/500000)
  | 11 => (-5711681/1000000)
  | 12 => (-1412847/250000)
  | 13 => (-4160981/1000000)
  | 14 => (-815747/500000)
  | 15 => (88247/100000)
  | _ => 0
def shortNegativeR002Q01U : ℕ → ℚ
  | 0 => (28927/10000)
  | 1 => (1729227/500000)
  | 2 => (3386209/1000000)
  | 3 => (753211/250000)
  | 4 => (2496199/1000000)
  | 5 => (74237/40000)
  | 6 => (527641/500000)
  | 7 => (6483/200000)
  | 8 => (-624031/500000)
  | 9 => (-2742871/1000000)
  | 10 => (-10543/2500)
  | 11 => (-258019/50000)
  | 12 => (-998231/200000)
  | 13 => (-1700699/500000)
  | 14 => (-438323/500000)
  | 15 => (766711/500000)
  | _ => 0
private theorem shortNegativeR002Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR002Q01P shortNegativeR002Q01F (shortNegativeNodes16 (0:Fin 16))).re (shortNegativeR002Q01L (0:Fin 16)) (shortNegativeR002Q01U (0:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR002Q01P shortNegativeR002Q01F (shortNegativeNodes16 (1:Fin 16))).re (shortNegativeR002Q01L (1:Fin 16)) (shortNegativeR002Q01U (1:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR002Q01P shortNegativeR002Q01F (shortNegativeNodes16 (2:Fin 16))).re (shortNegativeR002Q01L (2:Fin 16)) (shortNegativeR002Q01U (2:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR002Q01P shortNegativeR002Q01F (shortNegativeNodes16 (3:Fin 16))).re (shortNegativeR002Q01L (3:Fin 16)) (shortNegativeR002Q01U (3:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR002Q01P shortNegativeR002Q01F (shortNegativeNodes16 (4:Fin 16))).re (shortNegativeR002Q01L (4:Fin 16)) (shortNegativeR002Q01U (4:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR002Q01P shortNegativeR002Q01F (shortNegativeNodes16 (5:Fin 16))).re (shortNegativeR002Q01L (5:Fin 16)) (shortNegativeR002Q01U (5:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR002Q01P shortNegativeR002Q01F (shortNegativeNodes16 (6:Fin 16))).re (shortNegativeR002Q01L (6:Fin 16)) (shortNegativeR002Q01U (6:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR002Q01P shortNegativeR002Q01F (shortNegativeNodes16 (7:Fin 16))).re (shortNegativeR002Q01L (7:Fin 16)) (shortNegativeR002Q01U (7:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR002Q01P shortNegativeR002Q01F (shortNegativeNodes16 (8:Fin 16))).re (shortNegativeR002Q01L (8:Fin 16)) (shortNegativeR002Q01U (8:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR002Q01P shortNegativeR002Q01F (shortNegativeNodes16 (9:Fin 16))).re (shortNegativeR002Q01L (9:Fin 16)) (shortNegativeR002Q01U (9:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR002Q01P shortNegativeR002Q01F (shortNegativeNodes16 (10:Fin 16))).re (shortNegativeR002Q01L (10:Fin 16)) (shortNegativeR002Q01U (10:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR002Q01P shortNegativeR002Q01F (shortNegativeNodes16 (11:Fin 16))).re (shortNegativeR002Q01L (11:Fin 16)) (shortNegativeR002Q01U (11:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q01Point12 : containedInReported (sampledFactoredPrimal shortNegativeR002Q01P shortNegativeR002Q01F (shortNegativeNodes16 (12:Fin 16))).re (shortNegativeR002Q01L (12:Fin 16)) (shortNegativeR002Q01U (12:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q01Point13 : containedInReported (sampledFactoredPrimal shortNegativeR002Q01P shortNegativeR002Q01F (shortNegativeNodes16 (13:Fin 16))).re (shortNegativeR002Q01L (13:Fin 16)) (shortNegativeR002Q01U (13:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q01Point14 : containedInReported (sampledFactoredPrimal shortNegativeR002Q01P shortNegativeR002Q01F (shortNegativeNodes16 (14:Fin 16))).re (shortNegativeR002Q01L (14:Fin 16)) (shortNegativeR002Q01U (14:Fin 16))=true := by decide +kernel
private theorem shortNegativeR002Q01Point15 : containedInReported (sampledFactoredPrimal shortNegativeR002Q01P shortNegativeR002Q01F (shortNegativeNodes16 (15:Fin 16))).re (shortNegativeR002Q01L (15:Fin 16)) (shortNegativeR002Q01U (15:Fin 16))=true := by decide +kernel
theorem shortNegativeR002Q01Samples : ∀ k : Fin 16, containedInReported (sampledFactoredPrimal shortNegativeR002Q01P shortNegativeR002Q01F (shortNegativeNodes16 k)).re (shortNegativeR002Q01L k) (shortNegativeR002Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR002Q01Point00
  · exact shortNegativeR002Q01Point01
  · exact shortNegativeR002Q01Point02
  · exact shortNegativeR002Q01Point03
  · exact shortNegativeR002Q01Point04
  · exact shortNegativeR002Q01Point05
  · exact shortNegativeR002Q01Point06
  · exact shortNegativeR002Q01Point07
  · exact shortNegativeR002Q01Point08
  · exact shortNegativeR002Q01Point09
  · exact shortNegativeR002Q01Point10
  · exact shortNegativeR002Q01Point11
  · exact shortNegativeR002Q01Point12
  · exact shortNegativeR002Q01Point13
  · exact shortNegativeR002Q01Point14
  · exact shortNegativeR002Q01Point15

theorem shortNegativeR002Q01Bound {t a : ℝ} (tl : ((181/200):ℝ)≤t) (tu : t≤((363/400):ℝ)) (al : ((1001242694253913/1649267441664000):ℝ)≤a) (au : a≤((1002853306989913/1649267441664000):ℝ)) : (((-49158166072484769395849313940771/81129638414606681695789005144064):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-12993856946970429837095321498915/81129638414606681695789005144064):ℚ):ℝ) := by
  have ts : shortNegativeR002Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1001242694253913/1649267441664000) (1002853306989913/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR002Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR002Q01F_ok n) ts asb
  exact factored_negative_16_samples 17310 ps fs shortNegativeNodes16Sound (by linarith) (by linarith) (shortNegativeStrip000Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR002Q01L shortNegativeR002Q01U (-49158166072484769395849313940771/81129638414606681695789005144064) (-12993856946970429837095321498915/81129638414606681695789005144064) shortNegativeR002Q01Samples (by decide +kernel)

theorem short_original_negative_002 {t a : ℝ} (tb : RealMem negative_002.t t) (ab : RealMem negative_002.a a) : RealMem negative_002.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((181/200):ℝ) ((363/400):ℝ) := by simpa [negative_002,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((181/200):ℝ)<((363/400):ℝ)) tB
  have aB : a∈Icc ((999632081517913/1649267441664000):ℝ) ((1002853306989913/1649267441664000):ℝ) := by simpa [negative_002,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((999632081517913/1649267441664000):ℝ)<((1002853306989913/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR002Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_002,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR002Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_002,RealMem] using v

def shortNegativeR003Q00T := Grid.ofRats (363/400) (91/100)
def shortNegativeR003Q00P : PrimalThetaParameters := ⟨⟨⟨69313394971749511879471,69859924510004800696990,true⟩,⟨0,0,true⟩⟩, ⟨⟨1152632832822352691664456,1154487301803689154592519,true⟩,⟨0,0,true⟩⟩, ⟨(-1492686807991598837722268),(-1488977870028994631345478),true⟩, ⟨5895733322616867138246087,5939846531681468785195542,true⟩⟩
theorem shortNegativeR003Q00P_ok : shortNegativeR003Q00P.encloses (primalThetaParameters shortNegativeR003Q00T (Grid.ofRats (1001065609200107/1649267441664000) (1002676221936107/1649267441664000))) := by decide +kernel

def shortNegativeR003Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨591567127116617778635595,592729807539890553342808,true⟩,⟨2465713076581876835023237,2470559249048210254787811,true⟩,⟨⟨698145684653266759241610,700000153634603222217366,true⟩,⟨985378342422734529257204,987232811404070992237036,true⟩⟩⟩
  | 1 => ⟨⟨8121388938413425766408,8233783741727831896909,true⟩,⟨591567127116617778635595,592729807539890553342808,true⟩,⟨⟨(-1164964915204532881684795),(-1159401508260660931785433),true⟩,⟨330132429147586120632268,335695836091458070520204,true⟩⟩⟩
  | 2 => ⟨⟨6392549539421138446,6609530418640484020,true⟩,⟨8121388938413425766408,8233783741727831896909,true⟩,⟨⟨66194866184835758306987,75467211091243195118725,true⟩,⟨(-1211485210774219027062438),(-1202212865867811590235066),true⟩⟩⟩
  | 3 => ⟨⟨288458731772436,306632989438919,true⟩,⟨6392549539421138446,6609530418640484020,true⟩,⟨⟨1108769592551840552788449,1121750875420783476502996,true⟩,⟨460088663528467816712703,473069946397410740418319,true⟩⟩⟩
  | 4 => ⟨⟨(-33613265120),35181599184,true⟩,⟨288458731772436,306632989438919,true⟩,⟨⟨(-817995346779786679370010),(-801305125948308268723881),true⟩,⟨889412168633862806599509,906102389465341217246848,true⟩⟩⟩
  | _ => ⟨⟨(-34359738258),34359738496,true⟩,⟨(-33613265120),35181599184,true⟩,⟨⟨(-589096084237301514762003),(-568696925443287617214573),true⟩,⟨(-1071510313355065873080235),(-1051111154561051975526167),true⟩⟩⟩
theorem shortNegativeR003Q00F_ok : ∀ n : Fin 6, (shortNegativeR003Q00F n).encloses (FactoredFrequency.build shortNegativeR003Q00T (Grid.ofRats (1001065609200107/1649267441664000) (1002676221936107/1649267441664000)) n) := by decide +kernel
def shortNegativeR003Q00L : ℕ → ℚ
  | 0 => (2584921/1000000)
  | 1 => (1576337/500000)
  | 2 => (3090997/1000000)
  | 3 => (1366291/500000)
  | 4 => (445989/200000)
  | 5 => (320609/200000)
  | 6 => (797223/1000000)
  | 7 => (-254183/1000000)
  | 8 => (-1585323/1000000)
  | 9 => (-782433/250000)
  | 10 => (-930441/200000)
  | 11 => (-5697369/1000000)
  | 12 => (-2817361/500000)
  | 13 => (-207883/50000)
  | 14 => (-206637/125000)
  | 15 => (210151/250000)
  | _ => 0
def shortNegativeR003Q00U : ℕ → ℚ
  | 0 => (568773/200000)
  | 1 => (27331/8000)
  | 2 => (3353051/1000000)
  | 3 => (1493021/500000)
  | 4 => (2472667/1000000)
  | 5 => (1833659/1000000)
  | 6 => (516803/500000)
  | 7 => (12189/1000000)
  | 8 => (-252897/200000)
  | 9 => (-1375979/500000)
  | 10 => (-4215497/1000000)
  | 11 => (-128713/25000)
  | 12 => (-124447/25000)
  | 13 => (-3402741/1000000)
  | 14 => (-903137/1000000)
  | 15 => (1487137/1000000)
  | _ => 0
private theorem shortNegativeR003Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR003Q00P shortNegativeR003Q00F (shortNegativeNodes16 (0:Fin 16))).re (shortNegativeR003Q00L (0:Fin 16)) (shortNegativeR003Q00U (0:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR003Q00P shortNegativeR003Q00F (shortNegativeNodes16 (1:Fin 16))).re (shortNegativeR003Q00L (1:Fin 16)) (shortNegativeR003Q00U (1:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR003Q00P shortNegativeR003Q00F (shortNegativeNodes16 (2:Fin 16))).re (shortNegativeR003Q00L (2:Fin 16)) (shortNegativeR003Q00U (2:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR003Q00P shortNegativeR003Q00F (shortNegativeNodes16 (3:Fin 16))).re (shortNegativeR003Q00L (3:Fin 16)) (shortNegativeR003Q00U (3:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR003Q00P shortNegativeR003Q00F (shortNegativeNodes16 (4:Fin 16))).re (shortNegativeR003Q00L (4:Fin 16)) (shortNegativeR003Q00U (4:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR003Q00P shortNegativeR003Q00F (shortNegativeNodes16 (5:Fin 16))).re (shortNegativeR003Q00L (5:Fin 16)) (shortNegativeR003Q00U (5:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR003Q00P shortNegativeR003Q00F (shortNegativeNodes16 (6:Fin 16))).re (shortNegativeR003Q00L (6:Fin 16)) (shortNegativeR003Q00U (6:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR003Q00P shortNegativeR003Q00F (shortNegativeNodes16 (7:Fin 16))).re (shortNegativeR003Q00L (7:Fin 16)) (shortNegativeR003Q00U (7:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR003Q00P shortNegativeR003Q00F (shortNegativeNodes16 (8:Fin 16))).re (shortNegativeR003Q00L (8:Fin 16)) (shortNegativeR003Q00U (8:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR003Q00P shortNegativeR003Q00F (shortNegativeNodes16 (9:Fin 16))).re (shortNegativeR003Q00L (9:Fin 16)) (shortNegativeR003Q00U (9:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR003Q00P shortNegativeR003Q00F (shortNegativeNodes16 (10:Fin 16))).re (shortNegativeR003Q00L (10:Fin 16)) (shortNegativeR003Q00U (10:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR003Q00P shortNegativeR003Q00F (shortNegativeNodes16 (11:Fin 16))).re (shortNegativeR003Q00L (11:Fin 16)) (shortNegativeR003Q00U (11:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q00Point12 : containedInReported (sampledFactoredPrimal shortNegativeR003Q00P shortNegativeR003Q00F (shortNegativeNodes16 (12:Fin 16))).re (shortNegativeR003Q00L (12:Fin 16)) (shortNegativeR003Q00U (12:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q00Point13 : containedInReported (sampledFactoredPrimal shortNegativeR003Q00P shortNegativeR003Q00F (shortNegativeNodes16 (13:Fin 16))).re (shortNegativeR003Q00L (13:Fin 16)) (shortNegativeR003Q00U (13:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q00Point14 : containedInReported (sampledFactoredPrimal shortNegativeR003Q00P shortNegativeR003Q00F (shortNegativeNodes16 (14:Fin 16))).re (shortNegativeR003Q00L (14:Fin 16)) (shortNegativeR003Q00U (14:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q00Point15 : containedInReported (sampledFactoredPrimal shortNegativeR003Q00P shortNegativeR003Q00F (shortNegativeNodes16 (15:Fin 16))).re (shortNegativeR003Q00L (15:Fin 16)) (shortNegativeR003Q00U (15:Fin 16))=true := by decide +kernel
theorem shortNegativeR003Q00Samples : ∀ k : Fin 16, containedInReported (sampledFactoredPrimal shortNegativeR003Q00P shortNegativeR003Q00F (shortNegativeNodes16 k)).re (shortNegativeR003Q00L k) (shortNegativeR003Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR003Q00Point00
  · exact shortNegativeR003Q00Point01
  · exact shortNegativeR003Q00Point02
  · exact shortNegativeR003Q00Point03
  · exact shortNegativeR003Q00Point04
  · exact shortNegativeR003Q00Point05
  · exact shortNegativeR003Q00Point06
  · exact shortNegativeR003Q00Point07
  · exact shortNegativeR003Q00Point08
  · exact shortNegativeR003Q00Point09
  · exact shortNegativeR003Q00Point10
  · exact shortNegativeR003Q00Point11
  · exact shortNegativeR003Q00Point12
  · exact shortNegativeR003Q00Point13
  · exact shortNegativeR003Q00Point14
  · exact shortNegativeR003Q00Point15

theorem shortNegativeR003Q00Bound {t a : ℝ} (tl : ((363/400):ℝ)≤t) (tu : t≤((91/100):ℝ)) (al : ((1001065609200107/1649267441664000):ℝ)≤a) (au : a≤((1002676221936107/1649267441664000):ℝ)) : (((-1627565826149600786627626784516373/2596148429267413814265248164610048):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1917723350990063124510653282231379/10384593717069655257060992658440192):ℚ):ℝ) := by
  have ts : shortNegativeR003Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1001065609200107/1649267441664000) (1002676221936107/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR003Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR003Q00F_ok n) ts asb
  exact factored_negative_16_samples 17310 ps fs shortNegativeNodes16Sound (by linarith) (by linarith) (shortNegativeStrip000Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR003Q00L shortNegativeR003Q00U (-1627565826149600786627626784516373/2596148429267413814265248164610048) (-1917723350990063124510653282231379/10384593717069655257060992658440192) shortNegativeR003Q00Samples (by decide +kernel)

def shortNegativeR003Q01T := Grid.ofRats (363/400) (91/100)
def shortNegativeR003Q01P : PrimalThetaParameters := ⟨⟨⟨69313394971749511879471,69859924510004800696990,true⟩,⟨0,0,true⟩⟩, ⟨⟨1154487301803620435112105,1156341770784956898040174,true⟩,⟨0,0,true⟩⟩, ⟨(-1488977870029063350826958),(-1485268932066459144450180),true⟩, ⟨5886822762403036634452918,5930817606362012453812417,true⟩⟩
theorem shortNegativeR003Q01P_ok : shortNegativeR003Q01P.encloses (primalThetaParameters shortNegativeR003Q01T (Grid.ofRats (1002676221936107/1649267441664000) (1004286834672107/1649267441664000))) := by decide +kernel

def shortNegativeR003Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨591567127116617778635595,592729807539890553342808,true⟩,⟨2465713076581876835023237,2470559249048210254787811,true⟩,⟨⟨696631888947606174802406,698486357928942637777982,true⟩,⟨986449545993321663333730,988304014974658126313359,true⟩⟩⟩
  | 1 => ⟨⟨8121388938413425766408,8233783741727831896909,true⟩,⟨591567127116617778635595,592729807539890553342808,true⟩,⟨⟨(-1166484655184487883901733),(-1160921248240615934002475),true⟩,⟨324780622668291876380088,330344029612163826267832,true⟩⟩⟩
  | 2 => ⟨⟨6392549539421138446,6609530418640484020,true⟩,⟨8121388938413425766408,8233783741727831896909,true⟩,⟨⟨75449108229581592849603,84721453135989029661088,true⟩,⟨(-1210906451100929670115814),(-1201634106194522233288830),true⟩⟩⟩
  | 3 => ⟨⟨288458731772436,306632989438919,true⟩,⟨6392549539421138446,6609530418640484020,true⟩,⟨⟨1103695327886842384551191,1116676610755785308266285,true⟩,⟨472037049355724826077866,485018332224667749784268,true⟩⟩⟩
  | 4 => ⟨⟨(-33613265120),35181599184,true⟩,⟨288458731772436,306632989438919,true⟩,⟨⟨(-830312076030167333768359),(-813621855198688923122100),true⟩,⟨878149077252466798086104,894839298083945208733252,true⟩⟩⟩
  | _ => ⟨⟨(-34359738258),34359738496,true⟩,⟨(-33613265120),35181599184,true⟩,⟨⟨(-571106189890745313031302),(-550707031096731415483626),true⟩,⟨(-1081126939975365033391280),(-1060727781181351135836583),true⟩⟩⟩
theorem shortNegativeR003Q01F_ok : ∀ n : Fin 6, (shortNegativeR003Q01F n).encloses (FactoredFrequency.build shortNegativeR003Q01T (Grid.ofRats (1002676221936107/1649267441664000) (1004286834672107/1649267441664000)) n) := by decide +kernel
def shortNegativeR003Q01L : ℕ → ℚ
  | 0 => (2559909/1000000)
  | 1 => (313471/100000)
  | 2 => (1539733/500000)
  | 3 => (2725827/1000000)
  | 4 => (556701/250000)
  | 5 => (801561/500000)
  | 6 => (160143/200000)
  | 7 => (-246721/1000000)
  | 8 => (-786779/500000)
  | 9 => (-1557099/500000)
  | 10 => (-4634417/1000000)
  | 11 => (-5683153/1000000)
  | 12 => (-5630937/1000000)
  | 13 => (-4168617/1000000)
  | 14 => (-1676671/1000000)
  | 15 => (101601/125000)
  | _ => 0
def shortNegativeR003Q01U : ℕ → ℚ
  | 0 => (1409023/500000)
  | 1 => (1698891/500000)
  | 2 => (3341069/1000000)
  | 3 => (2978991/1000000)
  | 4 => (1234671/500000)
  | 5 => (916811/500000)
  | 6 => (64813/62500)
  | 7 => (19483/1000000)
  | 8 => (-250613/200000)
  | 9 => (-1368439/500000)
  | 10 => (-1050013/250000)
  | 11 => (-5137023/1000000)
  | 12 => (-199077/40000)
  | 13 => (-3416807/1000000)
  | 14 => (-232431/250000)
  | 15 => (1456323/1000000)
  | _ => 0
private theorem shortNegativeR003Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR003Q01P shortNegativeR003Q01F (shortNegativeNodes16 (0:Fin 16))).re (shortNegativeR003Q01L (0:Fin 16)) (shortNegativeR003Q01U (0:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR003Q01P shortNegativeR003Q01F (shortNegativeNodes16 (1:Fin 16))).re (shortNegativeR003Q01L (1:Fin 16)) (shortNegativeR003Q01U (1:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR003Q01P shortNegativeR003Q01F (shortNegativeNodes16 (2:Fin 16))).re (shortNegativeR003Q01L (2:Fin 16)) (shortNegativeR003Q01U (2:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR003Q01P shortNegativeR003Q01F (shortNegativeNodes16 (3:Fin 16))).re (shortNegativeR003Q01L (3:Fin 16)) (shortNegativeR003Q01U (3:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR003Q01P shortNegativeR003Q01F (shortNegativeNodes16 (4:Fin 16))).re (shortNegativeR003Q01L (4:Fin 16)) (shortNegativeR003Q01U (4:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR003Q01P shortNegativeR003Q01F (shortNegativeNodes16 (5:Fin 16))).re (shortNegativeR003Q01L (5:Fin 16)) (shortNegativeR003Q01U (5:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR003Q01P shortNegativeR003Q01F (shortNegativeNodes16 (6:Fin 16))).re (shortNegativeR003Q01L (6:Fin 16)) (shortNegativeR003Q01U (6:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR003Q01P shortNegativeR003Q01F (shortNegativeNodes16 (7:Fin 16))).re (shortNegativeR003Q01L (7:Fin 16)) (shortNegativeR003Q01U (7:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR003Q01P shortNegativeR003Q01F (shortNegativeNodes16 (8:Fin 16))).re (shortNegativeR003Q01L (8:Fin 16)) (shortNegativeR003Q01U (8:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR003Q01P shortNegativeR003Q01F (shortNegativeNodes16 (9:Fin 16))).re (shortNegativeR003Q01L (9:Fin 16)) (shortNegativeR003Q01U (9:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR003Q01P shortNegativeR003Q01F (shortNegativeNodes16 (10:Fin 16))).re (shortNegativeR003Q01L (10:Fin 16)) (shortNegativeR003Q01U (10:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR003Q01P shortNegativeR003Q01F (shortNegativeNodes16 (11:Fin 16))).re (shortNegativeR003Q01L (11:Fin 16)) (shortNegativeR003Q01U (11:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q01Point12 : containedInReported (sampledFactoredPrimal shortNegativeR003Q01P shortNegativeR003Q01F (shortNegativeNodes16 (12:Fin 16))).re (shortNegativeR003Q01L (12:Fin 16)) (shortNegativeR003Q01U (12:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q01Point13 : containedInReported (sampledFactoredPrimal shortNegativeR003Q01P shortNegativeR003Q01F (shortNegativeNodes16 (13:Fin 16))).re (shortNegativeR003Q01L (13:Fin 16)) (shortNegativeR003Q01U (13:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q01Point14 : containedInReported (sampledFactoredPrimal shortNegativeR003Q01P shortNegativeR003Q01F (shortNegativeNodes16 (14:Fin 16))).re (shortNegativeR003Q01L (14:Fin 16)) (shortNegativeR003Q01U (14:Fin 16))=true := by decide +kernel
private theorem shortNegativeR003Q01Point15 : containedInReported (sampledFactoredPrimal shortNegativeR003Q01P shortNegativeR003Q01F (shortNegativeNodes16 (15:Fin 16))).re (shortNegativeR003Q01L (15:Fin 16)) (shortNegativeR003Q01U (15:Fin 16))=true := by decide +kernel
theorem shortNegativeR003Q01Samples : ∀ k : Fin 16, containedInReported (sampledFactoredPrimal shortNegativeR003Q01P shortNegativeR003Q01F (shortNegativeNodes16 k)).re (shortNegativeR003Q01L k) (shortNegativeR003Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR003Q01Point00
  · exact shortNegativeR003Q01Point01
  · exact shortNegativeR003Q01Point02
  · exact shortNegativeR003Q01Point03
  · exact shortNegativeR003Q01Point04
  · exact shortNegativeR003Q01Point05
  · exact shortNegativeR003Q01Point06
  · exact shortNegativeR003Q01Point07
  · exact shortNegativeR003Q01Point08
  · exact shortNegativeR003Q01Point09
  · exact shortNegativeR003Q01Point10
  · exact shortNegativeR003Q01Point11
  · exact shortNegativeR003Q01Point12
  · exact shortNegativeR003Q01Point13
  · exact shortNegativeR003Q01Point14
  · exact shortNegativeR003Q01Point15

theorem shortNegativeR003Q01Bound {t a : ℝ} (tl : ((363/400):ℝ)≤t) (tu : t≤((91/100):ℝ)) (al : ((1002676221936107/1649267441664000):ℝ)≤a) (au : a≤((1004286834672107/1649267441664000):ℝ)) : (((-1627565826149600786627626784516373/2596148429267413814265248164610048):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1917723350990063124510653282231379/10384593717069655257060992658440192):ℚ):ℝ) := by
  have ts : shortNegativeR003Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1002676221936107/1649267441664000) (1004286834672107/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR003Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR003Q01F_ok n) ts asb
  exact factored_negative_16_samples 17310 ps fs shortNegativeNodes16Sound (by linarith) (by linarith) (shortNegativeStrip000Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR003Q01L shortNegativeR003Q01U (-1627565826149600786627626784516373/2596148429267413814265248164610048) (-1917723350990063124510653282231379/10384593717069655257060992658440192) shortNegativeR003Q01Samples (by decide +kernel)

theorem short_original_negative_003 {t a : ℝ} (tb : RealMem negative_003.t t) (ab : RealMem negative_003.a a) : RealMem negative_003.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((363/400):ℝ) ((91/100):ℝ) := by simpa [negative_003,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((363/400):ℝ)<((91/100):ℝ)) tB
  have aB : a∈Icc ((1001065609200107/1649267441664000):ℝ) ((1004286834672107/1649267441664000):ℝ) := by simpa [negative_003,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((1001065609200107/1649267441664000):ℝ)<((1004286834672107/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR003Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_003,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR003Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_003,RealMem] using v

def shortNegativeR004Q00T := Grid.ofRats (91/100) (73/80)
def shortNegativeR004Q00P : PrimalThetaParameters := ⟨⟨⟨68771141054216780992176,69313394971818231357150,true⟩,⟨0,0,true⟩⟩, ⟨⟨1154290737847461202013434,1156145206828797664941503,true⟩,⟨0,0,true⟩⟩, ⟨(-1489370997941381817024301),(-1485662059978777610647522),true⟩, ⟨5876286141831515692829946,5920048641684102472172498,true⟩⟩
theorem shortNegativeR004Q00P_ok : shortNegativeR004Q00P.encloses (primalThetaParameters shortNegativeR004Q00T (Grid.ofRats (66833700363939/109951162777600) (66941074546339/109951162777600))) := by decide +kernel

def shortNegativeR004Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨590406727371303220424390,591567127116686498133674,true⟩,⟨2470559249048141535222294,2475414946299737212120575,true⟩,⟨⟨696792421161542277757739,698646890142878740733297,true⟩,⟨986336114088353874295644,988190583069690337275273,true⟩⟩⟩
  | 1 => ⟨⟨8010528374126757293924,8121388938482145243552,true⟩,⟨590406727371303220424390,591567127116686498133674,true⟩,⟨⟨(-1166324737848269615202264),(-1160761330904397665302889),true⟩,⟨325348216659125817430521,330911623602997767318387,true⟩⟩⟩
  | 2 => ⟨⟨6182691878281041158,6392549608140615184,true⟩,⟨8010528374126757293924,8121388938482145243552,true⟩,⟨⟨74468420965581694903516,83740765871989131715103,true⟩,⟨(-1210971159358147783785125),(-1201698814451740346958025),true⟩⟩⟩
  | 3 => ⟨⟨271422378117078,288527451249173,true⟩,⟨6182691878281041158,6392549608140615184,true⟩,⟨⟨1104239248464097154140954,1117220531333040077855970,true⟩,⟨470773173469630144062070,483754456338573067768368,true⟩⟩⟩
  | 4 => ⟨⟨(-33681737543),35106211617,true⟩,⟨271422378117078,288527451249173,true⟩,⟨⟨(-829013949546892462579856),(-812323728715414051933202),true⟩,⟨879350948948065909488963,896041169779544320136537,true⟩⟩⟩
  | _ => ⟨⟨(-34359738272),34359738479,true⟩,⟨(-33681737543),35106211617,true⟩,⟨⟨(-573020680485081449521015),(-552621521691067551973275),true⟩,⟨(-1080122027755256109517720),(-1059722868961242211962997),true⟩⟩⟩
theorem shortNegativeR004Q00F_ok : ∀ n : Fin 6, (shortNegativeR004Q00F n).encloses (FactoredFrequency.build shortNegativeR004Q00T (Grid.ofRats (66833700363939/109951162777600) (66941074546339/109951162777600)) n) := by decide +kernel
def shortNegativeR004Q00L : ℕ → ℚ
  | 0 => (627983/250000)
  | 1 => (3093037/1000000)
  | 2 => (380803/125000)
  | 3 => (337369/125000)
  | 4 => (2203099/1000000)
  | 5 => (790323/500000)
  | 6 => (778889/1000000)
  | 7 => (-267273/1000000)
  | 8 => (-795041/500000)
  | 9 => (-3122853/1000000)
  | 10 => (-4631503/1000000)
  | 11 => (-708621/125000)
  | 12 => (-1122883/200000)
  | 13 => (-4165207/1000000)
  | 14 => (-1697813/1000000)
  | 15 => (385771/500000)
  | _ => 0
def shortNegativeR004Q00U : ℕ → ℚ
  | 0 => (2769631/1000000)
  | 1 => (671163/200000)
  | 2 => (661567/200000)
  | 3 => (1476029/500000)
  | 4 => (2445699/1000000)
  | 5 => (362259/200000)
  | 6 => (507667/500000)
  | 7 => (-169/250000)
  | 8 => (-634693/500000)
  | 9 => (-1372937/500000)
  | 10 => (-4198341/1000000)
  | 11 => (-5125269/1000000)
  | 12 => (-2481879/500000)
  | 13 => (-3418003/1000000)
  | 14 => (-238923/250000)
  | 15 => (1410697/1000000)
  | _ => 0
private theorem shortNegativeR004Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR004Q00P shortNegativeR004Q00F (shortNegativeNodes16 (0:Fin 16))).re (shortNegativeR004Q00L (0:Fin 16)) (shortNegativeR004Q00U (0:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR004Q00P shortNegativeR004Q00F (shortNegativeNodes16 (1:Fin 16))).re (shortNegativeR004Q00L (1:Fin 16)) (shortNegativeR004Q00U (1:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR004Q00P shortNegativeR004Q00F (shortNegativeNodes16 (2:Fin 16))).re (shortNegativeR004Q00L (2:Fin 16)) (shortNegativeR004Q00U (2:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR004Q00P shortNegativeR004Q00F (shortNegativeNodes16 (3:Fin 16))).re (shortNegativeR004Q00L (3:Fin 16)) (shortNegativeR004Q00U (3:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR004Q00P shortNegativeR004Q00F (shortNegativeNodes16 (4:Fin 16))).re (shortNegativeR004Q00L (4:Fin 16)) (shortNegativeR004Q00U (4:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR004Q00P shortNegativeR004Q00F (shortNegativeNodes16 (5:Fin 16))).re (shortNegativeR004Q00L (5:Fin 16)) (shortNegativeR004Q00U (5:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR004Q00P shortNegativeR004Q00F (shortNegativeNodes16 (6:Fin 16))).re (shortNegativeR004Q00L (6:Fin 16)) (shortNegativeR004Q00U (6:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR004Q00P shortNegativeR004Q00F (shortNegativeNodes16 (7:Fin 16))).re (shortNegativeR004Q00L (7:Fin 16)) (shortNegativeR004Q00U (7:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR004Q00P shortNegativeR004Q00F (shortNegativeNodes16 (8:Fin 16))).re (shortNegativeR004Q00L (8:Fin 16)) (shortNegativeR004Q00U (8:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR004Q00P shortNegativeR004Q00F (shortNegativeNodes16 (9:Fin 16))).re (shortNegativeR004Q00L (9:Fin 16)) (shortNegativeR004Q00U (9:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR004Q00P shortNegativeR004Q00F (shortNegativeNodes16 (10:Fin 16))).re (shortNegativeR004Q00L (10:Fin 16)) (shortNegativeR004Q00U (10:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR004Q00P shortNegativeR004Q00F (shortNegativeNodes16 (11:Fin 16))).re (shortNegativeR004Q00L (11:Fin 16)) (shortNegativeR004Q00U (11:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q00Point12 : containedInReported (sampledFactoredPrimal shortNegativeR004Q00P shortNegativeR004Q00F (shortNegativeNodes16 (12:Fin 16))).re (shortNegativeR004Q00L (12:Fin 16)) (shortNegativeR004Q00U (12:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q00Point13 : containedInReported (sampledFactoredPrimal shortNegativeR004Q00P shortNegativeR004Q00F (shortNegativeNodes16 (13:Fin 16))).re (shortNegativeR004Q00L (13:Fin 16)) (shortNegativeR004Q00U (13:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q00Point14 : containedInReported (sampledFactoredPrimal shortNegativeR004Q00P shortNegativeR004Q00F (shortNegativeNodes16 (14:Fin 16))).re (shortNegativeR004Q00L (14:Fin 16)) (shortNegativeR004Q00U (14:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q00Point15 : containedInReported (sampledFactoredPrimal shortNegativeR004Q00P shortNegativeR004Q00F (shortNegativeNodes16 (15:Fin 16))).re (shortNegativeR004Q00L (15:Fin 16)) (shortNegativeR004Q00U (15:Fin 16))=true := by decide +kernel
theorem shortNegativeR004Q00Samples : ∀ k : Fin 16, containedInReported (sampledFactoredPrimal shortNegativeR004Q00P shortNegativeR004Q00F (shortNegativeNodes16 k)).re (shortNegativeR004Q00L k) (shortNegativeR004Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR004Q00Point00
  · exact shortNegativeR004Q00Point01
  · exact shortNegativeR004Q00Point02
  · exact shortNegativeR004Q00Point03
  · exact shortNegativeR004Q00Point04
  · exact shortNegativeR004Q00Point05
  · exact shortNegativeR004Q00Point06
  · exact shortNegativeR004Q00Point07
  · exact shortNegativeR004Q00Point08
  · exact shortNegativeR004Q00Point09
  · exact shortNegativeR004Q00Point10
  · exact shortNegativeR004Q00Point11
  · exact shortNegativeR004Q00Point12
  · exact shortNegativeR004Q00Point13
  · exact shortNegativeR004Q00Point14
  · exact shortNegativeR004Q00Point15

theorem shortNegativeR004Q00Bound {t a : ℝ} (tl : ((91/100):ℝ)≤t) (tu : t≤((73/80):ℝ)) (al : ((66833700363939/109951162777600):ℝ)≤a) (au : a≤((66941074546339/109951162777600):ℝ)) : (((-420439307575482921754299270226013/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-135656853870550797712462081220701/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR004Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (66833700363939/109951162777600) (66941074546339/109951162777600)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR004Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR004Q00F_ok n) ts asb
  exact factored_negative_16_samples 17310 ps fs shortNegativeNodes16Sound (by linarith) (by linarith) (shortNegativeStrip000Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR004Q00L shortNegativeR004Q00U (-420439307575482921754299270226013/649037107316853453566312041152512) (-135656853870550797712462081220701/649037107316853453566312041152512) shortNegativeR004Q00Samples (by decide +kernel)

def shortNegativeR004Q01T := Grid.ofRats (91/100) (73/80)
def shortNegativeR004Q01P : PrimalThetaParameters := ⟨⟨⟨68771141054216780992176,69313394971818231357150,true⟩,⟨0,0,true⟩⟩, ⟨⟨1156145206828728945461083,1157999675810065408389157,true⟩,⟨0,0,true⟩⟩, ⟨(-1485662059978846330128991),(-1481953122016242123752224),true⟩, ⟨5867409879105809426726748,5911055017598770404587169,true⟩⟩
theorem shortNegativeR004Q01P_ok : shortNegativeR004Q01P.encloses (primalThetaParameters shortNegativeR004Q01T (Grid.ofRats (66941074546339/109951162777600) (67048448728739/109951162777600))) := by decide +kernel

def shortNegativeR004Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨590406727371303220424390,591567127116686498133674,true⟩,⟨2470559249048141535222294,2475414946299737212120575,true⟩,⟨⟨695277157845303506341342,697131626826639969317229,true⟩,⟨987405240652693257335458,989259709634029720315464,true⟩⟩⟩
  | 1 => ⟨⟨8010528374126757293924,8121388938482145243552,true⟩,⟨590406727371303220424390,591567127116686498133674,true⟩,⟨⟨(-1167822446836757629222573),(-1162259039892885679323596),true⟩,⟨319990203036122261232058,325553609979994211119426,true⟩⟩⟩
  | 2 => ⟨⟨6182691878281041158,6392549608140615184,true⟩,⟨8010528374126757293924,8121388938482145243552,true⟩,⟨⟨83718476969228316613104,92990821875635753424787,true⟩,⟨(-1210328958056709786213833),(-1201056613150302349386771),true⟩⟩⟩
  | 3 => ⟨⟨271422378117078,288527451249173,true⟩,⟨6182691878281041158,6392549608140615184,true⟩,⟨⟨1099050518348785917249335,1112031801217728840964646,true⟩,⟨482672298040702899197853,495653580909645822904688,true⟩⟩⟩
  | 4 => ⟨⟨(-33681737543),35106211617,true⟩,⟨271422378117078,288527451249173,true⟩,⟨⟨(-841190729689532341294414),(-824500508858053930648115),true⟩,⟨867936700297774880407093,884626921129253291053983,true⟩⟩⟩
  | _ => ⟨⟨(-34359738272),34359738479,true⟩,⟨(-33681737543),35106211617,true⟩,⟨⟨(-554887769263554547407265),(-534488610469540649860303),true⟩,⟨(-1089466188326796229918626),(-1069067029532782332364306),true⟩⟩⟩
theorem shortNegativeR004Q01F_ok : ∀ n : Fin 6, (shortNegativeR004Q01F n).encloses (FactoredFrequency.build shortNegativeR004Q01T (Grid.ofRats (66941074546339/109951162777600) (67048448728739/109951162777600)) n) := by decide +kernel
def shortNegativeR004Q01L : ℕ → ℚ
  | 0 => (24871/10000)
  | 1 => (1537553/500000)
  | 2 => (3034859/1000000)
  | 3 => (2692149/1000000)
  | 4 => (2199917/1000000)
  | 5 => (158069/100000)
  | 6 => (195587/250000)
  | 7 => (-129927/500000)
  | 8 => (-1578383/1000000)
  | 9 => (-621483/200000)
  | 10 => (-2306913/500000)
  | 11 => (-5654809/1000000)
  | 12 => (-5610533/1000000)
  | 13 => (-4175861/1000000)
  | 14 => (-1720969/1000000)
  | 15 => (148819/200000)
  | _ => 0
def shortNegativeR004Q01U : ℕ → ℚ
  | 0 => (2743993/1000000)
  | 1 => (1668627/500000)
  | 2 => (411977/125000)
  | 3 => (736239/250000)
  | 4 => (244233/100000)
  | 5 => (905611/500000)
  | 6 => (509351/500000)
  | 7 => (821/125000)
  | 8 => (-629017/500000)
  | 9 => (-2730891/1000000)
  | 10 => (-4182993/1000000)
  | 11 => (-5113811/1000000)
  | 12 => (-4962691/1000000)
  | 13 => (-428969/125000)
  | 14 => (-981849/1000000)
  | 15 => (1380249/1000000)
  | _ => 0
private theorem shortNegativeR004Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR004Q01P shortNegativeR004Q01F (shortNegativeNodes16 (0:Fin 16))).re (shortNegativeR004Q01L (0:Fin 16)) (shortNegativeR004Q01U (0:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR004Q01P shortNegativeR004Q01F (shortNegativeNodes16 (1:Fin 16))).re (shortNegativeR004Q01L (1:Fin 16)) (shortNegativeR004Q01U (1:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR004Q01P shortNegativeR004Q01F (shortNegativeNodes16 (2:Fin 16))).re (shortNegativeR004Q01L (2:Fin 16)) (shortNegativeR004Q01U (2:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR004Q01P shortNegativeR004Q01F (shortNegativeNodes16 (3:Fin 16))).re (shortNegativeR004Q01L (3:Fin 16)) (shortNegativeR004Q01U (3:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR004Q01P shortNegativeR004Q01F (shortNegativeNodes16 (4:Fin 16))).re (shortNegativeR004Q01L (4:Fin 16)) (shortNegativeR004Q01U (4:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR004Q01P shortNegativeR004Q01F (shortNegativeNodes16 (5:Fin 16))).re (shortNegativeR004Q01L (5:Fin 16)) (shortNegativeR004Q01U (5:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR004Q01P shortNegativeR004Q01F (shortNegativeNodes16 (6:Fin 16))).re (shortNegativeR004Q01L (6:Fin 16)) (shortNegativeR004Q01U (6:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR004Q01P shortNegativeR004Q01F (shortNegativeNodes16 (7:Fin 16))).re (shortNegativeR004Q01L (7:Fin 16)) (shortNegativeR004Q01U (7:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR004Q01P shortNegativeR004Q01F (shortNegativeNodes16 (8:Fin 16))).re (shortNegativeR004Q01L (8:Fin 16)) (shortNegativeR004Q01U (8:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR004Q01P shortNegativeR004Q01F (shortNegativeNodes16 (9:Fin 16))).re (shortNegativeR004Q01L (9:Fin 16)) (shortNegativeR004Q01U (9:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR004Q01P shortNegativeR004Q01F (shortNegativeNodes16 (10:Fin 16))).re (shortNegativeR004Q01L (10:Fin 16)) (shortNegativeR004Q01U (10:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR004Q01P shortNegativeR004Q01F (shortNegativeNodes16 (11:Fin 16))).re (shortNegativeR004Q01L (11:Fin 16)) (shortNegativeR004Q01U (11:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q01Point12 : containedInReported (sampledFactoredPrimal shortNegativeR004Q01P shortNegativeR004Q01F (shortNegativeNodes16 (12:Fin 16))).re (shortNegativeR004Q01L (12:Fin 16)) (shortNegativeR004Q01U (12:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q01Point13 : containedInReported (sampledFactoredPrimal shortNegativeR004Q01P shortNegativeR004Q01F (shortNegativeNodes16 (13:Fin 16))).re (shortNegativeR004Q01L (13:Fin 16)) (shortNegativeR004Q01U (13:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q01Point14 : containedInReported (sampledFactoredPrimal shortNegativeR004Q01P shortNegativeR004Q01F (shortNegativeNodes16 (14:Fin 16))).re (shortNegativeR004Q01L (14:Fin 16)) (shortNegativeR004Q01U (14:Fin 16))=true := by decide +kernel
private theorem shortNegativeR004Q01Point15 : containedInReported (sampledFactoredPrimal shortNegativeR004Q01P shortNegativeR004Q01F (shortNegativeNodes16 (15:Fin 16))).re (shortNegativeR004Q01L (15:Fin 16)) (shortNegativeR004Q01U (15:Fin 16))=true := by decide +kernel
theorem shortNegativeR004Q01Samples : ∀ k : Fin 16, containedInReported (sampledFactoredPrimal shortNegativeR004Q01P shortNegativeR004Q01F (shortNegativeNodes16 k)).re (shortNegativeR004Q01L k) (shortNegativeR004Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR004Q01Point00
  · exact shortNegativeR004Q01Point01
  · exact shortNegativeR004Q01Point02
  · exact shortNegativeR004Q01Point03
  · exact shortNegativeR004Q01Point04
  · exact shortNegativeR004Q01Point05
  · exact shortNegativeR004Q01Point06
  · exact shortNegativeR004Q01Point07
  · exact shortNegativeR004Q01Point08
  · exact shortNegativeR004Q01Point09
  · exact shortNegativeR004Q01Point10
  · exact shortNegativeR004Q01Point11
  · exact shortNegativeR004Q01Point12
  · exact shortNegativeR004Q01Point13
  · exact shortNegativeR004Q01Point14
  · exact shortNegativeR004Q01Point15

theorem shortNegativeR004Q01Bound {t a : ℝ} (tl : ((91/100):ℝ)≤t) (tu : t≤((73/80):ℝ)) (al : ((66941074546339/109951162777600):ℝ)≤a) (au : a≤((67048448728739/109951162777600):ℝ)) : (((-420439307575482921754299270226013/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-135656853870550797712462081220701/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR004Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (66941074546339/109951162777600) (67048448728739/109951162777600)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR004Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR004Q01F_ok n) ts asb
  exact factored_negative_16_samples 17310 ps fs shortNegativeNodes16Sound (by linarith) (by linarith) (shortNegativeStrip000Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR004Q01L shortNegativeR004Q01U (-420439307575482921754299270226013/649037107316853453566312041152512) (-135656853870550797712462081220701/649037107316853453566312041152512) shortNegativeR004Q01Samples (by decide +kernel)

theorem short_original_negative_004 {t a : ℝ} (tb : RealMem negative_004.t t) (ab : RealMem negative_004.a a) : RealMem negative_004.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((91/100):ℝ) ((73/80):ℝ) := by simpa [negative_004,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((91/100):ℝ)<((73/80):ℝ)) tB
  have aB : a∈Icc ((66833700363939/109951162777600):ℝ) ((67048448728739/109951162777600):ℝ) := by simpa [negative_004,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((66833700363939/109951162777600):ℝ)<((67048448728739/109951162777600):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR004Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_004,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR004Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_004,RealMem] using v

def shortNegativeR005Q00T := Grid.ofRats (73/80) (183/200)
def shortNegativeR005Q00P : PrimalThetaParameters := ⟨⟨⟨68233129308218127917223,68771141054285500469856,true⟩,⟨0,0,true⟩⟩, ⟨⟨1155955996650295706114643,1157810465631632169042717,true⟩,⟨0,0,true⟩⟩, ⟨(-1486040480335712808821872),(-1482331542373108602445103),true⟩, ⟨5856916526909050304966973,5900331588936569208641979,true⟩⟩
theorem shortNegativeR005Q00P_ok : shortNegativeR005Q00P.encloses (primalThetaParameters shortNegativeR005Q00T (Grid.ofRats (1003951788499499/1649267441664000) (1005562401235499/1649267441664000))) := by decide +kernel

def shortNegativeR005Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨589248603830171083876663,590406727371371939922461,true⟩,⟨2475414946299668492554907,2480280187056771098783225,true⟩,⟨⟨695431834213084752860751,697286303194421215836480,true⟩,⟨987296264908604680347030,989150733889941143326795,true⟩⟩⟩
  | 1 => ⟨⟨7901181105756231400994,8010528374195476771067,true⟩,⟨589248603830171083876663,590406727371371939922461,true⟩,⟨⟨(-1167670766366028625166536),(-1162107359422156675267579),true⟩,⟨320537192481618796715069,326100599425490746602431,true⟩⟩⟩
  | 2 => ⟨⟨5979723524361934927,6182691947000517895,true⟩,⟨7901181105756231400994,8010528374195476771067,true⟩,⟨⟨82774929146302492620478,92047274052709929432108,true⟩,⟨(-1210397731240041026218199),(-1201125386333633589391177),true⟩⟩⟩
  | 3 => ⟨⟨255392070548822,271491097593815,true⟩,⟨5979723524361934927,6182691947000517895,true⟩,⟨⟨1099585770393234476753891,1112567053262177400469180,true⟩,⟨481460799314759207566871,494442082183702131273665,true⟩⟩⟩
  | 4 => ⟨⟨(-33743929134),35037739194,true⟩,⟨255392070548822,271491097593815,true⟩,⟨⟨(-839955574238491836384319),(-823265353407013425738461),true⟩,⟨869108976013521864548815,885799196845000275195297,true⟩⟩⟩
  | _ => ⟨⟨(-34359738285),34359738465,true⟩,⟨(-33743929134),35037739194,true⟩,⟨⟨(-556745049079031810763038),(-536345890285017913216332),true⟩,⟨(-1088526842754916193013096),(-1068127683960902295459070),true⟩⟩⟩
theorem shortNegativeR005Q00F_ok : ∀ n : Fin 6, (shortNegativeR005Q00F n).encloses (FactoredFrequency.build shortNegativeR005Q00T (Grid.ofRats (1003951788499499/1649267441664000) (1005562401235499/1649267441664000)) n) := by decide +kernel
def shortNegativeR005Q00L : ℕ → ℚ
  | 0 => (1219773/500000)
  | 1 => (758389/250000)
  | 2 => (3001753/1000000)
  | 3 => (2665153/1000000)
  | 4 => (217611/100000)
  | 5 => (1558163/1000000)
  | 6 => (760533/1000000)
  | 7 => (-280333/1000000)
  | 8 => (-797399/500000)
  | 9 => (-124639/40000)
  | 10 => (-4610909/1000000)
  | 11 => (-22563/4000)
  | 12 => (-2797077/500000)
  | 13 => (-4172363/1000000)
  | 14 => (-1741659/1000000)
  | 15 => (703421/1000000)
  | _ => 0
def shortNegativeR005Q00U : ℕ → ℚ
  | 0 => (673999/250000)
  | 1 => (205963/62500)
  | 2 => (652503/200000)
  | 3 => (2917897/1000000)
  | 4 => (1209289/500000)
  | 5 => (1788837/1000000)
  | 6 => (124629/125000)
  | 7 => (-1679/125000)
  | 8 => (-637127/500000)
  | 9 => (-2739797/1000000)
  | 10 => (-167251/40000)
  | 11 => (-5102161/1000000)
  | 12 => (-4949631/1000000)
  | 13 => (-858201/250000)
  | 14 => (-125913/125000)
  | 15 => (667637/500000)
  | _ => 0
private theorem shortNegativeR005Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR005Q00P shortNegativeR005Q00F (shortNegativeNodes16 (0:Fin 16))).re (shortNegativeR005Q00L (0:Fin 16)) (shortNegativeR005Q00U (0:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR005Q00P shortNegativeR005Q00F (shortNegativeNodes16 (1:Fin 16))).re (shortNegativeR005Q00L (1:Fin 16)) (shortNegativeR005Q00U (1:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR005Q00P shortNegativeR005Q00F (shortNegativeNodes16 (2:Fin 16))).re (shortNegativeR005Q00L (2:Fin 16)) (shortNegativeR005Q00U (2:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR005Q00P shortNegativeR005Q00F (shortNegativeNodes16 (3:Fin 16))).re (shortNegativeR005Q00L (3:Fin 16)) (shortNegativeR005Q00U (3:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR005Q00P shortNegativeR005Q00F (shortNegativeNodes16 (4:Fin 16))).re (shortNegativeR005Q00L (4:Fin 16)) (shortNegativeR005Q00U (4:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR005Q00P shortNegativeR005Q00F (shortNegativeNodes16 (5:Fin 16))).re (shortNegativeR005Q00L (5:Fin 16)) (shortNegativeR005Q00U (5:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR005Q00P shortNegativeR005Q00F (shortNegativeNodes16 (6:Fin 16))).re (shortNegativeR005Q00L (6:Fin 16)) (shortNegativeR005Q00U (6:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR005Q00P shortNegativeR005Q00F (shortNegativeNodes16 (7:Fin 16))).re (shortNegativeR005Q00L (7:Fin 16)) (shortNegativeR005Q00U (7:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR005Q00P shortNegativeR005Q00F (shortNegativeNodes16 (8:Fin 16))).re (shortNegativeR005Q00L (8:Fin 16)) (shortNegativeR005Q00U (8:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR005Q00P shortNegativeR005Q00F (shortNegativeNodes16 (9:Fin 16))).re (shortNegativeR005Q00L (9:Fin 16)) (shortNegativeR005Q00U (9:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR005Q00P shortNegativeR005Q00F (shortNegativeNodes16 (10:Fin 16))).re (shortNegativeR005Q00L (10:Fin 16)) (shortNegativeR005Q00U (10:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR005Q00P shortNegativeR005Q00F (shortNegativeNodes16 (11:Fin 16))).re (shortNegativeR005Q00L (11:Fin 16)) (shortNegativeR005Q00U (11:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q00Point12 : containedInReported (sampledFactoredPrimal shortNegativeR005Q00P shortNegativeR005Q00F (shortNegativeNodes16 (12:Fin 16))).re (shortNegativeR005Q00L (12:Fin 16)) (shortNegativeR005Q00U (12:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q00Point13 : containedInReported (sampledFactoredPrimal shortNegativeR005Q00P shortNegativeR005Q00F (shortNegativeNodes16 (13:Fin 16))).re (shortNegativeR005Q00L (13:Fin 16)) (shortNegativeR005Q00U (13:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q00Point14 : containedInReported (sampledFactoredPrimal shortNegativeR005Q00P shortNegativeR005Q00F (shortNegativeNodes16 (14:Fin 16))).re (shortNegativeR005Q00L (14:Fin 16)) (shortNegativeR005Q00U (14:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q00Point15 : containedInReported (sampledFactoredPrimal shortNegativeR005Q00P shortNegativeR005Q00F (shortNegativeNodes16 (15:Fin 16))).re (shortNegativeR005Q00L (15:Fin 16)) (shortNegativeR005Q00U (15:Fin 16))=true := by decide +kernel
theorem shortNegativeR005Q00Samples : ∀ k : Fin 16, containedInReported (sampledFactoredPrimal shortNegativeR005Q00P shortNegativeR005Q00F (shortNegativeNodes16 k)).re (shortNegativeR005Q00L k) (shortNegativeR005Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR005Q00Point00
  · exact shortNegativeR005Q00Point01
  · exact shortNegativeR005Q00Point02
  · exact shortNegativeR005Q00Point03
  · exact shortNegativeR005Q00Point04
  · exact shortNegativeR005Q00Point05
  · exact shortNegativeR005Q00Point06
  · exact shortNegativeR005Q00Point07
  · exact shortNegativeR005Q00Point08
  · exact shortNegativeR005Q00Point09
  · exact shortNegativeR005Q00Point10
  · exact shortNegativeR005Q00Point11
  · exact shortNegativeR005Q00Point12
  · exact shortNegativeR005Q00Point13
  · exact shortNegativeR005Q00Point14
  · exact shortNegativeR005Q00Point15

theorem shortNegativeR005Q00Bound {t a : ℝ} (tl : ((73/80):ℝ)≤t) (tu : t≤((183/200):ℝ)) (al : ((1003951788499499/1649267441664000):ℝ)≤a) (au : a≤((1005562401235499/1649267441664000):ℝ)) : (((-3471279139182867311923862042433465/5192296858534827628530496329220096):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2421524725055440975430846819053425/10384593717069655257060992658440192):ℚ):ℝ) := by
  have ts : shortNegativeR005Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1003951788499499/1649267441664000) (1005562401235499/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR005Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR005Q00F_ok n) ts asb
  exact factored_negative_16_samples 17310 ps fs shortNegativeNodes16Sound (by linarith) (by linarith) (shortNegativeStrip000Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR005Q00L shortNegativeR005Q00U (-3471279139182867311923862042433465/5192296858534827628530496329220096) (-2421524725055440975430846819053425/10384593717069655257060992658440192) shortNegativeR005Q00Samples (by decide +kernel)

def shortNegativeR005Q01T := Grid.ofRats (73/80) (183/200)
def shortNegativeR005Q01P : PrimalThetaParameters := ⟨⟨⟨68233129308218127917223,68771141054285500469856,true⟩,⟨0,0,true⟩⟩, ⟨⟨1157810465631563449562292,1159664934612899912490372,true⟩,⟨0,0,true⟩⟩, ⟨(-1482331542373177321926563),(-1478622604410573115549806),true⟩, ⟨5848074701327352021841308,5891373399621066244587834,true⟩⟩
theorem shortNegativeR005Q01P_ok : shortNegativeR005Q01P.encloses (primalThetaParameters shortNegativeR005Q01T (Grid.ofRats (1005562401235499/1649267441664000) (1007173013971499/1649267441664000))) := by decide +kernel

def shortNegativeR005Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨589248603830171083876663,590406727371371939922461,true⟩,⟨2475414946299668492554907,2480280187056771098783225,true⟩,⟨⟨693915099645308130253499,695769568626644593229229,true⟩,⟨988363303229859598416780,990217772211196061396607,true⟩⟩⟩
  | 1 => ⟨⟨7901181105756231400994,8010528374195476771067,true⟩,⟨589248603830171083876663,590406727371371939922461,true⟩,⟨⟨(-1169146321123702363404879),(-1163582914179830413505679),true⟩,⟨315173035478361352890762,320736442422233302778282,true⟩⟩⟩
  | 2 => ⟨⟨5979723524361934927,6182691947000517895,true⟩,⟨7901181105756231400994,8010528374195476771067,true⟩,⟨⟨92020342730437066137563,101292687636844502948850,true⟩,⟨(-1209691837310000919419562),(-1200419492403593482593020),true⟩⟩⟩
  | 3 => ⟨⟨255392070548822,271491097593815,true⟩,⟨5979723524361934927,6182691947000517895,true⟩,⟨⟨1094282548468809397761811,1107263831337752321477344,true⟩,⟨493309340279272192797466,506290623148215116504729,true⟩⟩⟩
  | 4 => ⟨⟨(-33743929134),35037739194,true⟩,⟨255392070548822,271491097593815,true⟩,⟨⟨(-851989917240491515726954),(-835299696409013105080581),true⟩,⟨857544650032165199682065,874234870863643610328739,true⟩⟩⟩
  | _ => ⟨⟨(-34359738285),34359738465,true⟩,⟨(-33743929134),35037739194,true⟩,⟨⟨(-538472640497833058781331),(-518073481703819161234344),true⟩,⟨(-1097595188292898049739916),(-1077196029498884152185232),true⟩⟩⟩
theorem shortNegativeR005Q01F_ok : ∀ n : Fin 6, (shortNegativeR005Q01F n).encloses (FactoredFrequency.build shortNegativeR005Q01T (Grid.ofRats (1005562401235499/1649267441664000) (1007173013971499/1649267441664000)) n) := by decide +kernel
def shortNegativeR005Q01L : ℕ → ℚ
  | 0 => (1207447/500000)
  | 1 => (3015661/1000000)
  | 2 => (2990157/1000000)
  | 3 => (531661/200000)
  | 4 => (2172889/1000000)
  | 5 => (62327/40000)
  | 6 => (763961/1000000)
  | 7 => (-272957/1000000)
  | 8 => (-791583/500000)
  | 9 => (-387579/125000)
  | 10 => (-4593343/1000000)
  | 11 => (-5626649/1000000)
  | 12 => (-174693/31250)
  | 13 => (-4182721/1000000)
  | 14 => (-1764401/1000000)
  | 15 => (338161/500000)
  | _ => 0
def shortNegativeR005Q01U : ℕ → ℚ
  | 0 => (1335271/500000)
  | 1 => (1638441/500000)
  | 2 => (1625231/500000)
  | 3 => (1455373/500000)
  | 4 => (2415167/1000000)
  | 5 => (178873/100000)
  | 6 => (500183/500000)
  | 7 => (-3141/500000)
  | 8 => (-1262969/1000000)
  | 9 => (-544981/200000)
  | 10 => (-2083011/500000)
  | 11 => (-5090743/1000000)
  | 12 => (-4948453/1000000)
  | 13 => (-1723121/500000)
  | 14 => (-258259/250000)
  | 15 => (326297/250000)
  | _ => 0
private theorem shortNegativeR005Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR005Q01P shortNegativeR005Q01F (shortNegativeNodes16 (0:Fin 16))).re (shortNegativeR005Q01L (0:Fin 16)) (shortNegativeR005Q01U (0:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR005Q01P shortNegativeR005Q01F (shortNegativeNodes16 (1:Fin 16))).re (shortNegativeR005Q01L (1:Fin 16)) (shortNegativeR005Q01U (1:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR005Q01P shortNegativeR005Q01F (shortNegativeNodes16 (2:Fin 16))).re (shortNegativeR005Q01L (2:Fin 16)) (shortNegativeR005Q01U (2:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR005Q01P shortNegativeR005Q01F (shortNegativeNodes16 (3:Fin 16))).re (shortNegativeR005Q01L (3:Fin 16)) (shortNegativeR005Q01U (3:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR005Q01P shortNegativeR005Q01F (shortNegativeNodes16 (4:Fin 16))).re (shortNegativeR005Q01L (4:Fin 16)) (shortNegativeR005Q01U (4:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR005Q01P shortNegativeR005Q01F (shortNegativeNodes16 (5:Fin 16))).re (shortNegativeR005Q01L (5:Fin 16)) (shortNegativeR005Q01U (5:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR005Q01P shortNegativeR005Q01F (shortNegativeNodes16 (6:Fin 16))).re (shortNegativeR005Q01L (6:Fin 16)) (shortNegativeR005Q01U (6:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR005Q01P shortNegativeR005Q01F (shortNegativeNodes16 (7:Fin 16))).re (shortNegativeR005Q01L (7:Fin 16)) (shortNegativeR005Q01U (7:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR005Q01P shortNegativeR005Q01F (shortNegativeNodes16 (8:Fin 16))).re (shortNegativeR005Q01L (8:Fin 16)) (shortNegativeR005Q01U (8:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR005Q01P shortNegativeR005Q01F (shortNegativeNodes16 (9:Fin 16))).re (shortNegativeR005Q01L (9:Fin 16)) (shortNegativeR005Q01U (9:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR005Q01P shortNegativeR005Q01F (shortNegativeNodes16 (10:Fin 16))).re (shortNegativeR005Q01L (10:Fin 16)) (shortNegativeR005Q01U (10:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR005Q01P shortNegativeR005Q01F (shortNegativeNodes16 (11:Fin 16))).re (shortNegativeR005Q01L (11:Fin 16)) (shortNegativeR005Q01U (11:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q01Point12 : containedInReported (sampledFactoredPrimal shortNegativeR005Q01P shortNegativeR005Q01F (shortNegativeNodes16 (12:Fin 16))).re (shortNegativeR005Q01L (12:Fin 16)) (shortNegativeR005Q01U (12:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q01Point13 : containedInReported (sampledFactoredPrimal shortNegativeR005Q01P shortNegativeR005Q01F (shortNegativeNodes16 (13:Fin 16))).re (shortNegativeR005Q01L (13:Fin 16)) (shortNegativeR005Q01U (13:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q01Point14 : containedInReported (sampledFactoredPrimal shortNegativeR005Q01P shortNegativeR005Q01F (shortNegativeNodes16 (14:Fin 16))).re (shortNegativeR005Q01L (14:Fin 16)) (shortNegativeR005Q01U (14:Fin 16))=true := by decide +kernel
private theorem shortNegativeR005Q01Point15 : containedInReported (sampledFactoredPrimal shortNegativeR005Q01P shortNegativeR005Q01F (shortNegativeNodes16 (15:Fin 16))).re (shortNegativeR005Q01L (15:Fin 16)) (shortNegativeR005Q01U (15:Fin 16))=true := by decide +kernel
theorem shortNegativeR005Q01Samples : ∀ k : Fin 16, containedInReported (sampledFactoredPrimal shortNegativeR005Q01P shortNegativeR005Q01F (shortNegativeNodes16 k)).re (shortNegativeR005Q01L k) (shortNegativeR005Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR005Q01Point00
  · exact shortNegativeR005Q01Point01
  · exact shortNegativeR005Q01Point02
  · exact shortNegativeR005Q01Point03
  · exact shortNegativeR005Q01Point04
  · exact shortNegativeR005Q01Point05
  · exact shortNegativeR005Q01Point06
  · exact shortNegativeR005Q01Point07
  · exact shortNegativeR005Q01Point08
  · exact shortNegativeR005Q01Point09
  · exact shortNegativeR005Q01Point10
  · exact shortNegativeR005Q01Point11
  · exact shortNegativeR005Q01Point12
  · exact shortNegativeR005Q01Point13
  · exact shortNegativeR005Q01Point14
  · exact shortNegativeR005Q01Point15

theorem shortNegativeR005Q01Bound {t a : ℝ} (tl : ((73/80):ℝ)≤t) (tu : t≤((183/200):ℝ)) (al : ((1005562401235499/1649267441664000):ℝ)≤a) (au : a≤((1007173013971499/1649267441664000):ℝ)) : (((-3471279139182867311923862042433465/5192296858534827628530496329220096):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2421524725055440975430846819053425/10384593717069655257060992658440192):ℚ):ℝ) := by
  have ts : shortNegativeR005Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1005562401235499/1649267441664000) (1007173013971499/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR005Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR005Q01F_ok n) ts asb
  exact factored_negative_16_samples 17310 ps fs shortNegativeNodes16Sound (by linarith) (by linarith) (shortNegativeStrip000Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR005Q01L shortNegativeR005Q01U (-3471279139182867311923862042433465/5192296858534827628530496329220096) (-2421524725055440975430846819053425/10384593717069655257060992658440192) shortNegativeR005Q01Samples (by decide +kernel)

theorem short_original_negative_005 {t a : ℝ} (tb : RealMem negative_005.t t) (ab : RealMem negative_005.a a) : RealMem negative_005.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((73/80):ℝ) ((183/200):ℝ) := by simpa [negative_005,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((73/80):ℝ)<((183/200):ℝ)) tB
  have aB : a∈Icc ((1003951788499499/1649267441664000):ℝ) ((1007173013971499/1649267441664000):ℝ) := by simpa [negative_005,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((1003951788499499/1649267441664000):ℝ)<((1007173013971499/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR005Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_005,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR005Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_005,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_002
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_003
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_004
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_005
