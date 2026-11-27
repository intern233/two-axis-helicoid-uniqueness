import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip008

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR012Q00T := Grid.ofRats (189/200) (379/400)
def shortNegativeR012Q00P : PrimalThetaParameters := ⟨⟨⟨61610262312360220381888,62096053380993011070707,true⟩,⟨0,0,true⟩⟩, ⟨⟨1177313914601327782479796,1184731790526467475750902,true⟩,⟨0,0,true⟩⟩, ⟨(-1443324644433648656091431),(-1428488892583437989028905),true⟩, ⟨5565268262140799446875671,5682342704595980650213666,true⟩⟩
theorem shortNegativeR012Q00P_ok : shortNegativeR012Q00P.encloses (primalThetaParameters shortNegativeR012Q00T (Grid.ofRats (340833738081849/549755813888000) (342981221729849/549755813888000))) := by decide +kernel

def shortNegativeR012Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨574398112735797525054801,575527048760520661884196,true⟩,⟨2539414334180334347434019,2544405360891346491736854,true⟩,⟨⟨672779946806930041893462,680197822732069735212421,true⟩,⟨998221411969111392416472,1005639287894251085739962,true⟩⟩⟩
  | 1 => ⟨⟨6608351138382043136401,6699806470981934221342,true⟩,⟨574398112735797525054801,575527048760520661884196,true⟩,⟨⟨(-1193282787900535252805754),(-1171029160125253611877727),true⟩,⟨241872969583665300254975,264126597358946941170200,true⟩⟩⟩
  | 2 => ⟨⟨3874597727314304448,4006112358883197006,true⟩,⟨6608351138382043136401,6699806470981934221342,true⟩,⟨⟨188613420762687473885171,225702800388111062413492,true⟩,⟨(-1209589254282796418191645),(-1172499874657372829649789),true⟩⟩⟩
  | 3 => ⟨⟨115740307074247,123074928969664,true⟩,⟨3874597727314304448,4006112358883197006,true⟩,⟨⟨1001345278252227507092567,1053270409727793043213226,true⟩,⟨611328757761525221378717,663253889237090757494011,true⟩⟩⟩
  | 4 => ⟨⟨(-34183437740),34553843889,true⟩,⟨115740307074247,123074928969664,true⟩,⟨⟨(-1008438482189558543097494),(-941677598863851059364474),true⟩,⟨681296726669202193860424,748057609994909677589858,true⟩⟩⟩
  | _ => ⟨⟨(-34359738355),34359738384,true⟩,⟨(-34183437740),34553843889,true⟩,⟨⟨(-339262314624699035586246),(-257665679448849604269362),true⟩,⟨(-1212302000810361403953003),(-1130705365634511972624102),true⟩⟩⟩
theorem shortNegativeR012Q00F_ok : ∀ n : Fin 6, (shortNegativeR012Q00F n).encloses (FactoredFrequency.build shortNegativeR012Q00T (Grid.ofRats (340833738081849/549755813888000) (342981221729849/549755813888000)) n) := by decide +kernel
def shortNegativeR012Q00L : ℕ → ℚ
  | 0 => (181283/125000)
  | 1 => (2266933/1000000)
  | 2 => (2199219/1000000)
  | 3 => (1709707/1000000)
  | 4 => (939261/1000000)
  | 5 => (-206857/1000000)
  | 6 => (-5587/3125)
  | 7 => (-3650079/1000000)
  | 8 => (-1309373/250000)
  | 9 => (-697423/125000)
  | 10 => (-3913281/1000000)
  | 11 => (-1014443/1000000)
  | _ => 0
def shortNegativeR012Q00U : ℕ → ℚ
  | 0 => (928499/500000)
  | 1 => (1354913/500000)
  | 2 => (2652071/1000000)
  | 3 => (431073/200000)
  | 4 => (136681/100000)
  | 5 => (139001/500000)
  | 6 => (-1186733/1000000)
  | 7 => (-293577/100000)
  | 8 => (-4421351/1000000)
  | 9 => (-4529849/1000000)
  | 10 => (-685797/250000)
  | 11 => (-14993/1000000)
  | _ => 0
private theorem shortNegativeR012Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR012Q00P shortNegativeR012Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR012Q00L (0:Fin 12)) (shortNegativeR012Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR012Q00P shortNegativeR012Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR012Q00L (1:Fin 12)) (shortNegativeR012Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR012Q00P shortNegativeR012Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR012Q00L (2:Fin 12)) (shortNegativeR012Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR012Q00P shortNegativeR012Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR012Q00L (3:Fin 12)) (shortNegativeR012Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR012Q00P shortNegativeR012Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR012Q00L (4:Fin 12)) (shortNegativeR012Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR012Q00P shortNegativeR012Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR012Q00L (5:Fin 12)) (shortNegativeR012Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR012Q00P shortNegativeR012Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR012Q00L (6:Fin 12)) (shortNegativeR012Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR012Q00P shortNegativeR012Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR012Q00L (7:Fin 12)) (shortNegativeR012Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR012Q00P shortNegativeR012Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR012Q00L (8:Fin 12)) (shortNegativeR012Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR012Q00P shortNegativeR012Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR012Q00L (9:Fin 12)) (shortNegativeR012Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR012Q00P shortNegativeR012Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR012Q00L (10:Fin 12)) (shortNegativeR012Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR012Q00P shortNegativeR012Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR012Q00L (11:Fin 12)) (shortNegativeR012Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR012Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR012Q00P shortNegativeR012Q00F (shortNegativeNodes12 k)).re (shortNegativeR012Q00L k) (shortNegativeR012Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR012Q00Point00
  · exact shortNegativeR012Q00Point01
  · exact shortNegativeR012Q00Point02
  · exact shortNegativeR012Q00Point03
  · exact shortNegativeR012Q00Point04
  · exact shortNegativeR012Q00Point05
  · exact shortNegativeR012Q00Point06
  · exact shortNegativeR012Q00Point07
  · exact shortNegativeR012Q00Point08
  · exact shortNegativeR012Q00Point09
  · exact shortNegativeR012Q00Point10
  · exact shortNegativeR012Q00Point11

theorem shortNegativeR012Q00Bound {t a : ℝ} (tl : ((189/200):ℝ)≤t) (tu : t≤((379/400):ℝ)) (al : ((340833738081849/549755813888000):ℝ)≤a) (au : a≤((342981221729849/549755813888000):ℝ)) : (((-2959477560489782416989281383316617/2596148429267413814265248164610048):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-880783101376390580735217451367561/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : shortNegativeR012Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (340833738081849/549755813888000) (342981221729849/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR012Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR012Q00F_ok n) ts asb
  exact factored_negative_12_samples 17660 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip008Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR012Q00L shortNegativeR012Q00U (-2959477560489782416989281383316617/2596148429267413814265248164610048) (-880783101376390580735217451367561/2596148429267413814265248164610048) shortNegativeR012Q00Samples (by decide +kernel)

def shortNegativeR012Q10T := Grid.ofRats (379/400) (19/20)
def shortNegativeR012Q10P : PrimalThetaParameters := ⟨⟨⟨61128271694057437238855,61610262312428939859483,true⟩,⟨0,0,true⟩⟩, ⟨⟨1177313914601327782479796,1184731790526467475750902,true⟩,⟨0,0,true⟩⟩, ⟨(-1443324644433648656091431),(-1428488892583437989028905),true⟩, ⟨5555105812916313677583531,5671709721432562908822093,true⟩⟩
theorem shortNegativeR012Q10P_ok : shortNegativeR012Q10P.encloses (primalThetaParameters shortNegativeR012Q10T (Grid.ofRats (340833738081849/549755813888000) (342981221729849/549755813888000))) := by decide +kernel

def shortNegativeR012Q10F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨573271391197066067217433,574398112735866244552279,true⟩,⟨2544405360891277772168786,2549406197087608660608412,true⟩,⟨⟨672779946806930041893462,680197822732069735212421,true⟩,⟨998221411969111392416472,1005639287894251085739962,true⟩⟩⟩
  | 1 => ⟨⟨6518144211739109703015,6608351138450762613478,true⟩,⟨573271391197066067217433,574398112735866244552279,true⟩,⟨⟨(-1193282787900535252805754),(-1171029160125253611877727),true⟩,⟨241872969583665300254975,264126597358946941170200,true⟩⟩⟩
  | 2 => ⟨⟨3747400587153113021,3874597796033781185,true⟩,⟨6518144211739109703015,6608351138450762613478,true⟩,⟨⟨188613420762687473885171,225702800388111062413492,true⟩,⟨(-1209589254282796418191645),(-1172499874657372829649789),true⟩⟩⟩
  | 3 => ⟨⟨108903477263793,115809026550984,true⟩,⟨3747400587153113021,3874597796033781185,true⟩,⟨⟨1001345278252227507092567,1053270409727793043213226,true⟩,⟨611328757761525221378717,663253889237090757494011,true⟩⟩⟩
  | 4 => ⟨⟨(-34199609426),34536038997,true⟩,⟨108903477263793,115809026550984,true⟩,⟨⟨(-1008438482189558543097494),(-941677598863851059364474),true⟩,⟨681296726669202193860424,748057609994909677589858,true⟩⟩⟩
  | _ => ⟨⟨(-34359738357),34359738382,true⟩,⟨(-34199609426),34536038997,true⟩,⟨⟨(-339262314624699035586246),(-257665679448849604269362),true⟩,⟨(-1212302000810361403953003),(-1130705365634511972624102),true⟩⟩⟩
theorem shortNegativeR012Q10F_ok : ∀ n : Fin 6, (shortNegativeR012Q10F n).encloses (FactoredFrequency.build shortNegativeR012Q10T (Grid.ofRats (340833738081849/549755813888000) (342981221729849/549755813888000)) n) := by decide +kernel
def shortNegativeR012Q10L : ℕ → ℚ
  | 0 => (1407879/1000000)
  | 1 => (2229037/1000000)
  | 2 => (67791/31250)
  | 3 => (1684819/1000000)
  | 4 => (916891/1000000)
  | 5 => (-227109/1000000)
  | 6 => (-1802219/1000000)
  | 7 => (-3653209/1000000)
  | 8 => (-209047/40000)
  | 9 => (-2781573/500000)
  | 10 => (-978377/250000)
  | 11 => (-20849/20000)
  | _ => 0
def shortNegativeR012Q10U : ℕ → ℚ
  | 0 => (1813563/1000000)
  | 1 => (2671207/1000000)
  | 2 => (2621713/1000000)
  | 3 => (266283/125000)
  | 4 => (1344369/1000000)
  | 5 => (258119/1000000)
  | 6 => (-600551/500000)
  | 7 => (-1470059/500000)
  | 8 => (-4413631/1000000)
  | 9 => (-4519301/1000000)
  | 10 => (-2750713/1000000)
  | 11 => (-48693/1000000)
  | _ => 0
private theorem shortNegativeR012Q10Point00 : containedInReported (sampledFactoredPrimal shortNegativeR012Q10P shortNegativeR012Q10F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR012Q10L (0:Fin 12)) (shortNegativeR012Q10U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q10Point01 : containedInReported (sampledFactoredPrimal shortNegativeR012Q10P shortNegativeR012Q10F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR012Q10L (1:Fin 12)) (shortNegativeR012Q10U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q10Point02 : containedInReported (sampledFactoredPrimal shortNegativeR012Q10P shortNegativeR012Q10F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR012Q10L (2:Fin 12)) (shortNegativeR012Q10U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q10Point03 : containedInReported (sampledFactoredPrimal shortNegativeR012Q10P shortNegativeR012Q10F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR012Q10L (3:Fin 12)) (shortNegativeR012Q10U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q10Point04 : containedInReported (sampledFactoredPrimal shortNegativeR012Q10P shortNegativeR012Q10F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR012Q10L (4:Fin 12)) (shortNegativeR012Q10U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q10Point05 : containedInReported (sampledFactoredPrimal shortNegativeR012Q10P shortNegativeR012Q10F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR012Q10L (5:Fin 12)) (shortNegativeR012Q10U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q10Point06 : containedInReported (sampledFactoredPrimal shortNegativeR012Q10P shortNegativeR012Q10F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR012Q10L (6:Fin 12)) (shortNegativeR012Q10U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q10Point07 : containedInReported (sampledFactoredPrimal shortNegativeR012Q10P shortNegativeR012Q10F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR012Q10L (7:Fin 12)) (shortNegativeR012Q10U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q10Point08 : containedInReported (sampledFactoredPrimal shortNegativeR012Q10P shortNegativeR012Q10F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR012Q10L (8:Fin 12)) (shortNegativeR012Q10U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q10Point09 : containedInReported (sampledFactoredPrimal shortNegativeR012Q10P shortNegativeR012Q10F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR012Q10L (9:Fin 12)) (shortNegativeR012Q10U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q10Point10 : containedInReported (sampledFactoredPrimal shortNegativeR012Q10P shortNegativeR012Q10F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR012Q10L (10:Fin 12)) (shortNegativeR012Q10U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR012Q10Point11 : containedInReported (sampledFactoredPrimal shortNegativeR012Q10P shortNegativeR012Q10F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR012Q10L (11:Fin 12)) (shortNegativeR012Q10U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR012Q10Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR012Q10P shortNegativeR012Q10F (shortNegativeNodes12 k)).re (shortNegativeR012Q10L k) (shortNegativeR012Q10U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR012Q10Point00
  · exact shortNegativeR012Q10Point01
  · exact shortNegativeR012Q10Point02
  · exact shortNegativeR012Q10Point03
  · exact shortNegativeR012Q10Point04
  · exact shortNegativeR012Q10Point05
  · exact shortNegativeR012Q10Point06
  · exact shortNegativeR012Q10Point07
  · exact shortNegativeR012Q10Point08
  · exact shortNegativeR012Q10Point09
  · exact shortNegativeR012Q10Point10
  · exact shortNegativeR012Q10Point11

theorem shortNegativeR012Q10Bound {t a : ℝ} (tl : ((379/400):ℝ)≤t) (tu : t≤((19/20):ℝ)) (al : ((340833738081849/549755813888000):ℝ)≤a) (au : a≤((342981221729849/549755813888000):ℝ)) : (((-2959477560489782416989281383316617/2596148429267413814265248164610048):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-880783101376390580735217451367561/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : shortNegativeR012Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (340833738081849/549755813888000) (342981221729849/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR012Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR012Q10F_ok n) ts asb
  exact factored_negative_12_samples 17660 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip008Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR012Q10L shortNegativeR012Q10U (-2959477560489782416989281383316617/2596148429267413814265248164610048) (-880783101376390580735217451367561/2596148429267413814265248164610048) shortNegativeR012Q10Samples (by decide +kernel)

theorem short_original_negative_012 {t a : ℝ} (tb : RealMem negative_012.t t) (ab : RealMem negative_012.a a) : RealMem negative_012.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((189/200):ℝ) ((19/20):ℝ) := by simpa [negative_012,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((189/200):ℝ)<((19/20):ℝ)) tB
  have aB : a∈Icc ((340833738081849/549755813888000):ℝ) ((342981221729849/549755813888000):ℝ) := by simpa [negative_012,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((340833738081849/549755813888000):ℝ)<((342981221729849/549755813888000):ℝ)) aB
  fin_cases ti <;> fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR012Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_012,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR012Q10Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_012,RealMem] using v

def shortNegativeR013Q00T := Grid.ofRats (19/20) (381/400)
def shortNegativeR013Q00P : PrimalThetaParameters := ⟨⟨⟨60650051794258560915251,61128271694126156716448,true⟩,⟨0,0,true⟩⟩, ⟨⟨1180870774622648358594635,1188288650547788051865752,true⟩,⟨0,0,true⟩⟩, ⟨(-1436210924391007503861730),(-1421375172540796836799227),true⟩, ⟨5529209553639250980696628,5644814119254288952579627,true⟩⟩
theorem shortNegativeR013Q00P_ok : shortNegativeR013Q00P.encloses (primalThetaParameters shortNegativeR013Q00T (Grid.ofRats (1025590359498649/1649267441664000) (1032032810442649/1649267441664000))) := by decide +kernel

def shortNegativeR013Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨572146879800390603969937,573271391197134786714881,true⟩,⟨2549406197087539941040190,2554416862048990662975535,true⟩,⟨⟨669829178043036280579197,677247053968175973898171,true⟩,⟨1000207414936675231397675,1007625290861814924721218,true⟩⟩⟩
  | 1 => ⟨⟨6429168649689843058206,6518144211807829180082,true⟩,⟨572146879800390603969937,573271391197134786714881,true⟩,⟨⟨(-1195469811880569071790190),(-1173216184105287430862564),true⟩,⟨231428953794815385146508,253682581570097026061162,true⟩⟩⟩
  | 2 => ⟨⟨3624379135272450485,3747400655872589758,true⟩,⟨6429168649689843058206,6518144211807829180082,true⟩,⟨⟨206111625864377830222089,243201005489801418749702,true⟩,⟨(-1206413023070779067689594),(-1169323643445355479148726),true⟩⟩⟩
  | 3 => ⟨⟨102470382079782,108972196740530,true⟩,⟨3624379135272450485,3747400655872589758,true⟩,⟨⟨988003225546049313055560,1039928357021614849176964,true⟩,⟨632349678897736065949411,684274810373301602065930,true⟩⟩⟩
  | 4 => ⟨⟨(-34214297718),34519867311,true⟩,⟨102470382079782,108972196740530,true⟩,⟨⟨(-1027018740761366440466553),(-960257857435658956733076),true⟩,⟨655230165208342758340762,721991048534050242070040,true⟩⟩⟩
  | _ => ⟨⟨(-34359738358),34359738380,true⟩,⟨(-34214297718),34519867311,true⟩,⟨⟨(-301198301610338681979618),(-219601666434489250662607),true⟩,⟨(-1221346277499774069609791),(-1139749642323924638280115),true⟩⟩⟩
theorem shortNegativeR013Q00F_ok : ∀ n : Fin 6, (shortNegativeR013Q00F n).encloses (FactoredFrequency.build shortNegativeR013Q00T (Grid.ofRats (1025590359498649/1649267441664000) (1032032810442649/1649267441664000)) n) := by decide +kernel
def shortNegativeR013Q00L : ℕ → ℚ
  | 0 => (662273/500000)
  | 1 => (1081251/500000)
  | 2 => (1061499/500000)
  | 3 => (165299/100000)
  | 4 => (895943/1000000)
  | 5 => (-236661/1000000)
  | 6 => (-5612/3125)
  | 7 => (-3627899/1000000)
  | 8 => (-16203/3125)
  | 9 => (-2767689/500000)
  | 10 => (-3932241/1000000)
  | 11 => (-1110271/1000000)
  | _ => 0
def shortNegativeR013Q00U : ℕ → ℚ
  | 0 => (215829/125000)
  | 1 => (65051/25000)
  | 2 => (40214/15625)
  | 3 => (1048741/500000)
  | 4 => (1322957/1000000)
  | 5 => (248451/1000000)
  | 6 => (-597887/500000)
  | 7 => (-2917209/1000000)
  | 8 => (-4383709/1000000)
  | 9 => (-2252831/500000)
  | 10 => (-2785149/1000000)
  | 11 => (-25779/200000)
  | _ => 0
private theorem shortNegativeR013Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR013Q00P shortNegativeR013Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR013Q00L (0:Fin 12)) (shortNegativeR013Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR013Q00P shortNegativeR013Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR013Q00L (1:Fin 12)) (shortNegativeR013Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR013Q00P shortNegativeR013Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR013Q00L (2:Fin 12)) (shortNegativeR013Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR013Q00P shortNegativeR013Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR013Q00L (3:Fin 12)) (shortNegativeR013Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR013Q00P shortNegativeR013Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR013Q00L (4:Fin 12)) (shortNegativeR013Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR013Q00P shortNegativeR013Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR013Q00L (5:Fin 12)) (shortNegativeR013Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR013Q00P shortNegativeR013Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR013Q00L (6:Fin 12)) (shortNegativeR013Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR013Q00P shortNegativeR013Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR013Q00L (7:Fin 12)) (shortNegativeR013Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR013Q00P shortNegativeR013Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR013Q00L (8:Fin 12)) (shortNegativeR013Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR013Q00P shortNegativeR013Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR013Q00L (9:Fin 12)) (shortNegativeR013Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR013Q00P shortNegativeR013Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR013Q00L (10:Fin 12)) (shortNegativeR013Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR013Q00P shortNegativeR013Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR013Q00L (11:Fin 12)) (shortNegativeR013Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR013Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR013Q00P shortNegativeR013Q00F (shortNegativeNodes12 k)).re (shortNegativeR013Q00L k) (shortNegativeR013Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR013Q00Point00
  · exact shortNegativeR013Q00Point01
  · exact shortNegativeR013Q00Point02
  · exact shortNegativeR013Q00Point03
  · exact shortNegativeR013Q00Point04
  · exact shortNegativeR013Q00Point05
  · exact shortNegativeR013Q00Point06
  · exact shortNegativeR013Q00Point07
  · exact shortNegativeR013Q00Point08
  · exact shortNegativeR013Q00Point09
  · exact shortNegativeR013Q00Point10
  · exact shortNegativeR013Q00Point11

theorem shortNegativeR013Q00Bound {t a : ℝ} (tl : ((19/20):ℝ)≤t) (tu : t≤((381/400):ℝ)) (al : ((1025590359498649/1649267441664000):ℝ)≤a) (au : a≤((1032032810442649/1649267441664000):ℝ)) : (((-1524529472937095081241706128000729/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-500555674293813834936259418572505/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR013Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1025590359498649/1649267441664000) (1032032810442649/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR013Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR013Q00F_ok n) ts asb
  exact factored_negative_12_samples 17660 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip008Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR013Q00L shortNegativeR013Q00U (-1524529472937095081241706128000729/1298074214633706907132624082305024) (-500555674293813834936259418572505/1298074214633706907132624082305024) shortNegativeR013Q00Samples (by decide +kernel)

def shortNegativeR013Q10T := Grid.ofRats (381/400) (191/200)
def shortNegativeR013Q10P : PrimalThetaParameters := ⟨⟨⟨60175573113804280444092,60650051794327280392833,true⟩,⟨0,0,true⟩⟩, ⟨⟨1180870774622648358594635,1188288650547788051865752,true⟩,⟨0,0,true⟩⟩, ⟨(-1436210924391007503861730),(-1421375172540796836799227),true⟩, ⟨5519195320018300328980864,5634339427817887689182572,true⟩⟩
theorem shortNegativeR013Q10P_ok : shortNegativeR013Q10P.encloses (primalThetaParameters shortNegativeR013Q10T (Grid.ofRats (1025590359498649/1649267441664000) (1032032810442649/1649267441664000))) := by decide +kernel

def shortNegativeR013Q10F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨571024574210424965242254,572146879800459323467578,true⟩,⟨2554416862048921943405994,2559437375093186578286343,true⟩,⟨⟨669829178043036280579197,677247053968175973898171,true⟩,⟨1000207414936675231397675,1007625290861814924721218,true⟩⟩⟩
  | 1 => ⟨⟨6341407643560907749705,6429168649758562535269,true⟩,⟨571024574210424965242254,572146879800459323467578,true⟩,⟨⟨(-1195469811880569071790190),(-1173216184105287430862564),true⟩,⟨231428953794815385146508,253682581570097026061162,true⟩⟩⟩
  | 2 => ⟨⟨3505396290189242222,3624379203991927222,true⟩,⟨6341407643560907749705,6429168649758562535269,true⟩,⟨⟨206111625864377830222089,243201005489801418749702,true⟩,⟨(-1206413023070779067689594),(-1169323643445355479148726),true⟩⟩⟩
  | 3 => ⟨⟨96417179821732,102539101556519,true⟩,⟨3505396290189242222,3624379203991927222,true⟩,⟨⟨988003225546049313055560,1039928357021614849176964,true⟩,⟨632349678897736065949411,684274810373301602065930,true⟩⟩⟩
  | 4 => ⟨⟨(-34227638683),34505179019,true⟩,⟨96417179821732,102539101556519,true⟩,⟨⟨(-1027018740761366440466553),(-960257857435658956733076),true⟩,⟨655230165208342758340762,721991048534050242070040,true⟩⟩⟩
  | _ => ⟨⟨(-34359738359),34359738379,true⟩,⟨(-34227638683),34505179019,true⟩,⟨⟨(-301198301610338681979618),(-219601666434489250662607),true⟩,⟨(-1221346277499774069609791),(-1139749642323924638280115),true⟩⟩⟩
theorem shortNegativeR013Q10F_ok : ∀ n : Fin 6, (shortNegativeR013Q10F n).encloses (FactoredFrequency.build shortNegativeR013Q10T (Grid.ofRats (1025590359498649/1649267441664000) (1032032810442649/1649267441664000)) n) := by decide +kernel
def shortNegativeR013Q10L : ℕ → ℚ
  | 0 => (160399/125000)
  | 1 => (132813/62500)
  | 2 => (2093119/1000000)
  | 3 => (814027/500000)
  | 4 => (436791/500000)
  | 5 => (-256813/1000000)
  | 6 => (-113131/62500)
  | 7 => (-3631039/1000000)
  | 8 => (-5173937/1000000)
  | 9 => (-5519437/1000000)
  | 10 => (-1966039/500000)
  | 11 => (-568563/500000)
  | _ => 0
def shortNegativeR013Q10U : ℕ → ℚ
  | 0 => (421059/250000)
  | 1 => (2563817/1000000)
  | 2 => (508671/200000)
  | 3 => (2072317/1000000)
  | 4 => (1300509/1000000)
  | 5 => (228643/1000000)
  | 6 => (-605021/500000)
  | 7 => (-584313/200000)
  | 8 => (-21881/5000)
  | 9 => (-140477/31250)
  | 10 => (-2792091/1000000)
  | 11 => (-161307/1000000)
  | _ => 0
private theorem shortNegativeR013Q10Point00 : containedInReported (sampledFactoredPrimal shortNegativeR013Q10P shortNegativeR013Q10F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR013Q10L (0:Fin 12)) (shortNegativeR013Q10U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q10Point01 : containedInReported (sampledFactoredPrimal shortNegativeR013Q10P shortNegativeR013Q10F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR013Q10L (1:Fin 12)) (shortNegativeR013Q10U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q10Point02 : containedInReported (sampledFactoredPrimal shortNegativeR013Q10P shortNegativeR013Q10F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR013Q10L (2:Fin 12)) (shortNegativeR013Q10U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q10Point03 : containedInReported (sampledFactoredPrimal shortNegativeR013Q10P shortNegativeR013Q10F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR013Q10L (3:Fin 12)) (shortNegativeR013Q10U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q10Point04 : containedInReported (sampledFactoredPrimal shortNegativeR013Q10P shortNegativeR013Q10F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR013Q10L (4:Fin 12)) (shortNegativeR013Q10U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q10Point05 : containedInReported (sampledFactoredPrimal shortNegativeR013Q10P shortNegativeR013Q10F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR013Q10L (5:Fin 12)) (shortNegativeR013Q10U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q10Point06 : containedInReported (sampledFactoredPrimal shortNegativeR013Q10P shortNegativeR013Q10F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR013Q10L (6:Fin 12)) (shortNegativeR013Q10U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q10Point07 : containedInReported (sampledFactoredPrimal shortNegativeR013Q10P shortNegativeR013Q10F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR013Q10L (7:Fin 12)) (shortNegativeR013Q10U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q10Point08 : containedInReported (sampledFactoredPrimal shortNegativeR013Q10P shortNegativeR013Q10F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR013Q10L (8:Fin 12)) (shortNegativeR013Q10U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q10Point09 : containedInReported (sampledFactoredPrimal shortNegativeR013Q10P shortNegativeR013Q10F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR013Q10L (9:Fin 12)) (shortNegativeR013Q10U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q10Point10 : containedInReported (sampledFactoredPrimal shortNegativeR013Q10P shortNegativeR013Q10F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR013Q10L (10:Fin 12)) (shortNegativeR013Q10U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR013Q10Point11 : containedInReported (sampledFactoredPrimal shortNegativeR013Q10P shortNegativeR013Q10F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR013Q10L (11:Fin 12)) (shortNegativeR013Q10U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR013Q10Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR013Q10P shortNegativeR013Q10F (shortNegativeNodes12 k)).re (shortNegativeR013Q10L k) (shortNegativeR013Q10U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR013Q10Point00
  · exact shortNegativeR013Q10Point01
  · exact shortNegativeR013Q10Point02
  · exact shortNegativeR013Q10Point03
  · exact shortNegativeR013Q10Point04
  · exact shortNegativeR013Q10Point05
  · exact shortNegativeR013Q10Point06
  · exact shortNegativeR013Q10Point07
  · exact shortNegativeR013Q10Point08
  · exact shortNegativeR013Q10Point09
  · exact shortNegativeR013Q10Point10
  · exact shortNegativeR013Q10Point11

theorem shortNegativeR013Q10Bound {t a : ℝ} (tl : ((381/400):ℝ)≤t) (tu : t≤((191/200):ℝ)) (al : ((1025590359498649/1649267441664000):ℝ)≤a) (au : a≤((1032032810442649/1649267441664000):ℝ)) : (((-1524529472937095081241706128000729/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-500555674293813834936259418572505/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR013Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1025590359498649/1649267441664000) (1032032810442649/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR013Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR013Q10F_ok n) ts asb
  exact factored_negative_12_samples 17660 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip008Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR013Q10L shortNegativeR013Q10U (-1524529472937095081241706128000729/1298074214633706907132624082305024) (-500555674293813834936259418572505/1298074214633706907132624082305024) shortNegativeR013Q10Samples (by decide +kernel)

theorem short_original_negative_013 {t a : ℝ} (tb : RealMem negative_013.t t) (ab : RealMem negative_013.a a) : RealMem negative_013.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((19/20):ℝ) ((191/200):ℝ) := by simpa [negative_013,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((19/20):ℝ)<((191/200):ℝ)) tB
  have aB : a∈Icc ((1025590359498649/1649267441664000):ℝ) ((1032032810442649/1649267441664000):ℝ) := by simpa [negative_013,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((1025590359498649/1649267441664000):ℝ)<((1032032810442649/1649267441664000):ℝ)) aB
  fin_cases ti <;> fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR013Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_013,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR013Q10Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_013,RealMem] using v

def shortNegativeR014Q00T := Grid.ofRats (191/200) (383/400)
def shortNegativeR014Q00P : PrimalThetaParameters := ⟨⟨⟨59704806384313689332803,60175573113872999921673,true⟩,⟨0,0,true⟩⟩, ⟨⟨1184458735823178888368377,1191876611748318581639506,true⟩,⟨0,0,true⟩⟩, ⟨(-1429035001989946444314222),(-1414199250139735777251742),true⟩, ⟨5493446347975823865855225,5607604113261602530232928,true⟩⟩
theorem shortNegativeR014Q00P_ok : shortNegativeR014Q00P.encloses (primalThetaParameters shortNegativeR014Q00T (Grid.ofRats (342902172077887/549755813888000) (345049655725887/549755813888000))) := by decide +kernel

def shortNegativeR014Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨569904470100327061668201,571024574210493684739724,true⟩,⟨2559437375093117858716496,2564467755575857951899524,true⟩,⟨⟨666846700772733449430984,674264576697873142749855,true⟩,⟨1002201978913866250801068,1009619854839005944124581,true⟩⟩⟩
  | 1 => ⟨⟨6254844614124821122253,6341407643629627226766,true⟩,⟨569904470100327061668201,571024574210493684739724,true⟩,⟨⟨(-1197582476924728099041619),(-1175328849149446458114278),true⟩,⟨220874472699585944893149,243128100474867585807357,true⟩⟩⟩
  | 2 => ⟨⟨3390319470596609609,3505396358908718959,true⟩,⟨6254844614124821122253,6341407643629627226766,true⟩,⟨⟨223713567921866635034998,260802947547290223563199,true⟩,⟨(-1202948579493216638246750),(-1165859199867793049705583),true⟩⟩⟩
  | 3 => ⟨⟨90721436710711,96485899298469,true⟩,⟨3390319470596609609,3505396358908718959,true⟩,⟨⟨974108800705666934554730,1026033932181232470676842,true⟩,⟨653271487700966916596109,705196619176532452713808,true⟩⟩⟩
  | 4 => ⟨⟨(-34239755910),34491838054,true⟩,⟨90721436710711,96485899298469,true⟩,⟨⟨(-1045055601512777940231086),(-978294718187070456498431),true⟩,⟨628446581261968540920749,695207464587676024648590,true⟩⟩⟩
  | _ => ⟨⟨(-34359738361),34359738378,true⟩,⟨(-34239755910),34491838054,true⟩,⟨⟨(-262525264265616111860795),(-180928629089766680545157),true⟩,⟨(-1229216930050676038811095),(-1147620294874826607482153),true⟩⟩⟩
theorem shortNegativeR014Q00F_ok : ∀ n : Fin 6, (shortNegativeR014Q00F n).encloses (FactoredFrequency.build shortNegativeR014Q00T (Grid.ofRats (342902172077887/549755813888000) (345049655725887/549755813888000)) n) := by decide +kernel
def shortNegativeR014Q00L : ℕ → ℚ
  | 0 => (1201281/1000000)
  | 1 => (2058823/1000000)
  | 2 => (2046653/1000000)
  | 3 => (39901/25000)
  | 4 => (426287/500000)
  | 5 => (-266303/1000000)
  | 6 => (-901829/500000)
  | 7 => (-3605849/1000000)
  | 8 => (-1283269/250000)
  | 9 => (-686453/125000)
  | 10 => (-197477/50000)
  | 11 => (-1202867/1000000)
  | _ => 0
def shortNegativeR014Q00U : ℕ → ℚ
  | 0 => (1598729/1000000)
  | 1 => (2494973/1000000)
  | 2 => (623787/250000)
  | 3 => (509827/250000)
  | 4 => (1278997/1000000)
  | 5 => (218991/1000000)
  | 6 => (-602347/500000)
  | 7 => (-724699/250000)
  | 8 => (-4346519/1000000)
  | 9 => (-2240709/500000)
  | 10 => (-2825073/1000000)
  | 11 => (-239333/1000000)
  | _ => 0
private theorem shortNegativeR014Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR014Q00P shortNegativeR014Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR014Q00L (0:Fin 12)) (shortNegativeR014Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR014Q00P shortNegativeR014Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR014Q00L (1:Fin 12)) (shortNegativeR014Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR014Q00P shortNegativeR014Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR014Q00L (2:Fin 12)) (shortNegativeR014Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR014Q00P shortNegativeR014Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR014Q00L (3:Fin 12)) (shortNegativeR014Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR014Q00P shortNegativeR014Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR014Q00L (4:Fin 12)) (shortNegativeR014Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR014Q00P shortNegativeR014Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR014Q00L (5:Fin 12)) (shortNegativeR014Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR014Q00P shortNegativeR014Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR014Q00L (6:Fin 12)) (shortNegativeR014Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR014Q00P shortNegativeR014Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR014Q00L (7:Fin 12)) (shortNegativeR014Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR014Q00P shortNegativeR014Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR014Q00L (8:Fin 12)) (shortNegativeR014Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR014Q00P shortNegativeR014Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR014Q00L (9:Fin 12)) (shortNegativeR014Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR014Q00P shortNegativeR014Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR014Q00L (10:Fin 12)) (shortNegativeR014Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR014Q00P shortNegativeR014Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR014Q00L (11:Fin 12)) (shortNegativeR014Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR014Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR014Q00P shortNegativeR014Q00F (shortNegativeNodes12 k)).re (shortNegativeR014Q00L k) (shortNegativeR014Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR014Q00Point00
  · exact shortNegativeR014Q00Point01
  · exact shortNegativeR014Q00Point02
  · exact shortNegativeR014Q00Point03
  · exact shortNegativeR014Q00Point04
  · exact shortNegativeR014Q00Point05
  · exact shortNegativeR014Q00Point06
  · exact shortNegativeR014Q00Point07
  · exact shortNegativeR014Q00Point08
  · exact shortNegativeR014Q00Point09
  · exact shortNegativeR014Q00Point10
  · exact shortNegativeR014Q00Point11

theorem shortNegativeR014Q00Bound {t a : ℝ} (tl : ((191/200):ℝ)≤t) (tu : t≤((383/400):ℝ)) (al : ((342902172077887/549755813888000):ℝ)≤a) (au : a≤((345049655725887/549755813888000):ℝ)) : (((-1568661067290691200434821999382087/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-559777182277608603116908454104647/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR014Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (342902172077887/549755813888000) (345049655725887/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR014Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR014Q00F_ok n) ts asb
  exact factored_negative_12_samples 17660 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip008Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR014Q00L shortNegativeR014Q00U (-1568661067290691200434821999382087/1298074214633706907132624082305024) (-559777182277608603116908454104647/1298074214633706907132624082305024) shortNegativeR014Q00Samples (by decide +kernel)

def shortNegativeR014Q10T := Grid.ofRats (383/400) (24/25)
def shortNegativeR014Q10P : PrimalThetaParameters := ⟨⟨⟨59237722566378855401317,59704806384382408810372,true⟩,⟨0,0,true⟩⟩, ⟨⟨1184458735823178888368377,1191876611748318581639506,true⟩,⟨0,0,true⟩⟩, ⟨(-1429035001989946444314222),(-1414199250139735777251742),true⟩, ⟨5483578640086117259745835,5597285816981170586393920,true⟩⟩
theorem shortNegativeR014Q10P_ok : shortNegativeR014Q10P.encloses (primalThetaParameters shortNegativeR014Q10T (Grid.ofRats (342902172077887/549755813888000) (345049655725887/549755813888000))) := by decide +kernel

def shortNegativeR014Q10F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨568786563151742203246495,569904470100395781165760,true⟩,⟨2564467755575789232329623,2569508022890708417257957,true⟩,⟨⟨666846700772733449430984,674264576697873142749855,true⟩,⟨1002201978913866250801068,1009619854839005944124581,true⟩⟩⟩
  | 1 => ⟨⟨6169463208467915570505,6254844614193540599307,true⟩,⟨568786563151742203246495,569904470100395781165760,true⟩,⟨⟨(-1197582476924728099041619),(-1175328849149446458114278),true⟩,⟨220874472699585944893149,243128100474867585807357,true⟩⟩⟩
  | 2 => ⟨⟨3279020447629943154,3390319539316086346,true⟩,⟨6169463208467915570505,6254844614193540599307,true⟩,⟨⟨223713567921866635034998,260802947547290223563199,true⟩,⟨(-1202948579493216638246750),(-1165859199867793049705583),true⟩⟩⟩
  | 3 => ⟨⟨85362043747492,90790156187448,true⟩,⟨3279020447629943154,3390319539316086346,true⟩,⟨⟨974108800705666934554730,1026033932181232470676842,true⟩,⟨653271487700966916596109,705196619176532452713808,true⟩⟩⟩
  | 4 => ⟨⟨(-34250761649),34479720827,true⟩,⟨85362043747492,90790156187448,true⟩,⟨⟨(-1045055601512777940231086),(-978294718187070456498431),true⟩,⟨628446581261968540920749,695207464587676024648590,true⟩⟩⟩
  | _ => ⟨⟨(-34359738362),34359738376,true⟩,⟨(-34250761649),34479720827,true⟩,⟨⟨(-262525264265616111860795),(-180928629089766680545157),true⟩,⟨(-1229216930050676038811095),(-1147620294874826607482153),true⟩⟩⟩
theorem shortNegativeR014Q10F_ok : ∀ n : Fin 6, (shortNegativeR014Q10F n).encloses (FactoredFrequency.build shortNegativeR014Q10T (Grid.ofRats (342902172077887/549755813888000) (345049655725887/549755813888000)) n) := by decide +kernel
def shortNegativeR014Q10L : ℕ → ℚ
  | 0 => (1160949/1000000)
  | 1 => (8087/4000)
  | 2 => (80673/40000)
  | 3 => (1571073/1000000)
  | 4 => (830233/1000000)
  | 5 => (-5727/20000)
  | 6 => (-28403/15625)
  | 7 => (-1804499/500000)
  | 8 => (-5122339/1000000)
  | 9 => (-219039/40000)
  | 10 => (-3949007/1000000)
  | 11 => (-614303/500000)
  | _ => 0
def shortNegativeR014Q10U : ℕ → ℚ
  | 0 => (1557363/1000000)
  | 1 => (614291/250000)
  | 2 => (492969/200000)
  | 3 => (402819/200000)
  | 4 => (1256551/1000000)
  | 5 => (6227/31250)
  | 6 => (-60943/50000)
  | 7 => (-1451581/500000)
  | 8 => (-4339217/1000000)
  | 9 => (-447117/100000)
  | 10 => (-2831457/1000000)
  | 11 => (-54099/200000)
  | _ => 0
private theorem shortNegativeR014Q10Point00 : containedInReported (sampledFactoredPrimal shortNegativeR014Q10P shortNegativeR014Q10F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR014Q10L (0:Fin 12)) (shortNegativeR014Q10U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q10Point01 : containedInReported (sampledFactoredPrimal shortNegativeR014Q10P shortNegativeR014Q10F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR014Q10L (1:Fin 12)) (shortNegativeR014Q10U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q10Point02 : containedInReported (sampledFactoredPrimal shortNegativeR014Q10P shortNegativeR014Q10F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR014Q10L (2:Fin 12)) (shortNegativeR014Q10U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q10Point03 : containedInReported (sampledFactoredPrimal shortNegativeR014Q10P shortNegativeR014Q10F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR014Q10L (3:Fin 12)) (shortNegativeR014Q10U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q10Point04 : containedInReported (sampledFactoredPrimal shortNegativeR014Q10P shortNegativeR014Q10F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR014Q10L (4:Fin 12)) (shortNegativeR014Q10U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q10Point05 : containedInReported (sampledFactoredPrimal shortNegativeR014Q10P shortNegativeR014Q10F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR014Q10L (5:Fin 12)) (shortNegativeR014Q10U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q10Point06 : containedInReported (sampledFactoredPrimal shortNegativeR014Q10P shortNegativeR014Q10F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR014Q10L (6:Fin 12)) (shortNegativeR014Q10U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q10Point07 : containedInReported (sampledFactoredPrimal shortNegativeR014Q10P shortNegativeR014Q10F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR014Q10L (7:Fin 12)) (shortNegativeR014Q10U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q10Point08 : containedInReported (sampledFactoredPrimal shortNegativeR014Q10P shortNegativeR014Q10F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR014Q10L (8:Fin 12)) (shortNegativeR014Q10U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q10Point09 : containedInReported (sampledFactoredPrimal shortNegativeR014Q10P shortNegativeR014Q10F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR014Q10L (9:Fin 12)) (shortNegativeR014Q10U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q10Point10 : containedInReported (sampledFactoredPrimal shortNegativeR014Q10P shortNegativeR014Q10F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR014Q10L (10:Fin 12)) (shortNegativeR014Q10U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR014Q10Point11 : containedInReported (sampledFactoredPrimal shortNegativeR014Q10P shortNegativeR014Q10F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR014Q10L (11:Fin 12)) (shortNegativeR014Q10U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR014Q10Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR014Q10P shortNegativeR014Q10F (shortNegativeNodes12 k)).re (shortNegativeR014Q10L k) (shortNegativeR014Q10U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR014Q10Point00
  · exact shortNegativeR014Q10Point01
  · exact shortNegativeR014Q10Point02
  · exact shortNegativeR014Q10Point03
  · exact shortNegativeR014Q10Point04
  · exact shortNegativeR014Q10Point05
  · exact shortNegativeR014Q10Point06
  · exact shortNegativeR014Q10Point07
  · exact shortNegativeR014Q10Point08
  · exact shortNegativeR014Q10Point09
  · exact shortNegativeR014Q10Point10
  · exact shortNegativeR014Q10Point11

theorem shortNegativeR014Q10Bound {t a : ℝ} (tl : ((383/400):ℝ)≤t) (tu : t≤((24/25):ℝ)) (al : ((342902172077887/549755813888000):ℝ)≤a) (au : a≤((345049655725887/549755813888000):ℝ)) : (((-1568661067290691200434821999382087/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-559777182277608603116908454104647/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR014Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (342902172077887/549755813888000) (345049655725887/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR014Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR014Q10F_ok n) ts asb
  exact factored_negative_12_samples 17660 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip008Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR014Q10L shortNegativeR014Q10U (-1568661067290691200434821999382087/1298074214633706907132624082305024) (-559777182277608603116908454104647/1298074214633706907132624082305024) shortNegativeR014Q10Samples (by decide +kernel)

theorem short_original_negative_014 {t a : ℝ} (tb : RealMem negative_014.t t) (ab : RealMem negative_014.a a) : RealMem negative_014.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((191/200):ℝ) ((24/25):ℝ) := by simpa [negative_014,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((191/200):ℝ)<((24/25):ℝ)) tB
  have aB : a∈Icc ((342902172077887/549755813888000):ℝ) ((345049655725887/549755813888000):ℝ) := by simpa [negative_014,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((342902172077887/549755813888000):ℝ)<((345049655725887/549755813888000):ℝ)) aB
  fin_cases ti <;> fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR014Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_014,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR014Q10Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_014,RealMem] using v

def shortNegativeR015Q00T := Grid.ofRats (24/25) (97/100)
def shortNegativeR015Q00P : PrimalThetaParameters := ⟨⟨⟨57405643536170928863480,59237722566447574878887,true⟩,⟨0,0,true⟩⟩, ⟨⟨1186190598882744574143007,1193608474807884267414141,true⟩,⟨0,0,true⟩⟩, ⟨(-1425571275870815072764953),(-1410735524020604405702484),true⟩, ⟨5433830019360529249204289,5582283004343699787666945,true⟩⟩
theorem shortNegativeR015Q00P_ok : shortNegativeR015Q00P.encloses (primalThetaParameters shortNegativeR015Q00T (Grid.ofRats (1030210645301831/1649267441664000) (1036653096245831/1649267441664000))) := by decide +kernel

def shortNegativeR015Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨564336820901566989986902,568786563151810922743886,true⟩,⟨2569508022890639697687962,2589768349681638120160809,true⟩,⟨⟨665404981885241152398355,672822857810380845717366,true⟩,⟨1003161559964944203996991,1010579435890083897320749,true⟩⟩⟩
  | 1 => ⟨⟨5839434514518537929808,6169463208536635047553,true⟩,⟨564336820901566989986902,568786563151810922743886,true⟩,⟨⟨(-1198568586625988672342177),(-1176314958850707031414826),true⟩,⟨215773326453683716336886,238026954228965357251017,true⟩⟩⟩
  | 2 => ⟨⟨2869182208815317995,3279020516349419891,true⟩,⟨5839434514518537929808,6169463208536635047553,true⟩,⟨⟨232190949942110559138115,269280329567534147666840,true⟩,⟨(-1201182959228868843742211),(-1164093579603445255200661),true⟩⟩⟩
  | 3 => ⟨⟨66907906869837,85430763224229,true⟩,⟨2869182208815317995,3279020516349419891,true⟩,⟨⟨967247310245507046890445,1019172441721072583012736,true⟩,⟨663265828613582433909615,715190960089147970027732,true⟩⟩⟩
  | 4 => ⟨⟨(-34285573603),34468715088,true⟩,⟨66907906869837,85430763224229,true⟩,⟨⟨(-1053504263635118849432584),(-986743380309411365699270),true⟩,⟨615348334618575971584297,682109217944283455312494,true⟩⟩⟩
  | _ => ⟨⟨(-34359738365),34359738375,true⟩,⟨(-34285573603),34468715088,true⟩,⟨⟨(-243771173176185508755142),(-162174538000336077440200),true⟩,⟨(-1232563251299791381249730),(-1150966616123941949921177),true⟩⟩⟩
theorem shortNegativeR015Q00F_ok : ∀ n : Fin 6, (shortNegativeR015Q00F n).encloses (FactoredFrequency.build shortNegativeR015Q00T (Grid.ofRats (1030210645301831/1649267441664000) (1036653096245831/1649267441664000)) n) := by decide +kernel
def shortNegativeR015Q00L : ℕ → ℚ
  | 0 => (778439/1000000)
  | 1 => (1647843/1000000)
  | 2 => (1671333/1000000)
  | 3 => (626883/500000)
  | 4 => (107539/200000)
  | 5 => (-612517/1000000)
  | 6 => (-13699/6250)
  | 7 => (-4022523/1000000)
  | 8 => (-5589489/1000000)
  | 9 => (-3022571/500000)
  | 10 => (-581761/125000)
  | 11 => (-1931827/1000000)
  | _ => 0
def shortNegativeR015Q00U : ℕ → ℚ
  | 0 => (1707029/1000000)
  | 1 => (657189/250000)
  | 2 => (2655443/1000000)
  | 3 => (2207577/1000000)
  | 4 => (18039/12500)
  | 5 => (427217/1000000)
  | 6 => (-925097/1000000)
  | 7 => (-2528849/1000000)
  | 8 => (-1960583/500000)
  | 9 => (-3906287/1000000)
  | 10 => (-1105829/500000)
  | 11 => (247061/1000000)
  | _ => 0
private theorem shortNegativeR015Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR015Q00P shortNegativeR015Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR015Q00L (0:Fin 12)) (shortNegativeR015Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR015Q00P shortNegativeR015Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR015Q00L (1:Fin 12)) (shortNegativeR015Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR015Q00P shortNegativeR015Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR015Q00L (2:Fin 12)) (shortNegativeR015Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR015Q00P shortNegativeR015Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR015Q00L (3:Fin 12)) (shortNegativeR015Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR015Q00P shortNegativeR015Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR015Q00L (4:Fin 12)) (shortNegativeR015Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR015Q00P shortNegativeR015Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR015Q00L (5:Fin 12)) (shortNegativeR015Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR015Q00P shortNegativeR015Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR015Q00L (6:Fin 12)) (shortNegativeR015Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR015Q00P shortNegativeR015Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR015Q00L (7:Fin 12)) (shortNegativeR015Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR015Q00P shortNegativeR015Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR015Q00L (8:Fin 12)) (shortNegativeR015Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR015Q00P shortNegativeR015Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR015Q00L (9:Fin 12)) (shortNegativeR015Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR015Q00P shortNegativeR015Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR015Q00L (10:Fin 12)) (shortNegativeR015Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR015Q00P shortNegativeR015Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR015Q00L (11:Fin 12)) (shortNegativeR015Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR015Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR015Q00P shortNegativeR015Q00F (shortNegativeNodes12 k)).re (shortNegativeR015Q00L k) (shortNegativeR015Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR015Q00Point00
  · exact shortNegativeR015Q00Point01
  · exact shortNegativeR015Q00Point02
  · exact shortNegativeR015Q00Point03
  · exact shortNegativeR015Q00Point04
  · exact shortNegativeR015Q00Point05
  · exact shortNegativeR015Q00Point06
  · exact shortNegativeR015Q00Point07
  · exact shortNegativeR015Q00Point08
  · exact shortNegativeR015Q00Point09
  · exact shortNegativeR015Q00Point10
  · exact shortNegativeR015Q00Point11

theorem shortNegativeR015Q00Bound {t a : ℝ} (tl : ((24/25):ℝ)≤t) (tu : t≤((97/100):ℝ)) (al : ((1030210645301831/1649267441664000):ℝ)≤a) (au : a≤((1036653096245831/1649267441664000):ℝ)) : (((-2176644127125821268809538167999229/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-412685534891770158316163885837299/5192296858534827628530496329220096):ℚ):ℝ) := by
  have ts : shortNegativeR015Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1030210645301831/1649267441664000) (1036653096245831/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR015Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR015Q00F_ok n) ts asb
  exact factored_negative_12_samples 17660 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip008Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR015Q00L shortNegativeR015Q00U (-2176644127125821268809538167999229/1298074214633706907132624082305024) (-412685534891770158316163885837299/5192296858534827628530496329220096) shortNegativeR015Q00Samples (by decide +kernel)

def shortNegativeR015Q01T := Grid.ofRats (24/25) (97/100)
def shortNegativeR015Q01P : PrimalThetaParameters := ⟨⟨⟨57405643536170928863480,59237722566447574878887,true⟩,⟨0,0,true⟩⟩, ⟨⟨1193608474807815547933602,1201026350732955241204760,true⟩,⟨0,0,true⟩⟩, ⟨(-1410735524020673125183715),(-1395899772170462458121293),true⟩, ⟨5401964239245594895052732,5548861046473218340351747,true⟩⟩
theorem shortNegativeR015Q01P_ok : shortNegativeR015Q01P.encloses (primalThetaParameters shortNegativeR015Q01T (Grid.ofRats (1036653096245831/1649267441664000) (1043095547189831/1649267441664000))) := by decide +kernel

def shortNegativeR015Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨564336820901566989986902,568786563151810922743886,true⟩,⟨2569508022890639697687962,2589768349681638120160809,true⟩,⟨⟨659214344772872419212871,666632220698012112531644,true⟩,⟨1007248211741693233305745,1014666087666832926629357,true⟩⟩⟩
  | 1 => ⟨⟨5839434514518537929808,6169463208536635047553,true⟩,⟨564336820901566989986902,568786563151810922743886,true⟩,⟨⟨(-1202543901972139058452950),(-1180290274196857417525329),true⟩,⟨193877965449714836483362,216131593224996477397407,true⟩⟩⟩
  | 2 => ⟨⟨2869182208815317995,3279020516349419891,true⟩,⟨5839434514518537929808,6169463208536635047553,true⟩,⟨⟨268350154281688506511762,305439533907112095040536,true⟩,⟨(-1192935163957896890111349),(-1155845784332473301570362),true⟩⟩⟩
  | 3 => ⟨⟨66907906869837,85430763224229,true⟩,⟨2869182208815317995,3279020516349419891,true⟩,⟨⟨936737034457573502345937,988662165933139038469454,true⟩,⟨705276873238674594770842,757202004714240130891167,true⟩⟩⟩
  | 4 => ⟨⟨(-34285573603),34468715088,true⟩,⟨66907906869837,85430763224229,true⟩,⟨⟨(-1087755910386788375229242),(-1020995027061080891496749),true⟩,⟨558053416248651065801959,624814299574358549528073,true⟩⟩⟩
  | _ => ⟨⟨(-34359738365),34359738375,true⟩,⟨(-34285573603),34468715088,true⟩,⟨⟨(-162931719182914355021993),(-81335084007064923708173),true⟩,⟨(-1243538966915841918748773),(-1161942331739992487420080),true⟩⟩⟩
theorem shortNegativeR015Q01F_ok : ∀ n : Fin 6, (shortNegativeR015Q01F n).encloses (FactoredFrequency.build shortNegativeR015Q01T (Grid.ofRats (1036653096245831/1649267441664000) (1043095547189831/1649267441664000)) n) := by decide +kernel
def shortNegativeR015Q01L : ℕ → ℚ
  | 0 => (43749/62500)
  | 1 => (1591539/1000000)
  | 2 => (1638661/1000000)
  | 3 => (38751/31250)
  | 4 => (540971/1000000)
  | 5 => (-29491/50000)
  | 6 => (-2148017/1000000)
  | 7 => (-792443/200000)
  | 8 => (-2758769/500000)
  | 9 => (-1201489/200000)
  | 10 => (-584111/125000)
  | 11 => (-1995113/1000000)
  | _ => 0
def shortNegativeR015Q01U : ℕ → ℚ
  | 0 => (64657/40000)
  | 1 => (512609/200000)
  | 2 => (163519/62500)
  | 3 => (2189729/1000000)
  | 4 => (360939/250000)
  | 5 => (27907/62500)
  | 6 => (-88733/100000)
  | 7 => (-1238293/500000)
  | 8 => (-1938093/500000)
  | 9 => (-3908843/1000000)
  | 10 => (-2275351/1000000)
  | 11 => (140627/1000000)
  | _ => 0
private theorem shortNegativeR015Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR015Q01P shortNegativeR015Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR015Q01L (0:Fin 12)) (shortNegativeR015Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR015Q01P shortNegativeR015Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR015Q01L (1:Fin 12)) (shortNegativeR015Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR015Q01P shortNegativeR015Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR015Q01L (2:Fin 12)) (shortNegativeR015Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR015Q01P shortNegativeR015Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR015Q01L (3:Fin 12)) (shortNegativeR015Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR015Q01P shortNegativeR015Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR015Q01L (4:Fin 12)) (shortNegativeR015Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR015Q01P shortNegativeR015Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR015Q01L (5:Fin 12)) (shortNegativeR015Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR015Q01P shortNegativeR015Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR015Q01L (6:Fin 12)) (shortNegativeR015Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR015Q01P shortNegativeR015Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR015Q01L (7:Fin 12)) (shortNegativeR015Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR015Q01P shortNegativeR015Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR015Q01L (8:Fin 12)) (shortNegativeR015Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR015Q01P shortNegativeR015Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR015Q01L (9:Fin 12)) (shortNegativeR015Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR015Q01P shortNegativeR015Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR015Q01L (10:Fin 12)) (shortNegativeR015Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR015Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR015Q01P shortNegativeR015Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR015Q01L (11:Fin 12)) (shortNegativeR015Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR015Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR015Q01P shortNegativeR015Q01F (shortNegativeNodes12 k)).re (shortNegativeR015Q01L k) (shortNegativeR015Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR015Q01Point00
  · exact shortNegativeR015Q01Point01
  · exact shortNegativeR015Q01Point02
  · exact shortNegativeR015Q01Point03
  · exact shortNegativeR015Q01Point04
  · exact shortNegativeR015Q01Point05
  · exact shortNegativeR015Q01Point06
  · exact shortNegativeR015Q01Point07
  · exact shortNegativeR015Q01Point08
  · exact shortNegativeR015Q01Point09
  · exact shortNegativeR015Q01Point10
  · exact shortNegativeR015Q01Point11

theorem shortNegativeR015Q01Bound {t a : ℝ} (tl : ((24/25):ℝ)≤t) (tu : t≤((97/100):ℝ)) (al : ((1036653096245831/1649267441664000):ℝ)≤a) (au : a≤((1043095547189831/1649267441664000):ℝ)) : (((-2176644127125821268809538167999229/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-412685534891770158316163885837299/5192296858534827628530496329220096):ℚ):ℝ) := by
  have ts : shortNegativeR015Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1036653096245831/1649267441664000) (1043095547189831/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR015Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR015Q01F_ok n) ts asb
  exact factored_negative_12_samples 17660 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip008Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR015Q01L shortNegativeR015Q01U (-2176644127125821268809538167999229/1298074214633706907132624082305024) (-412685534891770158316163885837299/5192296858534827628530496329220096) shortNegativeR015Q01Samples (by decide +kernel)

theorem short_original_negative_015 {t a : ℝ} (tb : RealMem negative_015.t t) (ab : RealMem negative_015.a a) : RealMem negative_015.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((24/25):ℝ) ((97/100):ℝ) := by simpa [negative_015,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((24/25):ℝ)<((97/100):ℝ)) tB
  have aB : a∈Icc ((1030210645301831/1649267441664000):ℝ) ((1043095547189831/1649267441664000):ℝ) := by simpa [negative_015,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((1030210645301831/1649267441664000):ℝ)<((1043095547189831/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR015Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_015,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR015Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_015,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_012
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_013
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_014
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_015
