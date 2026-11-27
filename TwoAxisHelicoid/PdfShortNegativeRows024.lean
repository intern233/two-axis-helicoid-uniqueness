import TwoAxisHelicoid.PdfShortNegativeSamples
import TwoAxisHelicoid.PdfShortNegativePhases
import TwoAxisHelicoid.PdfShortNegativeStrip024

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeR024Q00T := Grid.ofRats (21/20) (53/50)
def shortNegativeR024Q00P : PrimalThetaParameters := ⟨⟨⟨43267391974066934018529,44648254144551759170335,true⟩,⟨0,0,true⟩⟩, ⟨⟨1257366770011990640305714,1264784645937130333577074,true⟩,⟨0,0,true⟩⟩, ⟨(-1283218933612322940439086),(-1268383181762112273377070),true⟩, ⟨4851291901296988269536539,4964704570877807834851004,true⟩⟩
theorem shortNegativeR024Q00P_ok : shortNegativeR024Q00P.encloses (primalThetaParameters shortNegativeR024Q00T (Grid.ofRats (1092027396554317/1649267441664000) (1098469847498317/1649267441664000))) := by decide +kernel

def shortNegativeR024Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨525823412514722824071157,529969480196606323622385,true⟩,⟨2757709060508156852255765,2779453334611463466570511,true⟩,⟨⟨604999820191749211216583,612417696116888904536246,true⟩,⟨1040788685336367885328291,1048206561261507578654033,true⟩⟩⟩
  | 1 => ⟨⟨3560258375086937590204,3761474335148930370452,true⟩,⟨525823412514722824071157,529969480196606323622385,true⟩,⟨⟨(-1219962953374776985491992),(-1197709325599495344565873),true⟩,⟨3598171706239913952075,25851799481521554861759,true⟩⟩⟩
  | 2 => ⟨⟨862748398443203291,985984730415429532,true⟩,⟨3560258375086937590204,3761474335148930370452,true⟩,⟨⟨564540915318556166716955,601630294943979755248272,true⟩,⟨(-1077559710678613382493824),(-1040470331053189793955955),true⟩⟩⟩
  | 3 => ⟨⟨7448160605695,9579604600372,true⟩,⟨862748398443203291,985984730415429532,true⟩,⟨⟨608008118615592743048830,659933250091158279181040,true⟩,⟨1003397822421493367333960,1055322953897058903471612,true⟩⟩⟩
  | 4 => ⟨⟨(-34357415778),34363151152,true⟩,⟨7448160605695,9579604600372,true⟩,⟨⟨(-1241499219959523543104778),(-1174738336633816059382616),true⟩,⟨10785776851582363541094,77546660177289847247236,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34357415778),34363151152,true⟩,⟨⟨516318113277067050710129,597914748452916482020772,true⟩,⟨(-1113702283370117063196054),(-1032105648194267631878316),true⟩⟩⟩
theorem shortNegativeR024Q00F_ok : ∀ n : Fin 6, (shortNegativeR024Q00F n).encloses (FactoredFrequency.build shortNegativeR024Q00T (Grid.ofRats (1092027396554317/1649267441664000) (1098469847498317/1649267441664000)) n) := by decide +kernel
def shortNegativeR024Q00L : ℕ → ℚ
  | 0 => (-47867/50000)
  | 1 => (21493/1000000)
  | 2 => (364157/1000000)
  | 3 => (122607/500000)
  | 4 => (-111961/500000)
  | 5 => (-1095987/1000000)
  | 6 => (-2268731/1000000)
  | 7 => (-3592989/1000000)
  | 8 => (-1171393/250000)
  | 9 => (-5136243/1000000)
  | 10 => (-4475851/1000000)
  | 11 => (-712999/250000)
  | _ => 0
def shortNegativeR024Q00U : ℕ → ℚ
  | 0 => (-17849/100000)
  | 1 => (861763/1000000)
  | 2 => (1247553/1000000)
  | 3 => (141913/125000)
  | 4 => (326743/500000)
  | 5 => (-37237/500000)
  | 6 => (-269003/250000)
  | 7 => (-1131649/500000)
  | 8 => (-1664627/500000)
  | 9 => (-728809/200000)
  | 10 => (-1424887/500000)
  | 11 => (-1402213/1000000)
  | _ => 0
private theorem shortNegativeR024Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR024Q00P shortNegativeR024Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR024Q00L (0:Fin 12)) (shortNegativeR024Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR024Q00P shortNegativeR024Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR024Q00L (1:Fin 12)) (shortNegativeR024Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR024Q00P shortNegativeR024Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR024Q00L (2:Fin 12)) (shortNegativeR024Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR024Q00P shortNegativeR024Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR024Q00L (3:Fin 12)) (shortNegativeR024Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR024Q00P shortNegativeR024Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR024Q00L (4:Fin 12)) (shortNegativeR024Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR024Q00P shortNegativeR024Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR024Q00L (5:Fin 12)) (shortNegativeR024Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR024Q00P shortNegativeR024Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR024Q00L (6:Fin 12)) (shortNegativeR024Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR024Q00P shortNegativeR024Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR024Q00L (7:Fin 12)) (shortNegativeR024Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR024Q00P shortNegativeR024Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR024Q00L (8:Fin 12)) (shortNegativeR024Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR024Q00P shortNegativeR024Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR024Q00L (9:Fin 12)) (shortNegativeR024Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR024Q00P shortNegativeR024Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR024Q00L (10:Fin 12)) (shortNegativeR024Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR024Q00P shortNegativeR024Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR024Q00L (11:Fin 12)) (shortNegativeR024Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR024Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR024Q00P shortNegativeR024Q00F (shortNegativeNodes12 k)).re (shortNegativeR024Q00L k) (shortNegativeR024Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR024Q00Point00
  · exact shortNegativeR024Q00Point01
  · exact shortNegativeR024Q00Point02
  · exact shortNegativeR024Q00Point03
  · exact shortNegativeR024Q00Point04
  · exact shortNegativeR024Q00Point05
  · exact shortNegativeR024Q00Point06
  · exact shortNegativeR024Q00Point07
  · exact shortNegativeR024Q00Point08
  · exact shortNegativeR024Q00Point09
  · exact shortNegativeR024Q00Point10
  · exact shortNegativeR024Q00Point11

theorem shortNegativeR024Q00Bound {t a : ℝ} (tl : ((21/20):ℝ)≤t) (tu : t≤((53/50):ℝ)) (al : ((1092027396554317/1649267441664000):ℝ)≤a) (au : a≤((1098469847498317/1649267441664000):ℝ)) : (((-2716771788565676911219781228721083/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2202428747504394337406474229442421/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : shortNegativeR024Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1092027396554317/1649267441664000) (1098469847498317/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR024Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR024Q00F_ok n) ts asb
  exact factored_negative_12_samples 4190 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip024Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR024Q00L shortNegativeR024Q00U (-2716771788565676911219781228721083/1298074214633706907132624082305024) (-2202428747504394337406474229442421/2596148429267413814265248164610048) shortNegativeR024Q00Samples (by decide +kernel)

def shortNegativeR024Q01T := Grid.ofRats (21/20) (53/50)
def shortNegativeR024Q01P : PrimalThetaParameters := ⟨⟨⟨43267391974066934018529,44648254144551759170335,true⟩,⟨0,0,true⟩⟩, ⟨⟨1264784645937061614096309,1272202521862201307367693,true⟩,⟨0,0,true⟩⟩, ⟨(-1268383181762180992857848),(-1253547429911970325795879),true⟩, ⟨4824670751629139027790763,4937210289067103195823466,true⟩⟩
theorem shortNegativeR024Q01P_ok : shortNegativeR024Q01P.encloses (primalThetaParameters shortNegativeR024Q01T (Grid.ofRats (1098469847498317/1649267441664000) (1104912298442317/1649267441664000))) := by decide +kernel

def shortNegativeR024Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨525823412514722824071157,529969480196606323622385,true⟩,⟨2757709060508156852255765,2779453334611463466570511,true⟩,⟨⟨598579444488520460846458,605997320413660154165795,true⟩,⟨1044503989688750475056892,1051921865613890168382404,true⟩⟩⟩
  | 1 => ⟨⟨3560258375086937590204,3761474335148930370452,true⟩,⟨525823412514722824071157,529969480196606323622385,true⟩,⟨⟨(-1220029193359574757228535),(-1197775565584293116302704),true⟩,⟨(-18655043294291444537717),3598584480990196371628,true⟩⟩⟩
  | 2 => ⟨⟨862748398443203291,985984730415429532,true⟩,⟨3560258375086937590204,3761474335148930370452,true⟩,⟨⟨596751602763580150202335,633840982389003738734300,true⟩,⟨(-1059175320571182722716982),(-1022085940945759134179171),true⟩⟩⟩
  | 3 => ⟨⟨7448160605695,9579604600372,true⟩,⟨862748398443203291,985984730415429532,true⟩,⟨⟨563224484222343794795549,615149615697909330928589,true⟩,⟨1029670068036953396326813,1081595199512518932466279,true⟩⟩⟩
  | 4 => ⟨⟨(-34357415778),34363151152,true⟩,⟨7448160605695,9579604600372,true⟩,⟨⟨(-1242095305447026790021650),(-1175334422121319306300342),true⟩,⟨(-55963962161458728779268),10796921164248754925862,true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34357415778),34363151152,true⟩,⟨⟨587410445060311987437316,669007080236161418747685,true⟩,⟨(-1073685236791994373005477),(-992088601616144941689541),true⟩⟩⟩
theorem shortNegativeR024Q01F_ok : ∀ n : Fin 6, (shortNegativeR024Q01F n).encloses (FactoredFrequency.build shortNegativeR024Q01T (Grid.ofRats (1098469847498317/1649267441664000) (1104912298442317/1649267441664000)) n) := by decide +kernel
def shortNegativeR024Q01L : ℕ → ℚ
  | 0 => (-1010119/1000000)
  | 1 => (-5881/250000)
  | 2 => (334511/1000000)
  | 3 => (28907/125000)
  | 4 => (-55597/250000)
  | 5 => (-53877/50000)
  | 6 => (-2233339/1000000)
  | 7 => (-886237/250000)
  | 8 => (-927547/200000)
  | 9 => (-1277529/250000)
  | 10 => (-1117731/250000)
  | 11 => (-2880937/1000000)
  | _ => 0
def shortNegativeR024Q01U : ℕ → ℚ
  | 0 => (-239159/1000000)
  | 1 => (32331/40000)
  | 2 => (1210861/1000000)
  | 3 => (1116137/1000000)
  | 4 => (651071/1000000)
  | 5 => (-30507/500000)
  | 6 => (-1047191/1000000)
  | 7 => (-1111589/500000)
  | 8 => (-3289723/1000000)
  | 9 => (-145473/40000)
  | 10 => (-57609/20000)
  | 11 => (-1463749/1000000)
  | _ => 0
private theorem shortNegativeR024Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR024Q01P shortNegativeR024Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR024Q01L (0:Fin 12)) (shortNegativeR024Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR024Q01P shortNegativeR024Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR024Q01L (1:Fin 12)) (shortNegativeR024Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR024Q01P shortNegativeR024Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR024Q01L (2:Fin 12)) (shortNegativeR024Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR024Q01P shortNegativeR024Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR024Q01L (3:Fin 12)) (shortNegativeR024Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR024Q01P shortNegativeR024Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR024Q01L (4:Fin 12)) (shortNegativeR024Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR024Q01P shortNegativeR024Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR024Q01L (5:Fin 12)) (shortNegativeR024Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR024Q01P shortNegativeR024Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR024Q01L (6:Fin 12)) (shortNegativeR024Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR024Q01P shortNegativeR024Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR024Q01L (7:Fin 12)) (shortNegativeR024Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR024Q01P shortNegativeR024Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR024Q01L (8:Fin 12)) (shortNegativeR024Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR024Q01P shortNegativeR024Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR024Q01L (9:Fin 12)) (shortNegativeR024Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR024Q01P shortNegativeR024Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR024Q01L (10:Fin 12)) (shortNegativeR024Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR024Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR024Q01P shortNegativeR024Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR024Q01L (11:Fin 12)) (shortNegativeR024Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR024Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR024Q01P shortNegativeR024Q01F (shortNegativeNodes12 k)).re (shortNegativeR024Q01L k) (shortNegativeR024Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR024Q01Point00
  · exact shortNegativeR024Q01Point01
  · exact shortNegativeR024Q01Point02
  · exact shortNegativeR024Q01Point03
  · exact shortNegativeR024Q01Point04
  · exact shortNegativeR024Q01Point05
  · exact shortNegativeR024Q01Point06
  · exact shortNegativeR024Q01Point07
  · exact shortNegativeR024Q01Point08
  · exact shortNegativeR024Q01Point09
  · exact shortNegativeR024Q01Point10
  · exact shortNegativeR024Q01Point11

theorem shortNegativeR024Q01Bound {t a : ℝ} (tl : ((21/20):ℝ)≤t) (tu : t≤((53/50):ℝ)) (al : ((1098469847498317/1649267441664000):ℝ)≤a) (au : a≤((1104912298442317/1649267441664000):ℝ)) : (((-2716771788565676911219781228721083/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-2202428747504394337406474229442421/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : shortNegativeR024Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1098469847498317/1649267441664000) (1104912298442317/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR024Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR024Q01F_ok n) ts asb
  exact factored_negative_12_samples 4190 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip024Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR024Q01L shortNegativeR024Q01U (-2716771788565676911219781228721083/1298074214633706907132624082305024) (-2202428747504394337406474229442421/2596148429267413814265248164610048) shortNegativeR024Q01Samples (by decide +kernel)

theorem short_original_negative_024 {t a : ℝ} (tb : RealMem negative_024.t t) (ab : RealMem negative_024.a a) : RealMem negative_024.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((21/20):ℝ) ((53/50):ℝ) := by simpa [negative_024,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((21/20):ℝ)<((53/50):ℝ)) tB
  have aB : a∈Icc ((1092027396554317/1649267441664000):ℝ) ((1104912298442317/1649267441664000):ℝ) := by simpa [negative_024,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((1092027396554317/1649267441664000):ℝ)<((1104912298442317/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR024Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_024,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR024Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_024,RealMem] using v

def shortNegativeR025Q00T := Grid.ofRats (53/50) (107/100)
def shortNegativeR025Q00P : PrimalThetaParameters := ⟨⟨⟨41929236520189271582175,43267391974135653495916,true⟩,⟨0,0,true⟩⟩, ⟨⟨1266003144412900966401505,1273421020338040659672894,true⟩,⟨0,0,true⟩⟩, ⟨(-1265946184810502288247447),(-1251110432960291621185486),true⟩, ⟨4791801697841460786315943,4902257096426518933135587,true⟩⟩
theorem shortNegativeR025Q00P_ok : shortNegativeR025Q00P.encloses (primalThetaParameters shortNegativeR025Q00T (Grid.ofRats (366509372548901/549755813888000) (368656856196901/549755813888000))) := by decide +kernel

def shortNegativeR025Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨521709780431304791419817,525823412514791543567318,true⟩,⟨2779453334611394746991843,2801369060251430769591024,true⟩,⟨⟨597522625726778988573964,604940501651918681893547,true⟩,⟨1045110514638574176096572,1052528390563713869422335,true⟩⟩⟩
  | 1 => ⟨⟨3369806243036885211188,3560258375155657067130,true⟩,⟨521709780431304791419817,525823412514791543567318,true⟩,⟨⟨(-1220000903323530337930302),(-1197747275548248697004319),true⟩,⟨(-22310427858621325823446),(-56800083339684913947),true⟩⟩⟩
  | 2 => ⟨⟨754915190269559359,862748467162680028,true⟩,⟨3369806243036885211188,3560258375155657067130,true⟩,⟨⟨601988120455385066609258,639077500080808655140879,true⟩,⟨(-1056061277011047154583670),(-1018971897385623566046314),true⟩⟩⟩
  | 3 => ⟨⟨5831190230098,7516880082432,true⟩,⟨754915190269559359,862748467162680028,true⟩,⟨⟨555761941220879989409941,607687072696445525542904,true⟩,⟨1033800726386738613843735,1085725857862304149983278,true⟩⟩⟩
  | 4 => ⟨⟨(-34358157715),34362060959,true⟩,⟨5831190230098,7516880082432,true⟩,⟨⟨(-1241840716230984042857679),(-1175079832905276559135382),true⟩,⟨(-66927455264991912829064),(-166571939284429122932),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34358157715),34362060959,true⟩,⟨⟨598823322014588981448169,680419957190438412759114,true⟩,⟨(-1066656882636291897208909),(-985060247460442465892644),true⟩⟩⟩
theorem shortNegativeR025Q00F_ok : ∀ n : Fin 6, (shortNegativeR025Q00F n).encloses (FactoredFrequency.build shortNegativeR025Q00T (Grid.ofRats (366509372548901/549755813888000) (368656856196901/549755813888000)) n) := by decide +kernel
def shortNegativeR025Q00L : ℕ → ℚ
  | 0 => (-1107391/1000000)
  | 1 => (-13717/100000)
  | 2 => (229533/1000000)
  | 3 => (69193/500000)
  | 4 => (-152749/500000)
  | 5 => (-1143537/1000000)
  | 6 => (-568347/250000)
  | 7 => (-1774037/500000)
  | 8 => (-1150623/250000)
  | 9 => (-5060517/1000000)
  | 10 => (-55509/12500)
  | 11 => (-2914039/1000000)
  | _ => 0
def shortNegativeR025Q00U : ℕ → ℚ
  | 0 => (-340411/1000000)
  | 1 => (690231/1000000)
  | 2 => (275127/250000)
  | 3 => (1019531/1000000)
  | 4 => (569427/1000000)
  | 5 => (-63047/500000)
  | 6 => (-136403/125000)
  | 7 => (-1118527/500000)
  | 8 => (-654297/200000)
  | 9 => (-3612499/1000000)
  | 10 => (-2890783/1000000)
  | 11 => (-61287/40000)
  | _ => 0
private theorem shortNegativeR025Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR025Q00P shortNegativeR025Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR025Q00L (0:Fin 12)) (shortNegativeR025Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR025Q00P shortNegativeR025Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR025Q00L (1:Fin 12)) (shortNegativeR025Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR025Q00P shortNegativeR025Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR025Q00L (2:Fin 12)) (shortNegativeR025Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR025Q00P shortNegativeR025Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR025Q00L (3:Fin 12)) (shortNegativeR025Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR025Q00P shortNegativeR025Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR025Q00L (4:Fin 12)) (shortNegativeR025Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR025Q00P shortNegativeR025Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR025Q00L (5:Fin 12)) (shortNegativeR025Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR025Q00P shortNegativeR025Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR025Q00L (6:Fin 12)) (shortNegativeR025Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR025Q00P shortNegativeR025Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR025Q00L (7:Fin 12)) (shortNegativeR025Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR025Q00P shortNegativeR025Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR025Q00L (8:Fin 12)) (shortNegativeR025Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR025Q00P shortNegativeR025Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR025Q00L (9:Fin 12)) (shortNegativeR025Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR025Q00P shortNegativeR025Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR025Q00L (10:Fin 12)) (shortNegativeR025Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR025Q00P shortNegativeR025Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR025Q00L (11:Fin 12)) (shortNegativeR025Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR025Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR025Q00P shortNegativeR025Q00F (shortNegativeNodes12 k)).re (shortNegativeR025Q00L k) (shortNegativeR025Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR025Q00Point00
  · exact shortNegativeR025Q00Point01
  · exact shortNegativeR025Q00Point02
  · exact shortNegativeR025Q00Point03
  · exact shortNegativeR025Q00Point04
  · exact shortNegativeR025Q00Point05
  · exact shortNegativeR025Q00Point06
  · exact shortNegativeR025Q00Point07
  · exact shortNegativeR025Q00Point08
  · exact shortNegativeR025Q00Point09
  · exact shortNegativeR025Q00Point10
  · exact shortNegativeR025Q00Point11

theorem shortNegativeR025Q00Bound {t a : ℝ} (tl : ((53/50):ℝ)≤t) (tu : t≤((107/100):ℝ)) (al : ((366509372548901/549755813888000):ℝ)≤a) (au : a≤((368656856196901/549755813888000):ℝ)) : (((-346423010325710959847783418303761/162259276829213363391578010288128):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-148182227706440186945073851667729/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : shortNegativeR025Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (366509372548901/549755813888000) (368656856196901/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR025Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR025Q00F_ok n) ts asb
  exact factored_negative_12_samples 4190 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip024Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR025Q00L shortNegativeR025Q00U (-346423010325710959847783418303761/162259276829213363391578010288128) (-148182227706440186945073851667729/162259276829213363391578010288128) shortNegativeR025Q00Samples (by decide +kernel)

def shortNegativeR025Q01T := Grid.ofRats (53/50) (107/100)
def shortNegativeR025Q01P : PrimalThetaParameters := ⟨⟨⟨41929236520189271582175,43267391974135653495916,true⟩,⟨0,0,true⟩⟩, ⟨⟨1273421020337971940192101,1280838896263111633463512,true⟩,⟨0,0,true⟩⟩, ⟨(-1251110432960360340666210),(-1236274681110149673604296),true⟩, ⟨4765629041675946907653234,4875386009831988125724621,true⟩⟩
theorem shortNegativeR025Q01P_ok : shortNegativeR025Q01P.encloses (primalThetaParameters shortNegativeR025Q01T (Grid.ofRats (368656856196901/549755813888000) (370804339844901/549755813888000))) := by decide +kernel

def shortNegativeR025Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨521709780431304791419817,525823412514791543567318,true⟩,⟨2779453334611394746991843,2801369060251430769591024,true⟩,⟨⟨591075872533551303990859,598493748458690997310320,true⟩,⟨1048779858431005152091507,1056197734356144845417280,true⟩⟩⟩
  | 1 => ⟨⟨3369806243036885211188,3560258375155657067130,true⟩,⟨521709780431304791419817,525823412514791543567318,true⟩,⟨⟨(-1219590244284487890128324),(-1197336616509206249202058),true⟩,⟨(-44559952005198317545617),(-22306324229916676635519),true⟩⟩⟩
  | 2 => ⟨⟨754915190269559359,862748467162680028,true⟩,⟨3369806243036885211188,3560258375155657067130,true⟩,⟨⟨633521725679680111895358,670611105305103700427547,true⟩,⟨(-1036538318043166998482333),(-999448938417743409945113),true⟩⟩⟩
  | 3 => ⟨⟨5831190230098,7516880082432,true⟩,⟨754915190269559359,862748467162680028,true⟩,⟨⟨509721044325044519328198,561646175800610055462037,true⟩,⟨1057801572458789836145441,1109726703934355372286825,true⟩⟩⟩
  | 4 => ⟨⟨(-34358157715),34362060959,true⟩,⟨5831190230098,7516880082432,true⟩,⟨⟨(-1238146880299058438891139),(-1171385996973350955167714),true⟩,⟨(-133577575687430215473686),(-66816692361722731765463),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34358157715),34362060959,true⟩,⟨⟨666554868713099074115153,748151503888948505424424,true⟩,⟨(-1021182480638660683941057),(-939585845462811252628034),true⟩⟩⟩
theorem shortNegativeR025Q01F_ok : ∀ n : Fin 6, (shortNegativeR025Q01F n).encloses (FactoredFrequency.build shortNegativeR025Q01T (Grid.ofRats (368656856196901/549755813888000) (370804339844901/549755813888000)) n) := by decide +kernel
def shortNegativeR025Q01L : ℕ → ℚ
  | 0 => (-144673/125000)
  | 1 => (-45293/250000)
  | 2 => (200387/1000000)
  | 3 => (124441/1000000)
  | 4 => (-304201/1000000)
  | 5 => (-225141/200000)
  | 6 => (-2239073/1000000)
  | 7 => (-1750727/500000)
  | 8 => (-4555781/1000000)
  | 9 => (-2517093/500000)
  | 10 => (-4434259/1000000)
  | 11 => (-2940231/1000000)
  | _ => 0
def shortNegativeR025Q01U : ℕ → ℚ
  | 0 => (-99517/250000)
  | 1 => (638519/1000000)
  | 2 => (1064557/1000000)
  | 3 => (31267/31250)
  | 4 => (35427/62500)
  | 5 => (-113071/1000000)
  | 6 => (-1063163/1000000)
  | 7 => (-1098983/500000)
  | 8 => (-3232789/1000000)
  | 9 => (-180217/50000)
  | 10 => (-2918487/1000000)
  | 11 => (-198719/125000)
  | _ => 0
private theorem shortNegativeR025Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR025Q01P shortNegativeR025Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR025Q01L (0:Fin 12)) (shortNegativeR025Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR025Q01P shortNegativeR025Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR025Q01L (1:Fin 12)) (shortNegativeR025Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR025Q01P shortNegativeR025Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR025Q01L (2:Fin 12)) (shortNegativeR025Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR025Q01P shortNegativeR025Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR025Q01L (3:Fin 12)) (shortNegativeR025Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR025Q01P shortNegativeR025Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR025Q01L (4:Fin 12)) (shortNegativeR025Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR025Q01P shortNegativeR025Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR025Q01L (5:Fin 12)) (shortNegativeR025Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR025Q01P shortNegativeR025Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR025Q01L (6:Fin 12)) (shortNegativeR025Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR025Q01P shortNegativeR025Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR025Q01L (7:Fin 12)) (shortNegativeR025Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR025Q01P shortNegativeR025Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR025Q01L (8:Fin 12)) (shortNegativeR025Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR025Q01P shortNegativeR025Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR025Q01L (9:Fin 12)) (shortNegativeR025Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR025Q01P shortNegativeR025Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR025Q01L (10:Fin 12)) (shortNegativeR025Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR025Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR025Q01P shortNegativeR025Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR025Q01L (11:Fin 12)) (shortNegativeR025Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR025Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR025Q01P shortNegativeR025Q01F (shortNegativeNodes12 k)).re (shortNegativeR025Q01L k) (shortNegativeR025Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR025Q01Point00
  · exact shortNegativeR025Q01Point01
  · exact shortNegativeR025Q01Point02
  · exact shortNegativeR025Q01Point03
  · exact shortNegativeR025Q01Point04
  · exact shortNegativeR025Q01Point05
  · exact shortNegativeR025Q01Point06
  · exact shortNegativeR025Q01Point07
  · exact shortNegativeR025Q01Point08
  · exact shortNegativeR025Q01Point09
  · exact shortNegativeR025Q01Point10
  · exact shortNegativeR025Q01Point11

theorem shortNegativeR025Q01Bound {t a : ℝ} (tl : ((53/50):ℝ)≤t) (tu : t≤((107/100):ℝ)) (al : ((368656856196901/549755813888000):ℝ)≤a) (au : a≤((370804339844901/549755813888000):ℝ)) : (((-346423010325710959847783418303761/162259276829213363391578010288128):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-148182227706440186945073851667729/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : shortNegativeR025Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (368656856196901/549755813888000) (370804339844901/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR025Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR025Q01F_ok n) ts asb
  exact factored_negative_12_samples 4190 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip024Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR025Q01L shortNegativeR025Q01U (-346423010325710959847783418303761/162259276829213363391578010288128) (-148182227706440186945073851667729/162259276829213363391578010288128) shortNegativeR025Q01Samples (by decide +kernel)

theorem short_original_negative_025 {t a : ℝ} (tb : RealMem negative_025.t t) (ab : RealMem negative_025.a a) : RealMem negative_025.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((53/50):ℝ) ((107/100):ℝ) := by simpa [negative_025,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((53/50):ℝ)<((107/100):ℝ)) tB
  have aB : a∈Icc ((366509372548901/549755813888000):ℝ) ((370804339844901/549755813888000):ℝ) := by simpa [negative_025,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((366509372548901/549755813888000):ℝ)<((370804339844901/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR025Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_025,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR025Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_025,RealMem] using v

def shortNegativeR026Q00T := Grid.ofRats (107/100) (27/25)
def shortNegativeR026Q00P : PrimalThetaParameters := ⟨⟨⟨40632466967727030118345,41929236520257991059551,true⟩,⟨0,0,true⟩⟩, ⟨⟨1274799943624297297339024,1282217819549436990610440,true⟩,⟨0,0,true⟩⟩, ⟨(-1248352586387709626372355),(-1233516834537498959310450),true⟩, ⟨4733130472981840515752992,4840904867023669634239518,true⟩⟩
theorem shortNegativeR026Q00P_ok : shortNegativeR026Q00P.encloses (primalThetaParameters shortNegativeR026Q00T (Grid.ofRats (369056056080957/549755813888000) (371203539728957/549755813888000))) := by decide +kernel

def shortNegativeR026Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨517628330195470906174884,521709780431373510915606,true⟩,⟨2801369060251362050012461,2823457589307215617405996,true⟩,⟨⟨589874997576608925093620,597292873501748618413237,true⟩,⟨1049457596257314572325358,1056875472182454265651305,true⟩⟩⟩
  | 1 => ⟨⟨3189542139714150918441,3369806243105604688104,true⟩,⟨517628330195470906174884,521709780431373510915606,true⟩,⟨⟨(-1219468766128263239680826),(-1197215138352981598753739),true⟩,⟨(-48694935829312148588553),(-26441308054030507677580),true⟩⟩⟩
  | 2 => ⟨⟨660559840000846971,754915258989036096,true⟩,⟨3189542139714150918441,3369806243105604688104,true⟩,⟨⟨639316802297432138123945,676406181922855726655749,true⟩,⟨(-1032802987550284139341088),(-995713607924860550804383),true⟩⟩⟩
  | 3 => ⟨⟨4563646661958,5899909706835,true⟩,⟨660559840000846971,754915258989036096,true⟩,⟨⟨501050930761316488172221,552976062236882024305768,true⟩,⟨1062044057329695077230842,1113969188805260613372111,true⟩⟩⟩
  | 4 => ⟨⟨(-34358662645),34361319022,true⟩,⟨4563646661958,5899909706835,true⟩,⟨⟨(-1237054838208136644747619),(-1170293954882429161023551),true⟩,⟨(-145939690204463881492782),(-79178806878756397783727),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34358662645),34361319022,true⟩,⟨⟨678799558746606947969576,760396193922456379278376,true⟩,⟨(-1012230525055710391860769),(-930633889879860960548503),true⟩⟩⟩
theorem shortNegativeR026Q00F_ok : ∀ n : Fin 6, (shortNegativeR026Q00F n).encloses (FactoredFrequency.build shortNegativeR026Q00T (Grid.ofRats (369056056080957/549755813888000) (371203539728957/549755813888000)) n) := by decide +kernel
def shortNegativeR026Q00L : ℕ → ℚ
  | 0 => (-1249257/1000000)
  | 1 => (-290771/1000000)
  | 2 => (3053/31250)
  | 3 => (33103/1000000)
  | 4 => (-192851/500000)
  | 5 => (-1189931/1000000)
  | 6 => (-2277517/1000000)
  | 7 => (-875971/250000)
  | 8 => (-4521223/1000000)
  | 9 => (-4985647/1000000)
  | 10 => (-220177/50000)
  | 11 => (-2969663/1000000)
  | _ => 0
def shortNegativeR026Q00U : ℕ → ℚ
  | 0 => (-494273/1000000)
  | 1 => (16383/31250)
  | 2 => (956309/1000000)
  | 3 => (905223/1000000)
  | 4 => (60793/125000)
  | 5 => (-44221/250000)
  | 6 => (-1105963/1000000)
  | 7 => (-2211249/1000000)
  | 8 => (-3215029/1000000)
  | 9 => (-3576719/1000000)
  | 10 => (-585363/200000)
  | 11 => (-1653233/1000000)
  | _ => 0
private theorem shortNegativeR026Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR026Q00P shortNegativeR026Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR026Q00L (0:Fin 12)) (shortNegativeR026Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR026Q00P shortNegativeR026Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR026Q00L (1:Fin 12)) (shortNegativeR026Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR026Q00P shortNegativeR026Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR026Q00L (2:Fin 12)) (shortNegativeR026Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR026Q00P shortNegativeR026Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR026Q00L (3:Fin 12)) (shortNegativeR026Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR026Q00P shortNegativeR026Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR026Q00L (4:Fin 12)) (shortNegativeR026Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR026Q00P shortNegativeR026Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR026Q00L (5:Fin 12)) (shortNegativeR026Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR026Q00P shortNegativeR026Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR026Q00L (6:Fin 12)) (shortNegativeR026Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR026Q00P shortNegativeR026Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR026Q00L (7:Fin 12)) (shortNegativeR026Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR026Q00P shortNegativeR026Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR026Q00L (8:Fin 12)) (shortNegativeR026Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR026Q00P shortNegativeR026Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR026Q00L (9:Fin 12)) (shortNegativeR026Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR026Q00P shortNegativeR026Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR026Q00L (10:Fin 12)) (shortNegativeR026Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR026Q00P shortNegativeR026Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR026Q00L (11:Fin 12)) (shortNegativeR026Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR026Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR026Q00P shortNegativeR026Q00F (shortNegativeNodes12 k)).re (shortNegativeR026Q00L k) (shortNegativeR026Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR026Q00Point00
  · exact shortNegativeR026Q00Point01
  · exact shortNegativeR026Q00Point02
  · exact shortNegativeR026Q00Point03
  · exact shortNegativeR026Q00Point04
  · exact shortNegativeR026Q00Point05
  · exact shortNegativeR026Q00Point06
  · exact shortNegativeR026Q00Point07
  · exact shortNegativeR026Q00Point08
  · exact shortNegativeR026Q00Point09
  · exact shortNegativeR026Q00Point10
  · exact shortNegativeR026Q00Point11

theorem shortNegativeR026Q00Bound {t a : ℝ} (tl : ((107/100):ℝ)≤t) (tu : t≤((27/25):ℝ)) (al : ((369056056080957/549755813888000):ℝ)≤a) (au : a≤((371203539728957/549755813888000):ℝ)) : (((-1405843944273241134380015739444009/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-638901376504426534809946666801961/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR026Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (369056056080957/549755813888000) (371203539728957/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR026Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR026Q00F_ok n) ts asb
  exact factored_negative_12_samples 4190 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip024Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR026Q00L shortNegativeR026Q00U (-1405843944273241134380015739444009/649037107316853453566312041152512) (-638901376504426534809946666801961/649037107316853453566312041152512) shortNegativeR026Q00Samples (by decide +kernel)

def shortNegativeR026Q01T := Grid.ofRats (107/100) (27/25)
def shortNegativeR026Q01P : PrimalThetaParameters := ⟨⟨⟨40632466967727030118345,41929236520257991059551,true⟩,⟨0,0,true⟩⟩, ⟨⟨1282217819549368271129619,1289635695474507964401059,true⟩,⟨0,0,true⟩⟩, ⟨(-1233516834537567678791117),(-1218681082687357011729259),true⟩, ⟨4707487490148614352142810,4814657391361602735718968,true⟩⟩
theorem shortNegativeR026Q01P_ok : shortNegativeR026Q01P.encloses (primalThetaParameters shortNegativeR026Q01T (Grid.ofRats (371203539728957/549755813888000) (373351023376957/549755813888000))) := by decide +kernel

def shortNegativeR026Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨517628330195470906174884,521709780431373510915606,true⟩,⟨2801369060251362050012461,2823457589307215617405996,true⟩,⟨⟨583401715156446888223212,590819591081586581542891,true⟩,⟨1053079933252993495634978,1060497809178133188961138,true⟩⟩⟩
  | 1 => ⟨⟨3189542139714150918441,3369806243105604688104,true⟩,⟨517628330195470906174884,521709780431373510915606,true⟩,⟨⟨(-1218572544731034729156637),(-1196318916955753088229408),true⟩,⟨(-70930195054304549266983),(-48676567279022908355551),true⟩⟩⟩
  | 2 => ⟨⟨660559840000846971,754915258989036096,true⟩,⟨3189542139714150918441,3369806243105604688104,true⟩,⟨⟨670119397845910907132211,707208777471334495664393,true⟩,⟨(-1012145923558030644201161),(-975056543932607055664796),true⟩⟩⟩
  | 3 => ⟨⟨4563646661958,5899909706835,true⟩,⟨660559840000846971,754915258989036096,true⟩,⟨⟨453847772911325372584209,505772904386890908718407,true⟩,⟨1083669659937161786462785,1135594791412727322605656,true⟩⟩⟩
  | 4 => ⟨⟨(-34358662645),34361319022,true⟩,⟨4563646661958,5899909706835,true⟩,⟨⟨(-1229007198347543646835867),(-1162246315021836163109163),true⟩,⟨(-212205205134114180818585),(-145444321808406697105874),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34358662645),34361319022,true⟩,⟨⟨742678278001221924139644,824274913177071355447669,true⟩,⟨(-961486137369930784882226),(-879889502194081353572312),true⟩⟩⟩
theorem shortNegativeR026Q01F_ok : ∀ n : Fin 6, (shortNegativeR026Q01F n).encloses (FactoredFrequency.build shortNegativeR026Q01T (Grid.ofRats (371203539728957/549755813888000) (373351023376957/549755813888000)) n) := by decide +kernel
def shortNegativeR026Q01L : ℕ → ℚ
  | 0 => (-1297183/1000000)
  | 1 => (-333137/1000000)
  | 2 => (13849/200000)
  | 3 => (19363/1000000)
  | 4 => (-38449/100000)
  | 5 => (-117251/100000)
  | 6 => (-561007/250000)
  | 7 => (-172921/50000)
  | 8 => (-895087/200000)
  | 9 => (-495893/100000)
  | 10 => (-4395431/1000000)
  | 11 => (-1496539/500000)
  | _ => 0
def shortNegativeR026Q01U : ℕ → ℚ
  | 0 => (-274583/500000)
  | 1 => (237079/500000)
  | 2 => (57561/62500)
  | 3 => (443153/500000)
  | 4 => (96697/200000)
  | 5 => (-164429/1000000)
  | 6 => (-1078833/1000000)
  | 7 => (-2173371/1000000)
  | 8 => (-794333/250000)
  | 9 => (-3555003/1000000)
  | 10 => (-1475979/500000)
  | 11 => (-853607/500000)
  | _ => 0
private theorem shortNegativeR026Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR026Q01P shortNegativeR026Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR026Q01L (0:Fin 12)) (shortNegativeR026Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR026Q01P shortNegativeR026Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR026Q01L (1:Fin 12)) (shortNegativeR026Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR026Q01P shortNegativeR026Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR026Q01L (2:Fin 12)) (shortNegativeR026Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR026Q01P shortNegativeR026Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR026Q01L (3:Fin 12)) (shortNegativeR026Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR026Q01P shortNegativeR026Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR026Q01L (4:Fin 12)) (shortNegativeR026Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR026Q01P shortNegativeR026Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR026Q01L (5:Fin 12)) (shortNegativeR026Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR026Q01P shortNegativeR026Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR026Q01L (6:Fin 12)) (shortNegativeR026Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR026Q01P shortNegativeR026Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR026Q01L (7:Fin 12)) (shortNegativeR026Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR026Q01P shortNegativeR026Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR026Q01L (8:Fin 12)) (shortNegativeR026Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR026Q01P shortNegativeR026Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR026Q01L (9:Fin 12)) (shortNegativeR026Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR026Q01P shortNegativeR026Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR026Q01L (10:Fin 12)) (shortNegativeR026Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR026Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR026Q01P shortNegativeR026Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR026Q01L (11:Fin 12)) (shortNegativeR026Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR026Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR026Q01P shortNegativeR026Q01F (shortNegativeNodes12 k)).re (shortNegativeR026Q01L k) (shortNegativeR026Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR026Q01Point00
  · exact shortNegativeR026Q01Point01
  · exact shortNegativeR026Q01Point02
  · exact shortNegativeR026Q01Point03
  · exact shortNegativeR026Q01Point04
  · exact shortNegativeR026Q01Point05
  · exact shortNegativeR026Q01Point06
  · exact shortNegativeR026Q01Point07
  · exact shortNegativeR026Q01Point08
  · exact shortNegativeR026Q01Point09
  · exact shortNegativeR026Q01Point10
  · exact shortNegativeR026Q01Point11

theorem shortNegativeR026Q01Bound {t a : ℝ} (tl : ((107/100):ℝ)≤t) (tu : t≤((27/25):ℝ)) (al : ((371203539728957/549755813888000):ℝ)≤a) (au : a≤((373351023376957/549755813888000):ℝ)) : (((-1405843944273241134380015739444009/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-638901376504426534809946666801961/649037107316853453566312041152512):ℚ):ℝ) := by
  have ts : shortNegativeR026Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (371203539728957/549755813888000) (373351023376957/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR026Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR026Q01F_ok n) ts asb
  exact factored_negative_12_samples 4190 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip024Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR026Q01L shortNegativeR026Q01U (-1405843944273241134380015739444009/649037107316853453566312041152512) (-638901376504426534809946666801961/649037107316853453566312041152512) shortNegativeR026Q01Samples (by decide +kernel)

theorem short_original_negative_026 {t a : ℝ} (tb : RealMem negative_026.t t) (ab : RealMem negative_026.a a) : RealMem negative_026.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((107/100):ℝ) ((27/25):ℝ) := by simpa [negative_026,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((107/100):ℝ)<((27/25):ℝ)) tB
  have aB : a∈Icc ((369056056080957/549755813888000):ℝ) ((373351023376957/549755813888000):ℝ) := by simpa [negative_026,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((369056056080957/549755813888000):ℝ)<((373351023376957/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR026Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_026,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR026Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_026,RealMem] using v

def shortNegativeR027Q00T := Grid.ofRats (27/25) (109/100)
def shortNegativeR027Q00P : PrimalThetaParameters := ⟨⟨⟨39375803351164242353245,40632466967795749595702,true⟩,⟨0,0,true⟩⟩, ⟨⟨1283762321596345975472060,1291180197521485668743505,true⟩,⟨0,0,true⟩⟩, ⟨(-1230427830443612270106225),(-1215592078593401603044377),true⟩, ⟨4675385429063843786515372,4780630611874047779977829,true⟩⟩
theorem shortNegativeR027Q00P_ok : shortNegativeR027Q00P.encloses (primalThetaParameters shortNegativeR027Q00T (Grid.ofRats (1114952024566399/1649267441664000) (1121394475510399/1649267441664000))) := by decide +kernel

def shortNegativeR027Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨513578810041556926252192,517628330195539625670752,true⟩,⟨2823457589307146897825568,2845720284317344398311370,true⟩,⟨⟨582051101780600068363093,589468977705739761682414,true⟩,⟨1053829152685224702003123,1061247028610364395328985,true⟩⟩⟩
  | 1 => ⟨⟨3018921067652802536598,3189542139782870395347,true⟩,⟨513578810041556926252192,517628330195539625670752,true⟩,⟨⟨(-1218334465450443876785003),(-1196080837675162235857248),true⟩,⟨(-75557577806166617280663),(-53303950030884976368635),true⟩⟩⟩
  | 2 => ⟨⟨577997777023039601,660559908720323709,true⟩,⟨3018921067652802536598,3189542139782870395347,true⟩,⟨⟨676452340118978191539239,713541719744401780071452,true⟩,⟨(-1007726556668869106514759),(-970637177043445517978507),true⟩⟩⟩
  | 3 => ⟨⟨3570018874225,4632366138695,true⟩,⟨577997777023039601,660559908720323709,true⟩,⟨⟨443905193772708387906668,495830325248273924041155,true⟩,⟨1087916209490246328271578,1139841340965811864414930,true⟩⟩⟩
  | 4 => ⟨⟨(-34359006279),34360814092,true⟩,⟨3570018874225,4632366138695,true⟩,⟨⟨(-1226872037981941625082214),(-1160111154656234141355252),true⟩,⟨(-225940683786242982490110),(-159179800460535498776920),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359006279),34360814092,true⟩,⟨⟨755539283350034069156861,837135918525883500465313,true⟩,⟨(-950385071374103828202214),(-868788436198254396892207),true⟩⟩⟩
theorem shortNegativeR027Q00F_ok : ∀ n : Fin 6, (shortNegativeR027Q00F n).encloses (FactoredFrequency.build shortNegativeR027Q00T (Grid.ofRats (1114952024566399/1649267441664000) (1121394475510399/1649267441664000)) n) := by decide +kernel
def shortNegativeR027Q00L : ℕ → ℚ
  | 0 => (-1385223/1000000)
  | 1 => (-438669/1000000)
  | 2 => (-15861/500000)
  | 3 => (-7189/100000)
  | 4 => (-58037/125000)
  | 5 => (-1234923/1000000)
  | 6 => (-285107/125000)
  | 7 => (-865033/250000)
  | 8 => (-444149/100000)
  | 9 => (-982271/200000)
  | 10 => (-2182103/500000)
  | 11 => (-603801/200000)
  | _ => 0
def shortNegativeR027Q00U : ℕ → ℚ
  | 0 => (-640507/1000000)
  | 1 => (181833/500000)
  | 2 => (814923/1000000)
  | 3 => (198091/250000)
  | 4 => (404207/1000000)
  | 5 => (-113487/500000)
  | 6 => (-17507/15625)
  | 7 => (-2186117/1000000)
  | 8 => (-790017/250000)
  | 9 => (-1762181/500000)
  | 10 => (-1479233/500000)
  | 11 => (-1766057/1000000)
  | _ => 0
private theorem shortNegativeR027Q00Point00 : containedInReported (sampledFactoredPrimal shortNegativeR027Q00P shortNegativeR027Q00F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR027Q00L (0:Fin 12)) (shortNegativeR027Q00U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q00Point01 : containedInReported (sampledFactoredPrimal shortNegativeR027Q00P shortNegativeR027Q00F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR027Q00L (1:Fin 12)) (shortNegativeR027Q00U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q00Point02 : containedInReported (sampledFactoredPrimal shortNegativeR027Q00P shortNegativeR027Q00F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR027Q00L (2:Fin 12)) (shortNegativeR027Q00U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q00Point03 : containedInReported (sampledFactoredPrimal shortNegativeR027Q00P shortNegativeR027Q00F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR027Q00L (3:Fin 12)) (shortNegativeR027Q00U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q00Point04 : containedInReported (sampledFactoredPrimal shortNegativeR027Q00P shortNegativeR027Q00F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR027Q00L (4:Fin 12)) (shortNegativeR027Q00U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q00Point05 : containedInReported (sampledFactoredPrimal shortNegativeR027Q00P shortNegativeR027Q00F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR027Q00L (5:Fin 12)) (shortNegativeR027Q00U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q00Point06 : containedInReported (sampledFactoredPrimal shortNegativeR027Q00P shortNegativeR027Q00F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR027Q00L (6:Fin 12)) (shortNegativeR027Q00U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q00Point07 : containedInReported (sampledFactoredPrimal shortNegativeR027Q00P shortNegativeR027Q00F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR027Q00L (7:Fin 12)) (shortNegativeR027Q00U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q00Point08 : containedInReported (sampledFactoredPrimal shortNegativeR027Q00P shortNegativeR027Q00F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR027Q00L (8:Fin 12)) (shortNegativeR027Q00U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q00Point09 : containedInReported (sampledFactoredPrimal shortNegativeR027Q00P shortNegativeR027Q00F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR027Q00L (9:Fin 12)) (shortNegativeR027Q00U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q00Point10 : containedInReported (sampledFactoredPrimal shortNegativeR027Q00P shortNegativeR027Q00F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR027Q00L (10:Fin 12)) (shortNegativeR027Q00U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q00Point11 : containedInReported (sampledFactoredPrimal shortNegativeR027Q00P shortNegativeR027Q00F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR027Q00L (11:Fin 12)) (shortNegativeR027Q00U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR027Q00Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR027Q00P shortNegativeR027Q00F (shortNegativeNodes12 k)).re (shortNegativeR027Q00L k) (shortNegativeR027Q00U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR027Q00Point00
  · exact shortNegativeR027Q00Point01
  · exact shortNegativeR027Q00Point02
  · exact shortNegativeR027Q00Point03
  · exact shortNegativeR027Q00Point04
  · exact shortNegativeR027Q00Point05
  · exact shortNegativeR027Q00Point06
  · exact shortNegativeR027Q00Point07
  · exact shortNegativeR027Q00Point08
  · exact shortNegativeR027Q00Point09
  · exact shortNegativeR027Q00Point10
  · exact shortNegativeR027Q00Point11

theorem shortNegativeR027Q00Bound {t a : ℝ} (tl : ((27/25):ℝ)≤t) (tu : t≤((109/100):ℝ)) (al : ((1114952024566399/1649267441664000):ℝ)≤a) (au : a≤((1121394475510399/1649267441664000):ℝ)) : (((-2861548112244269480494823029629265/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1354471238002269257712188206637393/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR027Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1114952024566399/1649267441664000) (1121394475510399/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR027Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR027Q00F_ok n) ts asb
  exact factored_negative_12_samples 4190 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip024Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR027Q00L shortNegativeR027Q00U (-2861548112244269480494823029629265/1298074214633706907132624082305024) (-1354471238002269257712188206637393/1298074214633706907132624082305024) shortNegativeR027Q00Samples (by decide +kernel)

def shortNegativeR027Q01T := Grid.ofRats (27/25) (109/100)
def shortNegativeR027Q01P : PrimalThetaParameters := ⟨⟨⟨39375803351164242353245,40632466967795749595702,true⟩,⟨0,0,true⟩⟩, ⟨⟨1291180197521416949262655,1298598073446556642534124,true⟩,⟨0,0,true⟩⟩, ⟨(-1215592078593470322524987),(-1200756326743259655463187),true⟩, ⟨4650350183130964006645391,4755006941541116971390251,true⟩⟩
theorem shortNegativeR027Q01P_ok : shortNegativeR027Q01P.encloses (primalThetaParameters shortNegativeR027Q01T (Grid.ofRats (1121394475510399/1649267441664000) (1127836926454399/1649267441664000))) := by decide +kernel

def shortNegativeR027Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨513578810041556926252192,517628330195539625670752,true⟩,⟨2823457589307146897825568,2845720284317344398311370,true⟩,⟨⟨575551143277086423129612,582969019202226116449601,true⟩,⟨1057403400865477961767240,1064821276790617655093919,true⟩⟩⟩
  | 1 => ⟨⟨3018921067652802536598,3189542139782870395347,true⟩,⟨513578810041556926252192,517628330195539625670752,true⟩,⟨⟨(-1216943982828974903609698),(-1194690355053693262681491),true⟩,⟨(-97767407244387268567942),(-75513779469105627655138),true⟩⟩⟩
  | 2 => ⟨⟨577997777023039601,660559908720323709,true⟩,⟨3018921067652802536598,3189542139782870395347,true⟩,⟨⟨706468245751610709416898,743557625377034297949143,true⟩,⟨(-985942167892588981789084),(-948852788267165393253511),true⟩⟩⟩
  | 3 => ⟨⟨3570018874225,4632366138695,true⟩,⟨577997777023039601,660559908720323709,true⟩,⟨⟨395643834733066857826249,447568966208632393961498,true⟩,⟨1107064212592242619220269,1158989344067808155365314,true⟩⟩⟩
  | 4 => ⟨⟨(-34359006279),34360814092,true⟩,⟨3570018874225,4632366138695,true⟩,⟨⟨(-1214424246590867423384900),(-1147663363265159939656972),true⟩,⟨(-291522201500472583809789),(-224761318174765100094562),true⟩⟩⟩
  | _ => ⟨⟨(-34359738368),34359738369,true⟩,⟨(-34359006279),34360814092,true⟩,⟨⟨815072171562503368076340,896668806738352799383350,true⟩,⟨(-894605873851225703557971),(-813009238675376272251002),true⟩⟩⟩
theorem shortNegativeR027Q01F_ok : ∀ n : Fin 6, (shortNegativeR027Q01F n).encloses (FactoredFrequency.build shortNegativeR027Q01T (Grid.ofRats (1121394475510399/1649267441664000) (1127836926454399/1649267441664000)) n) := by decide +kernel
def shortNegativeR027Q01L : ℕ → ℚ
  | 0 => (-35791/25000)
  | 1 => (-479393/1000000)
  | 2 => (-60067/1000000)
  | 3 => (-10713/125000)
  | 4 => (-463157/1000000)
  | 5 => (-1217909/1000000)
  | 6 => (-2248183/1000000)
  | 7 => (-3415803/1000000)
  | 8 => (-2198551/500000)
  | 9 => (-4884313/1000000)
  | 10 => (-272341/62500)
  | 11 => (-3039799/1000000)
  | _ => 0
def shortNegativeR027Q01U : ℕ → ℚ
  | 0 => (-692711/1000000)
  | 1 => (63039/200000)
  | 2 => (3121/4000)
  | 3 => (773547/1000000)
  | 4 => (401097/1000000)
  | 5 => (-215081/1000000)
  | 6 => (-218851/200000)
  | 7 => (-2149463/1000000)
  | 8 => (-3123409/1000000)
  | 9 => (-437827/125000)
  | 10 => (-1490621/500000)
  | 11 => (-908313/500000)
  | _ => 0
private theorem shortNegativeR027Q01Point00 : containedInReported (sampledFactoredPrimal shortNegativeR027Q01P shortNegativeR027Q01F (shortNegativeNodes12 (0:Fin 12))).re (shortNegativeR027Q01L (0:Fin 12)) (shortNegativeR027Q01U (0:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q01Point01 : containedInReported (sampledFactoredPrimal shortNegativeR027Q01P shortNegativeR027Q01F (shortNegativeNodes12 (1:Fin 12))).re (shortNegativeR027Q01L (1:Fin 12)) (shortNegativeR027Q01U (1:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q01Point02 : containedInReported (sampledFactoredPrimal shortNegativeR027Q01P shortNegativeR027Q01F (shortNegativeNodes12 (2:Fin 12))).re (shortNegativeR027Q01L (2:Fin 12)) (shortNegativeR027Q01U (2:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q01Point03 : containedInReported (sampledFactoredPrimal shortNegativeR027Q01P shortNegativeR027Q01F (shortNegativeNodes12 (3:Fin 12))).re (shortNegativeR027Q01L (3:Fin 12)) (shortNegativeR027Q01U (3:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q01Point04 : containedInReported (sampledFactoredPrimal shortNegativeR027Q01P shortNegativeR027Q01F (shortNegativeNodes12 (4:Fin 12))).re (shortNegativeR027Q01L (4:Fin 12)) (shortNegativeR027Q01U (4:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q01Point05 : containedInReported (sampledFactoredPrimal shortNegativeR027Q01P shortNegativeR027Q01F (shortNegativeNodes12 (5:Fin 12))).re (shortNegativeR027Q01L (5:Fin 12)) (shortNegativeR027Q01U (5:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q01Point06 : containedInReported (sampledFactoredPrimal shortNegativeR027Q01P shortNegativeR027Q01F (shortNegativeNodes12 (6:Fin 12))).re (shortNegativeR027Q01L (6:Fin 12)) (shortNegativeR027Q01U (6:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q01Point07 : containedInReported (sampledFactoredPrimal shortNegativeR027Q01P shortNegativeR027Q01F (shortNegativeNodes12 (7:Fin 12))).re (shortNegativeR027Q01L (7:Fin 12)) (shortNegativeR027Q01U (7:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q01Point08 : containedInReported (sampledFactoredPrimal shortNegativeR027Q01P shortNegativeR027Q01F (shortNegativeNodes12 (8:Fin 12))).re (shortNegativeR027Q01L (8:Fin 12)) (shortNegativeR027Q01U (8:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q01Point09 : containedInReported (sampledFactoredPrimal shortNegativeR027Q01P shortNegativeR027Q01F (shortNegativeNodes12 (9:Fin 12))).re (shortNegativeR027Q01L (9:Fin 12)) (shortNegativeR027Q01U (9:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q01Point10 : containedInReported (sampledFactoredPrimal shortNegativeR027Q01P shortNegativeR027Q01F (shortNegativeNodes12 (10:Fin 12))).re (shortNegativeR027Q01L (10:Fin 12)) (shortNegativeR027Q01U (10:Fin 12))=true := by decide +kernel
private theorem shortNegativeR027Q01Point11 : containedInReported (sampledFactoredPrimal shortNegativeR027Q01P shortNegativeR027Q01F (shortNegativeNodes12 (11:Fin 12))).re (shortNegativeR027Q01L (11:Fin 12)) (shortNegativeR027Q01U (11:Fin 12))=true := by decide +kernel
theorem shortNegativeR027Q01Samples : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal shortNegativeR027Q01P shortNegativeR027Q01F (shortNegativeNodes12 k)).re (shortNegativeR027Q01L k) (shortNegativeR027Q01U k)=true := by
  intro k
  fin_cases k
  · exact shortNegativeR027Q01Point00
  · exact shortNegativeR027Q01Point01
  · exact shortNegativeR027Q01Point02
  · exact shortNegativeR027Q01Point03
  · exact shortNegativeR027Q01Point04
  · exact shortNegativeR027Q01Point05
  · exact shortNegativeR027Q01Point06
  · exact shortNegativeR027Q01Point07
  · exact shortNegativeR027Q01Point08
  · exact shortNegativeR027Q01Point09
  · exact shortNegativeR027Q01Point10
  · exact shortNegativeR027Q01Point11

theorem shortNegativeR027Q01Bound {t a : ℝ} (tl : ((27/25):ℝ)≤t) (tu : t≤((109/100):ℝ)) (al : ((1121394475510399/1649267441664000):ℝ)≤a) (au : a≤((1127836926454399/1649267441664000):ℝ)) : (((-2861548112244269480494823029629265/1298074214633706907132624082305024):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1354471238002269257712188206637393/1298074214633706907132624082305024):ℚ):ℝ) := by
  have ts : shortNegativeR027Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (1121394475510399/1649267441664000) (1127836926454399/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound shortNegativeR027Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (shortNegativeR027Q01F_ok n) ts asb
  exact factored_negative_12_samples 4190 ps fs shortNegativeNodes12Sound (by linarith) (by linarith) (shortNegativeStrip024Bound (by linarith) (by linarith) (by linarith) (by linarith)) shortNegativeR027Q01L shortNegativeR027Q01U (-2861548112244269480494823029629265/1298074214633706907132624082305024) (-1354471238002269257712188206637393/1298074214633706907132624082305024) shortNegativeR027Q01Samples (by decide +kernel)

theorem short_original_negative_027 {t a : ℝ} (tb : RealMem negative_027.t t) (ab : RealMem negative_027.a a) : RealMem negative_027.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((27/25):ℝ) ((109/100):ℝ) := by simpa [negative_027,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((27/25):ℝ)<((109/100):ℝ)) tB
  have aB : a∈Icc ((1114952024566399/1649267441664000):ℝ) ((1127836926454399/1649267441664000):ℝ) := by simpa [negative_027,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((1114952024566399/1649267441664000):ℝ)<((1127836926454399/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @shortNegativeR027Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_027,RealMem] using v
  · norm_num at tl tu al au
    have v := @shortNegativeR027Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_027,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_024
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_025
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_026
#print axioms TwoAxisHelicoid.PdfVertical.short_original_negative_027
