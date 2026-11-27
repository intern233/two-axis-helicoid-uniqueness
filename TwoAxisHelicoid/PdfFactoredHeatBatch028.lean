import TwoAxisHelicoid.PdfFactoredPeriodicSamples
import TwoAxisHelicoid.PdfFactoredNodes32
import TwoAxisHelicoid.PdfHeatStripAll

namespace TwoAxisHelicoid.PdfVertical

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR028Q00T := Grid.ofRats (439/500) (879/1000)
def factoredHeatR028Q00P : HeatGridParameters := ⟨⟨⟨⟨76403426864565102248974,76643832740121012933001,true⟩,⟨0,0,true⟩⟩, ⟨⟨1134074899287874150058034,1135929368269210612986038,true⟩,⟨0,0,true⟩⟩, ⟨(-1529802675060555920935230),(-1526093737097951714558322),true⟩, ⟨6138011372700446993722473,6175646191448782285935304,true⟩⟩, ⟨386944255436444821841817,411336069434704606678802,true⟩, ⟨596830888634121467690902,603651718552788050850788,true⟩, ⟨(-1460926453476743773315081),(-1447328640513303086436006),true⟩, ⟨(-2726644978042809324199815),(-2719485463034534759244135),true⟩, ⟨(-600752105676552877356889),(-599295609144518935199549),true⟩⟩
theorem factoredHeatR028Q00P_ok : factoredHeatR028Q00P.encloses (heatGridParameters factoredHeatR028Q00T (Grid.ofRats (984947979621833/1649267441664000) (986558592357833/1649267441664000))) := by decide +kernel
def factoredHeatR028Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨606146985079018725132685,606623238807837932624998,true⟩,⟨2409241096999796286551026,2411134053797720630858635,true⟩,⟨⟨713203267790682906343413,715057736772019369318995,true⟩,⟨974531254140338585445640,976385723121675048424943,true⟩⟩⟩
  | 1 => ⟨⟨9630475413272991752200,9683567528101852474657,true⟩,⟨606146985079018725132685,606623238807837932624998,true⟩,⟨⟨(-1148406707144686242295229),(-1142843300200814292395988),true⟩,⟨383281747648101875575742,388845154591973825464515,true⟩⟩⟩
  | 2 => ⟨⟨9670093821080480697,9800072538516378632,true⟩,⟨9630475413272991752200,9683567528101852474657,true⟩,⟨⟨(-26553013278965508198635),(-17280668372558071388343),true⟩,⟨(-1213363308501336435883046),(-1204090963594928999056419),true⟩⟩⟩
  | 3 => ⟨⟨613624256831219,628817304650196,true⟩,⟨9670093821080480697,9800072538516378632,true⟩,⟨⟨1152377034654560644829257,1165358317523503568539994,true⟩,⟨337787366354160138786942,350768649223103062486470,true⟩⟩⟩
  | 4 => ⟨⟨(-31898599218),36917439404,true⟩,⟨613624256831219,628817304650196,true⟩,⟨⟨(-686643466217498022109762),(-669953245386019611463869),true⟩,⟨992361129120886008123991,1009051349952364418774319,true⟩⟩⟩
  | _ => ⟨⟨(-34359737745),34359739028,true⟩,⟨(-31898599218),36917439404,true⟩,⟨⟨(-759223382557648550158139),(-738824223763634652609917),true⟩,⟨(-959127911585308376140038),(-938728752791294478589062),true⟩⟩⟩
theorem factoredHeatR028Q00F_ok : ∀ n : Fin 6, (factoredHeatR028Q00F n).encloses (FactoredFrequency.build factoredHeatR028Q00T (Grid.ofRats (984947979621833/1649267441664000) (986558592357833/1649267441664000)) n) := by decide +kernel
def factoredHeatR028Q00U : ℕ → ℚ
  | 0 => (-21541751/500000)
  | 1 => (-8000849/250000)
  | 2 => (-2032907/100000)
  | 3 => (-1549929/125000)
  | 4 => (-7784303/1000000)
  | 5 => (-664281/125000)
  | 6 => (-1973759/500000)
  | 7 => (-3298877/1000000)
  | 8 => (-3201011/1000000)
  | 9 => (-153049/40000)
  | 10 => (-2969009/500000)
  | 11 => (-2521473/250000)
  | 12 => (-15735339/1000000)
  | 13 => (-1078719/50000)
  | 14 => (-988569/40000)
  | 15 => (-23153243/1000000)
  | 16 => (-756773/40000)
  | 17 => (-454631/31250)
  | 18 => (-11876599/1000000)
  | 19 => (-428649/40000)
  | 20 => (-5193973/500000)
  | 21 => (-1012829/100000)
  | 22 => (-9003187/1000000)
  | 23 => (-5980771/1000000)
  | 24 => (5241/12500)
  | 25 => (5431293/500000)
  | 26 => (24205039/1000000)
  | 27 => (8743923/250000)
  | 28 => (16707247/500000)
  | 29 => (5977081/500000)
  | 30 => (-1021223/50000)
  | 31 => (-41957289/1000000)
  | _ => 0
theorem factoredHeatR028Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR028Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR028Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR028Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR028Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR028Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR028Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR028Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR028Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR028Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR028Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR028Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR028Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR028Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR028Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR028Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR028Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR028Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR028Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR028Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR028Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR028Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR028Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR028Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR028Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR028Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR028Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR028Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR028Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR028Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR028Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR028Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR028Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR028Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR028Q00P factoredHeatR028Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR028Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR028Q00Point00
  · exact factoredHeatR028Q00Point01
  · exact factoredHeatR028Q00Point02
  · exact factoredHeatR028Q00Point03
  · exact factoredHeatR028Q00Point04
  · exact factoredHeatR028Q00Point05
  · exact factoredHeatR028Q00Point06
  · exact factoredHeatR028Q00Point07
  · exact factoredHeatR028Q00Point08
  · exact factoredHeatR028Q00Point09
  · exact factoredHeatR028Q00Point10
  · exact factoredHeatR028Q00Point11
  · exact factoredHeatR028Q00Point12
  · exact factoredHeatR028Q00Point13
  · exact factoredHeatR028Q00Point14
  · exact factoredHeatR028Q00Point15
  · exact factoredHeatR028Q00Point16
  · exact factoredHeatR028Q00Point17
  · exact factoredHeatR028Q00Point18
  · exact factoredHeatR028Q00Point19
  · exact factoredHeatR028Q00Point20
  · exact factoredHeatR028Q00Point21
  · exact factoredHeatR028Q00Point22
  · exact factoredHeatR028Q00Point23
  · exact factoredHeatR028Q00Point24
  · exact factoredHeatR028Q00Point25
  · exact factoredHeatR028Q00Point26
  · exact factoredHeatR028Q00Point27
  · exact factoredHeatR028Q00Point28
  · exact factoredHeatR028Q00Point29
  · exact factoredHeatR028Q00Point30
  · exact factoredHeatR028Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR028Q00Bound {t a : ℝ} (tl : ((439/500):ℝ)≤t) (tu : t≤((879/1000):ℝ)) (al : ((984947979621833/1649267441664000):ℝ)≤a) (au : a≤((986558592357833/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-323114554895302122125156629707933/40564819207303340847894502572032):ℚ):ℝ) := by
  have ts : factoredHeatR028Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (984947979621833/1649267441664000) (986558592357833/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR028Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR028Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR028Q00U (-323114554895302122125156629707933/40564819207303340847894502572032) factoredHeatR028Q00Samples (by decide +kernel)

theorem factored_original_heat_028 {t a : ℝ} (tb : RealMem derivative_028.t t) (ab : RealMem derivative_028.a a) : reportedHeatPeriod t a≤(derivative_028.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((439/500):ℝ) ((879/1000):ℝ) := by simpa [derivative_028,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((439/500):ℝ)<((879/1000):ℝ)) tB
  have aB : a∈Icc ((984947979621833/1649267441664000):ℝ) ((986558592357833/1649267441664000):ℝ) := by simpa [derivative_028,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((984947979621833/1649267441664000):ℝ)<((986558592357833/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR028Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_028] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR029Q00T := Grid.ofRats (879/1000) (22/25)
def factoredHeatR029Q00P : HeatGridParameters := ⟨⟨⟨⟨76163775061296151436759,76403426864633821726718,true⟩,⟨0,0,true⟩⟩, ⟨⟨1134702226317270074493659,1136556695298606537421665,true⟩,⟨0,0,true⟩⟩, ⟨(-1528548021001764072063976),(-1524839083039159865687072),true⟩, ⟨6129824853435079625690090,6167354819075034639280085,true⟩⟩, ⟨387679332174268968136165,412050378645354331881206,true⟩, ⟨596800549333248434245302,603609189835577085820294,true⟩, ⟨(-1458950203996053600482654),(-1445392731079171348328077),true⟩, ⟨(-2722819484469716482760622),(-2715682942829928245490980),true⟩, ⟨(-600259404179815741238050),(-598802907647781799080713),true⟩⟩
theorem factoredHeatR029Q00P_ok : factoredHeatR029Q00P.encloses (heatGridParameters factoredHeatR029Q00T (Grid.ofRats (985492815320563/1649267441664000) (987103428056563/1649267441664000))) := by decide +kernel
def factoredHeatR029Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨605671105252221934969711,606146985079087444631281,true⟩,⟨2411134053797651911295282,2413028497904357020631646,true⟩,⟨⟨712696993813146155666652,714551462794482618642044,true⟩,⟨974901694220039913570436,976756163201376376549488,true⟩⟩⟩
  | 1 => ⟨⟨9577674386755023021453,9630475413341711229416,true⟩,⟨605671105252221934969711,606146985079087444631281,true⟩,⟨⟨(-1149006318477656543526304),(-1143442911533784593627193),true⟩,⟨381497842283352150792920,387061249227224100681541,true⟩⟩⟩
  | 2 => ⟨⟨9541839082989718763,9670093889799957434,true⟩,⟨9577674386755023021453,9630475413341711229416,true⟩,⟨⟨(-23416823378343712912800),(-14144478471936276102549),true⟩,⟨(-1213416104650016355617906),(-1204143759743608918791275),true⟩⟩⟩
  | 3 => ⟨⟨598863719061949,613692976307956,true⟩,⟨9541839082989718763,9670093889799957434,true⟩,⟨⟨1151118840466869959079545,1164100123335812882790589,true⟩,⟨341994544395587614718838,354975827264530538418747,true⟩⟩⟩
  | 4 => ⟨⟨(-31991515564),36820877519,true⟩,⟨598863719061949,613692976307956,true⟩,⟨⟨(-691309565189439503563268),(-674619344357961092918031),true⟩,⟨989182428475576415335140,1005872649307054825984704,true⟩⟩⟩
  | _ => ⟨⟨(-34359737779),34359738992,true⟩,⟨(-31991515564),36820877519,true⟩,⟨⟨(-753794688578682605721421),(-733395529784668708173106),true⟩,⟨(-963387887619466618969542),(-942988728825452721418336),true⟩⟩⟩
theorem factoredHeatR029Q00F_ok : ∀ n : Fin 6, (factoredHeatR029Q00F n).encloses (FactoredFrequency.build factoredHeatR029Q00T (Grid.ofRats (985492815320563/1649267441664000) (987103428056563/1649267441664000)) n) := by decide +kernel
def factoredHeatR029Q00U : ℕ → ℚ
  | 0 => (-2681863/62500)
  | 1 => (-31972987/1000000)
  | 2 => (-2546923/125000)
  | 3 => (-498613/40000)
  | 4 => (-7843861/1000000)
  | 5 => (-670137/125000)
  | 6 => (-796267/200000)
  | 7 => (-3320073/1000000)
  | 8 => (-3208509/1000000)
  | 9 => (-59677/15625)
  | 10 => (-5912069/1000000)
  | 11 => (-10034613/1000000)
  | 12 => (-3913997/250000)
  | 13 => (-10738657/500000)
  | 14 => (-24628879/1000000)
  | 15 => (-23115853/1000000)
  | 16 => (-757057/40000)
  | 17 => (-14578751/1000000)
  | 18 => (-1488671/125000)
  | 19 => (-10740193/1000000)
  | 20 => (-5199909/500000)
  | 21 => (-10127269/1000000)
  | 22 => (-359603/40000)
  | 23 => (-5958361/1000000)
  | 24 => (87299/200000)
  | 25 => (2170287/200000)
  | 26 => (24137197/1000000)
  | 27 => (17426257/500000)
  | 28 => (16655433/500000)
  | 29 => (3001987/250000)
  | 30 => (-4033891/200000)
  | 31 => (-4165861/100000)
  | _ => 0
theorem factoredHeatR029Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR029Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR029Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR029Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR029Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR029Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR029Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR029Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR029Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR029Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR029Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR029Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR029Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR029Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR029Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR029Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR029Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR029Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR029Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR029Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR029Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR029Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR029Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR029Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR029Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR029Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR029Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR029Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR029Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR029Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR029Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR029Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR029Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR029Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR029Q00P factoredHeatR029Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR029Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR029Q00Point00
  · exact factoredHeatR029Q00Point01
  · exact factoredHeatR029Q00Point02
  · exact factoredHeatR029Q00Point03
  · exact factoredHeatR029Q00Point04
  · exact factoredHeatR029Q00Point05
  · exact factoredHeatR029Q00Point06
  · exact factoredHeatR029Q00Point07
  · exact factoredHeatR029Q00Point08
  · exact factoredHeatR029Q00Point09
  · exact factoredHeatR029Q00Point10
  · exact factoredHeatR029Q00Point11
  · exact factoredHeatR029Q00Point12
  · exact factoredHeatR029Q00Point13
  · exact factoredHeatR029Q00Point14
  · exact factoredHeatR029Q00Point15
  · exact factoredHeatR029Q00Point16
  · exact factoredHeatR029Q00Point17
  · exact factoredHeatR029Q00Point18
  · exact factoredHeatR029Q00Point19
  · exact factoredHeatR029Q00Point20
  · exact factoredHeatR029Q00Point21
  · exact factoredHeatR029Q00Point22
  · exact factoredHeatR029Q00Point23
  · exact factoredHeatR029Q00Point24
  · exact factoredHeatR029Q00Point25
  · exact factoredHeatR029Q00Point26
  · exact factoredHeatR029Q00Point27
  · exact factoredHeatR029Q00Point28
  · exact factoredHeatR029Q00Point29
  · exact factoredHeatR029Q00Point30
  · exact factoredHeatR029Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR029Q00Bound {t a : ℝ} (tl : ((879/1000):ℝ)≤t) (tu : t≤((22/25):ℝ)) (al : ((985492815320563/1649267441664000):ℝ)≤a) (au : a≤((987103428056563/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-647756950518524559778055322489267/81129638414606681695789005144064):ℚ):ℝ) := by
  have ts : factoredHeatR029Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (985492815320563/1649267441664000) (987103428056563/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR029Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR029Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR029Q00U (-647756950518524559778055322489267/81129638414606681695789005144064) factoredHeatR029Q00Samples (by decide +kernel)

theorem factored_original_heat_029 {t a : ℝ} (tb : RealMem derivative_029.t t) (ab : RealMem derivative_029.a a) : reportedHeatPeriod t a≤(derivative_029.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((879/1000):ℝ) ((22/25):ℝ) := by simpa [derivative_029,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((879/1000):ℝ)<((22/25):ℝ)) tB
  have aB : a∈Icc ((985492815320563/1649267441664000):ℝ) ((987103428056563/1649267441664000):ℝ) := by simpa [derivative_029,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((985492815320563/1649267441664000):ℝ)<((987103428056563/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR029Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_029] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR030Q00T := Grid.ofRats (22/25) (881/1000)
def factoredHeatR030Q00P : HeatGridParameters := ⟨⟨⟨⟨75924874964975003390344,76163775061364870914507,true⟩,⟨0,0,true⟩⟩, ⟨⟨1135330692604752872706693,1137185161586089335634701,true⟩,⟨0,0,true⟩⟩, ⟨(-1527291088426798475637903),(-1523582150464194269261003),true⟩, ⟨6121651053887473200865376,6159076516792147949272048,true⟩⟩, ⟨388414996400523660921713,412765385219479510518698,true⟩, ⟨596766942407079509481397,603563414659378496375265,true⟩, ⟨(-1456981783567384443250361),(-1443464506863159739574951),true⟩, ⟨(-2719000534931513426580027),(-2711886887187051184400813),true⟩, ⟨(-599765807911869538763820),(-598309311379835596606486),true⟩⟩
theorem factoredHeatR030Q00P_ok : factoredHeatR030Q00P.encloses (heatGridParameters factoredHeatR030Q00T (Grid.ofRats (328679546822963/549755813888000) (329216417734963/549755813888000))) := by decide +kernel
def factoredHeatR030Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨605195599033832225488930,605671105252290654468586,true⟩,⟨2413028497904288301067222,2414924430488362603783991,true⟩,⟨⟨712189607734479546139461,714044076715816009114869,true⟩,⟨975272543559776015702771,977127012541112478681850,true⟩⟩⟩
  | 1 => ⟨⟨9525162852529148080964,9577674386823742498669,true⟩,⟨605195599033832225488930,605671105252290654468586,true⟩,⟨⟨(-1149604233364000209386941),(-1144040826420128259487815),true⟩,⟨379709763443168359480403,385273170387040309368991,true⟩⟩⟩
  | 2 => ⟨⟨9415285391247485895,9541839151709195501,true⟩,⟨9525162852529148080964,9577674386823742498669,true⟩,⟨⟨(-20274811237301781737464),(-11002466330894344927547),true⟩,⟨(-1213460837285901207681969),(-1204188492379493770855630),true⟩⟩⟩
  | 3 => ⟨⟨584458221488247,598932438538686,true⟩,⟨9415285391247485895,9541839151709195501,true⟩,⟨⟨1149843045937576038538036,1162824328806518962248920,true⟩,⟨346204752325451114954121,359186035194394038653949,true⟩⟩⟩
  | 4 => ⟨⟨(-32080924004),36727961173,true⟩,⟨584458221488247,598932438538686,true⟩,⟨⟨(-695969201325770299507638),(-679278980494291888862608),true⟩,⟨985976138945379603584582,1002666359776858014233830,true⟩⟩⟩
  | _ => ⟨⟨(-34359737811),34359738958,true⟩,⟨(-32080924004),36727961173,true⟩,⟨⟨(-748331842337802281501984),(-727932683543788383953837),true⟩,⟨(-967624458819305802620772),(-947225300025291905069602),true⟩⟩⟩
theorem factoredHeatR030Q00F_ok : ∀ n : Fin 6, (factoredHeatR030Q00F n).encloses (FactoredFrequency.build factoredHeatR030Q00T (Grid.ofRats (328679546822963/549755813888000) (329216417734963/549755813888000)) n) := by decide +kernel
def factoredHeatR030Q00U : ℕ → ℚ
  | 0 => (-4273597/100000)
  | 1 => (-15970747/500000)
  | 2 => (-1021031/50000)
  | 3 => (-3132617/250000)
  | 4 => (-7902947/1000000)
  | 5 => (-2703817/500000)
  | 6 => (-1003733/250000)
  | 7 => (-334111/100000)
  | 8 => (-3215913/1000000)
  | 9 => (-3812411/1000000)
  | 10 => (-2943101/500000)
  | 11 => (-9983547/1000000)
  | 12 => (-15576981/1000000)
  | 13 => (-2138061/100000)
  | 14 => (-24543667/1000000)
  | 15 => (-23078153/1000000)
  | 16 => (-946649/50000)
  | 17 => (-14608791/1000000)
  | 18 => (-5970873/500000)
  | 19 => (-5381941/500000)
  | 20 => (-5205741/500000)
  | 21 => (-5063047/500000)
  | 22 => (-4488437/500000)
  | 23 => (-5935953/1000000)
  | 24 => (226811/500000)
  | 25 => (10840207/1000000)
  | 26 => (24069509/1000000)
  | 27 => (34729857/1000000)
  | 28 => (3320769/100000)
  | 29 => (12061043/1000000)
  | 30 => (-4979107/250000)
  | 31 => (-20680719/500000)
  | _ => 0
theorem factoredHeatR030Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR030Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR030Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR030Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR030Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR030Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR030Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR030Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR030Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR030Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR030Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR030Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR030Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR030Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR030Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR030Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR030Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR030Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR030Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR030Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR030Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR030Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR030Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR030Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR030Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR030Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR030Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR030Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR030Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR030Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR030Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR030Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR030Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR030Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR030Q00P factoredHeatR030Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR030Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR030Q00Point00
  · exact factoredHeatR030Q00Point01
  · exact factoredHeatR030Q00Point02
  · exact factoredHeatR030Q00Point03
  · exact factoredHeatR030Q00Point04
  · exact factoredHeatR030Q00Point05
  · exact factoredHeatR030Q00Point06
  · exact factoredHeatR030Q00Point07
  · exact factoredHeatR030Q00Point08
  · exact factoredHeatR030Q00Point09
  · exact factoredHeatR030Q00Point10
  · exact factoredHeatR030Q00Point11
  · exact factoredHeatR030Q00Point12
  · exact factoredHeatR030Q00Point13
  · exact factoredHeatR030Q00Point14
  · exact factoredHeatR030Q00Point15
  · exact factoredHeatR030Q00Point16
  · exact factoredHeatR030Q00Point17
  · exact factoredHeatR030Q00Point18
  · exact factoredHeatR030Q00Point19
  · exact factoredHeatR030Q00Point20
  · exact factoredHeatR030Q00Point21
  · exact factoredHeatR030Q00Point22
  · exact factoredHeatR030Q00Point23
  · exact factoredHeatR030Q00Point24
  · exact factoredHeatR030Q00Point25
  · exact factoredHeatR030Q00Point26
  · exact factoredHeatR030Q00Point27
  · exact factoredHeatR030Q00Point28
  · exact factoredHeatR030Q00Point29
  · exact factoredHeatR030Q00Point30
  · exact factoredHeatR030Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR030Q00Bound {t a : ℝ} (tl : ((22/25):ℝ)≤t) (tu : t≤((881/1000):ℝ)) (al : ((328679546822963/549755813888000):ℝ)≤a) (au : a≤((329216417734963/549755813888000):ℝ)) : reportedHeatPeriod t a≤(((-2596297883414406675683805505513979/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR030Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (328679546822963/549755813888000) (329216417734963/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR030Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR030Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR030Q00U (-2596297883414406675683805505513979/324518553658426726783156020576256) factoredHeatR030Q00Samples (by decide +kernel)

theorem factored_original_heat_030 {t a : ℝ} (tb : RealMem derivative_030.t t) (ab : RealMem derivative_030.a a) : reportedHeatPeriod t a≤(derivative_030.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((22/25):ℝ) ((881/1000):ℝ) := by simpa [derivative_030,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((22/25):ℝ)<((881/1000):ℝ)) tB
  have aB : a∈Icc ((328679546822963/549755813888000):ℝ) ((329216417734963/549755813888000):ℝ) := by simpa [derivative_030,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((328679546822963/549755813888000):ℝ)<((329216417734963/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR030Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_030] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR031Q00T := Grid.ofRats (881/1000) (441/500)
def factoredHeatR031Q00P : HeatGridParameters := ⟨⟨⟨⟨75686724217750276783807,75924874965043722868085,true⟩,⟨0,0,true⟩⟩, ⟨⟨1135960299166638582056180,1137814768147975044984190,true⟩,⟨0,0,true⟩⟩, ⟨(-1526031875303027056938926),(-1522322937340422850562030),true⟩, ⟨6113489970119183332478735,6150811279487852718993074,true⟩⟩, ⟨389151254603024146427922,413481095352419429538671,true⟩, ⟨596730072422201994967430,603514397552870271327079,true⟩, ⟨(-1455021171358494746529539),(-1441543947552827099030562),true⟩, ⟨(-2715188139803497004969462),(-2708097306815156352173213),true⟩, ⟨(-599271316074501520761034),(-597814819542467578603703),true⟩⟩
theorem factoredHeatR031Q00P_ok : factoredHeatR031Q00P.encloses (heatGridParameters factoredHeatR031Q00T (Grid.ofRats (197317091189897/329853488332800) (197639213737097/329853488332800))) := by decide +kernel
def factoredHeatR031Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨604720466130533440001966,605195599033900944987370,true⟩,⟨2414924430488293884220477,2416821852719243976388434,true⟩,⟨⟨711681107822389546038378,713535576803726009013696,true⟩,⟨975643801223958514023857,977498270205294977002873,true⟩⟩⟩
  | 1 => ⟨⟨9472939223395406846662,9525162852597867558169,true⟩,⟨604720466130533440001966,605195599033900944987370,true⟩,⟨⟨(-1150200436144260629786736),(-1144637029200388679887422),true⟩,⟨377917507511668885823505,383480914455540835712260,true⟩⟩⟩
  | 2 => ⟨⟨9290410184826229283,9415285459966962633,true⟩,⟨9472939223395406846662,9525162852597867558169,true⟩,⟨⟨(-17126992370471839480857),(-7854647464064402670062),true⟩,⟨(-1213497461745195769756314),(-1204225116838788332929054),true⟩⟩⟩
  | 3 => ⟨⟨570399224208487,584526940964984,true⟩,⟨9290410184826229283,9415285459966962633,true⟩,⟨⟨1148549582541906282774427,1161530865410849206485582,true⟩,⟨350417915940526276479505,363399198809469200179678,true⟩⟩⟩
  | 4 => ⟨⟨(-32166956972),36638552733,true⟩,⟨570399224208487,584526940964984,true⟩,⟨⟨(-700622198544081329717860),(-683931977712602919071799),true⟩,⟨982742206919845787731289,999432427751324198381459,true⟩⟩⟩
  | _ => ⟨⟨(-34359737841),34359738926,true⟩,⟨(-32166956972),36638552733,true⟩,⟨⟨(-742834881830066735875714),(-722435723036052838327350),true⟩,⟨(-971837323539634671061609),(-951438164745620773510090),true⟩⟩⟩
theorem factoredHeatR031Q00F_ok : ∀ n : Fin 6, (factoredHeatR031Q00F n).encloses (FactoredFrequency.build factoredHeatR031Q00T (Grid.ofRats (197317091189897/329853488332800) (197639213737097/329853488332800)) n) := by decide +kernel
def factoredHeatR031Q00U : ℕ → ℚ
  | 0 => (-21280999/500000)
  | 1 => (-31908857/1000000)
  | 2 => (-20464783/1000000)
  | 3 => (-629743/50000)
  | 4 => (-3980779/500000)
  | 5 => (-272693/50000)
  | 6 => (-4048309/1000000)
  | 7 => (-3361989/1000000)
  | 8 => (-3223223/1000000)
  | 9 => (-76109/20000)
  | 10 => (-1172083/200000)
  | 11 => (-2483173/250000)
  | 12 => (-3874579/250000)
  | 13 => (-21284267/1000000)
  | 14 => (-24458589/1000000)
  | 15 => (-11520073/500000)
  | 16 => (-18938993/1000000)
  | 17 => (-7319157/500000)
  | 18 => (-2394747/200000)
  | 19 => (-10787293/1000000)
  | 20 => (-10422937/1000000)
  | 21 => (-2024953/200000)
  | 22 => (-4481793/500000)
  | 23 => (-118271/20000)
  | 24 => (23533/50000)
  | 25 => (5414451/500000)
  | 26 => (960079/40000)
  | 27 => (34607717/1000000)
  | 28 => (8276241/250000)
  | 29 => (12113453/1000000)
  | 30 => (-19665363/1000000)
  | 31 => (-20532853/500000)
  | _ => 0
theorem factoredHeatR031Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR031Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR031Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR031Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR031Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR031Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR031Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR031Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR031Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR031Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR031Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR031Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR031Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR031Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR031Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR031Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR031Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR031Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR031Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR031Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR031Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR031Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR031Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR031Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR031Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR031Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR031Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR031Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR031Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR031Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR031Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR031Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR031Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR031Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR031Q00P factoredHeatR031Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR031Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR031Q00Point00
  · exact factoredHeatR031Q00Point01
  · exact factoredHeatR031Q00Point02
  · exact factoredHeatR031Q00Point03
  · exact factoredHeatR031Q00Point04
  · exact factoredHeatR031Q00Point05
  · exact factoredHeatR031Q00Point06
  · exact factoredHeatR031Q00Point07
  · exact factoredHeatR031Q00Point08
  · exact factoredHeatR031Q00Point09
  · exact factoredHeatR031Q00Point10
  · exact factoredHeatR031Q00Point11
  · exact factoredHeatR031Q00Point12
  · exact factoredHeatR031Q00Point13
  · exact factoredHeatR031Q00Point14
  · exact factoredHeatR031Q00Point15
  · exact factoredHeatR031Q00Point16
  · exact factoredHeatR031Q00Point17
  · exact factoredHeatR031Q00Point18
  · exact factoredHeatR031Q00Point19
  · exact factoredHeatR031Q00Point20
  · exact factoredHeatR031Q00Point21
  · exact factoredHeatR031Q00Point22
  · exact factoredHeatR031Q00Point23
  · exact factoredHeatR031Q00Point24
  · exact factoredHeatR031Q00Point25
  · exact factoredHeatR031Q00Point26
  · exact factoredHeatR031Q00Point27
  · exact factoredHeatR031Q00Point28
  · exact factoredHeatR031Q00Point29
  · exact factoredHeatR031Q00Point30
  · exact factoredHeatR031Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR031Q00Bound {t a : ℝ} (tl : ((881/1000):ℝ)≤t) (tu : t≤((441/500):ℝ)) (al : ((197317091189897/329853488332800):ℝ)≤a) (au : a≤((197639213737097/329853488332800):ℝ)) : reportedHeatPeriod t a≤(((-1300398697238686894360205819024121/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : factoredHeatR031Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (197317091189897/329853488332800) (197639213737097/329853488332800)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR031Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR031Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR031Q00U (-1300398697238686894360205819024121/162259276829213363391578010288128) factoredHeatR031Q00Samples (by decide +kernel)

theorem factored_original_heat_031 {t a : ℝ} (tb : RealMem derivative_031.t t) (ab : RealMem derivative_031.a a) : reportedHeatPeriod t a≤(derivative_031.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((881/1000):ℝ) ((441/500):ℝ) := by simpa [derivative_031,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((881/1000):ℝ)<((441/500):ℝ)) tB
  have aB : a∈Icc ((197317091189897/329853488332800):ℝ) ((197639213737097/329853488332800):ℝ) := by simpa [derivative_031,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((197317091189897/329853488332800):ℝ)<((197639213737097/329853488332800):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR031Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_031] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR032Q00T := Grid.ofRats (441/500) (883/1000)
def factoredHeatR032Q00P : HeatGridParameters := ⟨⟨⟨⟨75449320469166375513968,75686724217818996261547,true⟩,⟨0,0,true⟩⟩, ⟨⟨1136591047023841955002335,1138445516005178417930347,true⟩,⟨0,0,true⟩⟩, ⟨(-1524770379588620311046613),(-1521061441626016104669721),true⟩, ⟨6105341598060500545066609,6142559101922265811552630,true⟩⟩, ⟨389888113300269361517629,414197515274899805462488,true⟩, ⟨596689943946069185546941,603462143045747411521737,true⟩, ⟨(-1453068346573524838568468),(-1439631032869901838322060),true⟩, ⟨(-2711382309259439337228095),(-2704314212220046524976674),true⟩, ⟨(-598775927865887115662079),(-597319431333853173504751),true⟩⟩
theorem factoredHeatR032Q00P_ok : factoredHeatR032Q00P.encloses (heatGridParameters factoredHeatR032Q00T (Grid.ofRats (987133262649019/1649267441664000) (988743875385019/1649267441664000))) := by decide +kernel
def factoredHeatR032Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨604245706249239701349373,604720466130602159500507,true⟩,⟨2416821852719175256825081,2418720765767426623649490,true⟩,⟨⟨711171492339263348581094,713025961320599811556711,true⟩,⟨976015466274373259306488,977869935255709722285799,true⟩⟩⟩
  | 1 => ⟨⟨9421001920855983582034,9472939223464126323873,true⟩,⟨604245706249239701349373,604720466130602159500507,true⟩,⟨⟨(-1150794911108684268318455),(-1145231504164812318419277),true⟩,⟨376121070894374476004764,381684477838246425893342,true⟩⟩⟩
  | 2 => ⟨⟨9167191201925965478,9290410253545706021,true⟩,⟨9421001920855983582034,9472939223464126323873,true⟩,⟨⟨(-13973382500001174218660),(-4701037593593737408863),true⟩,⟨(-1213525933283133530279498),(-1204253588376726093453191),true⟩⟩⟩
  | 3 => ⟨⟨556678392734180,570467943685224,true⟩,⟨9167191201925965478,9290410253545706021,true⟩,⟨⟨1147238381883977924456915,1160219664752920848167712,true⟩,⟨354633960446319526738933,367615243315262450438824,true⟩⟩⟩
  | 4 => ⟨⟨(-32249741903),36552519765,true⟩,⟨556678392734180,570467943685224,true⟩,⟨⟨(-705268379769756913533999),(-688578158938278502888572),true⟩,⟨979480579655039526949996,996170800486517937599429,true⟩⟩⟩
  | _ => ⟨⟨(-34359737869),34359738896,true⟩,⟨(-32249741903),36552519765,true⟩,⟨⟨(-737303847360148271412994),(-716904688566134373864431),true⟩,⟨(-976026179176018676863583),(-955627020382004779311731),true⟩⟩⟩
theorem factoredHeatR032Q00F_ok : ∀ n : Fin 6, (factoredHeatR032Q00F n).encloses (FactoredFrequency.build factoredHeatR032Q00T (Grid.ofRats (987133262649019/1649267441664000) (988743875385019/1649267441664000)) n) := by decide +kernel
def factoredHeatR032Q00U : ℕ → ℚ
  | 0 => (-5298483/125000)
  | 1 => (-31875091/1000000)
  | 2 => (-20507879/1000000)
  | 3 => (-2531701/200000)
  | 4 => (-501231/62500)
  | 5 => (-2749887/500000)
  | 6 => (-816293/200000)
  | 7 => (-3382709/1000000)
  | 8 => (-1615219/500000)
  | 9 => (-1899233/500000)
  | 10 => (-583471/100000)
  | 11 => (-154407/15625)
  | 12 => (-1927499/125000)
  | 13 => (-21188283/1000000)
  | 14 => (-12186823/500000)
  | 15 => (-5750459/250000)
  | 16 => (-4736117/250000)
  | 17 => (-366683/25000)
  | 18 => (-6002667/500000)
  | 19 => (-432417/40000)
  | 20 => (-10434183/1000000)
  | 21 => (-5061641/500000)
  | 22 => (-8950211/1000000)
  | 23 => (-117823/20000)
  | 24 => (48761/100000)
  | 25 => (10817521/1000000)
  | 26 => (4786919/200000)
  | 27 => (34486091/1000000)
  | 28 => (8250671/250000)
  | 29 => (190081/15625)
  | 30 => (-3883249/200000)
  | 31 => (-40771311/1000000)
  | _ => 0
theorem factoredHeatR032Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR032Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR032Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR032Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR032Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR032Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR032Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR032Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR032Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR032Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR032Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR032Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR032Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR032Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR032Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR032Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR032Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR032Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR032Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR032Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR032Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR032Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR032Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR032Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR032Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR032Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR032Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR032Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR032Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR032Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR032Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR032Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR032Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR032Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR032Q00P factoredHeatR032Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR032Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR032Q00Point00
  · exact factoredHeatR032Q00Point01
  · exact factoredHeatR032Q00Point02
  · exact factoredHeatR032Q00Point03
  · exact factoredHeatR032Q00Point04
  · exact factoredHeatR032Q00Point05
  · exact factoredHeatR032Q00Point06
  · exact factoredHeatR032Q00Point07
  · exact factoredHeatR032Q00Point08
  · exact factoredHeatR032Q00Point09
  · exact factoredHeatR032Q00Point10
  · exact factoredHeatR032Q00Point11
  · exact factoredHeatR032Q00Point12
  · exact factoredHeatR032Q00Point13
  · exact factoredHeatR032Q00Point14
  · exact factoredHeatR032Q00Point15
  · exact factoredHeatR032Q00Point16
  · exact factoredHeatR032Q00Point17
  · exact factoredHeatR032Q00Point18
  · exact factoredHeatR032Q00Point19
  · exact factoredHeatR032Q00Point20
  · exact factoredHeatR032Q00Point21
  · exact factoredHeatR032Q00Point22
  · exact factoredHeatR032Q00Point23
  · exact factoredHeatR032Q00Point24
  · exact factoredHeatR032Q00Point25
  · exact factoredHeatR032Q00Point26
  · exact factoredHeatR032Q00Point27
  · exact factoredHeatR032Q00Point28
  · exact factoredHeatR032Q00Point29
  · exact factoredHeatR032Q00Point30
  · exact factoredHeatR032Q00Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR032Q00Bound {t a : ℝ} (tl : ((441/500):ℝ)≤t) (tu : t≤((883/1000):ℝ)) (al : ((987133262649019/1649267441664000):ℝ)≤a) (au : a≤((988743875385019/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-2604588122369560338253343229365837/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR032Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (987133262649019/1649267441664000) (988743875385019/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR032Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR032Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR032Q00U (-2604588122369560338253343229365837/324518553658426726783156020576256) factoredHeatR032Q00Samples (by decide +kernel)

theorem factored_original_heat_032 {t a : ℝ} (tb : RealMem derivative_032.t t) (ab : RealMem derivative_032.a a) : reportedHeatPeriod t a≤(derivative_032.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((441/500):ℝ) ((883/1000):ℝ) := by simpa [derivative_032,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((441/500):ℝ)<((883/1000):ℝ)) tB
  have aB : a∈Icc ((987133262649019/1649267441664000):ℝ) ((988743875385019/1649267441664000):ℝ) := by simpa [derivative_032,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((987133262649019/1649267441664000):ℝ)<((988743875385019/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR032Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_032] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_028
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_029
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_030
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_031
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_032
