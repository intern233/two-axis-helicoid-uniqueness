import TwoAxisHelicoid.PdfFactoredPeriodicSamples
import TwoAxisHelicoid.PdfFactoredNodes32
import TwoAxisHelicoid.PdfHeatStripAll

namespace TwoAxisHelicoid.PdfVertical

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR048Q00T := Grid.ofRats (449/500) (899/1000)
def factoredHeatR048Q00P : HeatGridParameters := ⟨⟨⟨⟨71750562644412931187454,71976328130888506163359,true⟩,⟨0,0,true⟩⟩, ⟨⟨1146839102423632923833020,1147766336914335515037237,true⟩,⟨0,0,true⟩⟩, ⟨(-1504274268789038373385177),(-1502419799807701910455999),true⟩, ⟨5986191016254104032821790,6007314309309478114502596,true⟩⟩, ⟨406015126445441446496094,419990344491109188471681,true⟩, ⟨597703369840335768238697,601406633552109125231981,true⟩, ⟨(-1420676296234318287803856),(-1413824440037321534315359),true⟩, ⟨(-2651389348064276811106500),(-2644674572129888453084295),true⟩, ⟨(-590727123976495985862929),(-589998875710444655044041),true⟩⟩
theorem factoredHeatR048Q00P_ok : factoredHeatR048Q00P.encloses (heatGridParameters factoredHeatR048Q00T (Grid.ofRats (996033734273437/1649267441664000) (996839040641437/1649267441664000))) := by decide +kernel
def factoredHeatR048Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨596700040872916465024065,597168872074668467445045,true⟩,⟨2447384158275791821200721,2449307084331348094598198,true⟩,⟨⟨703704989775654430407817,704632224266357021659538,true⟩,⟨982210392900943009796065,983137627391645601051697,true⟩⟩⟩
  | 1 => ⟨⟨8627690442659771024589,8675254276437628262587,true⟩,⟨596700040872916465024065,597168872074668467445045,true⟩,⟨⟨(-1158264716901757092888739),(-1155483013429786758160970),true⟩,⟨349528651038241213761576,352310354510211548478243,true⟩⟩⟩
  | 2 => ⟨⟨7403868508701009736,7503386208054408034,true⟩,⟨8627690442659771024589,8675254276437628262587,true⟩,⟨⟨37259728488528109819517,41895900941766188011076,true⟩,⟨(-1210595882891473921352197),(-1205959710438235843144554),true⟩⟩⟩
  | 3 => ⟨⟨377058667324476,386421281815268,true⟩,⟨7403868508701009736,7503386208054408034,true⟩,⟨⟨1128184233741137621656530,1134674875175643443302582,true⟩,⟨422628839838410304627562,429119481272916126263907,true⟩⟩⟩
  | 4 => ⟨⟨(-33219845695),35544354310,true⟩,⟨377058667324476,386421281815268,true⟩,⟨⟨(-771138815554811677650459),(-762793705139038112518583),true⟩,⟨930313609922638806593904,938658720338412371728084,true⟩⟩⟩
  | _ => ⟨⟨(-34359738164),34359738585,true⟩,⟨(-33219845695),35544354310,true⟩,⟨⟨(-643451897339798044688229),(-633252317942756736101945),true⟩,⟨(-1031748816387214263234327),(-1021549236990172954642692),true⟩⟩⟩
theorem factoredHeatR048Q00F_ok : ∀ n : Fin 6, (factoredHeatR048Q00F n).encloses (FactoredFrequency.build factoredHeatR048Q00T (Grid.ofRats (996033734273437/1649267441664000) (996839040641437/1649267441664000)) n) := by decide +kernel
def factoredHeatR048Q00U : ℕ → ℚ
  | 0 => (-7992939/200000)
  | 1 => (-31533033/1000000)
  | 2 => (-21310989/1000000)
  | 3 => (-3441101/250000)
  | 4 => (-4524177/500000)
  | 5 => (-6329917/1000000)
  | 6 => (-1180959/250000)
  | 7 => (-3834947/1000000)
  | 8 => (-3501223/1000000)
  | 9 => (-3914539/1000000)
  | 10 => (-5704083/1000000)
  | 11 => (-938789/100000)
  | 12 => (-3655691/250000)
  | 13 => (-20165691/1000000)
  | 14 => (-2345343/100000)
  | 15 => (-4544907/200000)
  | 16 => (-19263279/1000000)
  | 17 => (-122739/8000)
  | 18 => (-6354531/500000)
  | 19 => (-11372447/1000000)
  | 20 => (-10798567/1000000)
  | 21 => (-5136567/500000)
  | 22 => (-4461439/500000)
  | 23 => (-1435297/250000)
  | 24 => (241429/500000)
  | 25 => (2580319/250000)
  | 26 => (22552067/1000000)
  | 27 => (32231579/1000000)
  | 28 => (3854163/125000)
  | 29 => (2441917/200000)
  | 30 => (-8150661/500000)
  | 31 => (-36788479/1000000)
  | _ => 0
theorem factoredHeatR048Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR048Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR048Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR048Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR048Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR048Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR048Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR048Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR048Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR048Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR048Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR048Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR048Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR048Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR048Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR048Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR048Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR048Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR048Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR048Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR048Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR048Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR048Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR048Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR048Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR048Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR048Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR048Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR048Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR048Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR048Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR048Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR048Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR048Q00P factoredHeatR048Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR048Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR048Q00Point00
  · exact factoredHeatR048Q00Point01
  · exact factoredHeatR048Q00Point02
  · exact factoredHeatR048Q00Point03
  · exact factoredHeatR048Q00Point04
  · exact factoredHeatR048Q00Point05
  · exact factoredHeatR048Q00Point06
  · exact factoredHeatR048Q00Point07
  · exact factoredHeatR048Q00Point08
  · exact factoredHeatR048Q00Point09
  · exact factoredHeatR048Q00Point10
  · exact factoredHeatR048Q00Point11
  · exact factoredHeatR048Q00Point12
  · exact factoredHeatR048Q00Point13
  · exact factoredHeatR048Q00Point14
  · exact factoredHeatR048Q00Point15
  · exact factoredHeatR048Q00Point16
  · exact factoredHeatR048Q00Point17
  · exact factoredHeatR048Q00Point18
  · exact factoredHeatR048Q00Point19
  · exact factoredHeatR048Q00Point20
  · exact factoredHeatR048Q00Point21
  · exact factoredHeatR048Q00Point22
  · exact factoredHeatR048Q00Point23
  · exact factoredHeatR048Q00Point24
  · exact factoredHeatR048Q00Point25
  · exact factoredHeatR048Q00Point26
  · exact factoredHeatR048Q00Point27
  · exact factoredHeatR048Q00Point28
  · exact factoredHeatR048Q00Point29
  · exact factoredHeatR048Q00Point30
  · exact factoredHeatR048Q00Point31

def factoredHeatR048Q01T := Grid.ofRats (449/500) (899/1000)
def factoredHeatR048Q01P : HeatGridParameters := ⟨⟨⟨⟨71750562644412931187454,71976328130888506163359,true⟩,⟨0,0,true⟩⟩, ⟨⟨1147766336914266795556844,1148693571404969386761064,true⟩,⟨0,0,true⟩⟩, ⟨(-1502419799807770629937522),(-1500565330826434167008350),true⟩, ⟨5981649536643640933160178,6002745011944556579648426,true⟩⟩, ⟨407358160238496771347312,421348353244401844579980,true⟩, ⟨596390805019886757967640,600091279230385063548511,true⟩, ⟨(-1419066233912739508251336),(-1412225147250176668392050),true⟩, ⟨(-2651389348064276811106500),(-2644674572129888453084295),true⟩, ⟨(-589998875710513374524536),(-589270627444462043705652),true⟩⟩
theorem factoredHeatR048Q01P_ok : factoredHeatR048Q01P.encloses (heatGridParameters factoredHeatR048Q01T (Grid.ofRats (996839040641437/1649267441664000) (997644347009437/1649267441664000))) := by decide +kernel
def factoredHeatR048Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨596700040872916465024065,597168872074668467445045,true⟩,⟨2447384158275791821200721,2449307084331348094598198,true⟩,⟨⟨702951081201267651568609,703878315691970242820527,true⟩,⟨982750194364389594651824,983677428855092185907724,true⟩⟩⟩
  | 1 => ⟨⟨8627690442659771024589,8675254276437628262587,true⟩,⟨596700040872916465024065,597168872074668467445045,true⟩,⟨⟨(-1159069109337576313529270),(-1156287405865605978801824),true⟩,⟨346865790996708288731376,349647494468678623447675,true⟩⟩⟩
  | 2 => ⟨⟨7403868508701009736,7503386208054408034,true⟩,⟨8627690442659771024589,8675254276437628262587,true⟩,⟨⟨41893113414722711827523,46529285867960790019719,true⟩,⟨(-1210435219271745728089036),(-1205799046818507649880823),true⟩⟩⟩
  | 3 => ⟨⟨377058667324476,386421281815268,true⟩,⟨7403868508701009736,7503386208054408034,true⟩,⟨⟨1125881448057138184062692,1132372089491644005709659,true⟩,⟨428697241862548508467054,435187883297054330104426,true⟩⟩⟩
  | 4 => ⟨⟨(-33219845695),35544354310,true⟩,⟨377058667324476,386421281815268,true⟩,⟨⟨(-777571168551720303259140),(-769226058135946738126356),true⟩,⟨924997086035701423524617,933342196451474988659540,true⟩⟩⟩
  | _ => ⟨⟨(-34359738164),34359738585,true⟩,⟨(-33219845695),35544354310,true⟩,⟨⟨(-634767551547210384655302),(-624567972150169076069106),true⟩,⟨(-1037097922942648510107718),(-1026898343545607201515984),true⟩⟩⟩
theorem factoredHeatR048Q01F_ok : ∀ n : Fin 6, (factoredHeatR048Q01F n).encloses (FactoredFrequency.build factoredHeatR048Q01T (Grid.ofRats (996839040641437/1649267441664000) (997644347009437/1649267441664000)) n) := by decide +kernel
def factoredHeatR048Q01U : ℕ → ℚ
  | 0 => (-39929469/1000000)
  | 1 => (-31543289/1000000)
  | 2 => (-5334797/250000)
  | 3 => (-13793361/1000000)
  | 4 => (-4535381/500000)
  | 5 => (-6344299/1000000)
  | 6 => (-591211/125000)
  | 7 => (-3831859/1000000)
  | 8 => (-1743847/500000)
  | 9 => (-155571/40000)
  | 10 => (-566733/100000)
  | 11 => (-2335879/250000)
  | 12 => (-3644673/250000)
  | 13 => (-5033773/250000)
  | 14 => (-23446521/1000000)
  | 15 => (-22741391/1000000)
  | 16 => (-19290073/1000000)
  | 17 => (-240117/15625)
  | 18 => (-12726079/1000000)
  | 19 => (-5690917/500000)
  | 20 => (-1350287/125000)
  | 21 => (-2568391/250000)
  | 22 => (-8922919/1000000)
  | 23 => (-143627/25000)
  | 24 => (468087/1000000)
  | 25 => (10291599/1000000)
  | 26 => (1406791/62500)
  | 27 => (32192947/1000000)
  | 28 => (15417571/500000)
  | 29 => (6138951/500000)
  | 30 => (-16189603/1000000)
  | 31 => (-36697621/1000000)
  | _ => 0
theorem factoredHeatR048Q01Point00 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR048Q01U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point01 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR048Q01U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point02 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR048Q01U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point03 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR048Q01U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point04 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR048Q01U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point05 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR048Q01U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point06 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR048Q01U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point07 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR048Q01U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point08 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR048Q01U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point09 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR048Q01U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point10 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR048Q01U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point11 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR048Q01U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point12 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR048Q01U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point13 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR048Q01U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point14 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR048Q01U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point15 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR048Q01U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point16 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR048Q01U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point17 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR048Q01U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point18 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR048Q01U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point19 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR048Q01U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point20 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR048Q01U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point21 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR048Q01U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point22 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR048Q01U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point23 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR048Q01U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point24 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR048Q01U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point25 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR048Q01U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point26 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR048Q01U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point27 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR048Q01U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point28 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR048Q01U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point29 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR048Q01U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point30 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR048Q01U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Point31 : containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR048Q01U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR048Q01Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR048Q01P factoredHeatR048Q01F (factoredNodes32 k)).re (-10000) (factoredHeatR048Q01U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR048Q01Point00
  · exact factoredHeatR048Q01Point01
  · exact factoredHeatR048Q01Point02
  · exact factoredHeatR048Q01Point03
  · exact factoredHeatR048Q01Point04
  · exact factoredHeatR048Q01Point05
  · exact factoredHeatR048Q01Point06
  · exact factoredHeatR048Q01Point07
  · exact factoredHeatR048Q01Point08
  · exact factoredHeatR048Q01Point09
  · exact factoredHeatR048Q01Point10
  · exact factoredHeatR048Q01Point11
  · exact factoredHeatR048Q01Point12
  · exact factoredHeatR048Q01Point13
  · exact factoredHeatR048Q01Point14
  · exact factoredHeatR048Q01Point15
  · exact factoredHeatR048Q01Point16
  · exact factoredHeatR048Q01Point17
  · exact factoredHeatR048Q01Point18
  · exact factoredHeatR048Q01Point19
  · exact factoredHeatR048Q01Point20
  · exact factoredHeatR048Q01Point21
  · exact factoredHeatR048Q01Point22
  · exact factoredHeatR048Q01Point23
  · exact factoredHeatR048Q01Point24
  · exact factoredHeatR048Q01Point25
  · exact factoredHeatR048Q01Point26
  · exact factoredHeatR048Q01Point27
  · exact factoredHeatR048Q01Point28
  · exact factoredHeatR048Q01Point29
  · exact factoredHeatR048Q01Point30
  · exact factoredHeatR048Q01Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR048Q00Bound {t a : ℝ} (tl : ((449/500):ℝ)≤t) (tu : t≤((899/1000):ℝ)) (al : ((996033734273437/1649267441664000):ℝ)≤a) (au : a≤((996839040641437/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-1301644547200137874844636427988629/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : factoredHeatR048Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (996033734273437/1649267441664000) (996839040641437/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR048Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR048Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR048Q00U (-1301644547200137874844636427988629/162259276829213363391578010288128) factoredHeatR048Q00Samples (by decide +kernel)

theorem factoredHeatR048Q01Bound {t a : ℝ} (tl : ((449/500):ℝ)≤t) (tu : t≤((899/1000):ℝ)) (al : ((996839040641437/1649267441664000):ℝ)≤a) (au : a≤((997644347009437/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-1301644547200137874844636427988629/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : factoredHeatR048Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (996839040641437/1649267441664000) (997644347009437/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR048Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR048Q01F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR048Q01U (-1301644547200137874844636427988629/162259276829213363391578010288128) factoredHeatR048Q01Samples (by decide +kernel)

theorem factored_original_heat_048 {t a : ℝ} (tb : RealMem derivative_048.t t) (ab : RealMem derivative_048.a a) : reportedHeatPeriod t a≤(derivative_048.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((449/500):ℝ) ((899/1000):ℝ) := by simpa [derivative_048,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((449/500):ℝ)<((899/1000):ℝ)) tB
  have aB : a∈Icc ((996033734273437/1649267441664000):ℝ) ((997644347009437/1649267441664000):ℝ) := by simpa [derivative_048,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((996033734273437/1649267441664000):ℝ)<((997644347009437/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR048Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_048] using v
  · norm_num at tl tu al au
    have v := @factoredHeatR048Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_048] using v

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR049Q00T := Grid.ofRats (899/1000) (9/10)
def factoredHeatR049Q00P : HeatGridParameters := ⟨⟨⟨⟨71525505308257361912944,71750562644481650665151,true⟩,⟨0,0,true⟩⟩, ⟨⟨1147489418650557932622093,1148416653141260523826312,true⟩,⟨0,0,true⟩⟩, ⟨(-1502973636335188355807027),(-1501119167353851892877853),true⟩, ⟨5978238121052002605996993,5999296363558048553256488,true⟩⟩, ⟨406759752930039885461911,420721742713811199067274,true⟩, ⟨597605487785872708044517,601301622690339894127187,true⟩, ⟨(-1418857682394530027893392),(-1412028509923187750235597),true⟩, ⟨(-2647696484038104522640964),(-2641003153335017273544318),true⟩, ⟨(-590216366806241525736123),(-589488118540190194917238),true⟩⟩
theorem factoredHeatR049Q00P_ok : factoredHeatR049Q00P.encloses (heatGridParameters factoredHeatR049Q00T (Grid.ofRats (996598536169879/1649267441664000) (997403842537879/1649267441664000))) := by decide +kernel
def factoredHeatR049Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨596231577745836448294550,596700040872985184522236,true⟩,⟨2449307084331279375033499,2451231521242662008727464,true⟩,⟨⟨703176279096387840368894,704103513587090431620610,true⟩,⟨982589043402637348971551,983516277893339940227177,true⟩⟩⟩
  | 1 => ⟨⟨8580387387275398224920,8627690442728490501758,true⟩,⟨596231577745836448294550,596700040872985184522236,true⟩,⟨⟨(-1158829519533450053417373),(-1156047816061479718689606),true⟩,⟨347661246980141504752896,350442950452111839469535,true⟩⟩⟩
  | 2 => ⟨⟨7305670783317561648,7403868577420486474,true⟩,⟨8580387387275398224920,8627690442728490501758,true⟩,⟨⟨40509419596604230867486,45145592049842309059443,true⟩,⟨(-1210485062300648590752883),(-1205848889847410512544887),true⟩⟩⟩
  | 3 => ⟨⟨367988321503205,377127386801213,true⟩,⟨7305670783317561648,7403868577420486474,true⟩,⟨⟨1126572585909426165602920,1133063227343931987249683,true⟩,⟨426886211719758265911810,433376853154264087548938,true⟩⟩⟩
  | 4 => ⟨⟨(-33262880508),35499631042,true⟩,⟨367988321503205,377127386801213,true⟩,⟨⟨(-775653994188500644926109),(-767308883772727079794114),true⟩,⟨926589512476064488978437,934934622891838054112623,true⟩⟩⟩
  | _ => ⟨⟨(-34359738175),34359738573,true⟩,⟨(-33262880508),35499631042,true⟩,⟨⟨(-637365850515329559428096),(-627166271118288250841855),true⟩,⟨(-1035508090164941693836530),(-1025308510767900385244802),true⟩⟩⟩
theorem factoredHeatR049Q00F_ok : ∀ n : Fin 6, (factoredHeatR049Q00F n).encloses (FactoredFrequency.build factoredHeatR049Q00T (Grid.ofRats (996598536169879/1649267441664000) (997403842537879/1649267441664000)) n) := by decide +kernel
def factoredHeatR049Q00U : ℕ → ℚ
  | 0 => (-39786131/1000000)
  | 1 => (-31482691/1000000)
  | 2 => (-4267387/200000)
  | 3 => (-2763103/200000)
  | 4 => (-2274573/250000)
  | 5 => (-159257/25000)
  | 6 => (-190119/40000)
  | 7 => (-3852219/1000000)
  | 8 => (-3506543/1000000)
  | 9 => (-781289/200000)
  | 10 => (-5678507/1000000)
  | 11 => (-9339151/1000000)
  | 12 => (-1454799/100000)
  | 13 => (-10036851/500000)
  | 14 => (-23369749/1000000)
  | 15 => (-11339983/500000)
  | 16 => (-77037/4000)
  | 17 => (-7681207/500000)
  | 18 => (-12733807/1000000)
  | 19 => (-142383/12500)
  | 20 => (-1080603/100000)
  | 21 => (-641797/62500)
  | 22 => (-8907669/1000000)
  | 23 => (-5718853/1000000)
  | 24 => (249353/500000)
  | 25 => (10309379/1000000)
  | 26 => (2248853/100000)
  | 27 => (1605999/50000)
  | 28 => (30740727/1000000)
  | 29 => (12253177/1000000)
  | 30 => (-16081083/1000000)
  | 31 => (-18258137/500000)
  | _ => 0
theorem factoredHeatR049Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR049Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR049Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR049Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR049Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR049Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR049Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR049Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR049Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR049Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR049Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR049Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR049Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR049Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR049Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR049Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR049Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR049Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR049Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR049Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR049Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR049Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR049Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR049Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR049Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR049Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR049Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR049Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR049Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR049Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR049Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR049Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR049Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR049Q00P factoredHeatR049Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR049Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR049Q00Point00
  · exact factoredHeatR049Q00Point01
  · exact factoredHeatR049Q00Point02
  · exact factoredHeatR049Q00Point03
  · exact factoredHeatR049Q00Point04
  · exact factoredHeatR049Q00Point05
  · exact factoredHeatR049Q00Point06
  · exact factoredHeatR049Q00Point07
  · exact factoredHeatR049Q00Point08
  · exact factoredHeatR049Q00Point09
  · exact factoredHeatR049Q00Point10
  · exact factoredHeatR049Q00Point11
  · exact factoredHeatR049Q00Point12
  · exact factoredHeatR049Q00Point13
  · exact factoredHeatR049Q00Point14
  · exact factoredHeatR049Q00Point15
  · exact factoredHeatR049Q00Point16
  · exact factoredHeatR049Q00Point17
  · exact factoredHeatR049Q00Point18
  · exact factoredHeatR049Q00Point19
  · exact factoredHeatR049Q00Point20
  · exact factoredHeatR049Q00Point21
  · exact factoredHeatR049Q00Point22
  · exact factoredHeatR049Q00Point23
  · exact factoredHeatR049Q00Point24
  · exact factoredHeatR049Q00Point25
  · exact factoredHeatR049Q00Point26
  · exact factoredHeatR049Q00Point27
  · exact factoredHeatR049Q00Point28
  · exact factoredHeatR049Q00Point29
  · exact factoredHeatR049Q00Point30
  · exact factoredHeatR049Q00Point31

def factoredHeatR049Q01T := Grid.ofRats (899/1000) (9/10)
def factoredHeatR049Q01P : HeatGridParameters := ⟨⟨⟨⟨71525505308257361912944,71750562644481650665151,true⟩,⟨0,0,true⟩⟩, ⟨⟨1148416653141191804345917,1149343887631894395550140,true⟩,⟨0,0,true⟩⟩, ⟨(-1501119167353920612359372),(-1499264698372584149430204),true⟩, ⟨5973703427386461339947262,5994733942000706505665256,true⟩⟩, ⟨408104637366434522653982,422081622421557874427086,true⟩, ⟨596294382980172405712925,599987729893883430672959,true⟩, ⟨(-1417252616772331631136004),(-1410434181717183985774324),true⟩, ⟨(-2647696484038104522640964),(-2641003153335017273544318),true⟩, ⟨(-589488118540258914397729),(-588759870274207583578849),true⟩⟩
theorem factoredHeatR049Q01P_ok : factoredHeatR049Q01P.encloses (heatGridParameters factoredHeatR049Q01T (Grid.ofRats (997403842537879/1649267441664000) (998209148905879/1649267441664000))) := by decide +kernel
def factoredHeatR049Q01F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨596231577745836448294550,596700040872985184522236,true⟩,⟨2449307084331279375033499,2451231521242662008727464,true⟩,⟨⟨702422080256245510243003,703349314746948101494802,true⟩,⟨983128439238736353259229,984055673729438944514935,true⟩⟩⟩
  | 1 => ⟨⟨8580387387275398224920,8627690442728490501758,true⟩,⟨596231577745836448294550,596700040872985184522236,true⟩,⟨⟨(-1159629613634974161832404),(-1156847910163003827104697),true⟩,⟨344997092288630097806593,347778795760600432523115,true⟩⟩⟩
  | 2 => ⟨⟨7305670783317561648,7403868577420486474,true⟩,⟨8580387387275398224920,8627690442728490501758,true⟩,⟨⟨45142355635856186857189,49778528089094265048922,true⟩,⟨(-1210311937117061911191779),(-1205675764663823832984074),true⟩⟩⟩
  | 3 => ⟨⟨367988321503205,377127386801213,true⟩,⟨7305670783317561648,7403868577420486474,true⟩,⟨⟨1124246966020056935275247,1130737607454562756922357,true⟩,⟨432945899596470040580916,439436541030975862218515,true⟩⟩⟩
  | 4 => ⟨⟨(-33262880508),35499631042,true⟩,⟨367988321503205,377127386801213,true⟩,⟨⟨(-782060532692668333821813),(-773715422276894768689586),true⟩,⟨921241909675572291940118,929587020091345857074369,true⟩⟩⟩
  | _ => ⟨⟨(-34359738175),34359738573,true⟩,⟨(-33262880508),35499631042,true⟩,⟨⟨(-628650005108109109480220),(-618450425711067800894274),true⟩,⟨(-1040805716201579124870152),(-1030606136804537816278535),true⟩⟩⟩
theorem factoredHeatR049Q01F_ok : ∀ n : Fin 6, (factoredHeatR049Q01F n).encloses (FactoredFrequency.build factoredHeatR049Q01T (Grid.ofRats (997403842537879/1649267441664000) (998209148905879/1649267441664000)) n) := by decide +kernel
def factoredHeatR049Q01U : ℕ → ℚ
  | 0 => (-39750711/1000000)
  | 1 => (-492071/15625)
  | 2 => (-4272959/200000)
  | 3 => (-13844257/1000000)
  | 4 => (-142509/15625)
  | 5 => (-6384593/1000000)
  | 6 => (-4758791/1000000)
  | 7 => (-962281/250000)
  | 8 => (-698609/200000)
  | 9 => (-1940629/500000)
  | 10 => (-2820941/500000)
  | 11 => (-9294937/1000000)
  | 12 => (-14504061/1000000)
  | 13 => (-1002157/50000)
  | 14 => (-23362721/1000000)
  | 15 => (-2269659/100000)
  | 16 => (-19285831/1000000)
  | 17 => (-3077479/200000)
  | 18 => (-6375383/500000)
  | 19 => (-11400009/1000000)
  | 20 => (-10809759/1000000)
  | 21 => (-10269191/1000000)
  | 22 => (-8907723/1000000)
  | 23 => (-22891/4000)
  | 24 => (483969/1000000)
  | 25 => (2569953/250000)
  | 26 => (22445321/1000000)
  | 27 => (1604077/50000)
  | 28 => (30742481/1000000)
  | 29 => (12320943/1000000)
  | 30 => (-7985049/500000)
  | 31 => (-9106437/250000)
  | _ => 0
theorem factoredHeatR049Q01Point00 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR049Q01U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point01 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR049Q01U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point02 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR049Q01U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point03 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR049Q01U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point04 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR049Q01U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point05 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR049Q01U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point06 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR049Q01U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point07 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR049Q01U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point08 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR049Q01U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point09 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR049Q01U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point10 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR049Q01U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point11 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR049Q01U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point12 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR049Q01U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point13 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR049Q01U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point14 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR049Q01U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point15 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR049Q01U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point16 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR049Q01U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point17 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR049Q01U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point18 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR049Q01U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point19 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR049Q01U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point20 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR049Q01U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point21 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR049Q01U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point22 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR049Q01U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point23 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR049Q01U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point24 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR049Q01U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point25 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR049Q01U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point26 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR049Q01U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point27 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR049Q01U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point28 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR049Q01U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point29 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR049Q01U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point30 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR049Q01U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Point31 : containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR049Q01U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR049Q01Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR049Q01P factoredHeatR049Q01F (factoredNodes32 k)).re (-10000) (factoredHeatR049Q01U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR049Q01Point00
  · exact factoredHeatR049Q01Point01
  · exact factoredHeatR049Q01Point02
  · exact factoredHeatR049Q01Point03
  · exact factoredHeatR049Q01Point04
  · exact factoredHeatR049Q01Point05
  · exact factoredHeatR049Q01Point06
  · exact factoredHeatR049Q01Point07
  · exact factoredHeatR049Q01Point08
  · exact factoredHeatR049Q01Point09
  · exact factoredHeatR049Q01Point10
  · exact factoredHeatR049Q01Point11
  · exact factoredHeatR049Q01Point12
  · exact factoredHeatR049Q01Point13
  · exact factoredHeatR049Q01Point14
  · exact factoredHeatR049Q01Point15
  · exact factoredHeatR049Q01Point16
  · exact factoredHeatR049Q01Point17
  · exact factoredHeatR049Q01Point18
  · exact factoredHeatR049Q01Point19
  · exact factoredHeatR049Q01Point20
  · exact factoredHeatR049Q01Point21
  · exact factoredHeatR049Q01Point22
  · exact factoredHeatR049Q01Point23
  · exact factoredHeatR049Q01Point24
  · exact factoredHeatR049Q01Point25
  · exact factoredHeatR049Q01Point26
  · exact factoredHeatR049Q01Point27
  · exact factoredHeatR049Q01Point28
  · exact factoredHeatR049Q01Point29
  · exact factoredHeatR049Q01Point30
  · exact factoredHeatR049Q01Point31

open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR049Q00Bound {t a : ℝ} (tl : ((899/1000):ℝ)≤t) (tu : t≤((9/10):ℝ)) (al : ((996598536169879/1649267441664000):ℝ)≤a) (au : a≤((997403842537879/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-2600743855494627486243664565519511/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR049Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (996598536169879/1649267441664000) (997403842537879/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR049Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR049Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR049Q00U (-2600743855494627486243664565519511/324518553658426726783156020576256) factoredHeatR049Q00Samples (by decide +kernel)

theorem factoredHeatR049Q01Bound {t a : ℝ} (tl : ((899/1000):ℝ)≤t) (tu : t≤((9/10):ℝ)) (al : ((997403842537879/1649267441664000):ℝ)≤a) (au : a≤((998209148905879/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-2600743855494627486243664565519511/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR049Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (997403842537879/1649267441664000) (998209148905879/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR049Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR049Q01F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR049Q01U (-2600743855494627486243664565519511/324518553658426726783156020576256) factoredHeatR049Q01Samples (by decide +kernel)

theorem factored_original_heat_049 {t a : ℝ} (tb : RealMem derivative_049.t t) (ab : RealMem derivative_049.a a) : reportedHeatPeriod t a≤(derivative_049.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((899/1000):ℝ) ((9/10):ℝ) := by simpa [derivative_049,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((899/1000):ℝ)<((9/10):ℝ)) tB
  have aB : a∈Icc ((996598536169879/1649267441664000):ℝ) ((998209148905879/1649267441664000):ℝ) := by simpa [derivative_049,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((996598536169879/1649267441664000):ℝ)<((998209148905879/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR049Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_049] using v
  · norm_num at tl tu al au
    have v := @factoredHeatR049Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_049] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_048
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_049
