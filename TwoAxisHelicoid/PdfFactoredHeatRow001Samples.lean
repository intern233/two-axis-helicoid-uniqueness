import TwoAxisHelicoid.PdfFactoredPeriodicSamples
import TwoAxisHelicoid.PdfFactoredNodes32

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factoredHeatR001Q00T := Grid.ofRats (851/1000) (213/250)
def factoredHeatR001Q00P : HeatGridParameters := ⟨⟨⟨⟨83166993058074481897011,83428680715336961272073,true⟩,⟨0,0,true⟩⟩, ⟨⟨1117564274873145090944189,1119418743854481553872141,true⟩,⟨0,0,true⟩⟩, ⟨(-1562823923890014039163024),(-1559114985927409832786011),true⟩, ⟨6363865130511926987170630,6404467806033125955233321,true⟩⟩, ⟨367296568113136721070635,392291844366766163968224,true⟩, ⟨596398018493545819017229,603556105547281722159280,true⟩, ⟨(-1517321385517195039822099),(-1502578062700915989797782),true⟩, ⟨(-2832363245690133847362502),(-2824552133222773674601861),true⟩, ⟨(-613719519768426150292026),(-612263023236392208134603),true⟩⟩
theorem factoredHeatR001Q00P_ok : factoredHeatR001Q00P.encloses (heatGridParameters factoredHeatR001Q00T (Grid.ofRats (38824337804321/65970697666560) (38888762313761/65970697666560))) := by decide +kernel
def factoredHeatR001Q00F (n : Fin 6) : FactoredFrequency := match n.val with
  | 0 => ⟨⟨619138042499302898161975,619624503388578434782510,true⟩,⟨2358689221195028993719860,2360542459046988091502650,true⟩,⟨⟨726458352936019986215465,728312821917356449191047,true⟩,⟨964687515052250996604747,966541984033587459583706,true⟩⟩⟩
  | 1 => ⟨⟨11171577676578732775767,11233165776777898556041,true⟩,⟨619138042499302898161975,619624503388578434782510,true⟩,⟨⟨(-1131631976305222577559551),(-1126068569361350627660243),true⟩,⟨429882945945042991500744,435446352888914941390463,true⟩⟩⟩
  | 2 => ⟨⟨13867330773560948684,14053725819067863615,true⟩,⟨11171577676578732775767,11233165776777898556041,true⟩,⟨⟨(-108977356075500284122169),(-99705011169092847311145),true⟩,⟨(-1209050783262621419047905),(-1199778438356213982221740),true⟩⟩⟩
  | 3 => ⟨⟨1184158910609516,1213413446691473,true⟩,⟨13867330773560948684,14053725819067863615,true⟩,⟨⟨1179948482734282861725119,1192929765603225785432210,true⟩,⟨225595209001486995573286,238576491870429919267242,true⟩⟩⟩
  | 4 => ⟨⟨(-27403032397),41589388128,true⟩,⟨1184158910609516,1213413446691473,true⟩,⟨⟨(-558833246994258108195458),(-542143026162779697551727),true⟩,⟨1067974753201583819735663,1084664974033062230386631,true⟩⟩⟩
  | _ => ⟨⟨(-34359735557),34359741341,true⟩,⟨(-27403032397),41589388128,true⟩,⟨⟨(-892808726189650595003727),(-872409567395636697455739),true⟩,⟨(-836336814563697966632482),(-815937655769684069085268),true⟩⟩⟩
theorem factoredHeatR001Q00F_ok : ∀ n : Fin 6, (factoredHeatR001Q00F n).encloses (FactoredFrequency.build factoredHeatR001Q00T (Grid.ofRats (38824337804321/65970697666560) (38888762313761/65970697666560)) n) := by decide +kernel
def factoredHeatR001Q00U : ℕ → ℚ
  | 0 => (-9534541/200000)
  | 1 => (-32322157/1000000)
  | 2 => (-4661891/250000)
  | 3 => (-1291473/125000)
  | 4 => (-2998851/500000)
  | 5 => (-786173/200000)
  | 6 => (-737427/250000)
  | 7 => (-2666057/1000000)
  | 8 => (-36809/12500)
  | 9 => (-2002107/500000)
  | 10 => (-6669827/1000000)
  | 11 => (-5776541/500000)
  | 12 => (-18013529/1000000)
  | 13 => (-3041993/125000)
  | 14 => (-53999/2000)
  | 15 => (-12015347/500000)
  | 16 => (-4626741/250000)
  | 17 => (-540807/40000)
  | 18 => (-2710831/250000)
  | 19 => (-1245507/125000)
  | 20 => (-9983429/1000000)
  | 21 => (-1261243/125000)
  | 22 => (-9320779/1000000)
  | 23 => (-102499/15625)
  | 24 => (-79027/1000000)
  | 25 => (11131593/1000000)
  | 26 => (104379/4000)
  | 27 => (38508927/1000000)
  | 28 => (1137423/31250)
  | 29 => (1277463/125000)
  | 30 => (-14054243/500000)
  | 31 => (-12633117/250000)
  | _ => 0
theorem factoredHeatR001Q00Point00 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (0:Fin 32))).re (-10000) (factoredHeatR001Q00U (0:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point01 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (1:Fin 32))).re (-10000) (factoredHeatR001Q00U (1:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point02 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (2:Fin 32))).re (-10000) (factoredHeatR001Q00U (2:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point03 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (3:Fin 32))).re (-10000) (factoredHeatR001Q00U (3:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point04 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (4:Fin 32))).re (-10000) (factoredHeatR001Q00U (4:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point05 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (5:Fin 32))).re (-10000) (factoredHeatR001Q00U (5:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point06 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (6:Fin 32))).re (-10000) (factoredHeatR001Q00U (6:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point07 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (7:Fin 32))).re (-10000) (factoredHeatR001Q00U (7:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point08 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (8:Fin 32))).re (-10000) (factoredHeatR001Q00U (8:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point09 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (9:Fin 32))).re (-10000) (factoredHeatR001Q00U (9:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point10 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (10:Fin 32))).re (-10000) (factoredHeatR001Q00U (10:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point11 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (11:Fin 32))).re (-10000) (factoredHeatR001Q00U (11:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point12 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (12:Fin 32))).re (-10000) (factoredHeatR001Q00U (12:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point13 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (13:Fin 32))).re (-10000) (factoredHeatR001Q00U (13:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point14 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (14:Fin 32))).re (-10000) (factoredHeatR001Q00U (14:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point15 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (15:Fin 32))).re (-10000) (factoredHeatR001Q00U (15:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point16 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (16:Fin 32))).re (-10000) (factoredHeatR001Q00U (16:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point17 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (17:Fin 32))).re (-10000) (factoredHeatR001Q00U (17:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point18 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (18:Fin 32))).re (-10000) (factoredHeatR001Q00U (18:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point19 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (19:Fin 32))).re (-10000) (factoredHeatR001Q00U (19:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point20 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (20:Fin 32))).re (-10000) (factoredHeatR001Q00U (20:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point21 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (21:Fin 32))).re (-10000) (factoredHeatR001Q00U (21:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point22 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (22:Fin 32))).re (-10000) (factoredHeatR001Q00U (22:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point23 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (23:Fin 32))).re (-10000) (factoredHeatR001Q00U (23:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point24 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (24:Fin 32))).re (-10000) (factoredHeatR001Q00U (24:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point25 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (25:Fin 32))).re (-10000) (factoredHeatR001Q00U (25:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point26 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (26:Fin 32))).re (-10000) (factoredHeatR001Q00U (26:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point27 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (27:Fin 32))).re (-10000) (factoredHeatR001Q00U (27:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point28 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (28:Fin 32))).re (-10000) (factoredHeatR001Q00U (28:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point29 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (29:Fin 32))).re (-10000) (factoredHeatR001Q00U (29:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point30 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (30:Fin 32))).re (-10000) (factoredHeatR001Q00U (30:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Point31 : containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 (31:Fin 32))).re (-10000) (factoredHeatR001Q00U (31:Fin 32))=true := by decide +kernel
theorem factoredHeatR001Q00Samples : ∀ k : Fin 32, containedInReported (sampledFactoredHeat factoredHeatR001Q00P factoredHeatR001Q00F (factoredNodes32 k)).re (-10000) (factoredHeatR001Q00U k)=true := by
  intro k
  fin_cases k
  · exact factoredHeatR001Q00Point00
  · exact factoredHeatR001Q00Point01
  · exact factoredHeatR001Q00Point02
  · exact factoredHeatR001Q00Point03
  · exact factoredHeatR001Q00Point04
  · exact factoredHeatR001Q00Point05
  · exact factoredHeatR001Q00Point06
  · exact factoredHeatR001Q00Point07
  · exact factoredHeatR001Q00Point08
  · exact factoredHeatR001Q00Point09
  · exact factoredHeatR001Q00Point10
  · exact factoredHeatR001Q00Point11
  · exact factoredHeatR001Q00Point12
  · exact factoredHeatR001Q00Point13
  · exact factoredHeatR001Q00Point14
  · exact factoredHeatR001Q00Point15
  · exact factoredHeatR001Q00Point16
  · exact factoredHeatR001Q00Point17
  · exact factoredHeatR001Q00Point18
  · exact factoredHeatR001Q00Point19
  · exact factoredHeatR001Q00Point20
  · exact factoredHeatR001Q00Point21
  · exact factoredHeatR001Q00Point22
  · exact factoredHeatR001Q00Point23
  · exact factoredHeatR001Q00Point24
  · exact factoredHeatR001Q00Point25
  · exact factoredHeatR001Q00Point26
  · exact factoredHeatR001Q00Point27
  · exact factoredHeatR001Q00Point28
  · exact factoredHeatR001Q00Point29
  · exact factoredHeatR001Q00Point30
  · exact factoredHeatR001Q00Point31

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factoredHeatR001Q00Samples
