import TwoAxisHelicoid.PdfSharedChord426Gauss6
import TwoAxisHelicoid.PdfSharedChord426Disks

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP437Params : ChordParams := ⟨⟨(-364274203612359759078),(-345593024327194788367),true⟩,⟨4858081356661445941373140,4892035740771283568862129,true⟩,⟨19729431612776575236234,20300421597330451195375,true⟩,⟨21134153290093274753504,21736150138916362265467,true⟩,⟨40867819256477431576003,41958494579392420242708,true⟩,⟨1208197490667889736171948,1208234831097376280809678,true⟩,⟨(-4929586583359509071731602),(-4897631433248858282441487),true⟩,⟨⟨1204667007168968377796268,1211776170257976060747985,true⟩,⟨(-46),46,true⟩⟩⟩
theorem sharedDiskP437Params_ok : chordParams (Grid.ofRats (77/200) (31/80)) (Grid.ofRats (1108510757643/2199023255552) (1109047628555/2199023255552))=sharedDiskP437Params := by decide +kernel
def sharedDiskP437Values (i : Fin 14) (j : Fin 6) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-7677560367642463209528598),(-5813635406750347074246996),true⟩,⟨(-1174348082862168455728667),406820698478292542390971,true⟩⟩
  | 0,1 => ⟨⟨(-6714676598248808329338526),(-4990195186323082598906678),true⟩,⟨(-1392735549521749690636544),91485945672010501028452,true⟩⟩
  | 0,2 => ⟨⟨(-6143322699907170084553201),(-4516084388839707885432448),true⟩,⟨(-1535145582431163035075143),(-126654666179148244800008),true⟩⟩
  | 0,3 => ⟨⟨(-8862880499745160087523420),(-6874872483190112129848022),true⟩,⟨(-947098379790700213481106),684479721240573167567579,true⟩⟩
  | 0,4 => ⟨⟨(-9985750541483568872550133),(-7926724240928221888682178),true⟩,⟨(-780816895359653390772367),801343316045242821024928,true⟩⟩
  | 0,5 => ⟨⟨(-10733831162938046428775905),(-8647933301268145496126821),true⟩,⟨(-714480128302672450733606),794904017347824563022398,true⟩⟩
  | 1,0 => ⟨⟨(-3870355399372883469494293),(-2702664411968686594986671),true⟩,⟨(-2167693218450177511215976),(-1121998994433440966844774),true⟩⟩
  | 1,1 => ⟨⟨(-3274293239270173383330291),(-2235289178397117756645763),true⟩,⟨(-2337119806052459933703946),(-1392402422217330134576871),true⟩⟩
  | 1,2 => ⟨⟨(-2919663185649300425842600),(-1955791663619561168434041),true⟩,⟨(-2434737505468627180652448),(-1548188241028107082586525),true⟩⟩
  | 1,3 => ⟨⟨(-4618121022412939927612672),(-3289741156300693593917801),true⟩,⟨(-1952752959299599208913088),(-779221710919129472899563),true⟩⟩
  | 1,4 => ⟨⟨(-5356982501067874306663749),(-3876994424513632773116806),true⟩,⟨(-1745077372151307991789678),(-450754491123003286251304),true⟩⟩
  | 1,5 => ⟨⟨(-5873323116763049965326531),(-4294677324423428700516898),true⟩,⟨(-1605657445668417344335269),(-234170705416852725624764),true⟩⟩
  | 2,0 => ⟨⟨(-277138844247419810978339),240226495565294620984757,true⟩,⟨(-2980193718240149284452043),(-2391744745322884382337214),true⟩⟩
  | 2,1 => ⟨⟨431821624331580207872429,901020923445358764282661,true⟩,⟨(-3035493293794619971489579),(-2491378100006831458013368),true⟩⟩
  | 2,2 => ⟨⟨851619264557790580689019,1310919298806605534602370,true⟩,⟨(-3051019210218586439230014),(-2526731369957953837722982),true⟩⟩
  | 2,3 => ⟨⟨(-1160934248360334580888958),(-520464829806579075689714),true⟩,⟨(-2853314566649985440943658),(-2186836894244322249016546),true⟩⟩
  | 2,4 => ⟨⟨(-2036831004881149689060742),(-1247641686232197346986525),true⟩,⟨(-2666332753543333956585767),(-1905433100224862287906868),true⟩⟩
  | 2,5 => ⟨⟨(-2667330118259359148291076),(-1755422701379886869243192),true⟩,⟨(-2503251549461855572440520),(-1655410534746218463736686),true⟩⟩
  | 3,0 => ⟨⟨4238804792316687539342582,4707673318892340051038422,true⟩,⟨(-2731763682804588814985555),(-2311999973514751567986922),true⟩⟩
  | 3,1 => ⟨⟨5185663608933330776757266,5670882669139077387737450,true⟩,⟨(-2547588599562900559573394),(-2147949655952730303286950),true⟩⟩
  | 3,2 => ⟨⟨5750954334699566681370046,6246856327104340312758728,true⟩,⟨(-2424377296187890006135414),(-2035958054317461681920934),true⟩⟩
  | 3,3 => ⟨⟨3068617006682666678273350,3522326471737038294503661,true⟩,⟨(-2913040645723648450767407),(-2464737211470212392051950),true⟩⟩
  | 3,4 => ⟨⟨1936497945626952732128810,2385226222387935553767207,true⟩,⟨(-3024298714047488313480130),(-2542051546303950658673972),true⟩⟩
  | 3,5 => ⟨⟨1155802983860156195112060,1610160921859587665540427,true⟩,⟨(-3052749844345061727338218),(-2541461012584450292341806),true⟩⟩
  | 4,0 => ⟨⟨9605270759732489369771859,10168995619835191157576627,true⟩,⟨(-1345024169212732257159407),(-1031597534896405916594204),true⟩⟩
  | 4,1 => ⟨⟨10390319126944262319181246,10960605984343577051058441,true⟩,⟨(-1054886545592384189402618),(-760530828175449020345637),true⟩⟩
  | 4,2 => ⟨⟨10788189987646336965811218,11359015456106810058780304,true⟩,⟨(-888171604247882904512540),(-605267033966482239954462),true⟩⟩
  | 4,3 => ⟨⟨8444393425094213504681777,8991243403299848889517119,true⟩,⟨(-1717950429470700139817493),(-1380509024393656846263216),true⟩⟩
  | 4,4 => ⟨⟨7140216119490388449413205,7663212456621230969681427,true⟩,⟨(-2084405235195141197344237),(-1722275258632341873629257),true⟩⟩
  | 4,5 => ⟨⟨6152053556037200878827567,6655746886892012605820180,true⟩,⟨(-2331501815300037212547747),(-1950804493319697281949277),true⟩⟩
  | 5,0 => ⟨⟨11723293357947239021467366,12211314848156281090756326,true⟩,⟨79393323579113949796810,276095643921896923118618,true⟩⟩
  | 5,1 => ⟨⟨11343668948894460791165705,11787208129232714265758400,true⟩,⟨229944320510516336867079,404828903320960694779309,true⟩⟩
  | 5,2 => ⟨⟨11006110014666109962815335,11420115087558006021844847,true⟩,⟨297951258884684095018135,459769866954562874787293,true⟩⟩
  | 5,3 => ⟨⟨11834762914129727815174163,12366845050499540931577112,true⟩,⟨(-176461263015615748992352),48117366366463950005071,true⟩⟩
  | 5,4 => ⟨⟨11518908827383264643158693,12079063051723349844468178,true⟩,⟨(-502667572561412979020588),(-248812129054255296902444),true⟩⟩
  | 5,5 => ⟨⟨11036491710530518871830147,11606054382398935962327412,true⟩,⟨(-773185558833226525401468),(-498501190658541936246061),true⟩⟩
  | 6,0 => ⟨⟨6876681038044129194209788,7056940123876256652225553,true⟩,⟨391438822498049958461775,465214349433994296809384,true⟩⟩
  | 6,1 => ⟨⟨5672220152044548916085688,5802381469415450138238130,true⟩,⟨339622969374439837682837,395846219619285488685628,true⟩⟩
  | 6,2 => ⟨⟨4998120610937677659120727,5102753708125663310373961,true⟩,⟨303184975952721679151934,350435615391413772008246,true⟩⟩
  | 6,3 => ⟨⟨8426298887637967061784571,8680239816288851181638368,true⟩,⟨425231130649694938371900,525157213150995919797291,true⟩⟩
  | 6,4 => ⟨⟨9862262901083316685269448,10196699675808623385610279,true⟩,⟨401765106314369448426037,531510194525960154253649,true⟩⟩
  | 6,5 => ⟨⟨10720025843726208735953934,11111963257749548706077859,true⟩,⟨336877570317578515179631,489422244538087205257320,true⟩⟩
  | 7,0 => ⟨⟨2755612401816973070100520,2838200550113350141001691,true⟩,⟨140400345601417008231142,172720821781843331318245,true⟩⟩
  | 7,1 => ⟨⟨2343989248604262714027152,2422870731045725805042817,true⟩,⟨97505670324924478958693,127855648887243512419834,true⟩⟩
  | 7,2 => ⟨⟨2148729259136817426139695,2226548059350303370381968,true⟩,⟨70257056534678022436826,100224473287491578346437,true⟩⟩
  | 7,3 => ⟨⟨3390606788534969532837743,3479170113188475397718784,true⟩,⟨193830171383593205982287,229966191968520412205488,true⟩⟩
  | 7,4 => ⟨⟨4124084843483100717166492,4218555390893748648363554,true⟩,⟨247336284995654655264921,288091679740737838287123,true⟩⟩
  | 7,5 => ⟨⟨4689564062314115393262763,4787700055702737043424526,true⟩,⟨284558281198220300324843,328864492302664663291584,true⟩⟩
  | 8,0 => ⟨⟨1914059357023657887789261,1998491828804868248119826,true⟩,⟨(-20229679146928031018639),14599168975888896906676,true⟩⟩
  | 8,1 => ⟨⟨1944228441204419661913449,2036374092704611775965736,true⟩,⟨(-70987113011480553837795),(-30518600510321110371839),true⟩⟩
  | 8,2 => ⟨⟨2005901725064187643060048,2106117944361883511712750,true⟩,⟨(-119868946468877669050995),(-73333700101500784773829),true⟩⟩
  | 8,3 => ⟨⟨1947643219746296936206014,2027561304605783615225489,true⟩,⟨18402695370065922700833,50087439538681807432745,true⟩⟩
  | 8,4 => ⟨⟨2022476182768363862314094,2100637660434154657697142,true⟩,⟨44734698585179496396394,75145752790452933547021,true⟩⟩
  | 8,5 => ⟨⟨2089565521884081783830827,2167358431407463967664607,true⟩,⟨59671668869549294639662,89724679108098998100372,true⟩⟩
  | 9,0 => ⟨⟨2439258476080899498495594,2586027063278820070862339,true⟩,⟨(-411292052269745387396435),(-326609619187676168014554),true⟩⟩
  | 9,1 => ⟨⟨2724667293917778492163247,2904138760255696794443279,true⟩,⟨(-636688148341503224701948),(-522229242217400472425066),true⟩⟩
  | 9,2 => ⟨⟨2976538922250783763388094,3188115652552461129959464,true⟩,⟨(-871440464060062402877833),(-725817457921800307623442),true⟩⟩
  | 9,3 => ⟨⟨2224946831964608546180660,2348837651105116590040634,true⟩,⟨(-263826400409668000678739),(-198573142729752122170633),true⟩⟩
  | 9,4 => ⟨⟨2098795184606680631991275,2209354020592553037653822,true⟩,⟨(-181957780707820465996052),(-127424230996508262522491),true⟩⟩
  | 9,5 => ⟨⟨2040385423008104372677234,2144558477933008412212999,true⟩,⟨(-143558843467581475233960),(-93995759694253858026884),true⟩⟩
  | 10,0 => ⟨⟨3946030723692423831572790,4337679245869778738610671,true⟩,⟨(-2315081327774198755955849),(-1970823691567163065739207),true⟩⟩
  | 10,1 => ⟨⟨4287650616090664969200953,4804154861786993167721353,true⟩,⟨(-3357438322946177425935430),(-2860521225531225932411437),true⟩⟩
  | 10,2 => ⟨⟨4430063482605974654254086,5065973329019243965973976,true⟩,⟨(-4347826114022415771523144),(-3698111494925134178013396),true⟩⟩
  | 10,3 => ⟨⟨3554658463329009208788316,3858069303432919331686758,true⟩,⟨(-1590126324573568535786141),(-1347335580691250634650089),true⟩⟩
  | 10,4 => ⟨⟨3254431308430891609429059,3506284743021725522435804,true⟩,⟨(-1179841656215349211104441),(-992893987731446438093756),true⟩⟩
  | 10,5 => ⟨⟨3088096915165210114067836,3315143085308655508117701,true⟩,⟨(-988316430321388170677579),(-827090745383581691076549),true⟩⟩
  | 11,0 => ⟨⟨3387994067253916593739371,4595921984687331054529503,true⟩,⟨(-8692556620179848116726363),(-7270670956832835566546019),true⟩⟩
  | 11,1 => ⟨⟨1984181602547484046004278,3489027235670886164012814,true⟩,⟨(-10569207262744246454405929),(-8744181650636930815362687),true⟩⟩
  | 11,2 => ⟨⟨573119987003152419856211,2300811646574864711329901,true⟩,⟨(-11750240358872537291587205),(-9631678284714816682478781),true⟩⟩
  | 11,3 => ⟨⟨4158747121772783734700726,5108753139345352234690941,true⟩,⟨(-6835057920404943098072000),(-5765666279204496555228157),true⟩⟩
  | 11,4 => ⟨⟨4409571595011338715354753,5188761360323888273745661,true⟩,⟨(-5508347966324254741948361),(-4669505529177048178301500),true⟩⟩
  | 11,5 => ⟨⟨4444837808404059362568312,5136724590417564011229695,true⟩,⟨(-4805627157162590336857036),(-4082637930934680256746318),true⟩⟩
  | 12,0 => ⟨⟨(-5365072742221142193990589),(-2585282125045582583124359),true⟩,⟨(-13285771004406220124723807),(-10381016505369991474156700),true⟩⟩
  | 12,1 => ⟨⟨(-7599139252625335169551271),(-4474792486437472728127592),true⟩,⟨(-12780533788045390299493311),(-9746890055996869324628570),true⟩⟩
  | 12,2 => ⟨⟨(-8988402329600200517613321),(-5679330570475784601710701),true⟩,⟨(-12098800714859628259969351),(-9046848396423310492123016),true⟩⟩
  | 12,3 => ⟨⟨(-2976949169222492872994242),(-614923902397689033987502),true⟩,⟨(-13174579506608207984705065),(-10514406788396122004906076),true⟩⟩
  | 12,4 => ⟨⟨(-1128784890192557406037077),886673776486824282422206,true⟩,⟨(-12642159320143870246359111),(-10240701960992433256167780),true⟩⟩
  | 12,5 => ⟨⟨(-103799547178450172070658),1741279992187056549011663,true⟩,⟨(-12158726841410363946579657),(-9918933506693729768312481),true⟩⟩
  | 13,0 => ⟨⟨(-12657187510576007937953334),(-9333850351180329291958447),true⟩,⟨(-5262939560521746998227639),(-3005236060946374105667322),true⟩⟩
  | 13,1 => ⟨⟨(-12141964860128930811050679),(-9206548295205435949649979),true⟩,⟨(-2579365026636867392723181),(-819308129705011291453064),true⟩⟩
  | 13,2 => ⟨⟨(-11391523829023661182299133),(-8781769368647406771114682),true⟩,⟨(-1031823388169423379343267),451893265068923235395662,true⟩⟩
  | 13,3 => ⟨⟨(-12142606479871576551664170),(-8621160276014785487794217),true⟩,⟨(-8275493062800262611548206),(-5571133432323622600933896),true⟩⟩
  | 13,4 => ⟨⟨(-10816329152896448065670274),(-7322896719240785700105602),true⟩,⟨(-10529433725359349529496504),(-7568347409639858248583195),true⟩⟩
  | 13,5 => ⟨⟨(-9639628669054172328176818),(-6255025922291167282708267),true⟩,⟨(-11649306396680906953850587),(-8610921457000312672645188),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP437Value0_0 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 0 (0:Fin 6))=sharedDiskP437Values 0 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value0_1 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 0 (1:Fin 6))=sharedDiskP437Values 0 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value0_2 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 0 (2:Fin 6))=sharedDiskP437Values 0 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value0_3 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 0 (3:Fin 6))=sharedDiskP437Values 0 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value0_4 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 0 (4:Fin 6))=sharedDiskP437Values 0 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value0_5 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 0 (5:Fin 6))=sharedDiskP437Values 0 (5:Fin 6) := by decide +kernel
theorem sharedDiskP437Values0_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 0 j)=sharedDiskP437Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP437Value0_0
  · exact sharedDiskP437Value0_1
  · exact sharedDiskP437Value0_2
  · exact sharedDiskP437Value0_3
  · exact sharedDiskP437Value0_4
  · exact sharedDiskP437Value0_5
private theorem sharedDiskP437Value1_0 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 1 (0:Fin 6))=sharedDiskP437Values 1 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value1_1 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 1 (1:Fin 6))=sharedDiskP437Values 1 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value1_2 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 1 (2:Fin 6))=sharedDiskP437Values 1 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value1_3 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 1 (3:Fin 6))=sharedDiskP437Values 1 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value1_4 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 1 (4:Fin 6))=sharedDiskP437Values 1 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value1_5 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 1 (5:Fin 6))=sharedDiskP437Values 1 (5:Fin 6) := by decide +kernel
theorem sharedDiskP437Values1_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 1 j)=sharedDiskP437Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP437Value1_0
  · exact sharedDiskP437Value1_1
  · exact sharedDiskP437Value1_2
  · exact sharedDiskP437Value1_3
  · exact sharedDiskP437Value1_4
  · exact sharedDiskP437Value1_5
private theorem sharedDiskP437Value2_0 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 2 (0:Fin 6))=sharedDiskP437Values 2 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value2_1 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 2 (1:Fin 6))=sharedDiskP437Values 2 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value2_2 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 2 (2:Fin 6))=sharedDiskP437Values 2 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value2_3 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 2 (3:Fin 6))=sharedDiskP437Values 2 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value2_4 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 2 (4:Fin 6))=sharedDiskP437Values 2 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value2_5 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 2 (5:Fin 6))=sharedDiskP437Values 2 (5:Fin 6) := by decide +kernel
theorem sharedDiskP437Values2_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 2 j)=sharedDiskP437Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP437Value2_0
  · exact sharedDiskP437Value2_1
  · exact sharedDiskP437Value2_2
  · exact sharedDiskP437Value2_3
  · exact sharedDiskP437Value2_4
  · exact sharedDiskP437Value2_5
private theorem sharedDiskP437Value3_0 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 3 (0:Fin 6))=sharedDiskP437Values 3 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value3_1 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 3 (1:Fin 6))=sharedDiskP437Values 3 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value3_2 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 3 (2:Fin 6))=sharedDiskP437Values 3 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value3_3 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 3 (3:Fin 6))=sharedDiskP437Values 3 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value3_4 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 3 (4:Fin 6))=sharedDiskP437Values 3 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value3_5 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 3 (5:Fin 6))=sharedDiskP437Values 3 (5:Fin 6) := by decide +kernel
theorem sharedDiskP437Values3_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 3 j)=sharedDiskP437Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP437Value3_0
  · exact sharedDiskP437Value3_1
  · exact sharedDiskP437Value3_2
  · exact sharedDiskP437Value3_3
  · exact sharedDiskP437Value3_4
  · exact sharedDiskP437Value3_5
private theorem sharedDiskP437Value4_0 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 4 (0:Fin 6))=sharedDiskP437Values 4 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value4_1 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 4 (1:Fin 6))=sharedDiskP437Values 4 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value4_2 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 4 (2:Fin 6))=sharedDiskP437Values 4 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value4_3 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 4 (3:Fin 6))=sharedDiskP437Values 4 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value4_4 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 4 (4:Fin 6))=sharedDiskP437Values 4 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value4_5 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 4 (5:Fin 6))=sharedDiskP437Values 4 (5:Fin 6) := by decide +kernel
theorem sharedDiskP437Values4_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 4 j)=sharedDiskP437Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP437Value4_0
  · exact sharedDiskP437Value4_1
  · exact sharedDiskP437Value4_2
  · exact sharedDiskP437Value4_3
  · exact sharedDiskP437Value4_4
  · exact sharedDiskP437Value4_5
private theorem sharedDiskP437Value5_0 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 5 (0:Fin 6))=sharedDiskP437Values 5 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value5_1 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 5 (1:Fin 6))=sharedDiskP437Values 5 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value5_2 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 5 (2:Fin 6))=sharedDiskP437Values 5 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value5_3 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 5 (3:Fin 6))=sharedDiskP437Values 5 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value5_4 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 5 (4:Fin 6))=sharedDiskP437Values 5 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value5_5 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 5 (5:Fin 6))=sharedDiskP437Values 5 (5:Fin 6) := by decide +kernel
theorem sharedDiskP437Values5_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 5 j)=sharedDiskP437Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP437Value5_0
  · exact sharedDiskP437Value5_1
  · exact sharedDiskP437Value5_2
  · exact sharedDiskP437Value5_3
  · exact sharedDiskP437Value5_4
  · exact sharedDiskP437Value5_5
private theorem sharedDiskP437Value6_0 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 6 (0:Fin 6))=sharedDiskP437Values 6 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value6_1 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 6 (1:Fin 6))=sharedDiskP437Values 6 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value6_2 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 6 (2:Fin 6))=sharedDiskP437Values 6 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value6_3 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 6 (3:Fin 6))=sharedDiskP437Values 6 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value6_4 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 6 (4:Fin 6))=sharedDiskP437Values 6 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value6_5 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 6 (5:Fin 6))=sharedDiskP437Values 6 (5:Fin 6) := by decide +kernel
theorem sharedDiskP437Values6_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 6 j)=sharedDiskP437Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP437Value6_0
  · exact sharedDiskP437Value6_1
  · exact sharedDiskP437Value6_2
  · exact sharedDiskP437Value6_3
  · exact sharedDiskP437Value6_4
  · exact sharedDiskP437Value6_5
private theorem sharedDiskP437Value7_0 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 7 (0:Fin 6))=sharedDiskP437Values 7 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value7_1 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 7 (1:Fin 6))=sharedDiskP437Values 7 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value7_2 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 7 (2:Fin 6))=sharedDiskP437Values 7 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value7_3 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 7 (3:Fin 6))=sharedDiskP437Values 7 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value7_4 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 7 (4:Fin 6))=sharedDiskP437Values 7 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value7_5 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 7 (5:Fin 6))=sharedDiskP437Values 7 (5:Fin 6) := by decide +kernel
theorem sharedDiskP437Values7_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 7 j)=sharedDiskP437Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP437Value7_0
  · exact sharedDiskP437Value7_1
  · exact sharedDiskP437Value7_2
  · exact sharedDiskP437Value7_3
  · exact sharedDiskP437Value7_4
  · exact sharedDiskP437Value7_5
private theorem sharedDiskP437Value8_0 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 8 (0:Fin 6))=sharedDiskP437Values 8 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value8_1 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 8 (1:Fin 6))=sharedDiskP437Values 8 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value8_2 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 8 (2:Fin 6))=sharedDiskP437Values 8 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value8_3 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 8 (3:Fin 6))=sharedDiskP437Values 8 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value8_4 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 8 (4:Fin 6))=sharedDiskP437Values 8 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value8_5 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 8 (5:Fin 6))=sharedDiskP437Values 8 (5:Fin 6) := by decide +kernel
theorem sharedDiskP437Values8_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 8 j)=sharedDiskP437Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP437Value8_0
  · exact sharedDiskP437Value8_1
  · exact sharedDiskP437Value8_2
  · exact sharedDiskP437Value8_3
  · exact sharedDiskP437Value8_4
  · exact sharedDiskP437Value8_5
private theorem sharedDiskP437Value9_0 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 9 (0:Fin 6))=sharedDiskP437Values 9 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value9_1 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 9 (1:Fin 6))=sharedDiskP437Values 9 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value9_2 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 9 (2:Fin 6))=sharedDiskP437Values 9 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value9_3 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 9 (3:Fin 6))=sharedDiskP437Values 9 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value9_4 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 9 (4:Fin 6))=sharedDiskP437Values 9 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value9_5 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 9 (5:Fin 6))=sharedDiskP437Values 9 (5:Fin 6) := by decide +kernel
theorem sharedDiskP437Values9_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 9 j)=sharedDiskP437Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP437Value9_0
  · exact sharedDiskP437Value9_1
  · exact sharedDiskP437Value9_2
  · exact sharedDiskP437Value9_3
  · exact sharedDiskP437Value9_4
  · exact sharedDiskP437Value9_5
private theorem sharedDiskP437Value10_0 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 10 (0:Fin 6))=sharedDiskP437Values 10 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value10_1 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 10 (1:Fin 6))=sharedDiskP437Values 10 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value10_2 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 10 (2:Fin 6))=sharedDiskP437Values 10 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value10_3 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 10 (3:Fin 6))=sharedDiskP437Values 10 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value10_4 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 10 (4:Fin 6))=sharedDiskP437Values 10 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value10_5 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 10 (5:Fin 6))=sharedDiskP437Values 10 (5:Fin 6) := by decide +kernel
theorem sharedDiskP437Values10_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 10 j)=sharedDiskP437Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP437Value10_0
  · exact sharedDiskP437Value10_1
  · exact sharedDiskP437Value10_2
  · exact sharedDiskP437Value10_3
  · exact sharedDiskP437Value10_4
  · exact sharedDiskP437Value10_5
private theorem sharedDiskP437Value11_0 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 11 (0:Fin 6))=sharedDiskP437Values 11 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value11_1 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 11 (1:Fin 6))=sharedDiskP437Values 11 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value11_2 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 11 (2:Fin 6))=sharedDiskP437Values 11 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value11_3 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 11 (3:Fin 6))=sharedDiskP437Values 11 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value11_4 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 11 (4:Fin 6))=sharedDiskP437Values 11 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value11_5 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 11 (5:Fin 6))=sharedDiskP437Values 11 (5:Fin 6) := by decide +kernel
theorem sharedDiskP437Values11_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 11 j)=sharedDiskP437Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP437Value11_0
  · exact sharedDiskP437Value11_1
  · exact sharedDiskP437Value11_2
  · exact sharedDiskP437Value11_3
  · exact sharedDiskP437Value11_4
  · exact sharedDiskP437Value11_5
private theorem sharedDiskP437Value12_0 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 12 (0:Fin 6))=sharedDiskP437Values 12 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value12_1 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 12 (1:Fin 6))=sharedDiskP437Values 12 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value12_2 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 12 (2:Fin 6))=sharedDiskP437Values 12 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value12_3 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 12 (3:Fin 6))=sharedDiskP437Values 12 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value12_4 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 12 (4:Fin 6))=sharedDiskP437Values 12 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value12_5 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 12 (5:Fin 6))=sharedDiskP437Values 12 (5:Fin 6) := by decide +kernel
theorem sharedDiskP437Values12_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 12 j)=sharedDiskP437Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP437Value12_0
  · exact sharedDiskP437Value12_1
  · exact sharedDiskP437Value12_2
  · exact sharedDiskP437Value12_3
  · exact sharedDiskP437Value12_4
  · exact sharedDiskP437Value12_5
private theorem sharedDiskP437Value13_0 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 13 (0:Fin 6))=sharedDiskP437Values 13 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value13_1 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 13 (1:Fin 6))=sharedDiskP437Values 13 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value13_2 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 13 (2:Fin 6))=sharedDiskP437Values 13 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value13_3 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 13 (3:Fin 6))=sharedDiskP437Values 13 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value13_4 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 13 (4:Fin 6))=sharedDiskP437Values 13 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP437Value13_5 : truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 13 (5:Fin 6))=sharedDiskP437Values 13 (5:Fin 6) := by decide +kernel
theorem sharedDiskP437Values13_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points 13 j)=sharedDiskP437Values 13 j := by
  intro j
  fin_cases j
  · exact sharedDiskP437Value13_0
  · exact sharedDiskP437Value13_1
  · exact sharedDiskP437Value13_2
  · exact sharedDiskP437Value13_3
  · exact sharedDiskP437Value13_4
  · exact sharedDiskP437Value13_5
theorem sharedDiskP437Values_eq : ∀ (i : Fin 14) (j : Fin 6), truncatedChordCell 1 sharedDiskP437Params (sharedChord426Gauss6Points i j)=sharedDiskP437Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP437Values0_eq
  · exact sharedDiskP437Values1_eq
  · exact sharedDiskP437Values2_eq
  · exact sharedDiskP437Values3_eq
  · exact sharedDiskP437Values4_eq
  · exact sharedDiskP437Values5_eq
  · exact sharedDiskP437Values6_eq
  · exact sharedDiskP437Values7_eq
  · exact sharedDiskP437Values8_eq
  · exact sharedDiskP437Values9_eq
  · exact sharedDiskP437Values10_eq
  · exact sharedDiskP437Values11_eq
  · exact sharedDiskP437Values12_eq
  · exact sharedDiskP437Values13_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP437Box : HorizontalRectangle := ⟨(77/200),(31/80),(1108510757643/2199023255552),(1109047628555/2199023255552),(1393172979551659234396641931824389/324518553658426726783156020576256),(4323043297135578416718832787787013/324518553658426726783156020576256),(-867834652293400853588751882305449/162259276829213363391578010288128),(2610776454515077490109758874911069/649037107316853453566312041152512),true,[]⟩
noncomputable def sharedDiskP437Grid : CGrid := momentChordGrid sharedDiskP437Params chordGaussRule6 1 sharedChord426Bd sharedChord426M (995300573/4503599627370496)
theorem sharedDiskP437Columns : containedInReported sharedDiskP437Grid.re sharedDiskP437Box.reLo sharedDiskP437Box.reHi=true ∧ containedInReported sharedDiskP437Grid.im sharedDiskP437Box.imLo sharedDiskP437Box.imHi=true := by
  rw [sharedDiskP437Grid,momentChordGrid_eq_tabulated sharedDiskP437Params chordGaussRule6 1 sharedChord426Bd sharedChord426M (995300573/4503599627370496) sharedChord426Gauss6Points sharedChord426Gauss6Weights sharedDiskP437Values sharedChord426Gauss6Points_eq sharedChord426Gauss6Weights_eq sharedDiskP437Values_eq]
  decide +kernel
theorem sharedDiskP437Sound : sharedDiskP437Box.Sound := by
  intro t a tl tu al au
  change (((77/200):ℚ):ℝ)≤t at tl
  change t≤(((31/80):ℚ):ℝ) at tu
  change (((1108510757643/2199023255552):ℚ):ℝ)≤a at al
  change a≤(((1109047628555/2199023255552):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP437Params_ok] at ps
  have band := sharedChord426ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((143/400):ℚ)≤(77/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((31/80):ℚ)≤(31/80)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((1105678609191/2199023255552):ℚ)≤(1108510757643/2199023255552))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((1109047628555/2199023255552):ℚ)≤(1109047628555/2199023255552)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule6 chordGaussRule6_nodes chordGaussRule6_half_disk 1 sharedChord426Bd (by decide +kernel) (by decide +kernel) sharedChord426M (by decide +kernel) (sharedChord426Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP437Columns.1 sharedDiskP437Columns.2
def sharedDiskP437Rows : List SignRow := [positive_437.toSignRow]
theorem sharedDiskP437Rows_actual : ∀ r∈sharedDiskP437Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP437Rows.all (sharedDiskP437Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP437Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP437Rows_actual
