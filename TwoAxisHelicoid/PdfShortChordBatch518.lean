import TwoAxisHelicoid.PdfSharedChord514Gauss8
import TwoAxisHelicoid.PdfSharedChord514Disks

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP518Params : ChordParams := ⟨⟨(-19636026760355926637637),(-19371694373903972113821),true⟩,⟨2166895241673199743353815,2193543912665732568281303,true⟩,⟨116994014910254494520565,119806020261785652716720,true⟩,⟨196965875826670179911863,201355853586854921757142,true⟩,⟨301173153036773213001986,303286242216485706099083,true⟩,⟨1170281448856606222686872,1170793459609682377545210,true⟩,⟨(-2419839560250497678343619),(-2410850886793661275631444),true⟩,⟨⟨1147976066274789908963097,1190068422419946691793514,true⟩,⟨(-1240891),1240891,true⟩⟩⟩
theorem sharedDiskP518Params_ok : chordParams (Grid.ofRats (19/25) (61/80)) (Grid.ofRats (925329255912401/1649267441664000) (931771706856401/1649267441664000))=sharedDiskP518Params := by decide +kernel
def sharedDiskP518Values (i : Fin 8) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3264268921874751007229839),(-2628403178382651394159906),true⟩,⟨(-438235119974909104838250),63428541127329281805001,true⟩⟩
  | 0,1 => ⟨⟨(-2829633122129829961560630),(-2254947941781909036099363),true⟩,⟨(-522050300752472211647707),(-51012165482805345795834),true⟩⟩
  | 0,2 => ⟨⟨(-2522213964666182239002736),(-1993945968259761341757286),true⟩,⟨(-588711101281590616966848),(-145278167370202839434646),true⟩⟩
  | 0,3 => ⟨⟨(-2351772270851814168924281),(-1849829708308114489477938),true⟩,⟨(-627884640465857847584771),(-200751408701967625230991),true⟩⟩
  | 0,4 => ⟨⟨(-3791386837329341103856418),(-3089908962009353700142962),true⟩,⟨(-355991580643088791024296),165578120219074990230030,true⟩⟩
  | 0,5 => ⟨⟨(-4340745058285899241604570),(-3580896064368705856119016),true⟩,⟨(-296009286290525730118381),228550695961511206868344,true⟩⟩
  | 0,6 => ⟨⟨(-4813639810132767174142167),(-4011597075693749501935104),true⟩,⟨(-267269287308289231424348),243363858789473616279161,true⟩⟩
  | 0,7 => ⟨⟨(-5113729428114957606373309),(-4288252080453066549285139),true⟩,⟨(-267877221211296449761305),231905417545611245483258,true⟩⟩
  | 1,0 => ⟨⟨(-1354347943046472409680318),(-1014832830396067952991542),true⟩,⟨(-865744153835661300143455),(-554462841281382913892800),true⟩⟩
  | 1,1 => ⟨⟨(-1141755953245121896034224),(-836684475432470963519987),true⟩,⟨(-911419725900079663539875),(-626727758707799241591531),true⟩⟩
  | 1,2 => ⟨⟨(-988127476082756139463232),(-707367908602334442318272),true⟩,⟨(-941245426885177543565235),(-675560435643867669243446),true⟩⟩
  | 1,3 => ⟨⟨(-900966949500115461228052),(-633715902173291283724457),true⟩,⟨(-956659086262641682716134),(-701609592903994178516220),true⟩⟩
  | 1,4 => ⟨⟨(-1609920590255087694975581),(-1228323608054342598006313),true⟩,⟨(-806371255529580097254121),(-463288385287091992820452),true⟩⟩
  | 1,5 => ⟨⟨(-1879029365049344464070046),(-1453068099076769878954388),true⟩,⟨(-741338303410269439682825),(-365832524613662814423998),true⟩⟩
  | 1,6 => ⟨⟨(-2117104847914109259264328),(-1652424275878944364345598),true⟩,⟨(-683610398793348415632933),(-281058485961347106578510),true⟩⟩
  | 1,7 => ⟨⟨(-2272736344424369720503970),(-1783222854898765283687275),true⟩,⟨(-646456413431548309748869),(-227341841478722880924234),true⟩⟩
  | 2,0 => ⟨⟨49849224850130407343663,222557235610384042431972,true⟩,⟨(-1033980029322835039063376),(-850152226878956729490708),true⟩⟩
  | 2,1 => ⟨⟨251032354045538598745216,414987403614976179259530,true⟩,⟨(-1019122765770009993769582),(-844372693390795140222191),true⟩⟩
  | 2,2 => ⟨⟨395358630055334029425404,558028968159387767192732,true⟩,⟨(-1002984298615641651191881),(-831666877317483492292581),true⟩⟩
  | 2,3 => ⟨⟨477300831534340914652007,640114723740848602352798,true⟩,⟨(-991867624424149003402821),(-821916187294102414234016),true⟩⟩
  | 2,4 => ⟨⟨(-192073454188770045997546),(-2663156193232847433334),true⟩,⟨(-1036548083848824170397519),(-838736499905682590964580),true⟩⟩
  | 2,5 => ⟨⟨(-449084506952278043668938),(-236722049180377647870952),true⟩,⟨(-1021011005853562858676905),(-806247531388005656149515),true⟩⟩
  | 2,6 => ⟨⟨(-681480824348797337937312),(-444433304208642414793794),true⟩,⟨(-992315853264824803178768),(-760152629013876803358585),true⟩⟩
  | 2,7 => ⟨⟨(-839895900731598521684185),(-581801106048007890548096),true⟩,⟨(-966896653833184348464522),(-719007055630075452500255),true⟩⟩
  | 3,0 => ⟨⟨1423589079706719940013726,1601366535588199185465377,true⟩,⟨(-826311314799237641253067),(-659346396940032240973739),true⟩⟩
  | 3,1 => ⟨⟨1639021697890707366125820,1823815367448285841083288,true⟩,⟨(-813203885510020678234578),(-642542284602790371398399),true⟩⟩
  | 3,2 => ⟨⟨1802407205564966468598409,1993884093623857288743074,true⟩,⟨(-822138298245194152943577),(-646913694177702113408182),true⟩⟩
  | 3,3 => ⟨⟨1899405339938254638234374,2095546980748677936149918,true⟩,⟨(-837502437526737412339397),(-658691375647761193850695),true⟩⟩
  | 3,4 => ⟨⟨1173619455392034196199728,1345183437932506175804437,true⟩,⟨(-863832767268643767523088),(-698646163292412863271208),true⟩⟩
  | 3,5 => ⟨⟨914781147803578562256347,1081647190444877112606146,true⟩,⟨(-913696209043385407509234),(-748214027423999045035384),true⟩⟩
  | 3,6 => ⟨⟨685900520703855256842596,849999254511138882731800,true⟩,⟨(-957595497278134839044787),(-790366001514223144580249),true⟩⟩
  | 3,7 => ⟨⟨535010338923408357635157,698051984488693664109557,true⟩,⟨(-983171288683044110455881),(-814080536779670737223092),true⟩⟩
  | 4,0 => ⟨⟨2634891803433252876199603,2933948953439601931359222,true⟩,⟨(-1369477184520285904687598),(-1091412723590414502033380),true⟩⟩
  | 4,1 => ⟨⟨2850898433768670167669602,3203341090084951201007538,true⟩,⟨(-1754325202169710355449033),(-1419975325386333092505167),true⟩⟩
  | 4,2 => ⟨⟨3004153003418191532644200,3412999740730072085361932,true⟩,⟨(-2203539125036520817554410),(-1807250563532286980952175),true⟩⟩
  | 4,3 => ⟨⟨3072990051579974806000782,3523890485540534812285265,true⟩,⟨(-2559881084497880513523435),(-2115941276336524656874478),true⟩⟩
  | 4,4 => ⟨⟨2404966429584376935586840,2662058003798845914112472,true⟩,⟨(-1106971760540523188751056),(-871215745792079408245906),true⟩⟩
  | 4,5 => ⟨⟨2199193955413440953657525,2426875792325534033748577,true⟩,⟨(-954919858098682343691355),(-747499362788097396024591),true⟩⟩
  | 4,6 => ⟨⟨2040686268979240340220197,2249819915678045609523254,true⟩,⟨(-879221183207230655709065),(-688935540719745667080376),true⟩⟩
  | 4,7 => ⟨⟨1945856278454961800705488,2145386719212540552209474,true⟩,⟨(-848484820537265614886483),(-666786069721223357405059),true⟩⟩
  | 5,0 => ⟨⟨2713676071725050079547469,3404360336904504956473846,true⟩,⟨(-4820114678135540994527186),(-4082297170538866751786388),true⟩⟩
  | 5,1 => ⟨⟨2198077003444937773808649,2974854618406600371323461,true⟩,⟨(-5694899932964151985053989),(-4841746756125755617718953),true⟩⟩
  | 5,2 => ⟨⟨1542048124585115256664918,2388068776597173438861101,true⟩,⟨(-6412028139283397965927144),(-5461196815447341403659497),true⟩⟩
  | 5,3 => ⟨⟨1006309895943077250340744,1900263577055219074152997,true⟩,⟨(-6824738538347837119894059),(-5811200768146374480990932),true⟩⟩
  | 5,4 => ⟨⟨2994609829323398335132455,3601665518777988958172989,true⟩,⟨(-3996817904529787660395522),(-3365790932925163172697465),true⟩⟩
  | 5,5 => ⟨⟨3094580844209529461857711,3634120820120699662980755,true⟩,⟨(-3356825169678863278267853),(-2808618909144056003202069),true⟩⟩
  | 5,6 => ⟨⟨3104260064804477425204938,3597414425558280795136976,true⟩,⟨(-2932832473002867449121962),(-2439825034191764256341430),true⟩⟩
  | 5,7 => ⟨⟨3090197463778883712193821,3558183236354867693380940,true⟩,⟨(-2709023420956890116197696),(-2245384245823260226943889),true⟩⟩
  | 6,0 => ⟨⟨(-2129843577097291299992578),(-956423275654833774231196),true⟩,⟨(-7626513037079674573346832),(-6379888253951247883627296),true⟩⟩
  | 6,1 => ⟨⟨(-3173523541870618126816126),(-1932038486223210578745325),true⟩,⟨(-7406271097757640474762816),(-6138688141607412186288805),true⟩⟩
  | 6,2 => ⟨⟨(-3988021025780820854329726),(-2706056558678858065180817),true⟩,⟨(-7039355288808951650614178),(-5779847310443687993992394),true⟩⟩
  | 6,3 => ⟨⟨(-4453534108789704046090186),(-3154994937995277154701504),true⟩,⟨(-6730912103813625557308148),(-5488667035863888972975622),true⟩⟩
  | 6,4 => ⟨⟨(-1065691139543684140798091),22470973315270994030560,true⟩,⟨(-7605051838025019954474241),(-6409850475980532388087655),true⟩⟩
  | 6,5 => ⟨⟨(-174006216887740271072399),833094360261620398379433,true⟩,⟨(-7400004843920235185306056),(-6270313613304736869758798),true⟩⟩
  | 6,6 => ⟨⟨445575849831298848047693,1389988050219708229912884,true⟩,⟨(-7146639058553921357820616),(-6075721183919555375710961),true⟩⟩
  | 6,7 => ⟨⟨780602029497415176709428,1694822167975095723031658,true⟩,⟨(-6966025942614366855102591),(-5928537059420905594163995),true⟩⟩
  | 7,0 => ⟨⟨(-6218969884129944266719346),(-5068735779702544359254990),true⟩,⟨(-2813172395367229944749283),(-2006611464600965596240593),true⟩⟩
  | 7,1 => ⟨⟨(-5969212461518186100570256),(-4947886581117199910550821),true⟩,⟨(-1586666290028472272081023),(-959470262411003982542979),true⟩⟩
  | 7,2 => ⟨⟨(-5564754917798565384096123),(-4664550752096671840618692),true⟩,⟨(-727882184397044317075276),(-240930994799646696337909),true⟩⟩
  | 7,3 => ⟨⟨(-5253394439743229274850683),(-4431580706121128918239868),true⟩,⟨(-279055307917295485085507),137786515279801771943364,true⟩⟩
  | 7,4 => ⟨⟨(-6108535800655536888923931),(-4857997142886078989928969),true⟩,⟨(-4177351465157214750398181),(-3190565391524650899450945),true⟩⟩
  | 7,5 => ⟨⟨(-5650717644878021741571586),(-4350639779500152400247972),true⟩,⟨(-5357053603615101376152971),(-4235714316810065867207782),true⟩⟩
  | 7,6 => ⟨⟨(-5080891435840421545592538),(-3771174514843581933471289),true⟩,⟨(-6153738959391589384709985),(-4955858165396604088515512),true⟩⟩
  | 7,7 => ⟨⟨(-4668314987999161909173136),(-3364241355504333265193516),true⟩,⟨(-6557652881921854312993246),(-5327395821298881049452894),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP518Value0_0 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 0 (0:Fin 8))=sharedDiskP518Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value0_1 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 0 (1:Fin 8))=sharedDiskP518Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value0_2 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 0 (2:Fin 8))=sharedDiskP518Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value0_3 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 0 (3:Fin 8))=sharedDiskP518Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value0_4 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 0 (4:Fin 8))=sharedDiskP518Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value0_5 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 0 (5:Fin 8))=sharedDiskP518Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value0_6 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 0 (6:Fin 8))=sharedDiskP518Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value0_7 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 0 (7:Fin 8))=sharedDiskP518Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP518Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 0 j)=sharedDiskP518Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP518Value0_0
  · exact sharedDiskP518Value0_1
  · exact sharedDiskP518Value0_2
  · exact sharedDiskP518Value0_3
  · exact sharedDiskP518Value0_4
  · exact sharedDiskP518Value0_5
  · exact sharedDiskP518Value0_6
  · exact sharedDiskP518Value0_7
private theorem sharedDiskP518Value1_0 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 1 (0:Fin 8))=sharedDiskP518Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value1_1 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 1 (1:Fin 8))=sharedDiskP518Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value1_2 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 1 (2:Fin 8))=sharedDiskP518Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value1_3 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 1 (3:Fin 8))=sharedDiskP518Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value1_4 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 1 (4:Fin 8))=sharedDiskP518Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value1_5 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 1 (5:Fin 8))=sharedDiskP518Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value1_6 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 1 (6:Fin 8))=sharedDiskP518Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value1_7 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 1 (7:Fin 8))=sharedDiskP518Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP518Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 1 j)=sharedDiskP518Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP518Value1_0
  · exact sharedDiskP518Value1_1
  · exact sharedDiskP518Value1_2
  · exact sharedDiskP518Value1_3
  · exact sharedDiskP518Value1_4
  · exact sharedDiskP518Value1_5
  · exact sharedDiskP518Value1_6
  · exact sharedDiskP518Value1_7
private theorem sharedDiskP518Value2_0 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 2 (0:Fin 8))=sharedDiskP518Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value2_1 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 2 (1:Fin 8))=sharedDiskP518Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value2_2 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 2 (2:Fin 8))=sharedDiskP518Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value2_3 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 2 (3:Fin 8))=sharedDiskP518Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value2_4 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 2 (4:Fin 8))=sharedDiskP518Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value2_5 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 2 (5:Fin 8))=sharedDiskP518Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value2_6 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 2 (6:Fin 8))=sharedDiskP518Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value2_7 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 2 (7:Fin 8))=sharedDiskP518Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP518Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 2 j)=sharedDiskP518Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP518Value2_0
  · exact sharedDiskP518Value2_1
  · exact sharedDiskP518Value2_2
  · exact sharedDiskP518Value2_3
  · exact sharedDiskP518Value2_4
  · exact sharedDiskP518Value2_5
  · exact sharedDiskP518Value2_6
  · exact sharedDiskP518Value2_7
private theorem sharedDiskP518Value3_0 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 3 (0:Fin 8))=sharedDiskP518Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value3_1 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 3 (1:Fin 8))=sharedDiskP518Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value3_2 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 3 (2:Fin 8))=sharedDiskP518Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value3_3 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 3 (3:Fin 8))=sharedDiskP518Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value3_4 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 3 (4:Fin 8))=sharedDiskP518Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value3_5 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 3 (5:Fin 8))=sharedDiskP518Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value3_6 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 3 (6:Fin 8))=sharedDiskP518Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value3_7 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 3 (7:Fin 8))=sharedDiskP518Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP518Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 3 j)=sharedDiskP518Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP518Value3_0
  · exact sharedDiskP518Value3_1
  · exact sharedDiskP518Value3_2
  · exact sharedDiskP518Value3_3
  · exact sharedDiskP518Value3_4
  · exact sharedDiskP518Value3_5
  · exact sharedDiskP518Value3_6
  · exact sharedDiskP518Value3_7
private theorem sharedDiskP518Value4_0 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 4 (0:Fin 8))=sharedDiskP518Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value4_1 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 4 (1:Fin 8))=sharedDiskP518Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value4_2 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 4 (2:Fin 8))=sharedDiskP518Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value4_3 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 4 (3:Fin 8))=sharedDiskP518Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value4_4 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 4 (4:Fin 8))=sharedDiskP518Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value4_5 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 4 (5:Fin 8))=sharedDiskP518Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value4_6 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 4 (6:Fin 8))=sharedDiskP518Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value4_7 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 4 (7:Fin 8))=sharedDiskP518Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP518Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 4 j)=sharedDiskP518Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP518Value4_0
  · exact sharedDiskP518Value4_1
  · exact sharedDiskP518Value4_2
  · exact sharedDiskP518Value4_3
  · exact sharedDiskP518Value4_4
  · exact sharedDiskP518Value4_5
  · exact sharedDiskP518Value4_6
  · exact sharedDiskP518Value4_7
private theorem sharedDiskP518Value5_0 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 5 (0:Fin 8))=sharedDiskP518Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value5_1 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 5 (1:Fin 8))=sharedDiskP518Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value5_2 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 5 (2:Fin 8))=sharedDiskP518Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value5_3 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 5 (3:Fin 8))=sharedDiskP518Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value5_4 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 5 (4:Fin 8))=sharedDiskP518Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value5_5 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 5 (5:Fin 8))=sharedDiskP518Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value5_6 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 5 (6:Fin 8))=sharedDiskP518Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value5_7 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 5 (7:Fin 8))=sharedDiskP518Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP518Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 5 j)=sharedDiskP518Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP518Value5_0
  · exact sharedDiskP518Value5_1
  · exact sharedDiskP518Value5_2
  · exact sharedDiskP518Value5_3
  · exact sharedDiskP518Value5_4
  · exact sharedDiskP518Value5_5
  · exact sharedDiskP518Value5_6
  · exact sharedDiskP518Value5_7
private theorem sharedDiskP518Value6_0 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 6 (0:Fin 8))=sharedDiskP518Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value6_1 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 6 (1:Fin 8))=sharedDiskP518Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value6_2 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 6 (2:Fin 8))=sharedDiskP518Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value6_3 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 6 (3:Fin 8))=sharedDiskP518Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value6_4 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 6 (4:Fin 8))=sharedDiskP518Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value6_5 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 6 (5:Fin 8))=sharedDiskP518Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value6_6 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 6 (6:Fin 8))=sharedDiskP518Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value6_7 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 6 (7:Fin 8))=sharedDiskP518Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP518Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 6 j)=sharedDiskP518Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP518Value6_0
  · exact sharedDiskP518Value6_1
  · exact sharedDiskP518Value6_2
  · exact sharedDiskP518Value6_3
  · exact sharedDiskP518Value6_4
  · exact sharedDiskP518Value6_5
  · exact sharedDiskP518Value6_6
  · exact sharedDiskP518Value6_7
private theorem sharedDiskP518Value7_0 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 7 (0:Fin 8))=sharedDiskP518Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value7_1 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 7 (1:Fin 8))=sharedDiskP518Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value7_2 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 7 (2:Fin 8))=sharedDiskP518Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value7_3 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 7 (3:Fin 8))=sharedDiskP518Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value7_4 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 7 (4:Fin 8))=sharedDiskP518Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value7_5 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 7 (5:Fin 8))=sharedDiskP518Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value7_6 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 7 (6:Fin 8))=sharedDiskP518Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP518Value7_7 : truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 7 (7:Fin 8))=sharedDiskP518Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP518Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points 7 j)=sharedDiskP518Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP518Value7_0
  · exact sharedDiskP518Value7_1
  · exact sharedDiskP518Value7_2
  · exact sharedDiskP518Value7_3
  · exact sharedDiskP518Value7_4
  · exact sharedDiskP518Value7_5
  · exact sharedDiskP518Value7_6
  · exact sharedDiskP518Value7_7
theorem sharedDiskP518Values_eq : ∀ (i : Fin 8) (j : Fin 8), truncatedChordCell 2 sharedDiskP518Params (sharedChord514Gauss8Points i j)=sharedDiskP518Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP518Values0_eq
  · exact sharedDiskP518Values1_eq
  · exact sharedDiskP518Values2_eq
  · exact sharedDiskP518Values3_eq
  · exact sharedDiskP518Values4_eq
  · exact sharedDiskP518Values5_eq
  · exact sharedDiskP518Values6_eq
  · exact sharedDiskP518Values7_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP518Box : HorizontalRectangle := ⟨(19/25),(61/80),(925329255912401/1649267441664000),(931771706856401/1649267441664000),(727645283549825998775667931671393/1298074214633706907132624082305024),(2236688478055281055140220699339617/1298074214633706907132624082305024),(-4650304070938617711345697500084979/1298074214633706907132624082305024),(-3105780978144179747407182262614771/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP518Grid : CGrid := momentChordGrid sharedDiskP518Params chordGaussRule8 2 sharedChord514Bd sharedChord514M (23175049/18014398509481984)
theorem sharedDiskP518Columns : containedInReported sharedDiskP518Grid.re sharedDiskP518Box.reLo sharedDiskP518Box.reHi=true ∧ containedInReported sharedDiskP518Grid.im sharedDiskP518Box.imLo sharedDiskP518Box.imHi=true := by
  rw [sharedDiskP518Grid,momentChordGrid_eq_tabulated sharedDiskP518Params chordGaussRule8 2 sharedChord514Bd sharedChord514M (23175049/18014398509481984) sharedChord514Gauss8Points sharedChord514Gauss8Weights sharedDiskP518Values sharedChord514Gauss8Points_eq sharedChord514Gauss8Weights_eq sharedDiskP518Values_eq]
  decide +kernel
theorem sharedDiskP518Sound : sharedDiskP518Box.Sound := by
  intro t a tl tu al au
  change (((19/25):ℚ):ℝ)≤t at tl
  change t≤(((61/80):ℚ):ℝ) at tu
  change (((925329255912401/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((931771706856401/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP518Params_ok] at ps
  have band := sharedChord514ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3/4):ℚ)≤(19/25))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((61/80):ℚ)≤(77/100)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((921051395650439/1649267441664000):ℚ)≤(925329255912401/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((931771706856401/1649267441664000):ℚ)≤(311497591431881/549755813888000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord514Bd (by decide +kernel) (by decide +kernel) sharedChord514M (by decide +kernel) (sharedChord514Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP518Columns.1 sharedDiskP518Columns.2
def sharedDiskP518Rows : List SignRow := [positive_518.toSignRow]
theorem sharedDiskP518Rows_actual : ∀ r∈sharedDiskP518Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP518Rows.all (sharedDiskP518Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP518Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP519Params : ChordParams := ⟨⟨(-19902202985744914798180),(-19636026760355926637206),true⟩,⟨2156550670799594296433787,2183078052474533225387990,true⟩,⟨117574431787508862203268,120389095812575456948838,true⟩,⟨198678442550516932034705,203086213727285142936390,true⟩,⟨303155307732253937764437,305269227069428581654041,true⟩,⟨1169766089181784036850896,1170281448856606222687708,true⟩,⟨(-2410850886793661275640846),(-2401914086399971007570369),true⟩,⟨⟨1147367661988425192469691,1189553426232735867054649,true⟩,⟨(-1432904),1432904,true⟩⟩⟩
theorem sharedDiskP519Params_ok : chordParams (Grid.ofRats (61/80) (153/200)) (Grid.ofRats (308804434655183/549755813888000) (310951918303183/549755813888000))=sharedDiskP519Params := by decide +kernel
def sharedDiskP519Values (i : Fin 8) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3263395911154787449354019),(-2628529864752433489992788),true⟩,⟨(-434056580701762886630153),66380019605774666568080,true⟩⟩
  | 0,1 => ⟨⟨(-2832094481715800688479464),(-2257824734437599660231564),true⟩,⟨(-516747079274243784973379),(-46408218717843606496244),true⟩⟩
  | 0,2 => ⟨⟨(-2526664258160383733994764),(-1998502689217291641565625),true⟩,⟨(-582685270886202520691406),(-139745207962049965668869),true⟩⟩
  | 0,3 => ⟨⟨(-2357265509667167259469782),(-1855231320285340021193949),true⟩,⟨(-621505169851951213754868),(-194672574979695310646810),true⟩⟩
  | 0,4 => ⟨⟨(-3785878470950517085188855),(-3086091390504809738694548),true⟩,⟨(-353178736992222737620085),166653469931480825365475,true⟩⟩
  | 0,5 => ⟨⟨(-4329796882316783553273490),(-3572293302522223159261745),true⟩,⟨(-294433510454071083326945),228154074756940515092930,true⟩⟩
  | 0,6 => ⟨⟨(-4797590837437379984025253),(-3998390352011303364026906),true⟩,⟨(-266477821473779895110925),242180411660232286485532,true⟩⟩
  | 0,7 => ⟨⟨(-5094291668082885186983576),(-4271926966089960453801029),true⟩,⟨(-267433432942318303343490),230557150378502553650651,true⟩⟩
  | 1,0 => ⟨⟨(-1364675755305040453561263),(-1024216571269159608116940),true⟩,⟨(-858588962810554700723704),(-546779899441069491297480),true⟩⟩
  | 1,1 => ⟨⟨(-1152906123923097023850933),(-846798595602621294610323),true⟩,⟨(-904518452949411244952569),(-619216503044331250309716),true⟩⟩
  | 1,2 => ⟨⟨(-999848755571241566657827),(-718006472007957948404764),true⟩,⟨(-934645608152855868816248),(-668310583024780930485808),true⟩⟩
  | 1,3 => ⟨⟨(-913006759613456661757958),(-644653137486420878450656),true⟩,⟨(-950276374138177599653224),(-694560184093260341569284),true⟩⟩
  | 1,4 => ⟨⟨(-1619186194168025643994760),(-1236800488489132173172030),true⟩,⟨(-799138979527086869942890),(-455673715030500478970967),true⟩⟩
  | 1,5 => ⟨⟨(-1887059390551586666095779),(-1460524186042253648053589),true⟩,⟨(-734256037165103609395414),(-358575992750749364153778),true⟩⟩
  | 1,6 => ⟨⟨(-2123920336941357555264343),(-1658894332892649952447845),true⟩,⟨(-676822847367323755413775),(-274321778961450891195156),true⟩⟩
  | 1,7 => ⟨⟨(-2278689374214138616872456),(-1788996048786418054718696),true⟩,⟨(-639928235262890049368170),(-221027766193375957580599),true⟩⟩
  | 2,0 => ⟨⟨34748617750114794420233,207749737822014721823210,true⟩,⟨(-1031801201078852015946785),(-847871083262154129321887),true⟩⟩
  | 2,1 => ⟨⟨235244833052203440364952,399110858824277003365601,true⟩,⟨(-1018277493610937722848950),(-843608436009520190366789),true⟩⟩
  | 2,2 => ⟨⟨379450380003065954101116,541660934937127077711669,true⟩,⟨(-1002920836219078112071456),(-831884425548952908102993),true⟩⟩
  | 2,3 => ⟨⟨461151447671378956779887,623491244853954617162806,true⟩,⟨(-992377500334516153140333),(-822696058382910701419947),true⟩⟩
  | 2,4 => ⟨⟨(-206366712487336092687346),(-16493578418663015702888),true⟩,⟨(-1032891708002622666744799),(-834997993235767383381532),true⟩⟩
  | 2,5 => ⟨⟨(-462459371354569050392336),(-249562497556833133795323),true⟩,⟨(-1016002529444860729051263),(-801164683514010117103870),true⟩⟩
  | 2,6 => ⟨⟨(-694314508985991857659695),(-456393114547947195892547),true⟩,⟨(-986378214635682439209626),(-753821380809014840050752),true⟩⟩
  | 2,7 => ⟨⟨(-852157389270406830304630),(-593116260705448340207408),true⟩,⟨(-960503098770626778011354),(-712147625322607320144844),true⟩⟩
  | 3,0 => ⟨⟨1406734728988369410675482,1584202358333236549715221,true⟩,⟨(-833055718045497369109350),(-666021897580996039707356),true⟩⟩
  | 3,1 => ⟨⟨1622717849818054651742219,1807336396948548039601035,true⟩,⟨(-821266744544591604609262),(-650395657029026993023418),true⟩⟩
  | 3,2 => ⟨⟨1786670675221323234139879,1978099524256212693367893,true⟩,⟨(-831238563412927554278568),(-655679466397392825412121),true⟩⟩
  | 3,3 => ⟨⟨1884043744425040607334972,2080222459088116214778556,true⟩,⟨(-847253858009414462923870),(-668026301904002861565969),true⟩⟩
  | 3,4 => ⟨⟨1156475954067924359762420,1327621381162737968066834,true⟩,⟨(-869030463596612576113684),(-703905891608621972515761),true⟩⟩
  | 3,5 => ⟨⟨897734877717061440685562,1064121632596434214409869,true⟩,⟨(-917215472338502192179637),(-751897858449474960438187),true⟩⟩
  | 3,6 => ⟨⟨669228559340140058795651,832834973816538192771625,true⟩,⟨(-959559503112274825850907),(-792559808029739476096051),true⟩⟩
  | 3,7 => ⟨⟨518702137409400694883418,681261955901598105528283,true⟩,⟨(-984085095293877471990437),(-815254988752669370096641),true⟩⟩
  | 4,0 => ⟨⟨2621277978446211484967230,2920968279000804316988887,true⟩,⟨(-1386444299471946938569528),(-1107205325267832883184628),true⟩⟩
  | 4,1 => ⟨⟨2836032145911846493197657,3189351675309851663483722,true⟩,⟨(-1774742959678223053961149),(-1438880854570894061926174),true⟩⟩
  | 4,2 => ⟨⟨2986730295124724863724393,3396646259402804027082092,true⟩,⟨(-2227192224428984681895036),(-1829095111731739350748053),true⟩⟩
  | 4,3 => ⟨⟨3052966093731423610972250,3505028768290621204164956,true⟩,⟨(-2585541635022558891656196),(-2139623202502883145053072),true⟩⟩
  | 4,4 => ⟨⟨2391381857898762671271555,2648881253966468461008706,true⟩,⟨(-1121091078281279742299600),(-884454447160277461748787),true⟩⟩
  | 4,5 => ⟨⟨2185046295581399046835777,2412965803935470152097252,true⟩,⟨(-967009612613431504941556),(-758924341007643484382603),true⟩⟩
  | 4,6 => ⟨⟨2025916430165263822645541,2235178075153413278426286,true⟩,⟨(-890001335147655571646440),(-699189658490543220716012),true⟩⟩
  | 4,7 => ⟨⟨1930685158914131376874034,2130287005389281744068604,true⟩,⟨(-858562262376109933582652),(-676409874928231924157784),true⟩⟩
  | 5,0 => ⟨⟨2671195332895480514725484,3362505195890890597389011,true⟩,⟨(-4846215183291674777862969),(-4106697654614996352353087),true⟩⟩
  | 5,1 => ⟨⟨2146171478672681634782677,2922781446856511577749159,true⟩,⟨(-5714179515659346362083586),(-4860219542860612319146050),true⟩⟩
  | 5,2 => ⟨⟨1483246955796246990501031,2328098711281208330486740,true⟩,⟨(-6421353642027694197692617),(-5470965805619455235359955),true⟩⟩
  | 5,3 => ⟨⟨942667447737139393991499,1836474134163206094004689,true⟩,⟨(-6826699247330170551106713),(-5813669250807824855838383),true⟩⟩
  | 5,4 => ⟨⟨2961026325660332999541708,3569132510768934866232357,true⟩,⟨(-4025410429815657602171947),(-3392289784462508528923732),true⟩⟩
  | 5,5 => ⟨⟨3067493731141949379933832,3608229292698450830054649,true⟩,⟨(-3385171343410563602327324),(-2834806659549575785640623),true⟩⟩
  | 5,6 => ⟨⟨3081110680372871706215448,3575472376661626252281223,true⟩,⟨(-2960065370820280467459507),(-2464960481314814000751930),true⟩⟩
  | 5,7 => ⟨⟨3068967449927208224895415,3538139787032648999246687,true⟩,⟨(-2735378160689788647652754),(-2269705599005846657881580),true⟩⟩
  | 6,0 => ⟨⟨(-2183584908765398172490397),(-1012634382083573619911411),true⟩,⟨(-7583643582831307017551145),(-6342789426620096496828076),true⟩⟩
  | 6,1 => ⟨⟨(-3215411906962723407703317),(-1978243553931726306249986),true⟩,⟨(-7352167196343970929621725),(-6092326345946965466514526),true⟩⟩
  | 6,2 => ⟨⟨(-4017840813837299238388507),(-2741693609240925825657177),true⟩,⟨(-6978909283489869643142371),(-5728502199227401930262789),true⟩⟩
  | 6,3 => ⟨⟨(-4475251746435203398927847),(-3183396650498173054010547),true⟩,⟨(-6668199407556133276086234),(-5435711019475317396305455),true⟩⟩
  | 6,4 => ⟨⟨(-1127406069946409139907062),(-40044908540134892276876),true⟩,⟨(-7576080169324920926514472),(-6384516257442341357749238),true⟩⟩
  | 6,5 => ⟨⟨(-239020291565877710459536),768452826327995281766743,true⟩,⟨(-7383932484759927366249074),(-6256077459464955429623561),true⟩⟩
  | 6,6 => ⟨⟨380534289159396503981698,1325913608591980245125056,true⟩,⟨(-7139963738043119399429577),(-6069654459942671676155877),true⟩⟩
  | 6,7 => ⟨⟨716192956696171591137250,1629968763470062032699840,true⟩,⟨(-6964506765442653639519260),(-5927957989158916560484110),true⟩⟩
  | 7,0 => ⟨⟨(-6191352437192698594414430),(-5049971372615696291340463),true⟩,⟨(-2778088948315114286103341),(-1979508368592025098318588),true⟩⟩
  | 7,1 => ⟨⟨(-5940384082136860526209975),(-4926517848022325279432596),true⟩,⟨(-1567350313266349842543228),(-945780601472158296897604),true⟩⟩
  | 7,2 => ⟨⟨(-5539313895951191628029340),(-4645032879474570512908166),true⟩,⟨(-719669997995522216849784),(-236486198241979870313628),true⟩⟩
  | 7,3 => ⟨⟨(-5231394815035676667393886),(-4414447300737918980003020),true⟩,⟨(-276336754043223187596003),137810883510142141068668,true⟩⟩
  | 7,4 => ⟨⟨(-6089859701147498312100781),(-4848654900843343262250747),true⟩,⟨(-4126787452568989148529123),(-3149840016919115315255980),true⟩⟩
  | 7,5 => ⟨⟨(-5646292084219197897316567),(-4355019071040391043106660),true⟩,⟨(-5296756988972311007066287),(-4185993146238754513530999),true⟩⟩
  | 7,6 => ⟨⟨(-5090062486383922015009266),(-3788181542519578916901779),true⟩,⟨(-6090274419322453862171910),(-4902802769999396879592450),true⟩⟩
  | 7,7 => ⟨⟨(-4685965498965711170342254),(-3388974308789790574426155),true⟩,⟨(-6494334322393629280279898),(-5274093574614783629483736),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP519Value0_0 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 0 (0:Fin 8))=sharedDiskP519Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value0_1 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 0 (1:Fin 8))=sharedDiskP519Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value0_2 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 0 (2:Fin 8))=sharedDiskP519Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value0_3 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 0 (3:Fin 8))=sharedDiskP519Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value0_4 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 0 (4:Fin 8))=sharedDiskP519Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value0_5 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 0 (5:Fin 8))=sharedDiskP519Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value0_6 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 0 (6:Fin 8))=sharedDiskP519Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value0_7 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 0 (7:Fin 8))=sharedDiskP519Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP519Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 0 j)=sharedDiskP519Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP519Value0_0
  · exact sharedDiskP519Value0_1
  · exact sharedDiskP519Value0_2
  · exact sharedDiskP519Value0_3
  · exact sharedDiskP519Value0_4
  · exact sharedDiskP519Value0_5
  · exact sharedDiskP519Value0_6
  · exact sharedDiskP519Value0_7
private theorem sharedDiskP519Value1_0 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 1 (0:Fin 8))=sharedDiskP519Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value1_1 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 1 (1:Fin 8))=sharedDiskP519Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value1_2 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 1 (2:Fin 8))=sharedDiskP519Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value1_3 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 1 (3:Fin 8))=sharedDiskP519Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value1_4 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 1 (4:Fin 8))=sharedDiskP519Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value1_5 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 1 (5:Fin 8))=sharedDiskP519Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value1_6 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 1 (6:Fin 8))=sharedDiskP519Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value1_7 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 1 (7:Fin 8))=sharedDiskP519Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP519Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 1 j)=sharedDiskP519Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP519Value1_0
  · exact sharedDiskP519Value1_1
  · exact sharedDiskP519Value1_2
  · exact sharedDiskP519Value1_3
  · exact sharedDiskP519Value1_4
  · exact sharedDiskP519Value1_5
  · exact sharedDiskP519Value1_6
  · exact sharedDiskP519Value1_7
private theorem sharedDiskP519Value2_0 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 2 (0:Fin 8))=sharedDiskP519Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value2_1 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 2 (1:Fin 8))=sharedDiskP519Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value2_2 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 2 (2:Fin 8))=sharedDiskP519Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value2_3 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 2 (3:Fin 8))=sharedDiskP519Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value2_4 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 2 (4:Fin 8))=sharedDiskP519Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value2_5 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 2 (5:Fin 8))=sharedDiskP519Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value2_6 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 2 (6:Fin 8))=sharedDiskP519Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value2_7 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 2 (7:Fin 8))=sharedDiskP519Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP519Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 2 j)=sharedDiskP519Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP519Value2_0
  · exact sharedDiskP519Value2_1
  · exact sharedDiskP519Value2_2
  · exact sharedDiskP519Value2_3
  · exact sharedDiskP519Value2_4
  · exact sharedDiskP519Value2_5
  · exact sharedDiskP519Value2_6
  · exact sharedDiskP519Value2_7
private theorem sharedDiskP519Value3_0 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 3 (0:Fin 8))=sharedDiskP519Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value3_1 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 3 (1:Fin 8))=sharedDiskP519Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value3_2 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 3 (2:Fin 8))=sharedDiskP519Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value3_3 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 3 (3:Fin 8))=sharedDiskP519Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value3_4 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 3 (4:Fin 8))=sharedDiskP519Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value3_5 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 3 (5:Fin 8))=sharedDiskP519Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value3_6 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 3 (6:Fin 8))=sharedDiskP519Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value3_7 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 3 (7:Fin 8))=sharedDiskP519Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP519Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 3 j)=sharedDiskP519Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP519Value3_0
  · exact sharedDiskP519Value3_1
  · exact sharedDiskP519Value3_2
  · exact sharedDiskP519Value3_3
  · exact sharedDiskP519Value3_4
  · exact sharedDiskP519Value3_5
  · exact sharedDiskP519Value3_6
  · exact sharedDiskP519Value3_7
private theorem sharedDiskP519Value4_0 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 4 (0:Fin 8))=sharedDiskP519Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value4_1 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 4 (1:Fin 8))=sharedDiskP519Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value4_2 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 4 (2:Fin 8))=sharedDiskP519Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value4_3 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 4 (3:Fin 8))=sharedDiskP519Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value4_4 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 4 (4:Fin 8))=sharedDiskP519Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value4_5 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 4 (5:Fin 8))=sharedDiskP519Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value4_6 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 4 (6:Fin 8))=sharedDiskP519Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value4_7 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 4 (7:Fin 8))=sharedDiskP519Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP519Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 4 j)=sharedDiskP519Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP519Value4_0
  · exact sharedDiskP519Value4_1
  · exact sharedDiskP519Value4_2
  · exact sharedDiskP519Value4_3
  · exact sharedDiskP519Value4_4
  · exact sharedDiskP519Value4_5
  · exact sharedDiskP519Value4_6
  · exact sharedDiskP519Value4_7
private theorem sharedDiskP519Value5_0 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 5 (0:Fin 8))=sharedDiskP519Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value5_1 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 5 (1:Fin 8))=sharedDiskP519Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value5_2 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 5 (2:Fin 8))=sharedDiskP519Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value5_3 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 5 (3:Fin 8))=sharedDiskP519Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value5_4 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 5 (4:Fin 8))=sharedDiskP519Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value5_5 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 5 (5:Fin 8))=sharedDiskP519Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value5_6 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 5 (6:Fin 8))=sharedDiskP519Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value5_7 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 5 (7:Fin 8))=sharedDiskP519Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP519Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 5 j)=sharedDiskP519Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP519Value5_0
  · exact sharedDiskP519Value5_1
  · exact sharedDiskP519Value5_2
  · exact sharedDiskP519Value5_3
  · exact sharedDiskP519Value5_4
  · exact sharedDiskP519Value5_5
  · exact sharedDiskP519Value5_6
  · exact sharedDiskP519Value5_7
private theorem sharedDiskP519Value6_0 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 6 (0:Fin 8))=sharedDiskP519Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value6_1 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 6 (1:Fin 8))=sharedDiskP519Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value6_2 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 6 (2:Fin 8))=sharedDiskP519Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value6_3 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 6 (3:Fin 8))=sharedDiskP519Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value6_4 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 6 (4:Fin 8))=sharedDiskP519Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value6_5 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 6 (5:Fin 8))=sharedDiskP519Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value6_6 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 6 (6:Fin 8))=sharedDiskP519Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value6_7 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 6 (7:Fin 8))=sharedDiskP519Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP519Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 6 j)=sharedDiskP519Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP519Value6_0
  · exact sharedDiskP519Value6_1
  · exact sharedDiskP519Value6_2
  · exact sharedDiskP519Value6_3
  · exact sharedDiskP519Value6_4
  · exact sharedDiskP519Value6_5
  · exact sharedDiskP519Value6_6
  · exact sharedDiskP519Value6_7
private theorem sharedDiskP519Value7_0 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 7 (0:Fin 8))=sharedDiskP519Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value7_1 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 7 (1:Fin 8))=sharedDiskP519Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value7_2 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 7 (2:Fin 8))=sharedDiskP519Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value7_3 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 7 (3:Fin 8))=sharedDiskP519Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value7_4 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 7 (4:Fin 8))=sharedDiskP519Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value7_5 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 7 (5:Fin 8))=sharedDiskP519Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value7_6 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 7 (6:Fin 8))=sharedDiskP519Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP519Value7_7 : truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 7 (7:Fin 8))=sharedDiskP519Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP519Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points 7 j)=sharedDiskP519Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP519Value7_0
  · exact sharedDiskP519Value7_1
  · exact sharedDiskP519Value7_2
  · exact sharedDiskP519Value7_3
  · exact sharedDiskP519Value7_4
  · exact sharedDiskP519Value7_5
  · exact sharedDiskP519Value7_6
  · exact sharedDiskP519Value7_7
theorem sharedDiskP519Values_eq : ∀ (i : Fin 8) (j : Fin 8), truncatedChordCell 2 sharedDiskP519Params (sharedChord514Gauss8Points i j)=sharedDiskP519Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP519Values0_eq
  · exact sharedDiskP519Values1_eq
  · exact sharedDiskP519Values2_eq
  · exact sharedDiskP519Values3_eq
  · exact sharedDiskP519Values4_eq
  · exact sharedDiskP519Values5_eq
  · exact sharedDiskP519Values6_eq
  · exact sharedDiskP519Values7_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP519Box : HorizontalRectangle := ⟨(61/80),(153/200),(308804434655183/549755813888000),(310951918303183/549755813888000),(1393896220668344168855050687267241/2596148429267413814265248164610048),(4384450441184988426047580492710313/2596148429267413814265248164610048),(-2324771410956670008225348838053835/649037107316853453566312041152512),(-1559586743431082860552849190639563/649037107316853453566312041152512),true,[]⟩
noncomputable def sharedDiskP519Grid : CGrid := momentChordGrid sharedDiskP519Params chordGaussRule8 2 sharedChord514Bd sharedChord514M (23175049/18014398509481984)
theorem sharedDiskP519Columns : containedInReported sharedDiskP519Grid.re sharedDiskP519Box.reLo sharedDiskP519Box.reHi=true ∧ containedInReported sharedDiskP519Grid.im sharedDiskP519Box.imLo sharedDiskP519Box.imHi=true := by
  rw [sharedDiskP519Grid,momentChordGrid_eq_tabulated sharedDiskP519Params chordGaussRule8 2 sharedChord514Bd sharedChord514M (23175049/18014398509481984) sharedChord514Gauss8Points sharedChord514Gauss8Weights sharedDiskP519Values sharedChord514Gauss8Points_eq sharedChord514Gauss8Weights_eq sharedDiskP519Values_eq]
  decide +kernel
theorem sharedDiskP519Sound : sharedDiskP519Box.Sound := by
  intro t a tl tu al au
  change (((61/80):ℚ):ℝ)≤t at tl
  change t≤(((153/200):ℚ):ℝ) at tu
  change (((308804434655183/549755813888000):ℚ):ℝ)≤a at al
  change a≤(((310951918303183/549755813888000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP519Params_ok] at ps
  have band := sharedChord514ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3/4):ℚ)≤(61/80))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((153/200):ℚ)≤(77/100)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((921051395650439/1649267441664000):ℚ)≤(308804434655183/549755813888000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((310951918303183/549755813888000):ℚ)≤(311497591431881/549755813888000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord514Bd (by decide +kernel) (by decide +kernel) sharedChord514M (by decide +kernel) (sharedChord514Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP519Columns.1 sharedDiskP519Columns.2
def sharedDiskP519Rows : List SignRow := [positive_519.toSignRow]
theorem sharedDiskP519Rows_actual : ∀ r∈sharedDiskP519Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP519Rows.all (sharedDiskP519Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP519Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP520Params : ChordParams := ⟨⟨(-20440066785308027433318),(-19902202985744914797743),true⟩,⟨2137651319031893418670380,2171016035953856052238794,true⟩,⟨117991333131842507714971,121712076032422641774915,true⟩,⟨200670672173280705671212,206286043109864412071146,true⟩,⟨305069572369663988916128,309299717956431574778478,true⟩,⟨1168725380079466345313892,1169766089181784036851743,true⟩,⟨(-2401914086399971007579760),(-2384194200078954774926196),true⟩,⟨⟨1139917406317671448399896,1195598107713164561314377,true⟩,⟨(-1914572),1914572,true⟩⟩⟩
theorem sharedDiskP520Params_ok : chordParams (Grid.ofRats (153/200) (77/100)) (Grid.ofRats (309350107783881/549755813888000) (311497591431881/549755813888000))=sharedDiskP520Params := by decide +kernel
def sharedDiskP520Values (i : Fin 8) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3476380299549785147421908),(-2456425363279134782475258),true⟩,⟨(-593378632332412094132905),231582950324028670043120,true⟩⟩
  | 0,1 => ⟨⟨(-3027816758381379511194692),(-2106119546178869088529549),true⟩,⟨(-663276796682664087532007),106396910220789468420172,true⟩⟩
  | 0,2 => ⟨⟨(-2707578914547994446980243),(-1861935954944680229529998),true⟩,⟨(-718164640146301451214534),888785902618289391455,true⟩⟩
  | 0,3 => ⟨⟨(-2528595731768575132899211),(-1727290951641848019627082),true⟩,⟨(-750243885764394058147136),(-62511881024091733355052),true⟩⟩
  | 0,4 => ⟨⟨(-4014599336709304461590215),(-2890924434661751250149168),true⟩,⟨(-522925247859555487342255),345775934052101220297223,true⟩⟩
  | 0,5 => ⟨⟨(-4568653549149883199158342),(-3355305522569240626623312),true⟩,⟨(-468615819302908774286443),418707893211687395909086,true⟩⟩
  | 0,6 => ⟨⟨(-5040045562305474792310090),(-3764313382263767021092296),true⟩,⟨(-445899354365780337975113),432556496828199116229390,true⟩⟩
  | 0,7 => ⟨⟨(-5337146773384719063015222),(-4028238355714676157264211),true⟩,⟨(-447311306111820138019802),417722908038651888186117,true⟩⟩
  | 1,0 => ⟨⟨(-1484445619587323892817865),(-947975305762931392334592),true⟩,⟨(-943744692180810155595039),(-452685254977338894728800),true⟩⟩
  | 1,1 => ⟨⟨(-1262000389015173266329218),(-781325428169220864190223),true⟩,⟨(-980633460738302550813528),(-533437384197493480816073),true⟩⟩
  | 1,2 => ⟨⟨(-1101481903556750376463203),(-660121052451381257299210),true⟩,⟨(-1004553355046032043003207),(-588592893926647528508395),true⟩⟩
  | 1,3 => ⟨⟨(-1010534584800306224746599),(-590981947462304600229278),true⟩,⟨(-1016814274982478318354770),(-618281543038645042301061),true⟩⟩
  | 1,4 => ⟨⟨(-1752058827440754058500398),(-1147346180010743660373391),true⟩,⟨(-895594221963901091214630),(-351844425774992211804776),true⟩⟩
  | 1,5 => ⟨⟨(-2033678694942624920702317),(-1357030172757559163476465),true⟩,⟨(-842737648231486877887164),(-245002808340803727217054),true⟩⟩
  | 1,6 => ⟨⟨(-2282367414683181971420660),(-1543017378821246467374234),true⟩,⟨(-795732562013832137891799),(-152711805259979245182722),true⟩⟩
  | 1,7 => ⟨⟨(-2445409330885630593833728),(-1665097432309447801224504),true⟩,⟨(-765419937739605823597309),(-92985105986215565490393),true⟩⟩
  | 2,0 => ⟨⟨(-30362081302132372826193),228254618821948083522223,true⟩,⟨(-1077677539020563604020222),(-802532175086251372765139),true⟩⟩
  | 2,1 => ⟨⟨173180024070071318157089,416178933530903647937502,true⟩,⟨(-1062121020377557085802397),(-802566736940428883414623),true⟩⟩
  | 2,2 => ⟨⟨319699098736755155282221,557469311344327855911958,true⟩,⟨(-1045266129214374988516875),(-793189940727976611323239),true⟩⟩
  | 2,3 => ⟨⟨401193673415448035802354,638713814217225208137646,true⟩,⟨(-1034953126329894039340934),(-785274573004806447412601),true⟩⟩
  | 2,4 => ⟨⟨(-277032111650237826358038),10422251983609102713733,true⟩,⟨(-1082204236122394786072592),(-783188393149924212050170),true⟩⟩
  | 2,5 => ⟨⟨(-540381214639584709540787),(-213808692113958071569719),true⟩,⟨(-1070297076861392799804406),(-742059931768697549802922),true⟩⟩
  | 2,6 => ⟨⟨(-782009112410972838798124),(-411557791075901367533093),true⟩,⟨(-1046758562393499793382283),(-685930367374857209796606),true⟩⟩
  | 2,7 => ⟨⟨(-946872571683032153795702),(-541755915825349911693522),true⟩,⟨(-1025458937674028893598208),(-638182788910098126223891),true⟩⟩
  | 3,0 => ⟨⟨1342926688626641534164345,1600865239448899604562691,true⟩,⟨(-882589760692408019501772),(-638443566840801803974493),true⟩⟩
  | 3,1 => ⟨⟨1557782814918310512045255,1826870586071659743983321,true⟩,⟨(-873820354620997084892217),(-623451933033948495991181),true⟩⟩
  | 3,2 => ⟨⟨1720643839703270572909840,2000553702301700029100748,true⟩,⟨(-886728637208849766384955),(-628713634251705402031190),true⟩⟩
  | 3,3 => ⟨⟨1817195481564908232924138,2104720215070366540276626,true⟩,⟨(-904832817834590466361834),(-640824051883947863054983),true⟩⟩
  | 3,4 => ⟨⟨1093803632010317640917352,1342260441041723934538064,true⟩,⟨(-915913983617489696518591),(-674744639006103265020244),true⟩⟩
  | 3,5 => ⟨⟨836180811816883285740639,1077993106782213706642609,true⟩,⟨(-962026978703017753376054),(-720262496799751041309584),true⟩⟩
  | 3,6 => ⟨⟨608587789684969849864915,847026905377363471691471,true⟩,⟨(-1003001715547853451009363),(-758124077718909709757787),true⟩⟩
  | 3,7 => ⟨⟨458575621409591755411724,696132215470929093134768,true⟩,⟨(-1026861617940782197648043),(-778697439425898272840391),true⟩⟩
  | 4,0 => ⟨⟨2531278099414099702307008,2976715572452786067954534,true⟩,⟨(-1481702698360312806966857),(-1064382115999533436631675),true⟩⟩
  | 4,1 => ⟨⟨2730055446143220248105286,3258998450768310938877467,true⟩,⟨(-1891371750253271657916416),(-1385626539284345213406270),true⟩⟩
  | 4,2 => ⟨⟨2861534740398888838033247,3479666842527764242640803,true⟩,⟨(-2367084229763025153318315),(-1763173336065086810625844),true⟩⟩
  | 4,3 => ⟨⟨2912101555984119714552113,3597297321881271153772402,true⟩,⟨(-2742970733312869306079254),(-2063047734255117666182992),true⟩⟩
  | 4,4 => ⟨⟨2312153532253736668255782,2692677095153220982826166,true⟩,⟨(-1200314946868690033111086),(-848825394961262608524620),true⟩⟩
  | 4,5 => ⟨⟨2112283412958386543214201,2447765683788875308699575,true⟩,⟨(-1035561323414974205051945),(-727759753696149898087711),true⟩⟩
  | 4,6 => ⟨⟨1956734476542272523679427,2264030868498816281387212,true⟩,⟨(-952102553596755526521824),(-670514957126032047608706),true⟩⟩
  | 4,7 => ⟨⟨1863206125761740093527037,2155990966497996207805031,true⟩,⟨(-917409164109974127649911),(-648877740317207896484855),true⟩⟩
  | 5,0 => ⟨⟨2425292083548501717740053,3500559499795993447832716,true⟩,⟨(-5099598275490313661149190),(-3944761540102382835020535),true⟩⟩
  | 5,1 => ⟨⟨1858765651913256700601727,3077003419245942104791163,true⟩,⟨(-5997198046715657561970802),(-4654244249614417516382009),true⟩⟩
  | 5,2 => ⟨⟨1159447638257772690081877,2497124397363766748783658,true⟩,⟨(-6726306947058520614742367),(-5221821451583657234790702),true⟩⟩
  | 5,3 => ⟨⟨582987462034143004583034,2015586340342652405249104,true⟩,⟨(-7151463347881799569500167),(-5535584004849197724544016),true⟩⟩
  | 5,4 => ⟨⟨2754143933037928267352108,3691993597393882128535879,true⟩,⟨(-4246848947120977024886197),(-3265523067621631053143524),true⟩⟩
  | 5,5 => ⟨⟨2890473181343840209000920,3718426659415421509087809,true⟩,⟨(-3579375851180808144392325),(-2731967891452366239051052),true⟩⟩
  | 5,6 => ⟨⟨2923497199492560043790039,3676518377282106514728001,true⟩,⟨(-3135107011964407916320661),(-2376543731073545965099014),true⟩⟩
  | 5,7 => ⟨⟨2921444993841287440990187,3634014384797233576893983,true⟩,⟨(-2899937857039834451847994),(-2188484442221035141247719),true⟩⟩
  | 6,0 => ⟨⟨(-2649649191340962069226408),(-739885502697711581727302),true⟩,⟨(-7947270584754087402248743),(-5934536479618127337289625),true⟩⟩
  | 6,1 => ⟨⟨(-3694447773596106540693464),(-1666732401590820937004976),true⟩,⟨(-7714947509783551907745787),(-5660040369558409368244638),true⟩⟩
  | 6,2 => ⟨⟨(-4498716513009563234827696),(-2400373728674018688644081),true⟩,⟨(-7336426754915356153946505),(-5287552697381001317685703),true⟩⟩
  | 6,3 => ⟨⟨(-4953199979265139172027253),(-2825627761487896164242930),true⟩,⟨(-7020435090341843411274559),(-4995124683345644416199029),true⟩⟩
  | 6,4 => ⟨⟨(-1569141854224921290495135),194908829283019434697199,true⟩,⟨(-7934262837716105616368032),(-6012587753309484348944693),true⟩⟩
  | 6,5 => ⟨⟨(-651508294242751751962532),973968786357329975365235,true⟩,⟨(-7732128742091832145821986),(-5922710822442727231103215),true⟩⟩
  | 6,6 => ⟨⟨(-4781684542299223796438),1511085935356354031500430,true⟩,⟨(-7477600397968712750844285),(-5767490242100280813905116),true⟩⟩
  | 6,7 => ⟨⟨345635923101294829556093,1813004359583076508763067,true⟩,⟨(-7294888764390467695850628),(-5639010659009942112439711),true⟩⟩
  | 7,0 => ⟨⟨(-6561498497841975021462489),(-4673747824494567881500792),true⟩,⟨(-3037563451649184222692044),(-1681474412948901326415419),true⟩⟩
  | 7,1 => ⟨⟨(-6265620999110516055090004),(-4590273300737975065219878),true⟩,⟨(-1785636945198292791575929),(-709325717894656270185811),true⟩⟩
  | 7,2 => ⟨⟨(-5822729594873945833528386),(-4351725994978839953730575),true⟩,⟨(-902633028498816546450657),(-51229633749310046105011),true⟩⟩
  | 7,3 => ⟨⟨(-5489196889919245270548609),(-4149956501581847631375343),true⟩,⟨(-437625290673317135498019),313373910644785218975359,true⟩⟩
  | 7,4 => ⟨⟨(-6502954280162517465004303),(-4452220030763499056491642),true⟩,⟨(-4423828886937413662818675),(-2790229636227719232418141),true⟩⟩
  | 7,5 => ⟨⟨(-6094660772183698503639279),(-3961524823090751584662819),true⟩,⟨(-5621492524679336485456520),(-3778215707900271782927046),true⟩⟩
  | 7,6 => ⟨⟨(-5557833982803158143666912),(-3409797659408038273680616),true⟩,⟨(-6431608645771357557012689),(-4471558402517089456814447),true⟩⟩
  | 7,7 => ⟨⟨(-5161356479744629013180722),(-3023883493572904388436411),true⟩,⟨(-6843414677679889108657194),(-4835366774061115163250246),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP520Value0_0 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 0 (0:Fin 8))=sharedDiskP520Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value0_1 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 0 (1:Fin 8))=sharedDiskP520Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value0_2 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 0 (2:Fin 8))=sharedDiskP520Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value0_3 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 0 (3:Fin 8))=sharedDiskP520Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value0_4 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 0 (4:Fin 8))=sharedDiskP520Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value0_5 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 0 (5:Fin 8))=sharedDiskP520Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value0_6 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 0 (6:Fin 8))=sharedDiskP520Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value0_7 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 0 (7:Fin 8))=sharedDiskP520Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP520Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 0 j)=sharedDiskP520Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP520Value0_0
  · exact sharedDiskP520Value0_1
  · exact sharedDiskP520Value0_2
  · exact sharedDiskP520Value0_3
  · exact sharedDiskP520Value0_4
  · exact sharedDiskP520Value0_5
  · exact sharedDiskP520Value0_6
  · exact sharedDiskP520Value0_7
private theorem sharedDiskP520Value1_0 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 1 (0:Fin 8))=sharedDiskP520Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value1_1 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 1 (1:Fin 8))=sharedDiskP520Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value1_2 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 1 (2:Fin 8))=sharedDiskP520Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value1_3 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 1 (3:Fin 8))=sharedDiskP520Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value1_4 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 1 (4:Fin 8))=sharedDiskP520Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value1_5 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 1 (5:Fin 8))=sharedDiskP520Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value1_6 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 1 (6:Fin 8))=sharedDiskP520Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value1_7 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 1 (7:Fin 8))=sharedDiskP520Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP520Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 1 j)=sharedDiskP520Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP520Value1_0
  · exact sharedDiskP520Value1_1
  · exact sharedDiskP520Value1_2
  · exact sharedDiskP520Value1_3
  · exact sharedDiskP520Value1_4
  · exact sharedDiskP520Value1_5
  · exact sharedDiskP520Value1_6
  · exact sharedDiskP520Value1_7
private theorem sharedDiskP520Value2_0 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 2 (0:Fin 8))=sharedDiskP520Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value2_1 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 2 (1:Fin 8))=sharedDiskP520Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value2_2 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 2 (2:Fin 8))=sharedDiskP520Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value2_3 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 2 (3:Fin 8))=sharedDiskP520Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value2_4 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 2 (4:Fin 8))=sharedDiskP520Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value2_5 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 2 (5:Fin 8))=sharedDiskP520Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value2_6 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 2 (6:Fin 8))=sharedDiskP520Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value2_7 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 2 (7:Fin 8))=sharedDiskP520Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP520Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 2 j)=sharedDiskP520Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP520Value2_0
  · exact sharedDiskP520Value2_1
  · exact sharedDiskP520Value2_2
  · exact sharedDiskP520Value2_3
  · exact sharedDiskP520Value2_4
  · exact sharedDiskP520Value2_5
  · exact sharedDiskP520Value2_6
  · exact sharedDiskP520Value2_7
private theorem sharedDiskP520Value3_0 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 3 (0:Fin 8))=sharedDiskP520Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value3_1 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 3 (1:Fin 8))=sharedDiskP520Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value3_2 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 3 (2:Fin 8))=sharedDiskP520Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value3_3 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 3 (3:Fin 8))=sharedDiskP520Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value3_4 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 3 (4:Fin 8))=sharedDiskP520Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value3_5 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 3 (5:Fin 8))=sharedDiskP520Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value3_6 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 3 (6:Fin 8))=sharedDiskP520Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value3_7 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 3 (7:Fin 8))=sharedDiskP520Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP520Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 3 j)=sharedDiskP520Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP520Value3_0
  · exact sharedDiskP520Value3_1
  · exact sharedDiskP520Value3_2
  · exact sharedDiskP520Value3_3
  · exact sharedDiskP520Value3_4
  · exact sharedDiskP520Value3_5
  · exact sharedDiskP520Value3_6
  · exact sharedDiskP520Value3_7
private theorem sharedDiskP520Value4_0 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 4 (0:Fin 8))=sharedDiskP520Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value4_1 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 4 (1:Fin 8))=sharedDiskP520Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value4_2 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 4 (2:Fin 8))=sharedDiskP520Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value4_3 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 4 (3:Fin 8))=sharedDiskP520Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value4_4 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 4 (4:Fin 8))=sharedDiskP520Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value4_5 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 4 (5:Fin 8))=sharedDiskP520Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value4_6 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 4 (6:Fin 8))=sharedDiskP520Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value4_7 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 4 (7:Fin 8))=sharedDiskP520Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP520Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 4 j)=sharedDiskP520Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP520Value4_0
  · exact sharedDiskP520Value4_1
  · exact sharedDiskP520Value4_2
  · exact sharedDiskP520Value4_3
  · exact sharedDiskP520Value4_4
  · exact sharedDiskP520Value4_5
  · exact sharedDiskP520Value4_6
  · exact sharedDiskP520Value4_7
private theorem sharedDiskP520Value5_0 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 5 (0:Fin 8))=sharedDiskP520Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value5_1 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 5 (1:Fin 8))=sharedDiskP520Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value5_2 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 5 (2:Fin 8))=sharedDiskP520Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value5_3 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 5 (3:Fin 8))=sharedDiskP520Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value5_4 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 5 (4:Fin 8))=sharedDiskP520Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value5_5 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 5 (5:Fin 8))=sharedDiskP520Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value5_6 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 5 (6:Fin 8))=sharedDiskP520Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value5_7 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 5 (7:Fin 8))=sharedDiskP520Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP520Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 5 j)=sharedDiskP520Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP520Value5_0
  · exact sharedDiskP520Value5_1
  · exact sharedDiskP520Value5_2
  · exact sharedDiskP520Value5_3
  · exact sharedDiskP520Value5_4
  · exact sharedDiskP520Value5_5
  · exact sharedDiskP520Value5_6
  · exact sharedDiskP520Value5_7
private theorem sharedDiskP520Value6_0 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 6 (0:Fin 8))=sharedDiskP520Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value6_1 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 6 (1:Fin 8))=sharedDiskP520Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value6_2 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 6 (2:Fin 8))=sharedDiskP520Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value6_3 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 6 (3:Fin 8))=sharedDiskP520Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value6_4 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 6 (4:Fin 8))=sharedDiskP520Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value6_5 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 6 (5:Fin 8))=sharedDiskP520Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value6_6 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 6 (6:Fin 8))=sharedDiskP520Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value6_7 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 6 (7:Fin 8))=sharedDiskP520Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP520Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 6 j)=sharedDiskP520Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP520Value6_0
  · exact sharedDiskP520Value6_1
  · exact sharedDiskP520Value6_2
  · exact sharedDiskP520Value6_3
  · exact sharedDiskP520Value6_4
  · exact sharedDiskP520Value6_5
  · exact sharedDiskP520Value6_6
  · exact sharedDiskP520Value6_7
private theorem sharedDiskP520Value7_0 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 7 (0:Fin 8))=sharedDiskP520Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value7_1 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 7 (1:Fin 8))=sharedDiskP520Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value7_2 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 7 (2:Fin 8))=sharedDiskP520Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value7_3 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 7 (3:Fin 8))=sharedDiskP520Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value7_4 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 7 (4:Fin 8))=sharedDiskP520Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value7_5 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 7 (5:Fin 8))=sharedDiskP520Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value7_6 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 7 (6:Fin 8))=sharedDiskP520Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP520Value7_7 : truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 7 (7:Fin 8))=sharedDiskP520Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP520Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points 7 j)=sharedDiskP520Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP520Value7_0
  · exact sharedDiskP520Value7_1
  · exact sharedDiskP520Value7_2
  · exact sharedDiskP520Value7_3
  · exact sharedDiskP520Value7_4
  · exact sharedDiskP520Value7_5
  · exact sharedDiskP520Value7_6
  · exact sharedDiskP520Value7_7
theorem sharedDiskP520Values_eq : ∀ (i : Fin 8) (j : Fin 8), truncatedChordCell 2 sharedDiskP520Params (sharedChord514Gauss8Points i j)=sharedDiskP520Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP520Values0_eq
  · exact sharedDiskP520Values1_eq
  · exact sharedDiskP520Values2_eq
  · exact sharedDiskP520Values3_eq
  · exact sharedDiskP520Values4_eq
  · exact sharedDiskP520Values5_eq
  · exact sharedDiskP520Values6_eq
  · exact sharedDiskP520Values7_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP520Box : HorizontalRectangle := ⟨(153/200),(77/100),(309350107783881/549755813888000),(311497591431881/549755813888000),(100994588379610166727499131668117/649037107316853453566312041152512),(1286535756919913096479705916262037/649037107316853453566312041152512),(-5105836189037981866560438546818571/1298074214633706907132624082305024),(-2681106521100530995131130120857099/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP520Grid : CGrid := momentChordGrid sharedDiskP520Params chordGaussRule8 2 sharedChord514Bd sharedChord514M (23175049/18014398509481984)
theorem sharedDiskP520Columns : containedInReported sharedDiskP520Grid.re sharedDiskP520Box.reLo sharedDiskP520Box.reHi=true ∧ containedInReported sharedDiskP520Grid.im sharedDiskP520Box.imLo sharedDiskP520Box.imHi=true := by
  rw [sharedDiskP520Grid,momentChordGrid_eq_tabulated sharedDiskP520Params chordGaussRule8 2 sharedChord514Bd sharedChord514M (23175049/18014398509481984) sharedChord514Gauss8Points sharedChord514Gauss8Weights sharedDiskP520Values sharedChord514Gauss8Points_eq sharedChord514Gauss8Weights_eq sharedDiskP520Values_eq]
  decide +kernel
theorem sharedDiskP520Sound : sharedDiskP520Box.Sound := by
  intro t a tl tu al au
  change (((153/200):ℚ):ℝ)≤t at tl
  change t≤(((77/100):ℚ):ℝ) at tu
  change (((309350107783881/549755813888000):ℚ):ℝ)≤a at al
  change a≤(((311497591431881/549755813888000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP520Params_ok] at ps
  have band := sharedChord514ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3/4):ℚ)≤(153/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(77/100)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((921051395650439/1649267441664000):ℚ)≤(309350107783881/549755813888000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((311497591431881/549755813888000):ℚ)≤(311497591431881/549755813888000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord514Bd (by decide +kernel) (by decide +kernel) sharedChord514M (by decide +kernel) (sharedChord514Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP520Columns.1 sharedDiskP520Columns.2
def sharedDiskP520Rows : List SignRow := [positive_520.toSignRow]
theorem sharedDiskP520Rows_actual : ∀ r∈sharedDiskP520Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP520Rows.all (sharedDiskP520Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP520Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP518Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP519Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP520Rows_actual
