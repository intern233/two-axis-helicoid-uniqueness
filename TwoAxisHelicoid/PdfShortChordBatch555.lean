import TwoAxisHelicoid.PdfSharedChord521Gauss8
import TwoAxisHelicoid.PdfSharedChord521Disks

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP555Params : ChordParams := ⟨⟨(-29683564398693381597081),(-29521477054659314418450),true⟩,⟨1846144507635208255665636,1853254248961151531553234,true⟩,⟨136246896905855890552109,137181993467422882394628,true⟩,⟨260997677038767501413271,262537137242247326256919,true⟩,⟨368777274905030875669195,369836670564374384030172,true⟩,⟨1150981437983191381687700,1151290301429039650702175,true⟩,⟨(-2137007475993293709182026),(-2133283085537587169273418),true⟩,⟨⟨1139770181075064836695287,1154282517932547281647003,true⟩,⟨(-101433313),101433313,true⟩⟩⟩
theorem sharedDiskP555Params_ok : chordParams (Grid.ofRats (677/800) (339/400)) (Grid.ofRats (968223324287839/1649267441664000) (969833937023839/1649267441664000))=sharedDiskP555Params := by decide +kernel
def sharedDiskP555Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3025142276328211203697894),(-2731699747126654132112786),true⟩,⟨(-215995511673223624421926),24487005281705694557565,true⟩⟩
  | 0,1 => ⟨⟨(-2705235542626816966329605),(-2433774186705731146093573),true⟩,⟨(-267559124880529067041330),(-38892911791370921975054),true⟩⟩
  | 0,2 => ⟨⟨(-2472667877599748812002106),(-2218838778025328486620844),true⟩,⟨(-313650540999207298380489),(-96135548827133459369030),true⟩⟩
  | 0,3 => ⟨⟨(-2341220957942342115458260),(-2097709785733043391888524),true⟩,⟨(-342775308348811262852091),(-132051303482754861328959),true⟩⟩
  | 0,4 => ⟨⟨(-3401310302601031579341283),(-3085698975369293774097114),true⟩,⟨(-173811835154933274239689),74963440609025340094336,true⟩⟩
  | 0,5 => ⟨⟨(-3781671052973325618678774),(-3447900100761186792984333),true⟩,⟨(-152198355011159605674113),98879999856512705046245,true⟩⟩
  | 0,6 => ⟨⟨(-4101531026990047517571923),(-3755793494989907674644674),true⟩,⟨(-150837605122536217130397),97680413510992089885820,true⟩⟩
  | 0,7 => ⟨⟨(-4301536158972101227181368),(-3949739498306382522042679),true⟩,⟨(-159624552975473916440636),86277956007293665887051,true⟩⟩
  | 1,0 => ⟨⟨(-1539657135820773961211091),(-1364639264316802005891725),true⟩,⟨(-558817089865454038343542),(-399382695923727610392099),true⟩⟩
  | 1,1 => ⟨⟨(-1362586420878988413407534),(-1203175853009721180495673),true⟩,⟨(-612015989775858261337072),(-465239350097572057626867),true⟩⟩
  | 1,2 => ⟨⟨(-1233662141120262281954960),(-1085479525122972498253828),true⟩,⟨(-650793612198506591815476),(-513252661342266368138033),true⟩⟩
  | 1,3 => ⟨⟨(-1160226605301763315758380),(-1018351088329476203201503),true⟩,⟨(-672679265725895646387436),(-540364796665324480633876),true⟩⟩
  | 1,4 => ⟨⟨(-1749997054493027422583581),(-1556419923967642135567343),true⟩,⟨(-497093714266621365913845),(-322961231075402466761026),true⟩⟩
  | 1,5 => ⟨⟨(-1967976991279143410421823),(-1755453291889747830384285),true⟩,⟨(-436273449694963743781580),(-247657005663256642747083),true⟩⟩
  | 1,6 => ⟨⟨(-2157531114054808313249062),(-1928987930830653540252506),true⟩,⟨(-386909922471958089550613),(-186577601526911649860676),true⟩⟩
  | 1,7 => ⟨⟨(-2279706644188080997825475),(-2041139559690523720440228),true⟩,⟨(-357122852876115911614899),(-149764393816932430879999),true⟩⟩
  | 2,0 => ⟨⟨(-340425942606277683792015),(-255901145078828985927430),true⟩,⟨(-875008970802400861557438),(-789808295643461429951446),true⟩⟩
  | 2,1 => ⟨⟨(-164450850117682581434069),(-87269185671027322239703),true⟩,⟨(-900788662597657814377363),(-821386020127244922589108),true⟩⟩
  | 2,2 => ⟨⟨(-35495593266539364974734),37251529228306815956593,true⟩,⟨(-914576896822653741930470),(-838798713312380127217379),true⟩⟩
  | 2,3 => ⟨⟨38535394922572149270910,109212204914648021086324,true⟩,⟨(-920661687779529505848081),(-846734074970611553549476),true⟩⟩
  | 2,4 => ⟨⟨(-550334505521388705032583),(-455175310826165973490056),true⟩,⟨(-833896802944995447857630),(-740479012755776874647152),true⟩⟩
  | 2,5 => ⟨⟨(-773600173899874889878248),(-663177332375010291291307),true⟩,⟨(-780707536850882655125097),(-674750041022891528852672),true⟩⟩
  | 2,6 => ⟨⟨(-974601590595495229277094),(-848257113977362842996984),true⟩,⟨(-726521911885179972142505),(-607171136221829535559166),true⟩⟩
  | 2,7 => ⟨⟨(-1108667434830688502040884),(-971170768409636940281256),true⟩,⟨(-687887139619559670526258),(-559215259204969023653601),true⟩⟩
  | 3,0 => ⟨⟨934093003781685889216979,1003410337804679087186058,true⟩,⟨(-958398141435079287898273),(-889076073131295336412267),true⟩⟩
  | 3,1 => ⟨⟨1154261945408839201764926,1227089099289090033809238,true⟩,⟨(-990356796441767598837780),(-918543104880700782036939),true⟩⟩
  | 3,2 => ⟨⟨1324641870060797816853941,1401085837531487625238862,true⟩,⟨(-1034124539722009698140662),(-959377679297526127046681),true⟩⟩
  | 3,3 => ⟨⟨1426488158892118265589775,1505524886408853560328101,true⟩,⟨(-1070836221550162416756296),(-993851141450391064212244),true⟩⟩
  | 3,4 => ⟨⟨686978261607615232837058,753742808831648148029418,true⟩,⟨(-943177114824902655227723),(-875149112827594574193754),true⟩⟩
  | 3,5 => ⟨⟨440508432265511795954294,506127660965272895689264,true⟩,⟨(-937058170030625992974170),(-868887221226525128514778),true⟩⟩
  | 3,6 => ⟨⟨228634768465501351232820,295167704770297811181340,true⟩,⟨(-931022018111462515802107),(-861104188519813932826797),true⟩⟩
  | 3,7 => ⟨⟨90841213884351931406721,160234740209147149844766,true⟩,⟨(-924219855630350683672130),(-851501202634188926497297),true⟩⟩
  | 4,0 => ⟨⟨2156992554321137054935688,2282278512711384350626991,true⟩,⟨(-1793540473467265334756652),(-1669430272749537933734556),true⟩⟩
  | 4,1 => ⟨⟨2309682293027685511984824,2458878775642112694435080,true⟩,⟨(-2247184927892005446939877),(-2096854343452330387442553),true⟩⟩
  | 4,2 => ⟨⟨2362640854715921392698378,2536514349169752209019569,true⟩,⟨(-2742888691807177413057490),(-2564529208325502818904320),true⟩⟩
  | 4,3 => ⟨⟨2339847704603963566922517,2531594453896258955818476,true⟩,⟨(-3113267646901389920565580),(-2914046331502917553354865),true⟩⟩
  | 4,4 => ⟨⟨1949461052216324633343829,2055778452120329735768199,true⟩,⟨(-1463260394968316747722214),(-1359178860208513688634406),true⟩⟩
  | 4,5 => ⟨⟨1742732727571582575133131,1835821741768720212234900,true⟩,⟨(-1257209704606769741153492),(-1166589212691886396836992),true⟩⟩
  | 4,6 => ⟨⟨1576429457404510888097575,1661288314678005475204667,true⟩,⟨(-1143938226721505337439529),(-1061422179173310141438719),true⟩⟩
  | 4,7 => ⟨⟨1475640556148419988816873,1556300605977524321740093,true⟩,⟨(-1092088590733910687991528),(-1013606922867800272122339),true⟩⟩
  | 5,0 => ⟨⟨2057729371539802728876891,2293854186037769739129961,true⟩,⟨(-4054787650176515652841682),(-3801813725458006125678881),true⟩⟩
  | 5,1 => ⟨⟨1909944714578454682628975,2158925792603289714440242,true⟩,⟨(-4329605487233149356216830),(-4060531922070657665102594),true⟩⟩
  | 5,2 => ⟨⟨1763289282683117528011784,2022792384471840446489239,true⟩,⟨(-4554026650537230059373838),(-4271590762480355775859950),true⟩⟩
  | 5,3 => ⟨⟨1660689717991033915129402,1926647020336541146599616,true⟩,⟨(-4691182507829117655456351),(-4400463932290783208678188),true⟩⟩
  | 5,4 => ⟨⟨2176430979020047546947297,2399410652624477344256781,true⟩,⟨(-3774033263417209885493328),(-3537271833329756123200400),true⟩⟩
  | 5,5 => ⟨⟨2255880546887477334812676,2467274027871169257859691,true⟩,⟨(-3527506720345855535304291),(-3304831303580788759247451),true⟩⟩
  | 5,6 => ⟨⟨2300780214341945771239139,2503474015746122373490832,true⟩,⟨(-3343360389616863642373972),(-3131137512339072040186470),true⟩⟩
  | 5,7 => ⟨⟨2321158706189704673072178,2518811608348674152068755,true⟩,⟨(-3237154181098935287386041),(-3030939224930809328961413),true⟩⟩
  | 6,0 => ⟨⟨477556056915070474579482,803983875189323794210922,true⟩,⟨(-5666992440251558350088375),(-5305261055696471988513915),true⟩⟩
  | 6,1 => ⟨⟨(-3579506154639513702629),345687838584275268263313,true⟩,⟨(-5877550453538586459523115),(-5493252359963267320018527),true⟩⟩
  | 6,2 => ⟨⟨(-433267844495676438283024),(-64827424837610716327709),true⟩,⟨(-6003469757822674524045341),(-5602140801613347937172803),true⟩⟩
  | 6,3 => ⟨⟨(-711828906183976195881635),(-331456483065500439766353),true⟩,⟨(-6057117848312072878063041),(-5646146463218718118266934),true⟩⟩
  | 6,4 => ⟨⟨918117546820167602660365,1220941241998921894334115,true⟩,⟨(-5396978544216226492735203),(-5059789313928722662115494),true⟩⟩
  | 6,5 => ⟨⟨1260356304150102108424254,1546780304075754779608302,true⟩,⟨(-5121273070729682425115367),(-4803822322182931318051206),true⟩⟩
  | 6,6 => ⟨⟨1486900245152147450738128,1762528171673658297123084,true⟩,⟨(-4895541091083216586907253),(-4592283334481993687107750),true⟩⟩
  | 6,7 => ⟨⟨1606797266398819582196365,1875906961766070268905709,true⟩,⟨(-4757972751220983812418206),(-4463184019772172974439245),true⟩⟩
  | 7,0 => ⟨⟨(-3072685891802435775913044),(-2616381275205327779357763),true⟩,⟨(-5672206071475799961673360),(-5222353119395404195243625),true⟩⟩
  | 7,1 => ⟨⟨(-3715093521068135310867172),(-3247592163976535219237389),true⟩,⟨(-5252063749264071322052830),(-4808387012306217369804492),true⟩⟩
  | 7,2 => ⟨⟨(-4170423462380056770836248),(-3699380607626736782469363),true⟩,⟨(-4816241925301446509101630),(-4384622688835309160770658),true⟩⟩
  | 7,3 => ⟨⟨(-4412299063742773063349062),(-3941777015424540009321348),true⟩,⟨(-4512565667828580100178224),(-4091447379571011814771429),true⟩⟩
  | 7,4 => ⟨⟨(-2343918214012194328945764),(-1906064232766211375328027),true⟩,⟨(-5959656222890508260917773),(-5513033745087964552640395),true⟩⟩
  | 7,5 => ⟨⟨(-1666048470680667438907019),(-1249536506944791224565596),true⟩,⟨(-6085548650400317955321435),(-5649365999178512521915095),true⟩⟩
  | 7,6 => ⟨⟨(-1149631612419437084530526),(-751794872627794178804616),true⟩,⟨(-6099563597286607284438393),(-5675538346231495496057609),true⟩⟩
  | 7,7 => ⟨⟨(-851894442258785797664997),(-465767557846154873900615),true⟩,⟨(-6076181283562815729489143),(-5660757875556385364132910),true⟩⟩
  | 8,0 => ⟨⟨(-5062017778674198292921866),(-4667630531834333299111013),true⟩,⟨(-1699491965787072224386178),(-1423975516548075514294040),true⟩⟩
  | 8,1 => ⟨⟨(-4842985348409117737879460),(-4490106401416861804160240),true⟩,⟨(-934560629131616789346711),(-711292570498999565800267),true⟩⟩
  | 8,2 => ⟨⟨(-4568346847892185122797492),(-4251887410890089479614743),true⟩,⟨(-397943906020163154739624),(-215039538582897993176990),true⟩⟩
  | 8,3 => ⟨⟨(-4368623170986774100951000),(-4075252568239394729198534),true⟩,⟨(-111703815707470974539896),49382995891219937805015,true⟩⟩
  | 8,4 => ⟨⟨(-5106861542717479401169308),(-4676350297401068015526004),true⟩,⟨(-2579927385534303462729945),(-2250869642109267962747154),true⟩⟩
  | 8,5 => ⟨⟨(-4958180467448778489115471),(-4503949588542098404252230),true⟩,⟨(-3399825041948834867680543),(-3027175890289009873705047),true⟩⟩
  | 8,6 => ⟨⟨(-4714627708262640100031785),(-4248940142643403459965863),true⟩,⟨(-4012384952886454919202530),(-3611341104570965825687105),true⟩⟩
  | 8,7 => ⟨⟨(-4519073412482089494594604),(-4049582798460824609735228),true⟩,⟨(-4355147981543256562436553),(-3940006452721951894925692),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP555Value0_0 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP555Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value0_1 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP555Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value0_2 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP555Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value0_3 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP555Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value0_4 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP555Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value0_5 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP555Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value0_6 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP555Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value0_7 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP555Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP555Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 0 j)=sharedDiskP555Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP555Value0_0
  · exact sharedDiskP555Value0_1
  · exact sharedDiskP555Value0_2
  · exact sharedDiskP555Value0_3
  · exact sharedDiskP555Value0_4
  · exact sharedDiskP555Value0_5
  · exact sharedDiskP555Value0_6
  · exact sharedDiskP555Value0_7
private theorem sharedDiskP555Value1_0 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP555Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value1_1 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP555Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value1_2 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP555Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value1_3 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP555Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value1_4 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP555Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value1_5 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP555Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value1_6 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP555Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value1_7 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP555Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP555Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 1 j)=sharedDiskP555Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP555Value1_0
  · exact sharedDiskP555Value1_1
  · exact sharedDiskP555Value1_2
  · exact sharedDiskP555Value1_3
  · exact sharedDiskP555Value1_4
  · exact sharedDiskP555Value1_5
  · exact sharedDiskP555Value1_6
  · exact sharedDiskP555Value1_7
private theorem sharedDiskP555Value2_0 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP555Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value2_1 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP555Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value2_2 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP555Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value2_3 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP555Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value2_4 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP555Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value2_5 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP555Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value2_6 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP555Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value2_7 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP555Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP555Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 2 j)=sharedDiskP555Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP555Value2_0
  · exact sharedDiskP555Value2_1
  · exact sharedDiskP555Value2_2
  · exact sharedDiskP555Value2_3
  · exact sharedDiskP555Value2_4
  · exact sharedDiskP555Value2_5
  · exact sharedDiskP555Value2_6
  · exact sharedDiskP555Value2_7
private theorem sharedDiskP555Value3_0 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP555Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value3_1 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP555Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value3_2 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP555Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value3_3 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP555Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value3_4 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP555Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value3_5 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP555Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value3_6 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP555Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value3_7 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP555Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP555Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 3 j)=sharedDiskP555Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP555Value3_0
  · exact sharedDiskP555Value3_1
  · exact sharedDiskP555Value3_2
  · exact sharedDiskP555Value3_3
  · exact sharedDiskP555Value3_4
  · exact sharedDiskP555Value3_5
  · exact sharedDiskP555Value3_6
  · exact sharedDiskP555Value3_7
private theorem sharedDiskP555Value4_0 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP555Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value4_1 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP555Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value4_2 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP555Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value4_3 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP555Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value4_4 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP555Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value4_5 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP555Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value4_6 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP555Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value4_7 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP555Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP555Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 4 j)=sharedDiskP555Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP555Value4_0
  · exact sharedDiskP555Value4_1
  · exact sharedDiskP555Value4_2
  · exact sharedDiskP555Value4_3
  · exact sharedDiskP555Value4_4
  · exact sharedDiskP555Value4_5
  · exact sharedDiskP555Value4_6
  · exact sharedDiskP555Value4_7
private theorem sharedDiskP555Value5_0 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP555Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value5_1 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP555Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value5_2 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP555Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value5_3 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP555Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value5_4 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP555Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value5_5 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP555Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value5_6 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP555Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value5_7 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP555Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP555Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 5 j)=sharedDiskP555Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP555Value5_0
  · exact sharedDiskP555Value5_1
  · exact sharedDiskP555Value5_2
  · exact sharedDiskP555Value5_3
  · exact sharedDiskP555Value5_4
  · exact sharedDiskP555Value5_5
  · exact sharedDiskP555Value5_6
  · exact sharedDiskP555Value5_7
private theorem sharedDiskP555Value6_0 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP555Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value6_1 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP555Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value6_2 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP555Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value6_3 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP555Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value6_4 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP555Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value6_5 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP555Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value6_6 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP555Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value6_7 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP555Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP555Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 6 j)=sharedDiskP555Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP555Value6_0
  · exact sharedDiskP555Value6_1
  · exact sharedDiskP555Value6_2
  · exact sharedDiskP555Value6_3
  · exact sharedDiskP555Value6_4
  · exact sharedDiskP555Value6_5
  · exact sharedDiskP555Value6_6
  · exact sharedDiskP555Value6_7
private theorem sharedDiskP555Value7_0 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP555Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value7_1 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP555Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value7_2 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP555Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value7_3 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP555Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value7_4 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP555Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value7_5 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP555Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value7_6 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP555Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value7_7 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP555Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP555Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 7 j)=sharedDiskP555Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP555Value7_0
  · exact sharedDiskP555Value7_1
  · exact sharedDiskP555Value7_2
  · exact sharedDiskP555Value7_3
  · exact sharedDiskP555Value7_4
  · exact sharedDiskP555Value7_5
  · exact sharedDiskP555Value7_6
  · exact sharedDiskP555Value7_7
private theorem sharedDiskP555Value8_0 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP555Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value8_1 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP555Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value8_2 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP555Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value8_3 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP555Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value8_4 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP555Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value8_5 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP555Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value8_6 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP555Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP555Value8_7 : truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP555Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP555Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points 8 j)=sharedDiskP555Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP555Value8_0
  · exact sharedDiskP555Value8_1
  · exact sharedDiskP555Value8_2
  · exact sharedDiskP555Value8_3
  · exact sharedDiskP555Value8_4
  · exact sharedDiskP555Value8_5
  · exact sharedDiskP555Value8_6
  · exact sharedDiskP555Value8_7
theorem sharedDiskP555Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP555Params (sharedChord521Gauss8Points i j)=sharedDiskP555Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP555Values0_eq
  · exact sharedDiskP555Values1_eq
  · exact sharedDiskP555Values2_eq
  · exact sharedDiskP555Values3_eq
  · exact sharedDiskP555Values4_eq
  · exact sharedDiskP555Values5_eq
  · exact sharedDiskP555Values6_eq
  · exact sharedDiskP555Values7_eq
  · exact sharedDiskP555Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP555Box : HorizontalRectangle := ⟨(677/800),(339/400),(968223324287839/1649267441664000),(969833937023839/1649267441664000),(125284421821014801221555436810793/5192296858534827628530496329220096),(1920330750841223633649431824986665/5192296858534827628530496329220096),(-4161567891664315931673118491305509/1298074214633706907132624082305024),(-3698666997120618630176642015716901/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP555Grid : CGrid := momentChordGrid sharedDiskP555Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP555Columns : containedInReported sharedDiskP555Grid.re sharedDiskP555Box.reLo sharedDiskP555Box.reHi=true ∧ containedInReported sharedDiskP555Grid.im sharedDiskP555Box.imLo sharedDiskP555Box.imHi=true := by
  rw [sharedDiskP555Grid,momentChordGrid_eq_tabulated sharedDiskP555Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP555Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP555Values_eq]
  decide +kernel
theorem sharedDiskP555Sound : sharedDiskP555Box.Sound := by
  intro t a tl tu al au
  change (((677/800):ℚ):ℝ)≤t at tl
  change t≤(((339/400):ℚ):ℝ) at tu
  change (((968223324287839/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((969833937023839/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP555Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(677/800))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((339/400):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(968223324287839/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((969833937023839/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP555Columns.1 sharedDiskP555Columns.2
def sharedDiskP555Rows : List SignRow := [positive_555.toSignRow]
theorem sharedDiskP555Rows_actual : ∀ r∈sharedDiskP555Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP555Rows.all (sharedDiskP555Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP555Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP556Params : ChordParams := ⟨⟨(-29846060319024693745286),(-29683564398693381596470),true⟩,⟨1841682131914617615029017,1848774805221318215523505,true⟩,⟨136489019420159639743170,137424034049010269067825,true⟩,⟨261966547959398902031565,263508002599166865614198,true⟩,⟨369739765883409041735806,370799052319974381471966,true⟩,⟨1150671877112516436313066,1150981437983191381688866,true⟩,⟨(-2133283085537587169282377),(-2129568374567928708966070),true⟩,⟨⟨1139408812325126745840631,1153927874646105084596017,true⟩,⟨(-107541439),107541439,true⟩⟩⟩
theorem sharedDiskP556Params_ok : chordParams (Grid.ofRats (339/400) (679/800)) (Grid.ofRats (968865912960833/1649267441664000) (970476525696833/1649267441664000))=sharedDiskP556Params := by decide +kernel
def sharedDiskP556Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3024017712492455562673531),(-2730077206763856723009404),true⟩,⟨(-215285675847555558740274),25684976287948319199610,true⟩⟩
  | 0,1 => ⟨⟨(-2705356790118835987093049),(-2433347563600359003385645),true⟩,⟨(-266370172682846213863766),(-37186715977321011678470),true⟩⟩
  | 0,2 => ⟨⟨(-2473602297641781916132191),(-2219194804224945946383703),true⟩,⟨(-312105744879881307846236),(-94049893599292300060050),true⟩⟩
  | 0,3 => ⟨⟨(-2342564508459308463720866),(-2098476708403225158197686),true⟩,⟨(-341032849212277108855532),(-129785907137679535432547),true⟩⟩
  | 0,4 => ⟨⟨(-3398542408096066684911934),(-3082498072272957824043113),true⟩,⟨(-173608214478150520331434),75628452148524293231134,true⟩⟩
  | 0,5 => ⟨⟨(-3777064172675636268887716),(-3442927074482148393933492),true⟩,⟨(-152400209439191025388199),99138862740863055983194,true⟩⟩
  | 0,6 => ⟨⟨(-4095258695744559444864859),(-3749208035810496906673538),true⟩,⟨(-151270355859017332734482),97718315766062049911163,true⟩⟩
  | 0,7 => ⟨⟨(-4294172770513956127202266),(-3942095884355814715962127),true⟩,⟨(-160153818304200899113252),86249095997370140994231,true⟩⟩
  | 1,0 => ⟨⟨(-1543062984243945798995503),(-1367457348308490748710284),true⟩,⟨(-556145125246965640379847),(-396181200294987669863114),true⟩⟩
  | 1,1 => ⟨⟨(-1366345874202279952817125),(-1206362679066004811479642),true⟩,⟨(-609258007826037360329980),(-461966965210263213981101),true⟩⟩
  | 1,2 => ⟨⟨(-1237662957137365801750617),(-1088922635038080938062466),true⟩,⟨(-648013531698044276660405),(-509973214743577950809457),true⟩⟩
  | 1,3 => ⟨⟨(-1164360101167318599954956),(-1021936705489988967847650),true⟩,⟨(-669903494743253791240102),(-537099597524622035547094),true⟩⟩
  | 1,4 => ⟨⟨(-1752941376995813594782338),(-1558767061240219688567520),true⟩,⟨(-494594700562473706487360),(-319923348898077556691237),true⟩⟩
  | 1,5 => ⟨⟨(-1970386730699643787988639),(-1757265815632246020554001),true⟩,⟨(-434017178146503977173305),(-244861467451496151454812),true⟩⟩
  | 1,6 => ⟨⟨(-2159424151455479945681698),(-1930291214046572279591386),true⟩,⟨(-384903032480624343463389),(-184037549752112853227344),true⟩⟩
  | 1,7 => ⟨⟨(-2281239655506010012006205),(-2042090950923053834541848),true⟩,⟨(-355289954871937547766585),(-147404752585652202416236),true⟩⟩
  | 2,0 => ⟨⟨(-345930072645823975185659),(-261086316123920514651476),true⟩,⟨(-873191487643127567058221),(-787733802245473907815263),true⟩⟩
  | 2,1 => ⟨⟨(-170266847065294203983883),(-92801391811603197852771),true⟩,⟨(-899406079661726164168453),(-819772447449138858429237),true⟩⟩
  | 2,2 => ⟨⟨(-41541822707434302737772),31456769218488726989919,true⟩,⟨(-913548645354512078138589),(-837554968697478523595318),true⟩⟩
  | 2,3 => ⟨⟨32368334578036903887285,103274157412391006262497,true⟩,⟨(-919847706646723947465270),(-845712100150200649635926),true⟩⟩
  | 2,4 => ⟨⟨(-555475521318281913904138),(-459949387496246363101048),true⟩,⟨(-831652692405117752542823),(-737940484066097818462717),true⟩⟩
  | 2,5 => ⟨⟨(-778399996435615645599253),(-667492416324179022788472),true⟩,⟨(-778180497082241414236052),(-671797300355036176354044),true⟩⟩
  | 2,6 => ⟨⟨(-979059423378646993580232),(-852195490006994989470688),true⟩,⟨(-723816380798058026922875),(-604004945646562684544429),true⟩⟩
  | 2,7 => ⟨⟨(-1112892393952336810727858),(-974855267008135125953187),true⟩,⟨(-685122152060511696626258),(-555968353161562465139646),true⟩⟩
  | 3,0 => ⟨⟨926678818218566947110055,996073419754332757709220,true⟩,⟨(-960345365746447114134741),(-890903243466904681845695),true⟩⟩
  | 3,1 => ⟨⟨1146651090033019057293186,1219562456253445334233464,true⟩,⟨(-992983037763705571929255),(-921037546762754170255761),true⟩⟩
  | 3,2 => ⟨⟨1316891291955477555750397,1393429979550958955285068,true⟩,⟨(-1037281174337984307336238),(-962388977964615545208468),true⟩⟩
  | 3,3 => ⟨⟨1418648547392493424945812,1497788339733752463396197,true⟩,⟨(-1074316772783646667391896),(-997176392039034756470675),true⟩⟩
  | 3,4 => ⟨⟨679840100453047689047138,746683540217585781833852,true⟩,⟨(-944353929919691391472472),(-876211193896363363597691),true⟩⟩
  | 3,5 => ⟨⟨433715408889465996184962,499425841576113651867179,true⟩,⟨(-937454364378090676265189),(-869165118233932673618124),true⟩⟩
  | 3,6 => ⟨⟨222138180888599268349775,288874238897660004640794,true⟩,⟨(-930783900231097607675495),(-860672770234718158432231),true⟩⟩
  | 3,7 => ⟨⟨84582062653057713430534,154196779076421153814324,true⟩,⟨(-923561183576801152462288),(-850639227445357576057282),true⟩⟩
  | 4,0 => ⟨⟨2147277242838134830733273,2272748003230459653994480,true⟩,⟨(-1799784516497181440212002),(-1675404809939346213025135),true⟩⟩
  | 4,1 => ⟨⟨2298363759010243715658035,2447774227629518594484102,true⟩,⟨(-2254166162446513166888318),(-2103522046196967966612744),true⟩⟩
  | 4,2 => ⟨⟨2349330858154138270305126,2523432913013558622345102,true⟩,⟨(-2750124366182516039192060),(-2571423641878460982527747),true⟩⟩
  | 4,3 => ⟨⟨2324946789865930804109481,2516920978944169165419460,true⟩,⟨(-3120325092588595733852367),(-2920756409151721983409683),true⟩⟩
  | 4,4 => ⟨⟨1940720554819641662860531,2047191572547928079034370,true⟩,⟨(-1468609156976363901566225),(-1364301888413759306696512),true⟩⟩
  | 4,5 => ⟨⟨1734494810384198841837140,1827713236852533275222827,true⟩,⟨(-1261766609286519192105049),(-1170953795966366948604558),true⟩⟩
  | 4,6 => ⟨⟨1568434358741961849528588,1653407515365587190689607,true⟩,⟨(-1147913150848528423853414),(-1065226023170557650657984),true⟩⟩
  | 4,7 => ⟨⟨1467754143445461173454822,1548521105277238592780742,true⟩,⟨(-1095728550745527466668019),(-1017086564028938615539826),true⟩⟩
  | 5,0 => ⟨⟨2038667370759819612899938,2274965788514752834366396,true⟩,⟨(-4059849700049028952968385),(-3806577983958220618103492),true⟩⟩
  | 5,1 => ⟨⟨1889709528185394931038869,2138832578484839821082998,true⟩,⟨(-4333606676126894989390929),(-4064271050939061653607883),true⟩⟩
  | 5,2 => ⟨⟨1742138628970645603694450,2001751462654042208697673,true⟩,⟨(-4556969894159603516368811),(-4274310012499290074859065),true⟩⟩
  | 5,3 => ⟨⟨1639006360379436651412397,1905050515399832521557226,true⟩,⟨(-4693384522314222440678818),(-4402469693176248412576450),true⟩⟩
  | 5,4 => ⟨⟨2158602596617983456921915,2381780224756570284459222,true⟩,⟨(-3779940277749877577983029),(-3542855367296294818240330),true⟩⟩
  | 5,5 => ⟨⟨2239147785589612772456099,2450754568938564327088199,true⟩,⟨(-3533974160487292157892893),(-3310960723968605151901468),true⟩⟩
  | 5,6 => ⟨⟨2284865526133457554751251,2487780657330368102078380,true⟩,⟨(-3350142801079371795315151),(-3137575520179020389736324),true⟩⟩
  | 5,7 => ⟨⟨2305713588969165807460731,2503591171443947830369536,true⟩,⟨(-3244079594343294964384112),(-3037518193874558343359651),true⟩⟩
  | 6,0 => ⟨⟨453185097408418536622825,779920773237949724105196,true⟩,⟨(-5661031465066757517846106),(-5299161778412536428024645),true⟩⟩
  | 6,1 => ⟨⟨(-27714238202218044809103),321803609037272218746974,true⟩,⟨(-5868426299250171350831541),(-5484138364968565791949321),true⟩⟩
  | 6,2 => ⟨⟨(-456689011658520899662192),(-88056860941627957608337),true⟩,⟨(-5991667014318203631313585),(-5590485870561226276939210),true⟩⟩
  | 6,3 => ⟨⟨(-734575060143994034350946),(-354080806933403948052328),true⟩,⟨(-6043662307381050368458805),(-5632929627476489943294387),true⟩⟩
  | 6,4 => ⟨⟨894051720795446765718817,1197263154562997773465668,true⟩,⟨(-5394031411135513089906916),(-5056576364897947344965739),true⟩⟩
  | 6,5 => ⟨⟨1237204800164313693082757,1523625104803789268287005,true⟩,⟨(-5120592461289271160926160),(-4803059500060327519573945),true⟩⟩
  | 6,6 => ⟨⟨1464473898337677628757371,1740149538121337934897200,true⟩,⟨(-4896488561762669907101168),(-4593083104286085112882873),true⟩⟩
  | 6,7 => ⟨⟨1584863680875772621356281,1854048134569219539554976,true⟩,⟨(-4759785461300882658322254),(-4464815342355824928802003),true⟩⟩
  | 7,0 => ⟨⟨(-3083787537656498355026482),(-2628057289014147321128656),true⟩,⟨(-5648669083156910901943074),(-5199798798864874851732246),true⟩⟩
  | 7,1 => ⟨⟨(-3721216281726609493971264),(-3254497512500452363290590),true⟩,⟨(-5227713658596710715576788),(-4785177100966110108628945),true⟩⟩
  | 7,2 => ⟨⟨(-4172456520440110128821908),(-3702341790396365817796000),true⟩,⟨(-4792253789041325372758638),(-4361853776456834861492689),true⟩⟩
  | 7,3 => ⟨⟨(-4411920862074647882307794),(-3942400819194551408739706),true⟩,⟨(-4489256191721536978116144),(-4069380151902259345779735),true⟩⟩
  | 7,4 => ⟨⟨(-2359704384492009803249323),(-1922194252010719352960469),true⟩,⟨(-5938286846190996618615929),(-5492432997090233282604789),true⟩⟩
  | 7,5 => ⟨⟨(-1685324493824209115959442),(-1268952767250268749108958),true⟩,⟨(-6067043090787221215388146),(-5631412762534727891948565),true⟩⟩
  | 7,6 => ⟨⟨(-1171001450162637003215708),(-773159080765685191553108),true⟩,⟨(-6083663468300713452874745),(-5660021001995572928324979),true⟩⟩
  | 7,7 => ⟨⟨(-874241338310623879283757),(-488028992273396276391857),true⟩,⟨(-6061922284434214404680816),(-5646783580170850510224493),true⟩⟩
  | 8,0 => ⟨⟨(-5050982027365234195461556),(-4657595006392324660958004),true⟩,⟨(-1689739520702072391562811),(-1414990999206100513969951),true⟩⟩
  | 8,1 => ⟨⟨(-4832371139008530678822171),(-4480303059732881383907043),true⟩,⟨(-929340504349345179791707),(-706569013472748502962934),true⟩⟩
  | 8,2 => ⟨⟨(-4558988597820204632759063),(-4243161100417048760269881),true⟩,⟨(-395800711858335676033979),(-213191977008419229600436),true⟩⟩
  | 8,3 => ⟨⟨(-4360316708306701220256120),(-4067461009034911352650531),true⟩,⟨(-111102240071894222414725),49819339549638194619435,true⟩⟩
  | 8,4 => ⟨⟨(-5097120616190696568918648),(-4667726416482722362543901),true⟩,⟨(-2565113907848729262418742),(-2237072619730474630061679),true⟩⟩
  | 8,5 => ⟨⟨(-4951276226765461561117104),(-4498179376287145373602618),true⟩,⟨(-3380782724353989215181248),(-3009309398559006355873755),true⟩⟩
  | 8,6 => ⟨⟨(-4710904323802917026192896),(-4246302421974336746143333),true⟩,⟨(-3990712751621116143639098),(-3590906701620129381341002),true⟩⟩
  | 8,7 => ⟨⟨(-4517563505003486272969317),(-4049105963479397980282365),true⟩,⟨(-4332292515472807101588746),(-3918397009127364170102476),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP556Value0_0 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP556Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value0_1 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP556Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value0_2 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP556Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value0_3 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP556Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value0_4 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP556Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value0_5 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP556Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value0_6 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP556Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value0_7 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP556Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP556Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 0 j)=sharedDiskP556Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP556Value0_0
  · exact sharedDiskP556Value0_1
  · exact sharedDiskP556Value0_2
  · exact sharedDiskP556Value0_3
  · exact sharedDiskP556Value0_4
  · exact sharedDiskP556Value0_5
  · exact sharedDiskP556Value0_6
  · exact sharedDiskP556Value0_7
private theorem sharedDiskP556Value1_0 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP556Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value1_1 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP556Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value1_2 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP556Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value1_3 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP556Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value1_4 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP556Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value1_5 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP556Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value1_6 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP556Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value1_7 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP556Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP556Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 1 j)=sharedDiskP556Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP556Value1_0
  · exact sharedDiskP556Value1_1
  · exact sharedDiskP556Value1_2
  · exact sharedDiskP556Value1_3
  · exact sharedDiskP556Value1_4
  · exact sharedDiskP556Value1_5
  · exact sharedDiskP556Value1_6
  · exact sharedDiskP556Value1_7
private theorem sharedDiskP556Value2_0 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP556Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value2_1 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP556Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value2_2 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP556Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value2_3 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP556Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value2_4 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP556Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value2_5 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP556Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value2_6 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP556Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value2_7 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP556Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP556Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 2 j)=sharedDiskP556Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP556Value2_0
  · exact sharedDiskP556Value2_1
  · exact sharedDiskP556Value2_2
  · exact sharedDiskP556Value2_3
  · exact sharedDiskP556Value2_4
  · exact sharedDiskP556Value2_5
  · exact sharedDiskP556Value2_6
  · exact sharedDiskP556Value2_7
private theorem sharedDiskP556Value3_0 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP556Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value3_1 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP556Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value3_2 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP556Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value3_3 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP556Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value3_4 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP556Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value3_5 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP556Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value3_6 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP556Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value3_7 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP556Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP556Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 3 j)=sharedDiskP556Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP556Value3_0
  · exact sharedDiskP556Value3_1
  · exact sharedDiskP556Value3_2
  · exact sharedDiskP556Value3_3
  · exact sharedDiskP556Value3_4
  · exact sharedDiskP556Value3_5
  · exact sharedDiskP556Value3_6
  · exact sharedDiskP556Value3_7
private theorem sharedDiskP556Value4_0 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP556Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value4_1 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP556Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value4_2 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP556Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value4_3 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP556Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value4_4 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP556Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value4_5 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP556Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value4_6 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP556Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value4_7 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP556Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP556Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 4 j)=sharedDiskP556Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP556Value4_0
  · exact sharedDiskP556Value4_1
  · exact sharedDiskP556Value4_2
  · exact sharedDiskP556Value4_3
  · exact sharedDiskP556Value4_4
  · exact sharedDiskP556Value4_5
  · exact sharedDiskP556Value4_6
  · exact sharedDiskP556Value4_7
private theorem sharedDiskP556Value5_0 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP556Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value5_1 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP556Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value5_2 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP556Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value5_3 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP556Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value5_4 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP556Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value5_5 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP556Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value5_6 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP556Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value5_7 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP556Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP556Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 5 j)=sharedDiskP556Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP556Value5_0
  · exact sharedDiskP556Value5_1
  · exact sharedDiskP556Value5_2
  · exact sharedDiskP556Value5_3
  · exact sharedDiskP556Value5_4
  · exact sharedDiskP556Value5_5
  · exact sharedDiskP556Value5_6
  · exact sharedDiskP556Value5_7
private theorem sharedDiskP556Value6_0 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP556Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value6_1 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP556Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value6_2 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP556Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value6_3 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP556Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value6_4 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP556Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value6_5 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP556Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value6_6 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP556Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value6_7 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP556Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP556Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 6 j)=sharedDiskP556Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP556Value6_0
  · exact sharedDiskP556Value6_1
  · exact sharedDiskP556Value6_2
  · exact sharedDiskP556Value6_3
  · exact sharedDiskP556Value6_4
  · exact sharedDiskP556Value6_5
  · exact sharedDiskP556Value6_6
  · exact sharedDiskP556Value6_7
private theorem sharedDiskP556Value7_0 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP556Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value7_1 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP556Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value7_2 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP556Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value7_3 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP556Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value7_4 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP556Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value7_5 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP556Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value7_6 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP556Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value7_7 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP556Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP556Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 7 j)=sharedDiskP556Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP556Value7_0
  · exact sharedDiskP556Value7_1
  · exact sharedDiskP556Value7_2
  · exact sharedDiskP556Value7_3
  · exact sharedDiskP556Value7_4
  · exact sharedDiskP556Value7_5
  · exact sharedDiskP556Value7_6
  · exact sharedDiskP556Value7_7
private theorem sharedDiskP556Value8_0 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP556Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value8_1 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP556Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value8_2 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP556Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value8_3 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP556Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value8_4 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP556Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value8_5 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP556Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value8_6 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP556Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP556Value8_7 : truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP556Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP556Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points 8 j)=sharedDiskP556Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP556Value8_0
  · exact sharedDiskP556Value8_1
  · exact sharedDiskP556Value8_2
  · exact sharedDiskP556Value8_3
  · exact sharedDiskP556Value8_4
  · exact sharedDiskP556Value8_5
  · exact sharedDiskP556Value8_6
  · exact sharedDiskP556Value8_7
theorem sharedDiskP556Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP556Params (sharedChord521Gauss8Points i j)=sharedDiskP556Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP556Values0_eq
  · exact sharedDiskP556Values1_eq
  · exact sharedDiskP556Values2_eq
  · exact sharedDiskP556Values3_eq
  · exact sharedDiskP556Values4_eq
  · exact sharedDiskP556Values5_eq
  · exact sharedDiskP556Values6_eq
  · exact sharedDiskP556Values7_eq
  · exact sharedDiskP556Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP556Box : HorizontalRectangle := ⟨(339/400),(679/800),(968865912960833/1649267441664000),(970476525696833/1649267441664000),(15958955226897225882900617772185/1298074214633706907132624082305024),(461843585382389143679700120124569/1298074214633706907132624082305024),(-4158498361688106126698296875185789/1298074214633706907132624082305024),(-3698454769968160009136698907457149/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP556Grid : CGrid := momentChordGrid sharedDiskP556Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP556Columns : containedInReported sharedDiskP556Grid.re sharedDiskP556Box.reLo sharedDiskP556Box.reHi=true ∧ containedInReported sharedDiskP556Grid.im sharedDiskP556Box.imLo sharedDiskP556Box.imHi=true := by
  rw [sharedDiskP556Grid,momentChordGrid_eq_tabulated sharedDiskP556Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP556Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP556Values_eq]
  decide +kernel
theorem sharedDiskP556Sound : sharedDiskP556Box.Sound := by
  intro t a tl tu al au
  change (((339/400):ℚ):ℝ)≤t at tl
  change t≤(((679/800):ℚ):ℝ) at tu
  change (((968865912960833/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((970476525696833/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP556Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(339/400))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((679/800):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(968865912960833/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((970476525696833/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP556Columns.1 sharedDiskP556Columns.2
def sharedDiskP556Rows : List SignRow := [positive_556.toSignRow]
theorem sharedDiskP556Rows_actual : ∀ r∈sharedDiskP556Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP556Rows.all (sharedDiskP556Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP556Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP557Params : ChordParams := ⟨⟨(-30008963931755923068592),(-29846060319024693744675),true⟩,⟨1837228791705133868146624,1844304460573666303181054,true⟩,⟨136730393968587847770282,137665322268158890151782,true⟩,⟨262937036477965359748739,264480481492953711785504,true⟩,⟨370701663950475564196608,371760837442750305964061,true⟩,⟨1150361621080888320861762,1150671877112516436314232,true⟩,⟨(-2129568374567928708975014),(-2125863304564331866723650),true⟩,⟨⟨1139046331521745989987630,1153572043042957287189993,true⟩,⟨(-113998002),113998002,true⟩⟩⟩
theorem sharedDiskP557Params_ok : chordParams (Grid.ofRats (679/800) (17/20)) (Grid.ofRats (969510010986397/1649267441664000) (971120623722397/1649267441664000))=sharedDiskP557Params := by decide +kernel
def sharedDiskP557Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3022885054157831136512172),(-2728438328762798236096749),true⟩,⟨(-214588881654101764525853),26878396853918599572051,true⟩⟩
  | 0,1 => ⟨⟨(-2705465605855849335124205),(-2432900946157378898221950),true⟩,⟨(-265196260856300541337423),(-35487789934898975929951),true⟩⟩
  | 0,2 => ⟨⟨(-2474522004954293559208473),(-2219529058715338860108488),true⟩,⟨(-310577005764673072332691),(-91973087412023666290854),true⟩⟩
  | 0,3 => ⟨⟨(-2343892447906125074546568),(-2099221143525217239341553),true⟩,⟨(-339306791865964084444026),(-127529836997407376116042),true⟩⟩
  | 0,4 => ⟨⟨(-3395773415402474834945694),(-3079287084171638823993870),true⟩,⟨(-173414915218261401575578),76292335104551133010195,true⟩⟩
  | 0,5 => ⟨⟨(-3772465320147990908598303),(-3437952446017326636816792),true⟩,⟨(-152609869777864744464211),99399507062429226158722,true⟩⟩
  | 0,6 => ⟨⟨(-4089003510667894242429465),(-3742629661153391561215527),true⟩,⟨(-151709432689827785448959),97759569904021248070496,true⟩⟩
  | 0,7 => ⟨⟨(-4286832811139804280048766),(-3934465418929363773792964),true⟩,⟨(-160689004822896856677176),86223954562140631575156,true⟩⟩
  | 1,0 => ⟨⟨(-1546450197461962586431377),(-1370251532705115053412520),true⟩,⟨(-553486599075119713323247),(-392987712854985621337838),true⟩⟩
  | 1,1 => ⟨⟨(-1370086304157779219363472),(-1209525564722227254632046),true⟩,⟨(-606511452544956072280483),(-458700903098203934730960),true⟩⟩
  | 1,2 => ⟨⟨(-1241644437182514112266421),(-1092341747229641253677695),true⟩,⟨(-645243106573579231954250),(-506698558435985304306131),true⟩⟩
  | 1,3 => ⟨⟨(-1168474062684985079724252),(-1025498273682515403496289),true⟩,⟨(-667136262274298911862449),(-533838210207151806132970),true⟩⟩
  | 1,4 => ⟨⟨(-1755867548024110790908036),(-1561090369198367013514457),true⟩,⟨(-492110855641760707884083),(-316894806871875660074777),true⟩⟩
  | 1,5 => ⟨⟨(-1972778974084483265995171),(-1759054730691031116135839),true⟩,⟨(-431777120903246354724101),(-242075877907998780202294),true⟩⟩
  | 1,6 => ⟨⟨(-2161300499739771321485308),(-1931571310352554797675554),true⟩,⟨(-382912686034846380900322),(-181507372967476827320229),true⟩⟩
  | 1,7 => ⟨⟨(-2282756657762788297827712),(-2043019583904942633693186),true⟩,⟨(-353473552891966620246257),(-145054669487168460369474),true⟩⟩
  | 2,0 => ⟨⟨(-351411699246542946208003),(-266245703015224012195034),true⟩,⟨(-871367069467824039962350),(-785649117960151606398426),true⟩⟩
  | 2,1 => ⟨⟨(-176059792918958029307443),(-98307640710585258692900),true⟩,⟨(-898013208104884529077066),(-818145732309454330877090),true⟩⟩
  | 2,2 => ⟨⟨(-47564809428353796126520),25687965839095054958326,true⟩,⟨(-912507853768550005867012),(-836296102309165055430591),true⟩⟩
  | 2,3 => ⟨⟨26224459730668714870640,97361932177830651332810,true⟩,⟨(-919019989830519141581825),(-844673953742690864406679),true⟩⟩
  | 2,4 => ⟨⟨(-560594918946669698275039),(-464698098563369845698170),true⟩,⟨(-829405893214027553998392),(-735395505157556434700955),true⟩⟩
  | 2,5 => ⟨⟨(-783178922897341607252224),(-671782895385793267738823),true⟩,⟨(-775655072370901309264897),(-668842231608655361702566),true⟩⟩
  | 2,6 => ⟨⟨(-983497136043900061848175),(-856109611101373735722641),true⟩,⟨(-721116254879894723226328),(-600839796585305930317459),true⟩⟩
  | 2,7 => ⟨⟨(-1117097668724130040262065),(-978515670906363379555484),true⟩,⟨(-682364875177280508246112),(-552724529818567025444047),true⟩⟩
  | 3,0 => ⟨⟨919277912353939682539892,988751673647015039199919,true⟩,⟨(-962270786588914759213142),(-892707037642414474837379),true⟩⟩
  | 3,1 => ⟨⟨1139047921847664836874824,1212045198067003695496812,true⟩,⟨(-995586586335901274212240),(-923507891912572379775663),true⟩⟩
  | 3,2 => ⟨⟨1309143229287210861862372,1385778195295023844771640,true⟩,⟨(-1040414300006732127143566),(-965375477703789439595703),true⟩⟩
  | 3,3 => ⟨⟨1410808023812960519524807,1490052358842633633830003,true⟩,⟨(-1077773159196370007875762),(-1000476251624762432659847),true⟩⟩
  | 3,4 => ⟨⟨672719960255641150393732,739644431728142958785948,true⟩,⟨(-945510192151033545646529),(-877250918551515897835355),true⟩⟩
  | 3,5 => ⟨⟨426943501959349934702808,492747566523983917917969,true⟩,⟨(-937831915772364462914785),(-869422278902676323513079),true⟩⟩
  | 3,6 => ⟨⟨215664328795391619548378,282605832965785301395808,true⟩,⟨(-930529346910542689293421),(-860222815367142444728415),true⟩⟩
  | 3,7 => ⟨⟨78346042060596823481873,148184494149878529626403,true⟩,⟨(-922887977950926522649391),(-849760380735848730625064),true⟩⟩
  | 4,0 => ⟨⟨2137528764976095180946663,2263185406287796781785190,true⟩,⟨(-1805985251638865316878862),(-1681335244368765095880737),true⟩⟩
  | 4,1 => ⟨⟨2287003507045440306600252,2436628773376549381083938,true⟩,⟨(-2261087383937013267704805),(-2110129292092185865580597),true⟩⟩
  | 4,2 => ⟨⟨2335976380144895933906187,2510307479889702982081580,true⟩,⟨(-2757279374240009051827386),(-2578237433481541543852174),true⟩⟩
  | 4,3 => ⟨⟨2310003694320548482283696,2502205553700876476107973,true⟩,⟨(-3127285544511218604681203),(-2927369908513767137745089),true⟩⟩
  | 4,4 => ⟨⟨1931957449018462510333360,2038583334339744611982012,true⟩,⟨(-1473924795285357421614761),(-1369390794594071750292235),true⟩⟩
  | 4,5 => ⟨⟨1726243657431619782780983,1819592848661137392276374,true⟩,⟨(-1266295599515519117176757),(-1175289356581044571876256),true⟩⟩
  | 4,6 => ⟨⟨1560432804991409531978099,1645521676563279505871578,true⟩,⟨(-1151862554352210164948981),(-1069003176211287349147496),true⟩⟩
  | 4,7 => ⟨⟨1459865065910112462080237,1540740390033544259918329,true⟩,⟨(-1099343962424526833765384),(-1020540453620042811517532),true⟩⟩
  | 5,0 => ⟨⟨2019586967630019646094964,2256058652396082965705895,true⟩,⟨(-4064773993508575346387659),(-3811205921871326243349061),true⟩⟩
  | 5,1 => ⟨⟨1869468237101175972915583,2118732818220299028028805,true⟩,⟨(-4337459655788371810500256),(-4067863664577295134735440),true⟩⟩
  | 5,2 => ⟨⟨1720993940750275406060127,1980716016316008727661231,true⟩,⟨(-4559757393076303193753589),(-4276875388043903325741300),true⟩⟩
  | 5,3 => ⟨⟨1617337309584877245822661,1883467819110398536886955,true⟩,⟨(-4695426774048575724451138),(-4404317647600932155571156),true⟩⟩
  | 5,4 => ⟨⟨2140745870328365328565688,2364121261407135882848836,true⟩,⟨(-3785721168078458569220624),(-3548313919742867806599892),true⟩⟩
  | 5,5 => ⟨⟨2222380001516923364255418,2434200043720377966600276,true⟩,⟨(-3540326184190939633147232),(-3316975600358276916924933),true⟩⟩
  | 5,6 => ⟨⟨2268912019170395141446292,2472048555753287827762525,true⟩,⟨(-3356817958004455019360540),(-3143906941869772039788856),true⟩⟩
  | 5,7 => ⟨⟨2290227913288647023173886,2488330322566946255910006,true⟩,⟨(-3250902488259271002472812),(-3043995194589742789085205),true⟩⟩
  | 6,0 => ⟨⟨428915948146184971453150,755957123612320665032300,true⟩,⟨(-5654907351029918444273433),(-5292902621075964347477717),true⟩⟩
  | 6,1 => ⟨⟨(-51718109243126479654497),298047635432399039866050,true⟩,⟨(-5859152626774748628757524),(-5474877734239637624171967),true⟩⟩
  | 6,2 => ⟨⟨(-479957473387544285817768),(-111136337761819825404566),true⟩,⟨(-5979731809441621732876482),(-5578700770801717452022635),true⟩⟩
  | 6,3 => ⟨⟨(-757156443678027573535974),(-376542910367299496614090),true⟩,⟨(-6030087429623222194905324),(-5619595245630744931176703),true⟩⟩
  | 6,4 => ⟨⟨870057822859537437867503,1173654780746288405355945,true⟩,⟨(-5390915006459231577983782),(-5053197457824330858624801),true⟩⟩
  | 6,5 => ⟨⟨1214099097749695029723583,1500515333930590922457434,true⟩,⟨(-5119743648043449989418205),(-4802130536128646987330132),true⟩⟩
  | 6,6 => ⟨⟨1442075754116145502036487,1717798635377206166776092,true⟩,⟨(-4897271344912264114787514),(-4593720230004635620178854),true⟩⟩
  | 6,7 => ⟨⟨1562948744465572420109049,1832207461407974714683873,true⟩,⟨(-4761436646309566726675343),(-4466287130640279658962333),true⟩⟩
  | 7,0 => ⟨⟨(-3094703004650666650155097),(-2639544913994749484995685),true⟩,⟨(-5625162171533542201262738),(-5177268944715631132719371),true⟩⟩
  | 7,1 => ⟨⟨(-3727178752267167606041352),(-3261238043133272689670718),true⟩,⟨(-5203436143209293519792434),(-4762031455289282069507568),true⟩⟩
  | 7,2 => ⟨⟨(-4174359286939857232555605),(-3705166218070939196876946),true⟩,⟨(-4768364427102775608700503),(-4339173399422740227457550),true⟩⟩
  | 7,3 => ⟨⟨(-4411433414022827446210880),(-3942907780916202360802295),true⟩,⟨(-4466056713687391042580257),(-4047411712527501089299532),true⟩⟩
  | 7,4 => ⟨⟨(-2375293561447610443772681),(-1938127146287458187795671),true⟩,⟨(-5916897342187475070772473),(-5471809313093677358869075),true⟩⟩
  | 7,5 => ⟨⟨(-1704408308886768127941609),(-1288178124114257130262465),true⟩,⟨(-6048472648140383091576124),(-5613394062666284701534384),true⟩⟩
  | 7,6 => ⟨⟨(-1192191141033689917561301),(-794345231462345459465725),true⟩,⟨(-6067667382126672977481170),(-5644408523720527007082497),true⟩⟩
  | 7,7 => ⟨⟨(-896418055409361023446075),(-510122670679246594818682),true⟩,⟨(-6047551086775774469336638),(-5632698590648545395331780),true⟩⟩
  | 8,0 => ⟨⟨(-5039973572356606509535765),(-4647575983232583685218070),true⟩,⟨(-1680057064984096332922258),(-1406066000291991801393607),true⟩⟩
  | 8,1 => ⟨⟨(-4821791846257694704190564),(-4470525348918501030658373),true⟩,⟨(-924157836512564395712725),(-701874899877100501657090),true⟩⟩
  | 8,2 => ⟨⟨(-4549660877329044250680252),(-4234457686576474795086350),true⟩,⟨(-393672439600914427110773),(-211353269198884756023638),true⟩⟩
  | 8,3 => ⟨⟨(-4352034846512182334654618),(-4059687554017224357278509),true⟩,⟨(-110504794579766544386733),50256511204879297982348,true⟩⟩
  | 8,4 => ⟨⟨(-5087380195385659793922859),(-4659091835383454443171011),true⟩,⟨(-2550401623592002011063591),(-2223364527663189740628822),true⟩⟩
  | 8,5 => ⟨⟨(-4944332942668524448542526),(-4492359703516653460136188),true⟩,⟨(-3361858461124456382084444),(-2991548199211708833136778),true⟩⟩
  | 8,6 => ⟨⟨(-4707105051771650056041408),(-4243579699054763844168587),true⟩,⟨(-3969159674143931910742738),(-3570579158886630026495925),true⟩⟩
  | 8,7 => ⟨⟨(-4515955081824504295984076),(-4048522493856118822604370),true⟩,⟨(-4309551059889738519203840),(-3896889965732057981015180),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP557Value0_0 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP557Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value0_1 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP557Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value0_2 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP557Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value0_3 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP557Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value0_4 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP557Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value0_5 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP557Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value0_6 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP557Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value0_7 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP557Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP557Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 0 j)=sharedDiskP557Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP557Value0_0
  · exact sharedDiskP557Value0_1
  · exact sharedDiskP557Value0_2
  · exact sharedDiskP557Value0_3
  · exact sharedDiskP557Value0_4
  · exact sharedDiskP557Value0_5
  · exact sharedDiskP557Value0_6
  · exact sharedDiskP557Value0_7
private theorem sharedDiskP557Value1_0 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP557Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value1_1 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP557Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value1_2 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP557Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value1_3 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP557Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value1_4 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP557Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value1_5 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP557Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value1_6 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP557Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value1_7 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP557Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP557Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 1 j)=sharedDiskP557Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP557Value1_0
  · exact sharedDiskP557Value1_1
  · exact sharedDiskP557Value1_2
  · exact sharedDiskP557Value1_3
  · exact sharedDiskP557Value1_4
  · exact sharedDiskP557Value1_5
  · exact sharedDiskP557Value1_6
  · exact sharedDiskP557Value1_7
private theorem sharedDiskP557Value2_0 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP557Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value2_1 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP557Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value2_2 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP557Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value2_3 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP557Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value2_4 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP557Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value2_5 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP557Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value2_6 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP557Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value2_7 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP557Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP557Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 2 j)=sharedDiskP557Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP557Value2_0
  · exact sharedDiskP557Value2_1
  · exact sharedDiskP557Value2_2
  · exact sharedDiskP557Value2_3
  · exact sharedDiskP557Value2_4
  · exact sharedDiskP557Value2_5
  · exact sharedDiskP557Value2_6
  · exact sharedDiskP557Value2_7
private theorem sharedDiskP557Value3_0 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP557Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value3_1 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP557Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value3_2 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP557Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value3_3 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP557Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value3_4 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP557Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value3_5 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP557Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value3_6 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP557Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value3_7 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP557Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP557Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 3 j)=sharedDiskP557Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP557Value3_0
  · exact sharedDiskP557Value3_1
  · exact sharedDiskP557Value3_2
  · exact sharedDiskP557Value3_3
  · exact sharedDiskP557Value3_4
  · exact sharedDiskP557Value3_5
  · exact sharedDiskP557Value3_6
  · exact sharedDiskP557Value3_7
private theorem sharedDiskP557Value4_0 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP557Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value4_1 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP557Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value4_2 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP557Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value4_3 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP557Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value4_4 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP557Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value4_5 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP557Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value4_6 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP557Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value4_7 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP557Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP557Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 4 j)=sharedDiskP557Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP557Value4_0
  · exact sharedDiskP557Value4_1
  · exact sharedDiskP557Value4_2
  · exact sharedDiskP557Value4_3
  · exact sharedDiskP557Value4_4
  · exact sharedDiskP557Value4_5
  · exact sharedDiskP557Value4_6
  · exact sharedDiskP557Value4_7
private theorem sharedDiskP557Value5_0 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP557Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value5_1 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP557Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value5_2 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP557Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value5_3 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP557Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value5_4 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP557Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value5_5 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP557Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value5_6 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP557Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value5_7 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP557Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP557Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 5 j)=sharedDiskP557Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP557Value5_0
  · exact sharedDiskP557Value5_1
  · exact sharedDiskP557Value5_2
  · exact sharedDiskP557Value5_3
  · exact sharedDiskP557Value5_4
  · exact sharedDiskP557Value5_5
  · exact sharedDiskP557Value5_6
  · exact sharedDiskP557Value5_7
private theorem sharedDiskP557Value6_0 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP557Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value6_1 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP557Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value6_2 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP557Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value6_3 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP557Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value6_4 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP557Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value6_5 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP557Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value6_6 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP557Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value6_7 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP557Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP557Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 6 j)=sharedDiskP557Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP557Value6_0
  · exact sharedDiskP557Value6_1
  · exact sharedDiskP557Value6_2
  · exact sharedDiskP557Value6_3
  · exact sharedDiskP557Value6_4
  · exact sharedDiskP557Value6_5
  · exact sharedDiskP557Value6_6
  · exact sharedDiskP557Value6_7
private theorem sharedDiskP557Value7_0 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP557Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value7_1 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP557Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value7_2 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP557Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value7_3 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP557Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value7_4 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP557Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value7_5 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP557Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value7_6 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP557Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value7_7 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP557Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP557Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 7 j)=sharedDiskP557Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP557Value7_0
  · exact sharedDiskP557Value7_1
  · exact sharedDiskP557Value7_2
  · exact sharedDiskP557Value7_3
  · exact sharedDiskP557Value7_4
  · exact sharedDiskP557Value7_5
  · exact sharedDiskP557Value7_6
  · exact sharedDiskP557Value7_7
private theorem sharedDiskP557Value8_0 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP557Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value8_1 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP557Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value8_2 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP557Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value8_3 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP557Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value8_4 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP557Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value8_5 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP557Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value8_6 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP557Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP557Value8_7 : truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP557Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP557Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points 8 j)=sharedDiskP557Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP557Value8_0
  · exact sharedDiskP557Value8_1
  · exact sharedDiskP557Value8_2
  · exact sharedDiskP557Value8_3
  · exact sharedDiskP557Value8_4
  · exact sharedDiskP557Value8_5
  · exact sharedDiskP557Value8_6
  · exact sharedDiskP557Value8_7
theorem sharedDiskP557Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP557Params (sharedChord521Gauss8Points i j)=sharedDiskP557Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP557Values0_eq
  · exact sharedDiskP557Values1_eq
  · exact sharedDiskP557Values2_eq
  · exact sharedDiskP557Values3_eq
  · exact sharedDiskP557Values4_eq
  · exact sharedDiskP557Values5_eq
  · exact sharedDiskP557Values6_eq
  · exact sharedDiskP557Values7_eq
  · exact sharedDiskP557Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP557Box : HorizontalRectangle := ⟨(679/800),(17/20),(969510010986397/1649267441664000),(971120623722397/1649267441664000),(4048815533235523741519408834611/10384593717069655257060992658440192),(3550164219455323633977934559619123/10384593717069655257060992658440192),(-4155492542282694856216790553468361/1298074214633706907132624082305024),(-3698049782191720318239915527773641/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP557Grid : CGrid := momentChordGrid sharedDiskP557Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP557Columns : containedInReported sharedDiskP557Grid.re sharedDiskP557Box.reLo sharedDiskP557Box.reHi=true ∧ containedInReported sharedDiskP557Grid.im sharedDiskP557Box.imLo sharedDiskP557Box.imHi=true := by
  rw [sharedDiskP557Grid,momentChordGrid_eq_tabulated sharedDiskP557Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP557Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP557Values_eq]
  decide +kernel
theorem sharedDiskP557Sound : sharedDiskP557Box.Sound := by
  intro t a tl tu al au
  change (((679/800):ℚ):ℝ)≤t at tl
  change t≤(((17/20):ℚ):ℝ) at tu
  change (((969510010986397/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((971120623722397/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP557Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(679/800))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((17/20):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(969510010986397/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((971120623722397/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP557Columns.1 sharedDiskP557Columns.2
def sharedDiskP557Rows : List SignRow := [positive_557.toSignRow]
theorem sharedDiskP557Rows_actual : ∀ r∈sharedDiskP557Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP557Rows.all (sharedDiskP557Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP557Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP555Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP556Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP557Rows_actual
