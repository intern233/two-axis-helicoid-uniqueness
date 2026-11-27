import TwoAxisHelicoid.PdfSharedChord521Gauss8
import TwoAxisHelicoid.PdfSharedChord521Disks

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP543Params : ChordParams := ⟨⟨(-27765732673879735540566),(-27608616296371276550861),true⟩,⟨1900413783240883146112824,1907733428584145210272819,true⟩,⟨133283339430519140437668,134219067774081270439526,true⟩,⟨249497123452482638142712,251012328284083441661488,true⟩,⟨357182688325284603700800,358243095524105553335974,true⟩,⟨1154641125799335869255542,1154941445034835837240678,true⟩,⟨(-2182469509201696391246161),(-2178625872879184293079197),true⟩,⟨⟨1144020195019082037938655,1158445796177903330531989,true⟩,⟨(-49608945),49608945,true⟩⟩⟩
theorem sharedDiskP543Params_ok : chordParams (Grid.ofRats (133/160) (333/400)) (Grid.ofRats (960629562362359/1649267441664000) (962240175098359/1649267441664000))=sharedDiskP543Params := by decide +kernel
def sharedDiskP543Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3037951347041749022956633),(-2749855654997024779891925),true⟩,⟨(-225549353331402839169864),9724107049839225001896,true⟩⟩
  | 0,1 => ⟨⟨(-2702752410151184598512429),(-2437291632815934134102755),true⟩,⟨(-283021741916587619412172),(-59972415299951564706494),true⟩⟩
  | 0,2 => ⟨⟨(-2460420566092462585010716),(-2212826443390796968038124),true⟩,⟨(-333462670155678675254978),(-121567239291126757117706),true⟩⟩
  | 0,3 => ⟨⟨(-2323822576697410467324748),(-2086711728368560614922669),true⟩,⟨(-364985291649287344821294),(-160001568174503717696573),true⟩⟩
  | 0,4 => ⟨⟨(-3434396771098071670768652),(-3123292184690738238830069),true⟩,⟨(-177071541931962482025358),66873292177458262269712,true⟩⟩
  | 0,5 => ⟨⟨(-3837557507411527116369068),(-3507438445729531393081435),true⟩,⟨(-150387922358023196419480),95900805422128384422806,true⟩⟩
  | 0,6 => ⟨⟨(-4178137619797448477507576),(-3835380445215677678509572),true⟩,⟨(-146135884949159877786402),97481288653218158457714,true⟩⟩
  | 0,7 => ⟨⟨(-4391742754588838339665715),(-4042513709946353644179510),true⟩,⟨(-153731493850860622700286),86909888421215774818324,true⟩⟩
  | 1,0 => ⟨⟨(-1497278704736981789262058),(-1328921038747219088449196),true⟩,⟨(-591928506942393380935875),(-438441679874633962005456),true⟩⟩
  | 1,1 => ⟨⟨(-1315933986956060878402649),(-1163028579224849382687598),true⟩,⟨(-645995505838349535672620),(-505009719713114769991479),true⟩⟩
  | 1,2 => ⟨⟨(-1184088204553243176727855),(-1042251138909032462764899),true⟩,⟨(-684894782176099163408713),(-552982351345930568196956),true⟩⟩
  | 1,3 => ⟨⟨(-1109044451671584807291590),(-973407732267320224008243),true⟩,⟨(-706638568581567616970213),(-579843851223710328608183),true⟩⟩
  | 1,4 => ⟨⟨(-1713194375718279883294499),(-1526358570491895274733199),true⟩,⟨(-528272479102245693298558),(-360169089475225112155254),true⟩⟩
  | 1,5 => ⟨⟨(-1937639408816231148529294),(-1731823476976828111922965),true⟩,⟨(-464627541337381091429744),(-282011115159007817926566),true⟩⟩
  | 1,6 => ⟨⟨(-2133455753251327645061068),(-1911500466755671963227328),true⟩,⟨(-412301437675018177524304),(-217864305811939250565712),true⟩⟩
  | 1,7 => ⟨⟨(-2260003967416272306101585),(-2027907240548008927074928),true⟩,⟨(-380424719093825797071208),(-178863144762650872854696),true⟩⟩
  | 2,0 => ⟨⟨(-272557296187398981549367),(-191615479855691921012483),true⟩,⟨(-896238845280182518293769),(-813879425538474525380829),true⟩⟩
  | 2,1 => ⟨⟨(-92797475158080866520857),(-18805047605568558043555),true⟩,⟨(-916537851847267203612884),(-839694678502925519107889),true⟩⟩
  | 2,2 => ⟨⟨38865598648114154272643,108865760022661798517577,true⟩,⟨(-925899608667556347973221),(-852515521417359816417646),true⟩⟩
  | 2,3 => ⟨⟨114409244048358529451185,182534542963604929458856,true⟩,⟨(-929321052414239882703383),(-857708554403535820722955),true⟩⟩
  | 2,4 => ⟨⟨(-486893485253400144556209),(-395857725354679023523970),true⟩,⟨(-860580407109073385904653),(-770414369720499593369212),true⟩⟩
  | 2,5 => ⟨⟨(-714311675937579283487265),(-609430950527913773909441),true⟩,⟨(-811127661740809506102044),(-709984626913675091251911),true⟩⟩
  | 2,6 => ⟨⟨(-919479839765921898956879),(-799061877725567517926217),true⟩,⟨(-759386565284706741804955),(-645237835945579149062283),true⟩⟩
  | 2,7 => ⟨⟨(-1056375553748315324442035),(-925036576387705807960393),true⟩,⟨(-721650367159113397513473),(-598415602656575833669190),true⟩⟩
  | 3,0 => ⟨⟨1024116335449312391504213,1092648981804680348313616,true⟩,⟨(-933332482304382833569000),(-865334267410851060378116),true⟩⟩
  | 3,1 => ⟨⟨1246192537547524156606498,1318136285760357667598932,true⟩,⟨(-957088027337039905086985),(-886752313563579707511036),true⟩⟩
  | 3,2 => ⟨⟨1417831670021758763401362,1493255010340909965907263,true⟩,⟨(-994439733911089778278391),(-921342283321795306685463),true⟩⟩
  | 3,3 => ⟨⟨1520469989361975534355886,1598379495282555501726689,true⟩,⟨(-1027221171519654194593750),(-952010142401051516753979),true⟩⟩
  | 3,4 => ⟨⟨774075347853113354870228,840054951801598894845327,true⟩,⟨(-927439702188987249283489),(-860653890305932687960853),true⟩⟩
  | 3,5 => ⟨⟨523718357004783667195503,588427076640269357532057,true⟩,⟨(-930825477195969717614300),(-863917333520353679547011),true⟩⟩
  | 3,6 => ⟨⟨308407018274987565172106,373091831618098570110768,true⟩,⟨(-932576211344217740770847),(-864532493781955304037055),true⟩⟩
  | 3,7 => ⟨⟨167814785081455949975272,234743816001578767877932,true⟩,⟨(-930954309169152900034752),(-860501880851179512006015),true⟩⟩
  | 4,0 => ⟨⟨2270855947513001631728828,2393999797720885294657945,true⟩,⟨(-1715342832203007788178115),(-1594413127799917977758633),true⟩⟩
  | 4,1 => ⟨⟨2442046244860975145787644,2588727840836714815744268,true⟩,⟨(-2158852732038295470441551),(-2012259811445878279586436),true⟩⟩
  | 4,2 => ⟨⟨2518602266035172677007734,2689758274649677570043228,true⟩,⟨(-2649883550079170316116733),(-2475632775731392609072422),true⟩⟩
  | 4,3 => ⟨⟨2515014549890334959780526,2704035516547054281162384,true⟩,⟨(-3021102133027342921939306),(-2826095503561229829063472),true⟩⟩
  | 4,4 => ⟨⟨2052497996596880324509489,2157062046807423868441639,true⟩,⟨(-1396576943021475375618299),(-1295133776769126834366442),true⟩⟩
  | 4,5 => ⟨⟨1840499884927369340689987,1932134854044992296930731,true⟩,⟨(-1200413636572481785823814),(-1112021329589669734245915),true⟩⟩
  | 4,6 => ⟨⟨1671830297512234833096688,1755421898878746975374993,true⟩,⟨(-1094297434597254041617284),(-1013749421776222907769846),true⟩⟩
  | 4,7 => ⟨⟨1570042723010590714460192,1649527129335285866185588,true⟩,⟨(-1046534699543885111075297),(-969889159838411126747212),true⟩⟩
  | 5,0 => ⟨⟨2284535850372424421436249,2518530269662989313344284,true⟩,⟨(-3983237338247797098545704),(-3733970061112349627462781),true⟩⟩
  | 5,1 => ⟨⟨2151758233854710690511518,2398977940310583826926394,true⟩,⟨(-4269900830904783567965675),(-4004128187823862058402853),true⟩⟩
  | 5,2 => ⟨⟨2017012835838717985180440,2275135593863405161551822,true⟩,⟨(-4506363683251944195854843),(-4226788347119283086611298),true⟩⟩
  | 5,3 => ⟨⟨1921450331852838914734344,2186299873662520827484981,true⟩,⟨(-4652056408677381621386909),(-4363873996125961656404799),true⟩⟩
  | 5,4 => ⟨⟨2387697524707397325797746,2608268042268904951788866,true⟩,⟨(-3693309170678488865280190),(-3460537192316248980818770),true⟩⟩
  | 5,5 => ⟨⟨2453517383929747129219048,2662330812271557363211584,true⟩,⟨(-3440934177638374713911790),(-3222399654212297312332101),true⟩⟩
  | 5,6 => ⟨⟨2488334831884247101082579,2688362726178035351100685,true⟩,⟨(-3253670039751036452962000),(-3045647444632090938556722),true⟩⟩
  | 5,7 => ⟨⟨2502960986870927956463928,2697913949388195427351614,true⟩,⟨(-3146129545164790427022903),(-2944129520791637779738075),true⟩⟩
  | 6,0 => ⟨⟨777529236565397389975113,1100044546022477304846046,true⟩,⟨(-5725151384274483464231494),(-5365375642555788283281470),true⟩⟩
  | 6,1 => ⟨⟨295425498697353767648934,641966271100760860765180,true⟩,⟨(-5974622370077667499522733),(-5590474494995547542959845),true⟩⟩
  | 6,2 => ⟨⟨(-140474376733988940954171),225806577217786018527511,true⟩,⟨(-6133950263110622923000686),(-5731077432198319606567843),true⟩⟩
  | 6,3 => ⟨⟨(-426107219478401063456809),(-47439995669725665537294),true⟩,⟨(-6208429676319499990476362),(-5794786336832451133691918),true⟩⟩
  | 6,4 => ⟨⟨1211941535406459439717318,1512660185284199072520102,true⟩,⟨(-5418665883780945304764873),(-5083286219271568456400057),true⟩⟩
  | 6,5 => ⟨⟨1541202409651009136293851,1827610520364958675577456,true⟩,⟨(-5115919371022252862490435),(-4799650828390037121544636),true⟩⟩
  | 6,6 => ⟨⟨1757659401708415375480321,2032649229601195283921100,true⟩,⟨(-4871013081668695252272425),(-4569718506115863039109536),true⟩⟩
  | 6,7 => ⟨⟨1870897817184604641700271,2139044459964860635479031,true⟩,⟨(-4723358013002974044537036),(-4430930646358037824487086),true⟩⟩
  | 7,0 => ⟨⟨(-2924352215806396068654911),(-2461028511472334940747140),true⟩,⟨(-5956449922708674865827479),(-5494409035182251435917507),true⟩⟩
  | 7,1 => ⟨⟨(-3628451316290059702250935),(-3151243708695626981027049),true⟩,⟨(-5549613129390264210688395),(-5091634787869237109144816),true⟩⟩
  | 7,2 => ⟨⟨(-4135209440857570340282786),(-3652554053624116116832113),true⟩,⟨(-5111686872009925950459474),(-4664654773434406048976709),true⟩⟩
  | 7,3 => ⟨⟨(-4407699651589008704670608),(-3924583997167509029498405),true⟩,⟨(-4800852726695822486619654),(-4363961991937867915242557),true⟩⟩
  | 7,4 => ⟨⟨(-2138693994469176615979481),(-1696752985591756163580110),true⟩,⟨(-6213781974693090154243742),(-5757767682693020850212646),true⟩⟩
  | 7,5 => ⟨⟨(-1419520353543962520502032),(-1001476469887802692022587),true⟩,⟨(-6301717708055039701264493),(-5858916404247523507913546),true⟩⟩
  | 7,6 => ⟨⟨(-879084839890619977502159),(-481525736341270717073513),true⟩,⟨(-6282019442360303549195184),(-5853519475285623721276934),true⟩⟩
  | 7,7 => ⟨⟨(-570497069630740680953304),(-185630028032754457144772),true⟩,⟨(-6237683213362219387895693),(-5819014224060961166929016),true⟩⟩
  | 8,0 => ⟨⟨(-5196543741765801196138910),(-4789299108493336358106334),true⟩,⟨(-1822201765697025811776862),(-1536637349749630169324819),true⟩⟩
  | 8,1 => ⟨⟨(-4973120452851228826158789),(-4609776079286523337639616),true⟩,⟨(-1000244142324614251094017),(-770383001944147556344818),true⟩⟩
  | 8,2 => ⟨⟨(-4683073417939114519778498),(-4358429104244579293194945),true⟩,⟨(-424868430614161492097402),(-237940166167248169378984),true⟩⟩
  | 8,3 => ⟨⟨(-4470251842814354439048389),(-4170193032169257364987007),true⟩,⟨(-119250433614582587951706),44204894865233794138792,true⟩⟩
  | 8,4 => ⟨⟨(-5223599072034042913224106),(-4778801467882157051621094),true⟩,⟨(-2765859855877901055995212),(-2423630928875626499336100),true⟩⟩
  | 8,5 => ⟨⟨(-5037603035789050683441082),(-4568953915982506601516517),true⟩,⟨(-3637778496888892505534630),(-3250013015161625549646027),true⟩⟩
  | 8,6 => ⟨⟨(-4752865897246566463686064),(-4273452577742720825371105),true⟩,⟨(-4281876007975446813491271),(-3865020393188678761435874),true⟩⟩
  | 8,7 => ⟨⟨(-4528917550943886930669593),(-4046416557460182872416276),true⟩,⟨(-4638349360039723789781673),(-4207355275382853508705866),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP543Value0_0 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP543Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value0_1 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP543Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value0_2 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP543Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value0_3 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP543Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value0_4 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP543Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value0_5 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP543Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value0_6 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP543Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value0_7 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP543Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP543Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 0 j)=sharedDiskP543Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP543Value0_0
  · exact sharedDiskP543Value0_1
  · exact sharedDiskP543Value0_2
  · exact sharedDiskP543Value0_3
  · exact sharedDiskP543Value0_4
  · exact sharedDiskP543Value0_5
  · exact sharedDiskP543Value0_6
  · exact sharedDiskP543Value0_7
private theorem sharedDiskP543Value1_0 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP543Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value1_1 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP543Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value1_2 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP543Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value1_3 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP543Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value1_4 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP543Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value1_5 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP543Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value1_6 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP543Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value1_7 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP543Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP543Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 1 j)=sharedDiskP543Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP543Value1_0
  · exact sharedDiskP543Value1_1
  · exact sharedDiskP543Value1_2
  · exact sharedDiskP543Value1_3
  · exact sharedDiskP543Value1_4
  · exact sharedDiskP543Value1_5
  · exact sharedDiskP543Value1_6
  · exact sharedDiskP543Value1_7
private theorem sharedDiskP543Value2_0 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP543Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value2_1 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP543Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value2_2 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP543Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value2_3 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP543Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value2_4 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP543Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value2_5 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP543Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value2_6 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP543Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value2_7 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP543Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP543Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 2 j)=sharedDiskP543Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP543Value2_0
  · exact sharedDiskP543Value2_1
  · exact sharedDiskP543Value2_2
  · exact sharedDiskP543Value2_3
  · exact sharedDiskP543Value2_4
  · exact sharedDiskP543Value2_5
  · exact sharedDiskP543Value2_6
  · exact sharedDiskP543Value2_7
private theorem sharedDiskP543Value3_0 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP543Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value3_1 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP543Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value3_2 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP543Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value3_3 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP543Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value3_4 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP543Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value3_5 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP543Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value3_6 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP543Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value3_7 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP543Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP543Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 3 j)=sharedDiskP543Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP543Value3_0
  · exact sharedDiskP543Value3_1
  · exact sharedDiskP543Value3_2
  · exact sharedDiskP543Value3_3
  · exact sharedDiskP543Value3_4
  · exact sharedDiskP543Value3_5
  · exact sharedDiskP543Value3_6
  · exact sharedDiskP543Value3_7
private theorem sharedDiskP543Value4_0 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP543Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value4_1 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP543Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value4_2 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP543Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value4_3 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP543Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value4_4 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP543Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value4_5 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP543Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value4_6 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP543Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value4_7 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP543Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP543Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 4 j)=sharedDiskP543Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP543Value4_0
  · exact sharedDiskP543Value4_1
  · exact sharedDiskP543Value4_2
  · exact sharedDiskP543Value4_3
  · exact sharedDiskP543Value4_4
  · exact sharedDiskP543Value4_5
  · exact sharedDiskP543Value4_6
  · exact sharedDiskP543Value4_7
private theorem sharedDiskP543Value5_0 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP543Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value5_1 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP543Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value5_2 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP543Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value5_3 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP543Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value5_4 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP543Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value5_5 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP543Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value5_6 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP543Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value5_7 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP543Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP543Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 5 j)=sharedDiskP543Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP543Value5_0
  · exact sharedDiskP543Value5_1
  · exact sharedDiskP543Value5_2
  · exact sharedDiskP543Value5_3
  · exact sharedDiskP543Value5_4
  · exact sharedDiskP543Value5_5
  · exact sharedDiskP543Value5_6
  · exact sharedDiskP543Value5_7
private theorem sharedDiskP543Value6_0 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP543Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value6_1 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP543Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value6_2 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP543Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value6_3 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP543Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value6_4 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP543Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value6_5 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP543Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value6_6 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP543Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value6_7 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP543Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP543Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 6 j)=sharedDiskP543Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP543Value6_0
  · exact sharedDiskP543Value6_1
  · exact sharedDiskP543Value6_2
  · exact sharedDiskP543Value6_3
  · exact sharedDiskP543Value6_4
  · exact sharedDiskP543Value6_5
  · exact sharedDiskP543Value6_6
  · exact sharedDiskP543Value6_7
private theorem sharedDiskP543Value7_0 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP543Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value7_1 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP543Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value7_2 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP543Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value7_3 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP543Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value7_4 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP543Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value7_5 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP543Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value7_6 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP543Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value7_7 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP543Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP543Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 7 j)=sharedDiskP543Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP543Value7_0
  · exact sharedDiskP543Value7_1
  · exact sharedDiskP543Value7_2
  · exact sharedDiskP543Value7_3
  · exact sharedDiskP543Value7_4
  · exact sharedDiskP543Value7_5
  · exact sharedDiskP543Value7_6
  · exact sharedDiskP543Value7_7
private theorem sharedDiskP543Value8_0 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP543Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value8_1 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP543Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value8_2 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP543Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value8_3 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP543Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value8_4 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP543Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value8_5 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP543Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value8_6 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP543Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP543Value8_7 : truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP543Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP543Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points 8 j)=sharedDiskP543Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP543Value8_0
  · exact sharedDiskP543Value8_1
  · exact sharedDiskP543Value8_2
  · exact sharedDiskP543Value8_3
  · exact sharedDiskP543Value8_4
  · exact sharedDiskP543Value8_5
  · exact sharedDiskP543Value8_6
  · exact sharedDiskP543Value8_7
theorem sharedDiskP543Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP543Params (sharedChord521Gauss8Points i j)=sharedDiskP543Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP543Values0_eq
  · exact sharedDiskP543Values1_eq
  · exact sharedDiskP543Values2_eq
  · exact sharedDiskP543Values3_eq
  · exact sharedDiskP543Values4_eq
  · exact sharedDiskP543Values5_eq
  · exact sharedDiskP543Values6_eq
  · exact sharedDiskP543Values7_eq
  · exact sharedDiskP543Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP543Box : HorizontalRectangle := ⟨(133/160),(333/400),(960629562362359/1649267441664000),(962240175098359/1649267441664000),(1826585339881612961888457479873931/10384593717069655257060992658440192),(1384019809830252595186969229965667/2596148429267413814265248164610048),(-4183469769534442892219142185378209/1298074214633706907132624082305024),(-3705916353744398063607114176881057/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP543Grid : CGrid := momentChordGrid sharedDiskP543Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP543Columns : containedInReported sharedDiskP543Grid.re sharedDiskP543Box.reLo sharedDiskP543Box.reHi=true ∧ containedInReported sharedDiskP543Grid.im sharedDiskP543Box.imLo sharedDiskP543Box.imHi=true := by
  rw [sharedDiskP543Grid,momentChordGrid_eq_tabulated sharedDiskP543Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP543Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP543Values_eq]
  decide +kernel
theorem sharedDiskP543Sound : sharedDiskP543Box.Sound := by
  intro t a tl tu al au
  change (((133/160):ℚ):ℝ)≤t at tl
  change t≤(((333/400):ℚ):ℝ) at tu
  change (((960629562362359/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((962240175098359/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP543Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(133/160))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((333/400):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(960629562362359/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((962240175098359/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP543Columns.1 sharedDiskP543Columns.2
def sharedDiskP543Rows : List SignRow := [positive_543.toSignRow]
theorem sharedDiskP543Rows_actual : ∀ r∈sharedDiskP543Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP543Rows.all (sharedDiskP543Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP543Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP544Params : ChordParams := ⟨⟨(-27923268040297941485214),(-27765732673879735539989),true⟩,⟨1895839537872278760888757,1903141324520778262812433,true⟩,⟨133534382327535430782849,134470083322457912348231,true⟩,⟨250446640367260585570896,251963889518273090245348,true⟩,⟨358151959252201866338852,359212303793771632286682,true⟩,⟨1154340082294096505160734,1154641125799335869256646,true⟩,⟨(-2178625872879184293088223),(-2174792397169038045760930),true⟩,⟨⟨1143672101120846060016905,1158105360428991728294827,true⟩,⟨(-52706834),52706834,true⟩⟩⟩
theorem sharedDiskP544Params_ok : chordParams (Grid.ofRats (333/400) (667/800)) (Grid.ofRats (961254129192727/1649267441664000) (962864741928727/1649267441664000))=sharedDiskP544Params := by decide +kernel
def sharedDiskP544Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3036935641434177460530596),(-2748437869320777908654446),true⟩,⟨(-224678986894634655560724),10983664031619435236988,true⟩⟩
  | 0,1 => ⟨⟨(-2703035452254993404477193),(-2437114118501397880307174),true⟩,⟨(-281647527435616689183915),(-58170754436414268942052),true⟩⟩
  | 0,2 => ⟨⟨(-2461528796254854005909471),(-2213452763476047665249841),true⟩,⟨(-331720398749856274468979),(-119396080787316144367328),true⟩⟩
  | 0,3 => ⟨⟨(-2325365985869429999494880),(-2087757346177987625524807),true⟩,⟨(-363041438454585673515060),(-157616052475824432847808),true⟩⟩
  | 0,4 => ⟨⟨(-3431651258509676114297125),(-3120219018112766153987424),true⟩,⟨(-176741627312562578755446),67556594694702605807076,true⟩⟩
  | 0,5 => ⟨⟨(-3832859111237750283134812),(-3502487479799188996857863),true⟩,⟨(-150495451779618058472698),96140832166934387149429,true⟩⟩
  | 0,6 => ⟨⟨(-4171659276858823920580271),(-3828708085488712114124236),true⟩,⟨(-146493176493412083844283),97480198293052986548019,true⟩⟩
  | 0,7 => ⟨⟨(-4384094230951153832031662),(-4034706879123087045724711),true⟩,⟨(-154190502254741334631015),86837351910728407467830,true⟩⟩
  | 1,0 => ⟨⟨(-1500919976222273834873752),(-1332033937196297795923092),true⟩,⟨(-589095366747097375908200),(-435140586742198644061131),true⟩⟩
  | 1,1 => ⟨⟨(-1319933628472589767255753),(-1166510924489567115161584),true⟩,⟨(-643102042273680643781350),(-501659652510854527252094),true⟩⟩
  | 1,2 => ⟨⟨(-1188333130584222717209461),(-1045990728154465694261233),true⟩,⟨(-682001633449085637682711),(-549644882320357406534731),true⟩⟩
  | 1,3 => ⟨⟨(-1113424567350465262733799),(-977290638052059661686690),true⟩,⟨(-703763786489946136445167),(-576533092473541619241161),true⟩⟩
  | 1,4 => ⟨⟨(-1716368372967012659441183),(-1528999664264501048841087),true⟩,⟨(-525589840762914959197793),(-357013820445945331770234),true⟩⟩
  | 1,5 => ⟨⟨(-1940271174947714767375928),(-1733927526307625821760634),true⟩,⟨(-462173651365244606654210),(-279089387528139327485790),true⟩⟩
  | 1,6 => ⟨⟨(-2135561379713981038485682),(-1913090520721460892459301),true⟩,⟨(-410092039986477957045738),(-215198038661945403913359),true⟩⟩
  | 1,7 => ⟨⟨(-2261741552868984863928470),(-2029140472593395610900927),true⟩,⟨(-378389456477716587567691),(-176380720784331362491019),true⟩⟩
  | 2,0 => ⟨⟨(-278345275834870441281846),(-197121442327108733333238),true⟩,⟨(-894512975944342337516664),(-811933249771676522866975),true⟩⟩
  | 2,1 => ⟨⟨(-98903811581359623496320),(-24660241667336539934192),true⟩,⟨(-915287181665884202981810),(-838245089932273042358633),true⟩⟩
  | 2,2 => ⟨⟨32538234637768311839488,102748128916137276378054,true⟩,⟨(-925030040069167208292069),(-851459402241084282993722),true⟩⟩
  | 2,3 => ⟨⟨107950827894770835824460,176275423329264509896026,true⟩,⟨(-928679848802946701886196),(-856886626697633090548093),true⟩⟩
  | 2,4 => ⟨⟨(-492307462870278281980630),(-400947071608624127667466),true⟩,⟨(-858376320359987429722381),(-767958413170622661159399),true⟩⟩
  | 2,5 => ⟨⟨(-719375382281210915587200),(-614051316711317838781033),true⟩,⟨(-808587784812670014346122),(-707063459047686852281695),true⟩⟩
  | 2,6 => ⟨⟨(-924191731245869654432170),(-803300605954577614254891),true⟩,⟨(-756621210232945460151472),(-642061088244346956422775),true⟩⟩
  | 2,7 => ⟨⟨(-1060849035811142895487500),(-929019063823814422343497),true⟩,⟨(-718796755615645514989442),(-595132386848901985664062),true⟩⟩
  | 3,0 => ⟨⟨1016539006419978367135831,1085127294643597162166232,true⟩,⟨(-935540919314978773778933),(-867440267988137123351161),true⟩⟩
  | 3,1 => ⟨⟨1238489205986222318900901,1310497920284035517470421,true⟩,⟨(-959983035633128148562487),(-889531110820556770988938),true⟩⟩
  | 3,2 => ⟨⟨1410053692740774669691704,1485554234912394100218317,true⟩,⟨(-997872268858816560789617),(-924643680863651000750835),true⟩⟩
  | 3,3 => ⟨⟨1512646040733534677473710,1590642098048864578974357,true⟩,⟨(-1030983787697167671912189),(-955630872049277738748126),true⟩⟩
  | 3,4 => ⟨⟨766713655895274904147610,832747565300720090488911,true⟩,⟨(-928865789704893387925069),(-861985593473172696583799),true⟩⟩
  | 3,5 => ⟨⟨516661846181430666328825,581433790780118288946756,true⟩,⟨(-931450555009985415821630),(-864447844161721037051940),true⟩⟩
  | 3,6 => ⟨⟨301641506208712145176047,366439180766589605357861,true⟩,⟨(-932531091622688958888989),(-864362228329550749501564),true⟩⟩
  | 3,7 => ⟨⟨161265171295509110719297,228386715677018412694390,true⟩,⟨(-930477763780517966868880),(-859848178478448401358874),true⟩⟩
  | 4,0 => ⟨⟨2261567053488767158243576,2384884601911310542970362,true⟩,⟨(-1722082936684380600698449),(-1600891468503313238588131),true⟩⟩
  | 4,1 => ⟨⟨2431271967816385270948935,2578160020512900321999959,true⟩,⟨(-2166527166919159137540977),(-2019623931687413625239138),true⟩⟩
  | 4,2 => ⟨⟨2505887856188211775694721,2677269288461372139262082,true⟩,⟨(-2658061926623592462214613),(-2483467081208116615469174),true⟩⟩
  | 4,3 => ⟨⟨2500695644777133105462289,2689944376009808214268126,true⟩,⟨(-3029303534032192990042397),(-2833941598657383878396849),true⟩⟩
  | 4,4 => ⟨⟨2044047013539490723533073,2148751267585629308181292,true⟩,⟨(-1402304699345323107394217),(-1300646193346819704880415),true⟩⟩
  | 4,5 => ⟨⟨1832432585592455138815055,1924182144590779087684980,true⟩,⟨(-1205291623548502173669392),(-1116718848569474042389788),true⟩⟩
  | 4,6 => ⟨⟨1663920474251060775426068,1747610686267013677301669,true⟩,⟨(-1098568000236957751485438),(-1017861593049161206943072),true⟩⟩
  | 4,7 => ⟨⟨1562193982420661929453802,1641769140662162637563912,true⟩,⟨(-1050460468839783727285235),(-973667734391472060750268),true⟩⟩
  | 5,0 => ⟨⟨2265802745687313216300718,2499979278624894072892248,true⟩,⟨(-3989964343449004979654874),(-3740377530351496271855311),true⟩⟩
  | 5,1 => ⟨⟨2131711098529603098892260,2379083055425419107707288,true⟩,⟨(-4275707239686558758180664),(-4009647067280802995583589),true⟩⟩
  | 5,2 => ⟨⟨1995909238534184715570787,2254153036700477208825741,true⟩,⟨(-4511216699116146848555052),(-4231389207462401989713265),true⟩⟩
  | 5,3 => ⟨⟨1899715349787883154280851,2164663438696554942412465,true⟩,⟨(-4656225965505723038564436),(-4367817720789381401655028),true⟩⟩
  | 5,4 => ⟨⟨2370308811026013991351566,2591083590124559810764715,true⟩,⟨(-3700729090248713879252112),(-3467615961524908413887245),true⟩⟩
  | 5,5 => ⟨⟨2437296011093073634263376,2646326900682396725598264,true⟩,⟨(-3448777225585999897619630),(-3229890674493671050850260),true⟩⟩
  | 5,6 => ⟨⟨2472970411943628209299791,2673222111458010713646798,true⟩,⟨(-3261724780294093893849186),(-3053346500692936732046788),true⟩⟩
  | 5,7 => ⟨⟨2488083069697887609262787,2683262199155444635937867,true⟩,⟨(-3154267852168262383713672),(-2951911657547769194887798),true⟩⟩
  | 6,0 => ⟨⟨752028426325375132903077,1074887244465622718360177,true⟩,⟨(-5721286632727308472090977),(-5361324507625644746412705),true⟩⟩
  | 6,1 => ⟨⟨269831906269752024832530,616617146335945797463687,true⟩,⟨(-5967454545130671910718543),(-5583272069218743273286912),true⟩⟩
  | 6,2 => ⟨⟨(-165689169462433366411626),200781150996904872298249,true⟩,⟨(-6123913534230002865277285),(-5721150007481891710044462),true⟩⟩
  | 6,3 => ⟨⟨(-450810562359401541337705),(-71981365205193111067858),true⟩,⟨(-6196588507043684262655610),(-5783150990578704792916351),true⟩⟩
  | 6,4 => ⟨⟨1187193985334292526964443,1488017486595469951749679,true⟩,⟨(-5417816789913207500585320),(-5082316512845632728157444),true⟩⟩
  | 6,5 => ⟨⟨1517619386008734265702676,1804034963724686486606566,true⟩,⟨(-5117342224134422323281830),(-4800959260182182677485012),true⟩⟩
  | 6,6 => ⟨⟨1735015137601125158061964,2010064505494384731330561,true⟩,⟨(-4874002752304840659523997),(-4572529234612609175813720),true⟩⟩
  | 6,7 => ⟨⟨1848860884529059843904677,2117094087220734621237748,true⟩,⟨(-4727164322925492395815206),(-4434525380782636505049369),true⟩⟩
  | 7,0 => ⟨⟨(-2937814930728937277531543),(-2475082192926516840800538),true⟩,⟨(-5932671206209691524310009),(-5471671225903488898765671),true⟩⟩
  | 7,1 => ⟨⟨(-3636641154343062573180738),(-3160262200593839708826486),true⟩,⟨(-5524460987078033242890402),(-5067716251564829455899226),true⟩⟩
  | 7,2 => ⟨⟨(-4138947450347913841280603),(-3657291389571087103783293),true⟩,⟨(-5086539933011453904561825),(-4640846284627023538887826),true⟩⟩
  | 7,3 => ⟨⟨(-4408765858049335660053104),(-3926738336592907445572844),true⟩,⟨(-4776225726196098465538627),(-4340709758467356485276371),true⟩⟩
  | 7,4 => ⟨⟨(-2156934330406835710895534),(-1715328052137121447351007),true⟩,⟨(-6192814170077243092970022),(-5737591180418328468414258),true⟩⟩
  | 7,5 => ⟨⟨(-1441149371161905765820674),(-1023219451908069736726947),true⟩,⟨(-6284171853670669211763083),(-5841918041960485118894227),true⟩⟩
  | 7,6 => ⟨⟨(-902626917639286535215653),(-505026956900243854174051),true⟩,⟨(-6267456690580685250699924),(-5839317857784003273716071),true⟩⟩
  | 7,7 => ⟨⟨(-594875736669589843153336),(-209884400036324422851095),true⟩,⟨(-6224954820015374155085834),(-5806540933136574561082754),true⟩⟩
  | 8,0 => ⟨⟨(-5185187591510350413065599),(-4779075465232908820250216),true⟩,⟨(-1811561579969013611228813),(-1526894231295864746328743),true⟩⟩
  | 8,1 => ⟨⟨(-4962078427508169157143279),(-4599658677666309020578333),true⟩,⟨(-994548461680100315903124),(-765282055713843620859929),true⟩⟩
  | 8,2 => ⟨⟨(-4673338830899203480000015),(-4349419410100637604663901),true⟩,⟨(-422537008280079740753167),(-235977852710071396363108),true⟩⟩
  | 8,3 => ⟨⟨(-4461643209714048482599280),(-4162177840378873035099738),true⟩,⟨(-118598084451167730063634),44632719812526637715279,true⟩⟩
  | 8,4 => ⟨⟨(-5213894190480919908278281),(-4770349755413172248765858),true⟩,⟨(-2749772180399882662955248),(-2408710573034483940098210),true⟩⟩
  | 8,5 => ⟨⟨(-5031250553005287685159684),(-4563859851924547981935506),true⟩,⟨(-3617268677904509302292216),(-3230834503168729494109647),true⟩⟩
  | 8,6 => ⟨⟨(-4750166632097228450461058),(-4271945449109623065198409),true⟩,⟨(-4258746360811286313262354),(-3843275999643312267178779),true⟩⟩
  | 8,7 => ⟨⟨(-4528717726611558426627726),(-4047342895361320774824897),true⟩,⟨(-4614117447779766114481976),(-4184507488978605051334961),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP544Value0_0 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP544Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value0_1 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP544Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value0_2 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP544Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value0_3 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP544Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value0_4 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP544Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value0_5 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP544Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value0_6 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP544Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value0_7 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP544Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP544Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 0 j)=sharedDiskP544Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP544Value0_0
  · exact sharedDiskP544Value0_1
  · exact sharedDiskP544Value0_2
  · exact sharedDiskP544Value0_3
  · exact sharedDiskP544Value0_4
  · exact sharedDiskP544Value0_5
  · exact sharedDiskP544Value0_6
  · exact sharedDiskP544Value0_7
private theorem sharedDiskP544Value1_0 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP544Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value1_1 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP544Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value1_2 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP544Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value1_3 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP544Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value1_4 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP544Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value1_5 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP544Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value1_6 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP544Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value1_7 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP544Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP544Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 1 j)=sharedDiskP544Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP544Value1_0
  · exact sharedDiskP544Value1_1
  · exact sharedDiskP544Value1_2
  · exact sharedDiskP544Value1_3
  · exact sharedDiskP544Value1_4
  · exact sharedDiskP544Value1_5
  · exact sharedDiskP544Value1_6
  · exact sharedDiskP544Value1_7
private theorem sharedDiskP544Value2_0 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP544Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value2_1 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP544Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value2_2 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP544Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value2_3 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP544Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value2_4 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP544Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value2_5 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP544Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value2_6 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP544Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value2_7 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP544Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP544Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 2 j)=sharedDiskP544Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP544Value2_0
  · exact sharedDiskP544Value2_1
  · exact sharedDiskP544Value2_2
  · exact sharedDiskP544Value2_3
  · exact sharedDiskP544Value2_4
  · exact sharedDiskP544Value2_5
  · exact sharedDiskP544Value2_6
  · exact sharedDiskP544Value2_7
private theorem sharedDiskP544Value3_0 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP544Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value3_1 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP544Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value3_2 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP544Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value3_3 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP544Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value3_4 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP544Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value3_5 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP544Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value3_6 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP544Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value3_7 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP544Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP544Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 3 j)=sharedDiskP544Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP544Value3_0
  · exact sharedDiskP544Value3_1
  · exact sharedDiskP544Value3_2
  · exact sharedDiskP544Value3_3
  · exact sharedDiskP544Value3_4
  · exact sharedDiskP544Value3_5
  · exact sharedDiskP544Value3_6
  · exact sharedDiskP544Value3_7
private theorem sharedDiskP544Value4_0 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP544Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value4_1 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP544Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value4_2 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP544Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value4_3 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP544Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value4_4 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP544Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value4_5 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP544Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value4_6 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP544Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value4_7 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP544Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP544Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 4 j)=sharedDiskP544Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP544Value4_0
  · exact sharedDiskP544Value4_1
  · exact sharedDiskP544Value4_2
  · exact sharedDiskP544Value4_3
  · exact sharedDiskP544Value4_4
  · exact sharedDiskP544Value4_5
  · exact sharedDiskP544Value4_6
  · exact sharedDiskP544Value4_7
private theorem sharedDiskP544Value5_0 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP544Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value5_1 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP544Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value5_2 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP544Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value5_3 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP544Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value5_4 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP544Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value5_5 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP544Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value5_6 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP544Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value5_7 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP544Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP544Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 5 j)=sharedDiskP544Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP544Value5_0
  · exact sharedDiskP544Value5_1
  · exact sharedDiskP544Value5_2
  · exact sharedDiskP544Value5_3
  · exact sharedDiskP544Value5_4
  · exact sharedDiskP544Value5_5
  · exact sharedDiskP544Value5_6
  · exact sharedDiskP544Value5_7
private theorem sharedDiskP544Value6_0 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP544Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value6_1 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP544Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value6_2 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP544Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value6_3 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP544Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value6_4 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP544Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value6_5 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP544Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value6_6 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP544Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value6_7 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP544Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP544Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 6 j)=sharedDiskP544Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP544Value6_0
  · exact sharedDiskP544Value6_1
  · exact sharedDiskP544Value6_2
  · exact sharedDiskP544Value6_3
  · exact sharedDiskP544Value6_4
  · exact sharedDiskP544Value6_5
  · exact sharedDiskP544Value6_6
  · exact sharedDiskP544Value6_7
private theorem sharedDiskP544Value7_0 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP544Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value7_1 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP544Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value7_2 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP544Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value7_3 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP544Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value7_4 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP544Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value7_5 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP544Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value7_6 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP544Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value7_7 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP544Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP544Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 7 j)=sharedDiskP544Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP544Value7_0
  · exact sharedDiskP544Value7_1
  · exact sharedDiskP544Value7_2
  · exact sharedDiskP544Value7_3
  · exact sharedDiskP544Value7_4
  · exact sharedDiskP544Value7_5
  · exact sharedDiskP544Value7_6
  · exact sharedDiskP544Value7_7
private theorem sharedDiskP544Value8_0 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP544Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value8_1 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP544Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value8_2 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP544Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value8_3 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP544Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value8_4 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP544Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value8_5 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP544Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value8_6 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP544Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP544Value8_7 : truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP544Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP544Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points 8 j)=sharedDiskP544Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP544Value8_0
  · exact sharedDiskP544Value8_1
  · exact sharedDiskP544Value8_2
  · exact sharedDiskP544Value8_3
  · exact sharedDiskP544Value8_4
  · exact sharedDiskP544Value8_5
  · exact sharedDiskP544Value8_6
  · exact sharedDiskP544Value8_7
theorem sharedDiskP544Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP544Params (sharedChord521Gauss8Points i j)=sharedDiskP544Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP544Values0_eq
  · exact sharedDiskP544Values1_eq
  · exact sharedDiskP544Values2_eq
  · exact sharedDiskP544Values3_eq
  · exact sharedDiskP544Values4_eq
  · exact sharedDiskP544Values5_eq
  · exact sharedDiskP544Values6_eq
  · exact sharedDiskP544Values7_eq
  · exact sharedDiskP544Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP544Box : HorizontalRectangle := ⟨(333/400),(667/800),(961254129192727/1649267441664000),(962864741928727/1649267441664000),(1696305527284470261588489251732349/10384593717069655257060992658440192),(2695298998470182249803391965535679/5192296858534827628530496329220096),(-4181682411025449075039099136299737/1298074214633706907132624082305024),(-3706005518302366834775835659784921/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP544Grid : CGrid := momentChordGrid sharedDiskP544Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP544Columns : containedInReported sharedDiskP544Grid.re sharedDiskP544Box.reLo sharedDiskP544Box.reHi=true ∧ containedInReported sharedDiskP544Grid.im sharedDiskP544Box.imLo sharedDiskP544Box.imHi=true := by
  rw [sharedDiskP544Grid,momentChordGrid_eq_tabulated sharedDiskP544Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP544Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP544Values_eq]
  decide +kernel
theorem sharedDiskP544Sound : sharedDiskP544Box.Sound := by
  intro t a tl tu al au
  change (((333/400):ℚ):ℝ)≤t at tl
  change t≤(((667/800):ℚ):ℝ) at tu
  change (((961254129192727/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((962864741928727/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP544Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(333/400))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((667/800):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(961254129192727/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((962864741928727/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP544Columns.1 sharedDiskP544Columns.2
def sharedDiskP544Rows : List SignRow := [positive_544.toSignRow]
theorem sharedDiskP544Rows_actual : ∀ r∈sharedDiskP544Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP544Rows.all (sharedDiskP544Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP544Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP545Params : ChordParams := ⟨⟨(-28081221542463034002799),(-27923268040297941484630),true⟩,⟨1891274862630912867166872,1898558858481976289037098,true⟩,⟨133784685994288522879280,134720354960590771112578,true⟩,⟨251397766632007811563819,252917055864714610130690,true⟩,⟨359120689534891512282007,360180967401261134659115,true⟩,⟨1154038316731465059957654,1154340082294096505161852,true⟩,⟨(-2174792397169038045769964),(-2170969040601617726000686),true⟩,⟨⟨1143322905690061897826715,1157763744175621320440779,true⟩,⟨(-55988131),55988131,true⟩⟩⟩
theorem sharedDiskP545Params_ok : chordParams (Grid.ofRats (667/800) (167/200)) (Grid.ofRats (320626730609339/549755813888000) (321163601521339/549755813888000))=sharedDiskP545Params := by decide +kernel
def sharedDiskP545Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3035910011692598598111754),(-2747002382192515449078761),true⟩,⟨(-223822298772571262719477),12237578905281900275604,true⟩⟩
  | 0,1 => ⟨⟨(-2703304096910004031552189),(-2436915174602207294865803),true⟩,⟨(-280289105390455695970545),(-56377648173941451319512),true⟩⟩
  | 0,2 => ⟨⟨(-2462620440950884137130309),(-2214055900198079602243472),true⟩,⟨(-329994936772978974861316),(-117234902478846348269670),true⟩⟩
  | 0,3 => ⟨⟨(-2326891834120117100834527),(-2088779094542228680458783),true⟩,⟨(-361114704150045583035982),(-155241140243650332892588),true⟩⟩
  | 0,4 => ⟨⟨(-3428903208866381496303274),(-3117134710136512003508847),true⟩,⟨(-176422421380081296627869),68238026310049308133660,true⟩⟩
  | 0,5 => ⟨⟨(-3828167987945234386662628),(-3497534460551568245354447),true⟩,⟨(-150610893997594853400629),96382244914825865570984,true⟩⟩
  | 0,6 => ⟨⟨(-4165198118753850867640310),(-3822043097456600271239144),true⟩,⟨(-146856726231129193011847),97482270870711515299509,true⟩⟩
  | 0,7 => ⟨⟨(-4376469758744755897898878),(-4026914039681994128874607),true⟩,⟨(-154655309689223255997178),86768389681813599956381,true⟩⟩
  | 1,0 => ⟨⟨(-1504540772562696701748015),(-1335121677250760007805641),true⟩,⟨(-586275648870448723007636),(-431848035550121418588618),true⟩⟩
  | 1,1 => ⟨⟨(-1323912387976505134482783),(-1169968034565901726599045),true⟩,⟨(-640219746705321735968701),(-498316177512243199115870),true⟩⟩
  | 1,2 => ⟨⟨(-1192556833817567514932483),(-1049704980619938676065956),true⟩,⟨(-679117700927765640867314),(-546312274921999332979176),true⟩⟩
  | 1,3 => ⟨⟨(-1117783240769425426202946),(-981148124492072476680321),true⟩,⟨(-700897001816723352086884),(-573226104593664092554370),true⟩⟩
  | 1,4 => ⟨⟨(-1719522371903409015584100),(-1531615674768491729773737),true⟩,⟨(-522922619041150562100085),(-353868708745685299684170),true⟩⟩
  | 1,5 => ⟨⟨(-1942883565563296603341274),(-1736006681166743259559962),true⟩,⟨(-459736451112803182932641),(-276178662397718137428926),true⟩⟩
  | 1,6 => ⟨⟨(-2137648399664656625821433),(-1914656055121879947500234),true⟩,⟨(-407899809482396399066113),(-212542844910479147015897),true⟩⟩
  | 1,7 => ⟨⟨(-2263461189001252321140811),(-2030349580544670691875253),true⟩,⟨(-376371381384233379974260),(-173909112701200094901341),true⟩⟩
  | 2,0 => ⟨⟨(-284108586072267827473634),(-202599825110630714817394),true⟩,⟨(-892778868439773088230493),(-809975941021025254619938),true⟩⟩
  | 2,1 => ⟨⟨(-104984942979864942768815),(-30487664157482601907368),true⟩,⟨(-914024913928734223281540),(-836781381705753656131133),true⟩⟩
  | 2,2 => ⟨⟨26236157809720280845955,96658251582880345423386,true⟩,⟨(-924146663195318420352400),(-850387203915209592188493),true⟩⟩
  | 2,3 => ⟨⟨101517658464977892905834,170043893820559293660065,true⟩,⟨(-928023681853198334301729),(-856047598945017416737564),true⟩⟩
  | 2,4 => ⟨⟨(-497697699066718975926516),(-406009335484135948313126),true⟩,⟨(-856168337430363483693826),(-765495194205128969120552),true⟩⟩
  | 2,5 => ⟨⟨(-724416135956043540798385),(-618645496842959168633154),true⟩,⟨(-806048502268741065507555),(-704139386743355150737348),true⟩⟩
  | 2,6 => ⟨⟨(-928881528481962916292758),(-807513614173308853093347),true⟩,⟨(-753860472701288569995913),(-638885067904015365970684),true⟩⟩
  | 2,7 => ⟨⟨(-1065300908881342143171108),(-932976061877871330941925),true⟩,⟨(-715950243190397203821090),(-591852134968119143916517),true⟩⟩
  | 3,0 => ⟨⟨1008975565421344182091569,1077621223161691863694898,true⟩,⟨(-937727638605641486927082),(-869523169866498132888186),true⟩⟩
  | 3,1 => ⟨⟨1230793620113971113101324,1302868826432428207156773,true⟩,⟨(-962855922269129289379620),(-892286574994588290509352),true⟩⟩
  | 3,2 => ⟨⟨1402277824978615691027553,1477856946894740184347698,true⟩,⟨(-1001282280023145641996231),(-927921460562468686412946),true⟩⟩
  | 3,3 => ⟨⟨1504820477480353302399661,1582904377509167027355518,true⟩,⟨(-1034723489748112645937894),(-959227660168630353847739),true⟩⟩
  | 3,4 => ⟨⟨759371135028260774892248,825461324711801854246364,true⟩,⟨(-930270931600368098827604),(-863294744731958146509024),true⟩⟩
  | 3,5 => ⟨⟨509628039275085869248789,574465461811270924576662,true⟩,⟨(-932056200994389362502110),(-864957041379998787214965),true⟩⟩
  | 3,6 => ⟨⟨294884640390899307163452,359813467889737731456123,true⟩,⟨(-932479644227485037823233),(-864172452688439859675371),true⟩⟩
  | 3,7 => ⟨⟨154740712765500805262552,222057031158633263109943,true⟩,⟨(-929985493142009770611640),(-859176704181315332108757),true⟩⟩
  | 4,0 => ⟨⟨2252240670227784602019213,2375732714767418814421071,true⟩,⟨(-1728783460877203199957306),(-1607329707527558588196976),true⟩⟩
  | 4,1 => ⟨⟨2420449312964050615547747,2567544297197941913601486,true⟩,⟨(-2174145877827743432087980),(-2026932204561057154402335),true⟩⟩
  | 4,2 => ⟨⟨2493119494739594671590839,2664726427217529086670237,true⟩,⟨(-2666163733491159735754043),(-2491225226731708656843791),true⟩⟩
  | 4,3 => ⟨⟨2486322901637500703362788,2675799156580508336952708,true⟩,⟨(-3037411267711072641256978),(-2841694890294499855186515),true⟩⟩
  | 4,4 => ⟨⟨2035570658393096916541044,2140416124436902920421003,true⟩,⟨(-1408002238664985758037533),(-1306127636451405267450558),true⟩⟩
  | 4,5 => ⟨⟨1824350266658409281513887,1916215553081336504134179,true⟩,⟨(-1210143879777205566470421),(-1121389749270902250296617),true⟩⟩
  | 4,6 => ⟨⟨1656003019108644859801559,1739793058995958004890533,true⟩,⟨(-1102814715632212423266539),(-1021948951318465219570781),true⟩⟩
  | 4,7 => ⟨⟨1554341724783980650130269,1634008895246554108943959,true⟩,⟨(-1054363074093589701854469),(-977422142663708248864661),true⟩⟩
  | 5,0 => ⟨⟨2247034473866276450654212,2481392098775345996550622,true⟩,⟨(-3996552116532441543388065),(-3746647891794037783679491),true⟩⟩
  | 5,1 => ⟨⟨2111639993499786653520798,2359162995183302935901671,true⟩,⟨(-4281361692672794801440996),(-4015016470539062514964133),true⟩⟩
  | 5,2 => ⟨⟨1974793089596370386016184,2233156603659865640806702,true⟩,⟨(-4515908048932650375559281),(-4235831147490228626885133),true⟩⟩
  | 5,3 => ⟨⟨1877975900190398976294926,2143021158516632378152553,true⟩,⟨(-4660228361886558223559707),(-4371597176717147192474141),true⟩⟩
  | 5,4 => ⟨⟨2352876356979991672327755,2573854593178966038736771,true⟩,⟨(-3708023305552977921709500),(-3474570771880071214529577),true⟩⟩
  | 5,5 => ⟨⟨2421025556640999987750411,2630273308527884721888494,true⟩,⟨(-3456506606383409872539014),(-3237269438191501888082752),true⟩⟩
  | 5,6 => ⟨⟨2457554166471614011014606,2658029230567727414007088,true⟩,⟨(-3269674814921809591005210),(-3060942014685153116456616),true⟩⟩
  | 5,7 => ⟨⟨2473152206970628495144014,2668557154879153314847568,true⟩,⟨(-3162306577259877780775865),(-2959595236401669375780302),true⟩⟩
  | 6,0 => ⟨⟨726614681965220133184583,1049813517709428790794481,true⟩,⟨(-5717237522781249705640096),(-5357093657135762701937270),true⟩⟩
  | 6,1 => ⟨⟨244358093377338278528778,591384209252207782043896,true⟩,⟨(-5960112204603935057464382),(-5575899585436722223144019),true⟩⟩
  | 6,2 => ⟨⟨(-190757879386198489944040),175897986236230454521526,true⟩,⟨(-6113716994249374102747578),(-5711066773442184717076636),true⟩⟩
  | 6,3 => ⟨⟨(-475352845915815716761176),(-96365706244400485223989),true⟩,⟨(-6184599660958932671578585),(-5771371533059755806691797),true⟩⟩
  | 6,4 => ⟨⟨1162429407937431690871567,1463427060660609857392554,true⟩,⟨(-5416825343191339768896519),(-5081164621888790692265589),true⟩⟩
  | 6,5 => ⟨⟨1494063556701966246066199,1780485195730201659581402,true⟩,⟨(-5118584090328869000690098),(-4802089916209295945135576),true⟩⟩
  | 6,6 => ⟨⟨1712380169335357897632049,1987487655165708684042039,true⟩,⟨(-4876817924225098110292753),(-4575168539842504872250944),true⟩⟩
  | 6,7 => ⟨⟨1826823747502659975650090,2095142112810096865834614,true⟩,⟨(-4730800949728673555454254),(-4437953388873693867499765),true⟩⟩
  | 7,0 => ⟨⟨(-2951071926024209537077803),(-2488929510464386947612399),true⟩,⟨(-5908903546256694781738988),(-5448940307828042557446176),true⟩⟩
  | 7,1 => ⟨⟨(-3644648372082654708402133),(-3169094857012647156494616),true⟩,⟨(-5499370242421123451233085),(-5043851814298458547755022),true⟩⟩
  | 7,2 => ⟨⟨(-4142533041384595580524798),(-3661870859788920129085873),true⟩,⟨(-5061487253330450206786631),(-4617122411900503462134157),true⟩⟩
  | 7,3 => ⟨⟨(-4409701878769960020130103),(-3928755701032611834023032),true⟩,⟨(-4751708012492385820281110),(-4317555938496059289099493),true⟩⟩
  | 7,4 => ⟨⟨(-2174964033739246462204913),(-1733694033231471963610114),true⟩,⟨(-6171800950485264043986539),(-5717368195792450403791299),true⟩⟩
  | 7,5 => ⟨⟨(-1462579475415337073393192),(-1044766483645907975135682),true⟩,⟨(-6266532700565789374362223),(-5824827651784418812760679),true⟩⟩
  | 7,6 => ⟨⟨(-925987799319717572484097),(-528350651350990969845964),true⟩,⟨(-6252768961653118501200855),(-5824993926530919089884003),true⟩⟩
  | 7,7 => ⟨⟨(-619086430266180489976236),(-233974737222216399620568),true⟩,⟨(-6212085553026138864561083),(-5793930073949108531771413),true⟩⟩
  | 8,0 => ⟨⟨(-5173857553403769639178404),(-4768866709678363270725725),true⟩,⟨(-1800998887626616885628138),(-1517217586781290431995054),true⟩⟩
  | 8,1 => ⟨⟨(-4951072678154909584043037),(-4589567899337384156034257),true⟩,⟨(-988894335796583663269378),(-760214333017241409698282),true⟩⟩
  | 8,2 => ⟨⟨(-4663636330489145269278247),(-4340433953686831672006608),true⟩,⟨(-420221950306048517610786),(-234025728638912718519912),true⟩⟩
  | 8,3 => ⟨⟨(-4453060263459584087720150),(-4154181745150413317519888),true⟩,⟨(-117950058242912048810724),45061151212149537617362,true⟩⟩
  | 8,4 => ⟨⟨(-5204183101218302255165726),(-4761880377819882296240550),true⟩,⟨(-2733795027093142306132003),(-2393887899257555009398837),true⟩⟩
  | 8,5 => ⟨⟨(-5024845853165509386244083),(-4558703264239073009342695),true⟩,⟨(-3596884726015152834347601),(-3211768742107155741758585),true⟩⟩
  | 8,6 => ⟨⟨(-4747373601427365797462023),(-4270335913375602886523270),true⟩,⟨(-4235739968056067981370624),(-3821642569810512424807227),true⟩⟩
  | 8,7 => ⟨⟨(-4528399291065395032776081),(-4048143202236011785279648),true⟩,⟨(-4590000545569642079490718),(-4161763315515139576668626),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP545Value0_0 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP545Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value0_1 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP545Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value0_2 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP545Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value0_3 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP545Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value0_4 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP545Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value0_5 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP545Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value0_6 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP545Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value0_7 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP545Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP545Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 0 j)=sharedDiskP545Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP545Value0_0
  · exact sharedDiskP545Value0_1
  · exact sharedDiskP545Value0_2
  · exact sharedDiskP545Value0_3
  · exact sharedDiskP545Value0_4
  · exact sharedDiskP545Value0_5
  · exact sharedDiskP545Value0_6
  · exact sharedDiskP545Value0_7
private theorem sharedDiskP545Value1_0 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP545Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value1_1 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP545Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value1_2 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP545Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value1_3 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP545Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value1_4 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP545Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value1_5 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP545Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value1_6 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP545Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value1_7 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP545Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP545Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 1 j)=sharedDiskP545Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP545Value1_0
  · exact sharedDiskP545Value1_1
  · exact sharedDiskP545Value1_2
  · exact sharedDiskP545Value1_3
  · exact sharedDiskP545Value1_4
  · exact sharedDiskP545Value1_5
  · exact sharedDiskP545Value1_6
  · exact sharedDiskP545Value1_7
private theorem sharedDiskP545Value2_0 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP545Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value2_1 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP545Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value2_2 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP545Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value2_3 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP545Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value2_4 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP545Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value2_5 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP545Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value2_6 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP545Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value2_7 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP545Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP545Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 2 j)=sharedDiskP545Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP545Value2_0
  · exact sharedDiskP545Value2_1
  · exact sharedDiskP545Value2_2
  · exact sharedDiskP545Value2_3
  · exact sharedDiskP545Value2_4
  · exact sharedDiskP545Value2_5
  · exact sharedDiskP545Value2_6
  · exact sharedDiskP545Value2_7
private theorem sharedDiskP545Value3_0 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP545Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value3_1 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP545Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value3_2 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP545Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value3_3 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP545Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value3_4 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP545Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value3_5 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP545Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value3_6 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP545Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value3_7 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP545Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP545Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 3 j)=sharedDiskP545Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP545Value3_0
  · exact sharedDiskP545Value3_1
  · exact sharedDiskP545Value3_2
  · exact sharedDiskP545Value3_3
  · exact sharedDiskP545Value3_4
  · exact sharedDiskP545Value3_5
  · exact sharedDiskP545Value3_6
  · exact sharedDiskP545Value3_7
private theorem sharedDiskP545Value4_0 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP545Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value4_1 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP545Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value4_2 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP545Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value4_3 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP545Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value4_4 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP545Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value4_5 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP545Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value4_6 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP545Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value4_7 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP545Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP545Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 4 j)=sharedDiskP545Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP545Value4_0
  · exact sharedDiskP545Value4_1
  · exact sharedDiskP545Value4_2
  · exact sharedDiskP545Value4_3
  · exact sharedDiskP545Value4_4
  · exact sharedDiskP545Value4_5
  · exact sharedDiskP545Value4_6
  · exact sharedDiskP545Value4_7
private theorem sharedDiskP545Value5_0 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP545Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value5_1 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP545Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value5_2 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP545Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value5_3 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP545Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value5_4 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP545Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value5_5 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP545Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value5_6 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP545Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value5_7 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP545Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP545Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 5 j)=sharedDiskP545Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP545Value5_0
  · exact sharedDiskP545Value5_1
  · exact sharedDiskP545Value5_2
  · exact sharedDiskP545Value5_3
  · exact sharedDiskP545Value5_4
  · exact sharedDiskP545Value5_5
  · exact sharedDiskP545Value5_6
  · exact sharedDiskP545Value5_7
private theorem sharedDiskP545Value6_0 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP545Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value6_1 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP545Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value6_2 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP545Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value6_3 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP545Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value6_4 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP545Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value6_5 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP545Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value6_6 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP545Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value6_7 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP545Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP545Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 6 j)=sharedDiskP545Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP545Value6_0
  · exact sharedDiskP545Value6_1
  · exact sharedDiskP545Value6_2
  · exact sharedDiskP545Value6_3
  · exact sharedDiskP545Value6_4
  · exact sharedDiskP545Value6_5
  · exact sharedDiskP545Value6_6
  · exact sharedDiskP545Value6_7
private theorem sharedDiskP545Value7_0 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP545Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value7_1 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP545Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value7_2 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP545Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value7_3 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP545Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value7_4 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP545Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value7_5 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP545Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value7_6 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP545Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value7_7 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP545Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP545Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 7 j)=sharedDiskP545Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP545Value7_0
  · exact sharedDiskP545Value7_1
  · exact sharedDiskP545Value7_2
  · exact sharedDiskP545Value7_3
  · exact sharedDiskP545Value7_4
  · exact sharedDiskP545Value7_5
  · exact sharedDiskP545Value7_6
  · exact sharedDiskP545Value7_7
private theorem sharedDiskP545Value8_0 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP545Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value8_1 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP545Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value8_2 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP545Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value8_3 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP545Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value8_4 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP545Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value8_5 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP545Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value8_6 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP545Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP545Value8_7 : truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP545Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP545Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points 8 j)=sharedDiskP545Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP545Value8_0
  · exact sharedDiskP545Value8_1
  · exact sharedDiskP545Value8_2
  · exact sharedDiskP545Value8_3
  · exact sharedDiskP545Value8_4
  · exact sharedDiskP545Value8_5
  · exact sharedDiskP545Value8_6
  · exact sharedDiskP545Value8_7
theorem sharedDiskP545Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP545Params (sharedChord521Gauss8Points i j)=sharedDiskP545Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP545Values0_eq
  · exact sharedDiskP545Values1_eq
  · exact sharedDiskP545Values2_eq
  · exact sharedDiskP545Values3_eq
  · exact sharedDiskP545Values4_eq
  · exact sharedDiskP545Values5_eq
  · exact sharedDiskP545Values6_eq
  · exact sharedDiskP545Values7_eq
  · exact sharedDiskP545Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP545Box : HorizontalRectangle := ⟨(667/800),(167/200),(320626730609339/549755813888000),(321163601521339/549755813888000),(1566209809077775164011177442478813/10384593717069655257060992658440192),(2622745724097443331812015768438127/5192296858534827628530496329220096),(-2089919893557554385452210140302505/649037107316853453566312041152512),(-1853007798392319716168331462790313/649037107316853453566312041152512),true,[]⟩
noncomputable def sharedDiskP545Grid : CGrid := momentChordGrid sharedDiskP545Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP545Columns : containedInReported sharedDiskP545Grid.re sharedDiskP545Box.reLo sharedDiskP545Box.reHi=true ∧ containedInReported sharedDiskP545Grid.im sharedDiskP545Box.imLo sharedDiskP545Box.imHi=true := by
  rw [sharedDiskP545Grid,momentChordGrid_eq_tabulated sharedDiskP545Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP545Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP545Values_eq]
  decide +kernel
theorem sharedDiskP545Sound : sharedDiskP545Box.Sound := by
  intro t a tl tu al au
  change (((667/800):ℚ):ℝ)≤t at tl
  change t≤(((167/200):ℚ):ℝ) at tu
  change (((320626730609339/549755813888000):ℚ):ℝ)≤a at al
  change a≤(((321163601521339/549755813888000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP545Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(667/800))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((167/200):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(320626730609339/549755813888000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((321163601521339/549755813888000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP545Columns.1 sharedDiskP545Columns.2
def sharedDiskP545Rows : List SignRow := [positive_545.toSignRow]
theorem sharedDiskP545Rows_actual : ∀ r∈sharedDiskP545Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP545Rows.all (sharedDiskP545Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP545Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP546Params : ChordParams := ⟨⟨(-28239592324432526845030),(-28081221542463034002216),true⟩,⟨1886719711719830179617024,1893985984297297574377336,true⟩,⟨134034249639088713760486,134969881921049435001357,true⟩,⟨252350502801947284962962,253871827893286310714245,true⟩,⟨360088874633735785885788,361149081832413294113483,true⟩,⟨1153735831328601702836388,1154038316731465059958770,true⟩,⟨(-2170969040601617726009702),(-2167155761964273800108053),true⟩,⟨⟨1142972607893532352070693,1157420946813192142493332,true⟩,⟨(-59463091),59463091,true⟩⟩⟩
theorem sharedDiskP546Params_ok : chordParams (Grid.ofRats (167/200) (669/800)) (Grid.ofRats (962507751314657/1649267441664000) (964118364050657/1649267441664000))=sharedDiskP546Params := by decide +kernel
def sharedDiskP546Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3034874616875577934614824),(-2745549313593357286178289),true⟩,⟨(-222979231645628654067942),13485947212807519953627,true⟩⟩
  | 0,1 => ⟨⟨(-2703558514315663034376863),(-2436694926679698632311317),true⟩,⟨(-278946408736325760539802),(-54592984559283137592476),true⟩⟩
  | 0,2 => ⟨⟨(-2463695669766055200142378),(-2214635976764211882054878),true⟩,⟨(-328286217596414132147534),(-115083592084912620627272),true⟩⟩
  | 0,3 => ⟨⟨(-2328400289738138576193520),(-2089777094013172083709525),true⟩,⟨(-359205025486677247730648),(-152876721210687193489404),true⟩⟩
  | 0,4 => ⟨⟨(-3426152747911764697793885),(-3114039354679558789082280),true⟩,⟨(-176113888653088436602674),68917651967863751680289,true⟩⟩
  | 0,5 => ⟨⟨(-3823484203950637769316534),(-3492579429441836499033926),true⟩,⟨(-150734238451391276457745),96625077820472377428188,true⟩⟩
  | 0,6 => ⟨⟨(-4158754142510601630335256),(-3815385457968553776408508),true⟩,⟨(-147226539273478095607677),97487522108712575621367,true⟩⟩
  | 0,7 => ⟨⟨(-4368869283787884012678837),(-4019135119665976863364531),true⟩,⟨(-155125926151249983056077),86703013473124166220192,true⟩⟩
  | 1,0 => ⟨⟨(-1508141253361241134344675),(-1338184370242366303138458),true⟩,⟨(-583469355401788994041566),(-428563982992695789307187),true⟩⟩
  | 1,1 => ⟨⟨(-1327870427206677976715886),(-1173400024533663408165022),true⟩,⟨(-637348642369776782342150),(-494979274525596682901813),true⟩⟩
  | 1,2 => ⟨⟨(-1196759478843151654335044),(-1053394015688304735454240),true⟩,⟨(-676243023489650781685465),(-542984526148200191791769),true⟩⟩
  | 1,3 => ⟨⟨(-1122120638584759375993909),(-984980313944772572268626),true⟩,⟨(-698038262234837087921304),(-569922894275412678932302),true⟩⟩
  | 1,4 => ⟨⟨(-1722656532234648479651678),(-1534206712254368178292508),true⟩,⟨(-520270792824648723449711),(-350733686022730644201388),true⟩⟩
  | 1,5 => ⟨⟨(-1945476742876876006932536),(-1738061054059651336430248),true⟩,⟨(-457315899254949245771673),(-273278850206479612654247),true⟩⟩
  | 1,6 => ⟨⟨(-2139716978507207670043458),(-1916197186284287685844428),true⟩,⟨(-405724691497004932241242),(-209898621778717261836811),true⟩⟩
  | 1,7 => ⟨⟨(-2265163043229075304381456),(-2031534683556458935312011),true⟩,⟨(-374370432942036016912099),(-171448212149076949174296),true⟩⟩
  | 2,0 => ⟨⟨(-289847418087293247040805),(-208050789252448168749895),true⟩,⟨(-891036634338647867273381),(-808007581532305644077017),true⟩⟩
  | 2,1 => ⟨⟨(-111041059679388291515310),(-36287477789986128450884),true⟩,⟨(-912751159977840734091943),(-835303638228277769179269),true⟩⟩
  | 2,2 => ⟨⟨19959182225882390558378,90595966833525566647128,true⟩,⟨(-923249585315874958309275),(-849299008472213734308568),true⟩⟩
  | 2,3 => ⟨⟨95109553405520652465703,163839795838440152664334,true⟩,⟨(-927352655024646243837833),(-855191550304871083030311),true⟩⟩
  | 2,4 => ⟨⟨(-503064380956962367193587),(-411044670969832720833470),true⟩,⟨(-853956562404977658187859),(-763024784767472329381891),true⟩⟩
  | 2,5 => ⟨⟨(-729434117718617403358503),(-623213632719048648149755),true⟩,⟨(-803509902705293429068121),(-701212462329658756099713),true⟩⟩
  | 2,6 => ⟨⟨(-933549404471730816246548),(-811701033560593666680364),true⟩,⟨(-751104421514355520421083),(-635709805040441557950069),true⟩⟩
  | 2,7 => ⟨⟨(-1069731341233755251584118),(-936907695191636171768041),true⟩,⟨(-713110883620192672901251),(-588574860402140383756317),true⟩⟩
  | 3,0 => ⟨⟨1001425955169892032037156,1070130723350112174577486,true⟩,⟨(-939892628052464255380435),(-871582945278722415279547),true⟩⟩
  | 3,1 => ⟨⟨1223105769124106241401427,1295249007341787004097966,true⟩,⟨(-965706633246924360391653),(-895018636342307484077667),true⟩⟩
  | 3,2 => ⟨⟨1394504094736424786783516,1470163188985661539280840,true⟩,⟨(-1004669677748638177574135),(-931175516738942455523544),true⟩⟩
  | 3,3 => ⟨⟨1496993352172872698394872,1575166401450115798498775,true⟩,⟨(-1038440165132816672996222),(-962800377968773648921960),true⟩⟩
  | 3,4 => ⟨⟨752047681657756638501215,818196139569655232376132,true⟩,⟨(-931655157284282095758974),(-864581357464255961614224),true⟩⟩
  | 3,5 => ⟨⟨502616794986475279869425,567521962288967455770448,true⟩,⟨(-932642479295042561905084),(-865444972201230660532465),true⟩⟩
  | 3,6 => ⟨⟨288152240382029746184182,353214543190732093628788,true⟩,⟨(-932410781416294807213623),(-863963235391761585260666),true⟩⟩
  | 3,7 => ⟨⟨148241230309248802764542,215754606340788969842341,true⟩,⟨(-929477597390133919731659),(-858487534435411936752951),true⟩⟩
  | 4,0 => ⟨⟨2242877145111795123084995,2366544506427136138046089,true⟩,⟨(-1735444071403085821288254),(-1613727489448107716143795),true⟩⟩
  | 4,1 => ⟨⟨2409578820975818826159073,2556881238780999924922523,true⟩,⟨(-2181708472019223364475743),(-2034184211644708681882545),true⟩⟩
  | 4,2 => ⟨⟨2480297959996761668621882,2652130502193797482318424,true⟩,⟨(-2674188577956034270464500),(-2498906788780844037752998),true⟩⟩
  | 4,3 => ⟨⟨2471897287895419551929301,2661600863866104164712144,true⟩,⟨(-3045424993049230273834542),(-2849355001600143302392067),true⟩⟩
  | 4,4 => ⟨⟨2027069151581270140041436,2132056857411411215156500,true⟩,⟨(-1413669303372882709197489),(-1311577828865894952134874),true⟩⟩
  | 4,5 => ⟨⟨1816253069122855605169263,1908235238017885999291879,true⟩,⟨(-1214970211711179321269539),(-1126033820179000827888832),true⟩⟩
  | 4,6 => ⟨⟨1648078023628839607212248,1731969124785126363293542,true⟩,⟨(-1107037431955197620485905),(-1026011330813315058523418),true⟩⟩
  | 4,7 => ⟨⟨1546486015010314660806617,1626246473497111138216801,true⟩,⟨(-1058242391234262044038114),(-981152244158709667121843),true⟩⟩
  | 5,0 => ⟨⟨2228232464964725560371785,2462770216416663600386511,true⟩,⟨(-4003000691054258365161676),(-3752781123248281280238690),true⟩⟩
  | 5,1 => ⟨⟨2091546456912381675475453,2339219360789990972263007,true⟩,⟨(-4286864409473053177964278),(-4020236553209853867160650),true⟩⟩
  | 5,2 => ⟨⟨1953665996717138194309529,2212147971621559013669801,true⟩,⟨(-4520438133477144296938222),(-4240114496250246061466374),true⟩⟩
  | 5,3 => ⟨⟨1856233622215318180688449,2121374745466760717419225,true⟩,⟨(-4664064123001813531372536),(-4375212812164276216005542),true⟩⟩
  | 5,4 => ⟨⟨2335401464464656015372730,2556582403373379628021399,true⟩,⟨(-3715191698050788830573285),(-3481401456273310366007020),true⟩⟩
  | 5,5 => ⟨⟨2404707200789881069258451,2614171261219666132029104,true⟩,⟨(-3464122097356809144160323),(-3244535679438280324241737),true⟩⟩
  | 5,6 => ⟨⟨2442087181705292048579114,2642785211654861929490229,true⟩,⟨(-3277519859956786455014829),(-3068433663242583167825274),true⟩⟩
  | 5,7 => ⟨⟨2458169430147687369341505,2653799888157799627813125,true⟩,⟨(-3170245407766088845285673),(-2967179906831242083640406),true⟩⟩
  | 6,0 => ⟨⟨701289386086609108258200,1024824842979334554513602,true⟩,⟨(-5713005794436417995858083),(-5352684715164820813300691),true⟩⟩
  | 6,1 => ⟨⟨219005123621469172390412,566268632074340748915595,true⟩,⟨(-5952597442129155711558426),(-5568359003614830310364710),true⟩⟩
  | 6,2 => ⟨⟨(-215679789280884904837898),151157919697019475213006,true⟩,⟨(-6103362968901860101206943),(-5700829909210057513315004),true⟩⟩
  | 6,3 => ⟨⟨(-499733600481624034180208),(-120592422713314059904806),true⟩,⟨(-6172465569335540389445934),(-5759450242291623015303955),true⟩⟩
  | 6,4 => ⟨⟨1137720906313007279045349,1438890582878116640351711,true⟩,⟨(-5415649189443105558931662),(-5079831780947493025440520),true⟩⟩
  | 6,5 => ⟨⟨1470536581266377295070924,1756962962876409883295282,true⟩,⟨(-5119645957287842945238495),(-4803043688371109923876871),true⟩⟩
  | 6,6 => ⟨⟨1689756162944979871897782,1964920424155476796877520,true⟩,⟨(-4879459328239570847796135),(-4577637067230053352487996),true⟩⟩
  | 6,7 => ⟨⟨1804788056922565029256622,2073190262757379861294607,true⟩,⟨(-4734268483081572638244084),(-4441215180704785050555860),true⟩⟩
  | 7,0 => ⟨⟨(-2964124830327341241029397),(-2502571952300143083089050),true⟩,⟨(-5885148701805325012435511),(-5426217907448390441817694),true⟩⟩
  | 7,1 => ⟨⟨(-3652474888521252301359874),(-3177743477213781094842140),true⟩,⟨(-5474341977158474291039991),(-5020042462411784197710208),true⟩⟩
  | 7,2 => ⟨⟨(-4145968149178202380608011),(-3666294305149704969213079),true⟩,⟨(-5036529323027321457899547),(-4593483586509524271908334),true⟩⟩
  | 7,3 => ⟨⟨(-4410509561651511233516100),(-3930637862441865837072946),true⟩,⟨(-4727299731823671167664026),(-4294500642714315004186978),true⟩⟩
  | 7,4 => ⟨⟨(-2192784175329158741773454),(-1751851851562688686298404),true⟩,⟨(-6150744591098595065349155),(-5697100847723595740467679),true⟩⟩
  | 7,5 => ⟨⟨(-1483811108105581544781482),(-1066117862512088969857030),true⟩,⟨(-6248802754552887887116390),(-5807647576125525824264095),true⟩⟩
  | 7,6 => ⟨⟨(-949167427064073861967381),(-551496625659403882136836),true⟩,⟨(-6237958777525975341783693),(-5810550042945584557952435),true⟩⟩
  | 7,7 => ⟨⟨(-643128810100655229601935),(-257900569499984140257951),true⟩,⟨(-6199077882835224928321001),(-5781183960914330590269794),true⟩⟩
  | 8,0 => ⟨⟨(-5162553747635714379330803),(-4758672999624688349442281),true⟩,⟨(-1790513027847224299657379),(-1507606804103839784824972),true⟩⟩
  | 8,1 => ⟨⟨(-4940103090835214109822991),(-4579503663207704177665866),true⟩,⟨(-983281401093112262314744),(-755179499132339050543812),true⟩⟩
  | 8,2 => ⟨⟨(-4653965781512895450895579),(-4331472619602932754834096),true⟩,⟨(-417923128249292226142550),(-232083675821538574899631),true⟩⟩
  | 8,3 => ⟨⟨(-4444502909668846672747419),(-4146204661113743562463672),true⟩,⟨(-117306337340637058058256),45490208372866110645770,true⟩⟩
  | 8,4 => ⟨⟨(-5194466423945410349729112),(-4753393975000200705073287),true⟩,⟨(-2717927589354456088278721),(-2379162150678443752485155),true⟩⟩
  | 8,5 => ⟨⟨(-5018390128112163530552947),(-4553485331408950713694951),true⟩,⟨(-3576625994038244765925655),(-3192815112830892382057585),true⟩⟩
  | 8,6 => ⟨⟨(-4744488402092866127727366),(-4268625521149441534681602),true⟩,⟨(-4212856530791619967778787),(-3800119802355217830309942),true⟩⟩
  | 8,7 => ⟨⟨(-4527964024974585034922725),(-4048819192308143933865374),true⟩,⟨(-4565998643443032125018528),(-4139122720643233715832135),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP546Value0_0 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP546Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value0_1 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP546Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value0_2 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP546Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value0_3 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP546Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value0_4 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP546Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value0_5 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP546Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value0_6 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP546Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value0_7 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP546Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP546Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 0 j)=sharedDiskP546Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP546Value0_0
  · exact sharedDiskP546Value0_1
  · exact sharedDiskP546Value0_2
  · exact sharedDiskP546Value0_3
  · exact sharedDiskP546Value0_4
  · exact sharedDiskP546Value0_5
  · exact sharedDiskP546Value0_6
  · exact sharedDiskP546Value0_7
private theorem sharedDiskP546Value1_0 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP546Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value1_1 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP546Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value1_2 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP546Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value1_3 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP546Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value1_4 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP546Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value1_5 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP546Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value1_6 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP546Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value1_7 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP546Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP546Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 1 j)=sharedDiskP546Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP546Value1_0
  · exact sharedDiskP546Value1_1
  · exact sharedDiskP546Value1_2
  · exact sharedDiskP546Value1_3
  · exact sharedDiskP546Value1_4
  · exact sharedDiskP546Value1_5
  · exact sharedDiskP546Value1_6
  · exact sharedDiskP546Value1_7
private theorem sharedDiskP546Value2_0 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP546Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value2_1 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP546Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value2_2 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP546Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value2_3 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP546Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value2_4 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP546Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value2_5 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP546Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value2_6 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP546Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value2_7 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP546Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP546Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 2 j)=sharedDiskP546Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP546Value2_0
  · exact sharedDiskP546Value2_1
  · exact sharedDiskP546Value2_2
  · exact sharedDiskP546Value2_3
  · exact sharedDiskP546Value2_4
  · exact sharedDiskP546Value2_5
  · exact sharedDiskP546Value2_6
  · exact sharedDiskP546Value2_7
private theorem sharedDiskP546Value3_0 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP546Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value3_1 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP546Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value3_2 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP546Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value3_3 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP546Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value3_4 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP546Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value3_5 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP546Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value3_6 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP546Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value3_7 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP546Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP546Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 3 j)=sharedDiskP546Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP546Value3_0
  · exact sharedDiskP546Value3_1
  · exact sharedDiskP546Value3_2
  · exact sharedDiskP546Value3_3
  · exact sharedDiskP546Value3_4
  · exact sharedDiskP546Value3_5
  · exact sharedDiskP546Value3_6
  · exact sharedDiskP546Value3_7
private theorem sharedDiskP546Value4_0 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP546Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value4_1 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP546Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value4_2 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP546Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value4_3 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP546Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value4_4 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP546Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value4_5 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP546Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value4_6 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP546Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value4_7 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP546Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP546Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 4 j)=sharedDiskP546Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP546Value4_0
  · exact sharedDiskP546Value4_1
  · exact sharedDiskP546Value4_2
  · exact sharedDiskP546Value4_3
  · exact sharedDiskP546Value4_4
  · exact sharedDiskP546Value4_5
  · exact sharedDiskP546Value4_6
  · exact sharedDiskP546Value4_7
private theorem sharedDiskP546Value5_0 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP546Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value5_1 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP546Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value5_2 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP546Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value5_3 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP546Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value5_4 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP546Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value5_5 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP546Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value5_6 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP546Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value5_7 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP546Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP546Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 5 j)=sharedDiskP546Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP546Value5_0
  · exact sharedDiskP546Value5_1
  · exact sharedDiskP546Value5_2
  · exact sharedDiskP546Value5_3
  · exact sharedDiskP546Value5_4
  · exact sharedDiskP546Value5_5
  · exact sharedDiskP546Value5_6
  · exact sharedDiskP546Value5_7
private theorem sharedDiskP546Value6_0 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP546Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value6_1 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP546Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value6_2 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP546Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value6_3 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP546Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value6_4 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP546Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value6_5 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP546Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value6_6 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP546Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value6_7 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP546Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP546Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 6 j)=sharedDiskP546Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP546Value6_0
  · exact sharedDiskP546Value6_1
  · exact sharedDiskP546Value6_2
  · exact sharedDiskP546Value6_3
  · exact sharedDiskP546Value6_4
  · exact sharedDiskP546Value6_5
  · exact sharedDiskP546Value6_6
  · exact sharedDiskP546Value6_7
private theorem sharedDiskP546Value7_0 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP546Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value7_1 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP546Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value7_2 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP546Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value7_3 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP546Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value7_4 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP546Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value7_5 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP546Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value7_6 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP546Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value7_7 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP546Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP546Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 7 j)=sharedDiskP546Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP546Value7_0
  · exact sharedDiskP546Value7_1
  · exact sharedDiskP546Value7_2
  · exact sharedDiskP546Value7_3
  · exact sharedDiskP546Value7_4
  · exact sharedDiskP546Value7_5
  · exact sharedDiskP546Value7_6
  · exact sharedDiskP546Value7_7
private theorem sharedDiskP546Value8_0 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP546Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value8_1 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP546Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value8_2 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP546Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value8_3 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP546Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value8_4 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP546Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value8_5 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP546Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value8_6 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP546Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP546Value8_7 : truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP546Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP546Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points 8 j)=sharedDiskP546Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP546Value8_0
  · exact sharedDiskP546Value8_1
  · exact sharedDiskP546Value8_2
  · exact sharedDiskP546Value8_3
  · exact sharedDiskP546Value8_4
  · exact sharedDiskP546Value8_5
  · exact sharedDiskP546Value8_6
  · exact sharedDiskP546Value8_7
theorem sharedDiskP546Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP546Params (sharedChord521Gauss8Points i j)=sharedDiskP546Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP546Values0_eq
  · exact sharedDiskP546Values1_eq
  · exact sharedDiskP546Values2_eq
  · exact sharedDiskP546Values3_eq
  · exact sharedDiskP546Values4_eq
  · exact sharedDiskP546Values5_eq
  · exact sharedDiskP546Values6_eq
  · exact sharedDiskP546Values7_eq
  · exact sharedDiskP546Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP546Box : HorizontalRectangle := ⟨(167/200),(669/800),(962507751314657/1649267441664000),(964118364050657/1649267441664000),(1436264054802574120306007805418271/10384593717069655257060992658440192),(5100797388876187115926483809229599/10384593717069655257060992658440192),(-2088973736386897029190110702760205/649037107316853453566312041152512),(-1852970700245276498001927382528269/649037107316853453566312041152512),true,[]⟩
noncomputable def sharedDiskP546Grid : CGrid := momentChordGrid sharedDiskP546Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP546Columns : containedInReported sharedDiskP546Grid.re sharedDiskP546Box.reLo sharedDiskP546Box.reHi=true ∧ containedInReported sharedDiskP546Grid.im sharedDiskP546Box.imLo sharedDiskP546Box.imHi=true := by
  rw [sharedDiskP546Grid,momentChordGrid_eq_tabulated sharedDiskP546Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP546Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP546Values_eq]
  decide +kernel
theorem sharedDiskP546Sound : sharedDiskP546Box.Sound := by
  intro t a tl tu al au
  change (((167/200):ℚ):ℝ)≤t at tl
  change t≤(((669/800):ℚ):ℝ) at tu
  change (((962507751314657/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((964118364050657/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP546Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(167/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((669/800):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(962507751314657/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((964118364050657/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP546Columns.1 sharedDiskP546Columns.2
def sharedDiskP546Rows : List SignRow := [positive_546.toSignRow]
theorem sharedDiskP546Rows_actual : ∀ r∈sharedDiskP546Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP546Rows.all (sharedDiskP546Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP546Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP543Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP544Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP545Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP546Rows_actual
