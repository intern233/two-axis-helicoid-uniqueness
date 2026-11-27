import TwoAxisHelicoid.PdfSharedChord493Gauss8
import TwoAxisHelicoid.PdfSharedChord493Disks

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP493Params : ChordParams := ⟨⟨(-10355301624808752221592),(-9270165264322248947326),true⟩,⟨2631242692799986480441591,2750261597609105345108391,true⟩,⟨85964182741115032902036,95655958582392096941405,true⟩,⟨124278425929753393067960,137136194096695030260787,true⟩,⟨209927514674177675726745,222071940883877386587581,true⟩,⟨1188391110619212476355800,1190526576341392739903106,true⟩,⟨(-2899340733439943857683825),(-2828364229327828210647342),true⟩,⟨⟨1122615292887647528754107,1259603907481231683077603,true⟩,⟨(-1448),1448,true⟩⟩⟩
theorem sharedDiskP493Params_ok : chordParams (Grid.ofRats (129/200) (33/50)) (Grid.ofRats (878940159632233/1649267441664000) (298379040327903/549755813888000))=sharedDiskP493Params := by decide +kernel
def sharedDiskP493Values (i : Fin 13) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-6779065323490376127392287),(-2288567430722748074719448),true⟩,⟨(-1976817680045618814412231),1956446644902927534644062,true⟩⟩
  | 0,1 => ⟨⟨(-6221703855421365443440511),(-1997614402469700586097547),true⟩,⟨(-1996122634120021619134585),1747864637374024113914333,true⟩⟩
  | 0,2 => ⟨⟨(-5795994228947562468437721),(-1791853794461693810145650),true⟩,⟨(-2006234450888752395494845),1557198742539863566061890,true⟩⟩
  | 0,3 => ⟨⟨(-5546962812054686637131915),(-1676915932118131108510240),true⟩,⟨(-2011818121726193009884435),1435400032970694963947341,true⟩⟩
  | 0,4 => ⟨⟨(-7396393075992217891056972),(-2639607331234023670334046),true⟩,⟨(-1947646335568177400010173),2119964853862206344694091,true⟩⟩
  | 0,5 => ⟨⟨(-7984378118921455494541282),(-2997139457692982140807024),true⟩,⟨(-1913300103812346617360492),2195732395696411957739154,true⟩⟩
  | 0,6 => ⟨⟨(-8455098849166924239650519),(-3319681118819157602382063),true⟩,⟨(-1882636792462227845820946),2191367016335805486104549,true⟩⟩
  | 0,7 => ⟨⟨(-8740023440791107519758409),(-3531238592945551808810793),true⟩,⟨(-1863494619921339445705851),2157960190462703462391298,true⟩⟩
  | 1,0 => ⟨⟨(-3906974622091755386860130),(-994759998775440527530677),true⟩,⟨(-2018223706916125718352219),598678893699408904795563,true⟩⟩
  | 1,1 => ⟨⟨(-3521166223328546546153135),(-848314298700697957586287),true⟩,⟨(-2006169458553557972297154),407437318194846303525200,true⟩⟩
  | 1,2 => ⟨⟨(-3236956509847552190791653),(-742066277817062588242201),true⟩,⟨(-1994233016504766297465876),266175893050528202313315,true⟩⟩
  | 1,3 => ⟨⟨(-3074288756036535694621825),(-680853968484245353906188),true⟩,⟨(-1987652288529073782316963),185736746158126484273734,true⟩⟩
  | 1,4 => ⟨⟨(-4355680959631468603213705),(-1170261027133570448448219),true⟩,⟨(-2026047704417670822370569),816935128317062599367552,true⟩⟩
  | 1,5 => ⟨⟨(-4807537143723349023401977),(-1354535669487033182359595),true⟩,⟨(-2026898510096394326287567),1040468893078595983787994,true⟩⟩
  | 1,6 => ⟨⟨(-5188992136892935987978273),(-1516973108059462854324900),true⟩,⟨(-2021911569070735225658795),1249524942049600734774941,true⟩⟩
  | 1,7 => ⟨⟨(-5428377857889221787704420),(-1623063744673953111336622),true⟩,⟨(-2015762797799614536226285),1375121464463488902819525,true⟩⟩
  | 2,0 => ⟨⟨(-2066461009810880080523142),(-275828010098588312886216),true⟩,⟨(-1940645986338764316835069),(-251113375699480153291873),true⟩⟩
  | 2,1 => ⟨⟨(-1838611325872074567275672),(-176180028437891139858604),true⟩,⟨(-1924368888225669110992411),(-331766159757008949529909),true⟩⟩
  | 2,2 => ⟨⟨(-1669874935831311647932633),(-100319293707138888565340),true⟩,⟨(-1910480812258638244160027),(-388512146324815167992238),true⟩⟩
  | 2,3 => ⟨⟨(-1572704198069725728412819),(-55734907938123825139242),true⟩,⟨(-1901674710128066876654629),(-419871674891485602042927),true⟩⟩
  | 2,4 => ⟨⟨(-2331373560616993472967126),(-388348520236878241423314),true⟩,⟨(-1956576905707926160273905),(-152599868207667278954456),true⟩⟩
  | 2,5 => ⟨⟨(-2603693914360148105340117),(-499543922261959510741164),true⟩,⟨(-1970027086675207106438681),(-41530486741662794874657),true⟩⟩
  | 2,6 => ⟨⟨(-2844411628659932373462664),(-592780741815287826993453),true⟩,⟨(-1979718425318971104358858),73198460859549114357499,true⟩⟩
  | 2,7 => ⟨⟨(-2997654040322851053204537),(-651567050126559279793685),true⟩,⟨(-1985140498967073940991330),148051344990867526748770,true⟩⟩
  | 3,0 => ⟨⟨(-943140611971133335969597),260341587518515201836275,true⟩,⟨(-1826738574783491168410948),(-591617456899164501979517),true⟩⟩
  | 3,1 => ⟨⟨(-800092329411590851312380),342689515323969169798008,true⟩,⟨(-1804794715534178708254284),(-616682953895039644278337),true⟩⟩
  | 3,2 => ⟨⟨(-692772832232176549873821),406232934201808774219444,true⟩,⟨(-1786628207523354199488853),(-633035942188281926300644),true⟩⟩
  | 3,3 => ⟨⟨(-630390032841117145421206),443879591391871629798234,true⟩,⟨(-1775351360725947778259509),(-641523041142659507753306),true⟩⟩
  | 3,4 => ⟨⟨(-1113932171285967943431676),169137130628491440271093,true⟩,⟨(-1850427907428125652700375),(-552379862386915486776710),true⟩⟩
  | 3,5 => ⟨⟨(-1287931216750236797246707),81145405747513491724728,true⟩,⟨(-1871929007740322029372421),(-505406598098456529496198),true⟩⟩
  | 3,6 => ⟨⟨(-1434377372587923807538291),9190951063436363006077,true⟩,⟨(-1888004525576051631182359),(-462671833974354675037921),true⟩⟩
  | 3,7 => ⟨⟨(-1526733771620093897857417),(-34397978407566974123916),true⟩,⟨(-1897285081123429071463645),(-434343892752438957765478),true⟩⟩
  | 4,0 => ⟨⟨614771132627566931695587,1466753780131606574357654,true⟩,⟨(-1419304060634089104476475),(-552371585947848017184299),true⟩⟩
  | 4,1 => ⟨⟨843019615214101302314990,1690387906290452696657049,true⟩,⟨(-1322806659469622130683822),(-488546110798286998461204),true⟩⟩
  | 4,2 => ⟨⟨1004411963000032524917732,1849769649190589258373685,true⟩,⟨(-1247891589293109169555267),(-435830590759181781315502),true⟩⟩
  | 4,3 => ⟨⟨1094406324977919461947507,1938887407831318556781965,true⟩,⟨(-1203936278669399635876708),(-404024418452018260951815),true⟩⟩
  | 4,4 => ⟨⟨333785944553581337854691,1196026678152344529595819,true⟩,⟨(-1521356220653437153798139),(-611314798042645511787377),true⟩⟩
  | 4,5 => ⟨⟨(-358197576268924156807),911129279497883702089325,true⟩,⟨(-1627577115331413309349612),(-648027062992339721976345),true⟩⟩
  | 4,6 => ⟨⟨(-330657581104026915746253),659856335370920808883410,true⟩,⟨(-1713148017117032271229120),(-655622306832289561613617),true⟩⟩
  | 4,7 => ⟨⟨(-556945032412252766159379),495693148953668755029983,true⟩,⟨(-1761366414788064980639750),(-646749220273995185678902),true⟩⟩
  | 5,0 => ⟨⟨1968083388704420424621285,2795336068615024230550285,true⟩,⟨(-738558312139937002554759),(-52339861850640779179458),true⟩⟩
  | 5,1 => ⟨⟨2117763071539591204293616,2939792956064198663315122,true⟩,⟨(-675568321398028792489239),(-4594305768369396770967),true⟩⟩
  | 5,2 => ⟨⟨2220666106604084922181622,3040989811036033683385889,true⟩,⟨(-648060772879651461954014),17035843043799106289708,true⟩⟩
  | 5,3 => ⟨⟨2278366298886910672671362,3099436756089894090515265,true⟩,⟨(-641499734608527771341975),22857033909971348815111,true⟩⟩
  | 5,4 => ⟨⟨1771149428686884004258811,2605178674148594877549878,true⟩,⟨(-840693356351257145926716),(-130041729120893180397405),true⟩⟩
  | 5,5 => ⟨⟨1540235380600964008835387,2379653418572332593612520,true⟩,⟨(-968134121329129389235958),(-227271882566485938346281),true⟩⟩
  | 5,6 => ⟨⟨1314856965234616413372804,2157294228164648292349748,true⟩,⟨(-1090514392636158248155272),(-319935946083020587049794),true⟩⟩
  | 5,7 => ⟨⟨1156691126843611099742950,2000609844975693537616381,true⟩,⟨(-1172673391040022505220587),(-381098929221794288472545),true⟩⟩
  | 6,0 => ⟨⟨2636791785441464273774274,3751767894567324298925418,true⟩,⟨(-992012710704074315835298),(-70514409505790620355863),true⟩⟩
  | 6,1 => ⟨⟨2767628467443770523782155,4048502882871409599377133,true⟩,⟨(-1277572123642214374829267),(-193350783226520827333778),true⟩⟩
  | 6,2 => ⟨⟨2886410559297725665168207,4352738716102570692124973,true⟩,⟨(-1626092138361957909109507),(-352312844484292329939070),true⟩⟩
  | 6,3 => ⟨⟨2961381336536003125163214,4573702571571563917154065,true⟩,⟨(-1915547971628487024762347),(-488046218778849305496902),true⟩⟩
  | 6,4 => ⟨⟨2518756827768766048262020,3509227625742373195107689,true⟩,⟨(-804989360126239024192806),462104366548061956515,true⟩⟩
  | 6,5 => ⟨⟨2421875935908203731072663,3327955359395662945109539,true⟩,⟨(-702799314976706311924569),29351794133271565386230,true⟩⟩
  | 6,6 => ⟨⟨2348163028799816107114273,3202130463171826264329494,true⟩,⟨(-657715002005069963581929),31809581834696676009039,true⟩⟩
  | 6,7 => ⟨⟨2302848548208559502213648,3130195331114388013393004,true⟩,⟨(-643184381982850149075383),25719191833636757004346,true⟩⟩
  | 7,0 => ⟨⟨3092282391953140266433040,5127326845555849538768844,true⟩,⟨(-2806028266390890059969753),(-915325788054596460696619),true⟩⟩
  | 7,1 => ⟨⟨3108976607189383048677212,5288739755926228214379206,true⟩,⟨(-3124586930416810239115679),(-1069927624159100309784865),true⟩⟩
  | 7,2 => ⟨⟨3112196086026560361255312,5420712231200785104789944,true⟩,⟨(-3412699760188471027135831),(-1210088844754371611239805),true⟩⟩
  | 7,3 => ⟨⟨3108444555618243721912719,5501388021441500011643684,true⟩,⟨(-3603796909140354410907524),(-1303147447334052466060746),true⟩⟩
  | 7,4 => ⟨⟨3063698170568055000776305,4962597463555377285673660,true⟩,⟨(-2512105123974266566589982),(-773259164323911514236163),true⟩⟩
  | 7,5 => ⟨⟨3030711906006179790629910,4817886036008562241911776,true⟩,⟨(-2275637793099063925811931),(-659573982926008861403024),true⟩⟩
  | 7,6 => ⟨⟨3001901914057664552962516,4709573277825136598465561,true⟩,⟨(-2110285630683052271310100),(-580523753412454210179771),true⟩⟩
  | 7,7 => ⟨⟨2983799583379863884396137,4646950656834800567017272,true⟩,⟨(-2018849626800522343077628),(-537008143263302021651583),true⟩⟩
  | 8,0 => ⟨⟨2827191421350756508213126,6053953333271796344291978,true⟩,⟨(-5562831879036745149090824),(-2254042589150350705928293),true⟩⟩
  | 8,1 => ⟨⟨2607726557272614637251789,6146017888734326450650125,true⟩,⟨(-6319811541324063223316861),(-2617004577375271297622718),true⟩⟩
  | 8,2 => ⟨⟨2359913239802593614229500,6173024006003006144564146,true⟩,⟨(-6995553767696835256187811),(-2937647358457318547473488),true⟩⟩
  | 8,3 => ⟨⟨2171030754197816989111022,6161933269616536558182462,true⟩,⟨(-7435956400154862333676189),(-3144581284941217847148476),true⟩⟩
  | 8,4 => ⟨⟨2976222673022611666466210,5910257706495874231016083,true⟩,⟨(-4862358735581120984362787),(-1915407891336308977372608),true⟩⟩
  | 8,5 => ⟨⟨3057299610397727092870317,5753293758933526438142517,true⟩,⟨(-4302143631080955712587334),(-1643235846850648093780096),true⟩⟩
  | 8,6 => ⟨⟨3092791694536833399610768,5621438386102659554210561,true⟩,⟨(-3914242775942794554953686),(-1454373557048244628738353),true⟩⟩
  | 8,7 => ⟨⟨3104769822551796986740806,5540656988416796337814609,true⟩,⟨(-3701614327736706285053368),(-1350795238549640361227064),true⟩⟩
  | 9,0 => ⟨⟨1074254168954581974376860,5823630102150661616128567,true⟩,⟨(-9333228437408670366581149),(-4011870609061805681818522),true⟩⟩
  | 9,1 => ⟨⟨591105787954849638187473,5619599968939992972901097,true⟩,⟨(-9915044634978823248848992),(-4252468177129697904186954),true⟩⟩
  | 9,2 => ⟨⟨136866261713239231355683,5413180139979478709192175,true⟩,⟨(-10389968625267772863032882),(-4438582959429628730170725),true⟩⟩
  | 9,3 => ⟨⟨(-166784404953996107883469),5267461381703365368724926,true⟩,⟨(-10676040753540016650414527),(-4547331516896595984902419),true⟩⟩
  | 9,4 => ⟨⟨1462259848685922149227738,5981605112488313017829218,true⟩,⟨(-8755726198088186620474491),(-3752746298385239632112721),true⟩⟩
  | 9,5 => ⟨⟨1769737202421229753884691,6080797524921435170966879,true⟩,⟨(-8234007564358125315735243),(-3514718027643897251867863),true⟩⟩
  | 9,6 => ⟨⟨1980010408439060916973184,6131475984476112477348327,true⟩,⟨(-7835485584143723008440505),(-3330721878555467411787493),true⟩⟩
  | 9,7 => ⟨⟨2093879086350879124916156,6151667554212826601222210,true⟩,⟨(-7602198333216404528900188),(-3222226592387525654607109),true⟩⟩
  | 10,0 => ⟨⟨(-3124134753856735602281031),3581725961630832510347061,true⟩,⟨(-12592332841675003580778939),(-5163576110797313371481038),true⟩⟩
  | 10,1 => ⟨⟨(-4150776837409607922910558),2902261009111312800261046,true⟩,⟨(-12963451983445143629813705),(-5227840235947710043225912),true⟩⟩
  | 10,2 => ⟨⟨(-5011902272365935857406118),2299285137715864424608270,true⟩,⟨(-13167065974510058156036203),(-5227882018668446485340950),true⟩⟩
  | 10,3 => ⟨⟨(-5546466712559811362109134),1945607140460141826235871,true⟩,⟨(-13243025156222813191002684),(-5184608288477309830909911),true⟩⟩
  | 10,4 => ⟨⟨(-2114240703456243045928722),4206525430023662600751558,true⟩,⟨(-12088278043856057110844873),(-5030067927166139092462687),true⟩⟩
  | 10,5 => ⟨⟨(-1266449162657109400670504),4694236265133336318998304,true⟩,⟨(-11550942585197626664025405),(-4859713365677294219323884),true⟩⟩
  | 10,6 => ⟨⟨(-660686024316589292893144),5019220851536875462620005,true⟩,⟨(-11096115389957271964849288),(-4701600284170799661767185),true⟩⟩
  | 10,7 => ⟨⟨(-323151140368171421605259),5190634325803013994719267,true⟩,⟨(-10814161560625348852013046),(-4598814898255651106400661),true⟩⟩
  | 11,0 => ⟨⟨(-9446655263880661370196030),(-745659166031137747782408),true⟩,⟨(-12303318249167698469903956),(-3988073121421692220395855),true⟩⟩
  | 11,1 => ⟨⟨(-10335903819459569123084774),(-1475731685606731913234822),true⟩,⟨(-11480751832933753134505769),(-3383486555933153159005576),true⟩⟩
  | 11,2 => ⟨⟨(-10952859302903727156585187),(-2010217287562486223691087),true⟩,⟨(-10655329827306323584136737),(-2777273722414916612883622),true⟩⟩
  | 11,3 => ⟨⟨(-11243733660222403962058693),(-2306365439201625828624145),true⟩,⟨(-10088343583281617576903607),(-2395345458257699699351331),true⟩⟩
  | 11,4 => ⟨⟨(-8358533498634555183632500),71092753248106318291104,true⟩,⟨(-12901657284193563894974903),(-4492861899568135080734058),true⟩⟩
  | 11,5 => ⟨⟨(-7253529989033920446097751),846286005614811235519779,true⟩,⟨(-13202851257727040258064090),(-4850548320903001856279494),true⟩⟩
  | 11,6 => ⟨⟨(-6352515909708479905058244),1439462194424600996940742,true⟩,⟨(-13280624688804675203010147),(-5056212045938266846576053),true⟩⟩
  | 11,7 => ⟨⟨(-5808742986285638929642942),1783290456851079440476996,true⟩,⟨(-13265670837810425137237576),(-5148263969995753834011962),true⟩⟩
  | 12,0 => ⟨⟨(-11099570987545793415677744),(-3602304790121000192573850),true⟩,⟨(-4898224880576310996263939),417735110620993637501157,true⟩⟩
  | 12,1 => ⟨⟨(-10358036983987427345574251),(-3639658431803910271377470),true⟩,⟨(-3445611161280942622946052),1218417404665174585433191,true⟩⟩
  | 12,2 => ⟨⟨(-9608459602805731282370254),(-3579153194868304570410582),true⟩,⟨(-2392297256185655903969949),1776429726850611793431152,true⟩⟩
  | 12,3 => ⟨⟨(-9108447351520829931307747),(-3489255716635838424967541),true⟩,⟨(-1812037210288373169010976),2048621345205815168176440,true⟩⟩
  | 12,4 => ⟨⟨(-11575588735255005215338090),(-3404247940131020387433699),true⟩,⟨(-6531343522599942495046859),(-405732736857800139130885),true⟩⟩
  | 12,5 => ⟨⟨(-11694216971041526727711774),(-3067263667220062842772073),true⟩,⟨(-8037466672217724520792140),(-1175886818912952121925771),true⟩⟩
  | 12,6 => ⟨⟨(-11548315704499484110403832),(-2701004907704395320235310),true⟩,⟨(-9163101454919460281456807),(-1817455018357596839691476),true⟩⟩
  | 12,7 => ⟨⟨(-11360598786725544725423358),(-2441646970950858794590075),true⟩,⟨(-9796212836642678471642075),(-2207309926930156077436738),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP493Value0_0 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 0 (0:Fin 8))=sharedDiskP493Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value0_1 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 0 (1:Fin 8))=sharedDiskP493Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value0_2 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 0 (2:Fin 8))=sharedDiskP493Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value0_3 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 0 (3:Fin 8))=sharedDiskP493Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value0_4 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 0 (4:Fin 8))=sharedDiskP493Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value0_5 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 0 (5:Fin 8))=sharedDiskP493Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value0_6 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 0 (6:Fin 8))=sharedDiskP493Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value0_7 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 0 (7:Fin 8))=sharedDiskP493Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP493Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 0 j)=sharedDiskP493Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP493Value0_0
  · exact sharedDiskP493Value0_1
  · exact sharedDiskP493Value0_2
  · exact sharedDiskP493Value0_3
  · exact sharedDiskP493Value0_4
  · exact sharedDiskP493Value0_5
  · exact sharedDiskP493Value0_6
  · exact sharedDiskP493Value0_7
private theorem sharedDiskP493Value1_0 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 1 (0:Fin 8))=sharedDiskP493Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value1_1 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 1 (1:Fin 8))=sharedDiskP493Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value1_2 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 1 (2:Fin 8))=sharedDiskP493Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value1_3 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 1 (3:Fin 8))=sharedDiskP493Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value1_4 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 1 (4:Fin 8))=sharedDiskP493Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value1_5 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 1 (5:Fin 8))=sharedDiskP493Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value1_6 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 1 (6:Fin 8))=sharedDiskP493Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value1_7 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 1 (7:Fin 8))=sharedDiskP493Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP493Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 1 j)=sharedDiskP493Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP493Value1_0
  · exact sharedDiskP493Value1_1
  · exact sharedDiskP493Value1_2
  · exact sharedDiskP493Value1_3
  · exact sharedDiskP493Value1_4
  · exact sharedDiskP493Value1_5
  · exact sharedDiskP493Value1_6
  · exact sharedDiskP493Value1_7
private theorem sharedDiskP493Value2_0 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 2 (0:Fin 8))=sharedDiskP493Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value2_1 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 2 (1:Fin 8))=sharedDiskP493Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value2_2 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 2 (2:Fin 8))=sharedDiskP493Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value2_3 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 2 (3:Fin 8))=sharedDiskP493Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value2_4 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 2 (4:Fin 8))=sharedDiskP493Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value2_5 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 2 (5:Fin 8))=sharedDiskP493Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value2_6 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 2 (6:Fin 8))=sharedDiskP493Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value2_7 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 2 (7:Fin 8))=sharedDiskP493Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP493Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 2 j)=sharedDiskP493Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP493Value2_0
  · exact sharedDiskP493Value2_1
  · exact sharedDiskP493Value2_2
  · exact sharedDiskP493Value2_3
  · exact sharedDiskP493Value2_4
  · exact sharedDiskP493Value2_5
  · exact sharedDiskP493Value2_6
  · exact sharedDiskP493Value2_7
private theorem sharedDiskP493Value3_0 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 3 (0:Fin 8))=sharedDiskP493Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value3_1 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 3 (1:Fin 8))=sharedDiskP493Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value3_2 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 3 (2:Fin 8))=sharedDiskP493Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value3_3 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 3 (3:Fin 8))=sharedDiskP493Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value3_4 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 3 (4:Fin 8))=sharedDiskP493Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value3_5 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 3 (5:Fin 8))=sharedDiskP493Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value3_6 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 3 (6:Fin 8))=sharedDiskP493Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value3_7 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 3 (7:Fin 8))=sharedDiskP493Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP493Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 3 j)=sharedDiskP493Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP493Value3_0
  · exact sharedDiskP493Value3_1
  · exact sharedDiskP493Value3_2
  · exact sharedDiskP493Value3_3
  · exact sharedDiskP493Value3_4
  · exact sharedDiskP493Value3_5
  · exact sharedDiskP493Value3_6
  · exact sharedDiskP493Value3_7
private theorem sharedDiskP493Value4_0 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 4 (0:Fin 8))=sharedDiskP493Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value4_1 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 4 (1:Fin 8))=sharedDiskP493Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value4_2 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 4 (2:Fin 8))=sharedDiskP493Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value4_3 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 4 (3:Fin 8))=sharedDiskP493Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value4_4 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 4 (4:Fin 8))=sharedDiskP493Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value4_5 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 4 (5:Fin 8))=sharedDiskP493Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value4_6 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 4 (6:Fin 8))=sharedDiskP493Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value4_7 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 4 (7:Fin 8))=sharedDiskP493Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP493Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 4 j)=sharedDiskP493Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP493Value4_0
  · exact sharedDiskP493Value4_1
  · exact sharedDiskP493Value4_2
  · exact sharedDiskP493Value4_3
  · exact sharedDiskP493Value4_4
  · exact sharedDiskP493Value4_5
  · exact sharedDiskP493Value4_6
  · exact sharedDiskP493Value4_7
private theorem sharedDiskP493Value5_0 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 5 (0:Fin 8))=sharedDiskP493Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value5_1 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 5 (1:Fin 8))=sharedDiskP493Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value5_2 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 5 (2:Fin 8))=sharedDiskP493Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value5_3 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 5 (3:Fin 8))=sharedDiskP493Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value5_4 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 5 (4:Fin 8))=sharedDiskP493Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value5_5 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 5 (5:Fin 8))=sharedDiskP493Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value5_6 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 5 (6:Fin 8))=sharedDiskP493Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value5_7 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 5 (7:Fin 8))=sharedDiskP493Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP493Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 5 j)=sharedDiskP493Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP493Value5_0
  · exact sharedDiskP493Value5_1
  · exact sharedDiskP493Value5_2
  · exact sharedDiskP493Value5_3
  · exact sharedDiskP493Value5_4
  · exact sharedDiskP493Value5_5
  · exact sharedDiskP493Value5_6
  · exact sharedDiskP493Value5_7
private theorem sharedDiskP493Value6_0 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 6 (0:Fin 8))=sharedDiskP493Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value6_1 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 6 (1:Fin 8))=sharedDiskP493Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value6_2 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 6 (2:Fin 8))=sharedDiskP493Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value6_3 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 6 (3:Fin 8))=sharedDiskP493Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value6_4 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 6 (4:Fin 8))=sharedDiskP493Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value6_5 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 6 (5:Fin 8))=sharedDiskP493Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value6_6 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 6 (6:Fin 8))=sharedDiskP493Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value6_7 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 6 (7:Fin 8))=sharedDiskP493Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP493Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 6 j)=sharedDiskP493Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP493Value6_0
  · exact sharedDiskP493Value6_1
  · exact sharedDiskP493Value6_2
  · exact sharedDiskP493Value6_3
  · exact sharedDiskP493Value6_4
  · exact sharedDiskP493Value6_5
  · exact sharedDiskP493Value6_6
  · exact sharedDiskP493Value6_7
private theorem sharedDiskP493Value7_0 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 7 (0:Fin 8))=sharedDiskP493Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value7_1 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 7 (1:Fin 8))=sharedDiskP493Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value7_2 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 7 (2:Fin 8))=sharedDiskP493Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value7_3 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 7 (3:Fin 8))=sharedDiskP493Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value7_4 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 7 (4:Fin 8))=sharedDiskP493Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value7_5 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 7 (5:Fin 8))=sharedDiskP493Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value7_6 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 7 (6:Fin 8))=sharedDiskP493Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value7_7 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 7 (7:Fin 8))=sharedDiskP493Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP493Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 7 j)=sharedDiskP493Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP493Value7_0
  · exact sharedDiskP493Value7_1
  · exact sharedDiskP493Value7_2
  · exact sharedDiskP493Value7_3
  · exact sharedDiskP493Value7_4
  · exact sharedDiskP493Value7_5
  · exact sharedDiskP493Value7_6
  · exact sharedDiskP493Value7_7
private theorem sharedDiskP493Value8_0 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 8 (0:Fin 8))=sharedDiskP493Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value8_1 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 8 (1:Fin 8))=sharedDiskP493Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value8_2 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 8 (2:Fin 8))=sharedDiskP493Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value8_3 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 8 (3:Fin 8))=sharedDiskP493Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value8_4 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 8 (4:Fin 8))=sharedDiskP493Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value8_5 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 8 (5:Fin 8))=sharedDiskP493Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value8_6 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 8 (6:Fin 8))=sharedDiskP493Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value8_7 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 8 (7:Fin 8))=sharedDiskP493Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP493Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 8 j)=sharedDiskP493Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP493Value8_0
  · exact sharedDiskP493Value8_1
  · exact sharedDiskP493Value8_2
  · exact sharedDiskP493Value8_3
  · exact sharedDiskP493Value8_4
  · exact sharedDiskP493Value8_5
  · exact sharedDiskP493Value8_6
  · exact sharedDiskP493Value8_7
private theorem sharedDiskP493Value9_0 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 9 (0:Fin 8))=sharedDiskP493Values 9 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value9_1 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 9 (1:Fin 8))=sharedDiskP493Values 9 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value9_2 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 9 (2:Fin 8))=sharedDiskP493Values 9 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value9_3 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 9 (3:Fin 8))=sharedDiskP493Values 9 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value9_4 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 9 (4:Fin 8))=sharedDiskP493Values 9 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value9_5 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 9 (5:Fin 8))=sharedDiskP493Values 9 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value9_6 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 9 (6:Fin 8))=sharedDiskP493Values 9 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value9_7 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 9 (7:Fin 8))=sharedDiskP493Values 9 (7:Fin 8) := by decide +kernel
theorem sharedDiskP493Values9_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 9 j)=sharedDiskP493Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP493Value9_0
  · exact sharedDiskP493Value9_1
  · exact sharedDiskP493Value9_2
  · exact sharedDiskP493Value9_3
  · exact sharedDiskP493Value9_4
  · exact sharedDiskP493Value9_5
  · exact sharedDiskP493Value9_6
  · exact sharedDiskP493Value9_7
private theorem sharedDiskP493Value10_0 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 10 (0:Fin 8))=sharedDiskP493Values 10 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value10_1 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 10 (1:Fin 8))=sharedDiskP493Values 10 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value10_2 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 10 (2:Fin 8))=sharedDiskP493Values 10 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value10_3 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 10 (3:Fin 8))=sharedDiskP493Values 10 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value10_4 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 10 (4:Fin 8))=sharedDiskP493Values 10 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value10_5 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 10 (5:Fin 8))=sharedDiskP493Values 10 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value10_6 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 10 (6:Fin 8))=sharedDiskP493Values 10 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value10_7 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 10 (7:Fin 8))=sharedDiskP493Values 10 (7:Fin 8) := by decide +kernel
theorem sharedDiskP493Values10_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 10 j)=sharedDiskP493Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP493Value10_0
  · exact sharedDiskP493Value10_1
  · exact sharedDiskP493Value10_2
  · exact sharedDiskP493Value10_3
  · exact sharedDiskP493Value10_4
  · exact sharedDiskP493Value10_5
  · exact sharedDiskP493Value10_6
  · exact sharedDiskP493Value10_7
private theorem sharedDiskP493Value11_0 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 11 (0:Fin 8))=sharedDiskP493Values 11 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value11_1 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 11 (1:Fin 8))=sharedDiskP493Values 11 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value11_2 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 11 (2:Fin 8))=sharedDiskP493Values 11 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value11_3 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 11 (3:Fin 8))=sharedDiskP493Values 11 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value11_4 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 11 (4:Fin 8))=sharedDiskP493Values 11 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value11_5 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 11 (5:Fin 8))=sharedDiskP493Values 11 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value11_6 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 11 (6:Fin 8))=sharedDiskP493Values 11 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value11_7 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 11 (7:Fin 8))=sharedDiskP493Values 11 (7:Fin 8) := by decide +kernel
theorem sharedDiskP493Values11_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 11 j)=sharedDiskP493Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP493Value11_0
  · exact sharedDiskP493Value11_1
  · exact sharedDiskP493Value11_2
  · exact sharedDiskP493Value11_3
  · exact sharedDiskP493Value11_4
  · exact sharedDiskP493Value11_5
  · exact sharedDiskP493Value11_6
  · exact sharedDiskP493Value11_7
private theorem sharedDiskP493Value12_0 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 12 (0:Fin 8))=sharedDiskP493Values 12 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value12_1 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 12 (1:Fin 8))=sharedDiskP493Values 12 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value12_2 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 12 (2:Fin 8))=sharedDiskP493Values 12 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value12_3 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 12 (3:Fin 8))=sharedDiskP493Values 12 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value12_4 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 12 (4:Fin 8))=sharedDiskP493Values 12 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value12_5 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 12 (5:Fin 8))=sharedDiskP493Values 12 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value12_6 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 12 (6:Fin 8))=sharedDiskP493Values 12 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP493Value12_7 : truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 12 (7:Fin 8))=sharedDiskP493Values 12 (7:Fin 8) := by decide +kernel
theorem sharedDiskP493Values12_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points 12 j)=sharedDiskP493Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP493Value12_0
  · exact sharedDiskP493Value12_1
  · exact sharedDiskP493Value12_2
  · exact sharedDiskP493Value12_3
  · exact sharedDiskP493Value12_4
  · exact sharedDiskP493Value12_5
  · exact sharedDiskP493Value12_6
  · exact sharedDiskP493Value12_7
theorem sharedDiskP493Values_eq : ∀ (i : Fin 13) (j : Fin 8), truncatedChordCell 2 sharedDiskP493Params (sharedChord493Gauss8Points i j)=sharedDiskP493Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP493Values0_eq
  · exact sharedDiskP493Values1_eq
  · exact sharedDiskP493Values2_eq
  · exact sharedDiskP493Values3_eq
  · exact sharedDiskP493Values4_eq
  · exact sharedDiskP493Values5_eq
  · exact sharedDiskP493Values6_eq
  · exact sharedDiskP493Values7_eq
  · exact sharedDiskP493Values8_eq
  · exact sharedDiskP493Values9_eq
  · exact sharedDiskP493Values10_eq
  · exact sharedDiskP493Values11_eq
  · exact sharedDiskP493Values12_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP493Box : HorizontalRectangle := ⟨(129/200),(33/50),(878940159632233/1649267441664000),(298379040327903/549755813888000),(328930826878382276563947452783719/649037107316853453566312041152512),(2785485203845803814581243782820943/649037107316853453566312041152512),(-2960686564377736957798013347508261/649037107316853453566312041152512),(-400669743547995544631486607470629/649037107316853453566312041152512),true,[]⟩
noncomputable def sharedDiskP493Grid : CGrid := momentChordGrid sharedDiskP493Params chordGaussRule8 2 sharedChord493Bd sharedChord493M (23175049/18014398509481984)
theorem sharedDiskP493Columns : containedInReported sharedDiskP493Grid.re sharedDiskP493Box.reLo sharedDiskP493Box.reHi=true ∧ containedInReported sharedDiskP493Grid.im sharedDiskP493Box.imLo sharedDiskP493Box.imHi=true := by
  rw [sharedDiskP493Grid,momentChordGrid_eq_tabulated sharedDiskP493Params chordGaussRule8 2 sharedChord493Bd sharedChord493M (23175049/18014398509481984) sharedChord493Gauss8Points sharedChord493Gauss8Weights sharedDiskP493Values sharedChord493Gauss8Points_eq sharedChord493Gauss8Weights_eq sharedDiskP493Values_eq]
  decide +kernel
theorem sharedDiskP493Sound : sharedDiskP493Box.Sound := by
  intro t a tl tu al au
  change (((129/200):ℚ):ℝ)≤t at tl
  change t≤(((33/50):ℚ):ℝ) at tu
  change (((878940159632233/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((298379040327903/549755813888000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP493Params_ok] at ps
  have band := sharedChord493ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((129/200):ℚ)≤(129/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((33/50):ℚ)≤(3/4)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((878940159632233/1649267441664000):ℚ)≤(878940159632233/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((298379040327903/549755813888000):ℚ)≤(929134916903873/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord493Bd (by decide +kernel) (by decide +kernel) sharedChord493M (by decide +kernel) (sharedChord493Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP493Columns.1 sharedDiskP493Columns.2
def sharedDiskP493Rows : List SignRow := [positive_493.toSignRow, positive_494.toSignRow, positive_495.toSignRow]
theorem sharedDiskP493Rows_actual : ∀ r∈sharedDiskP493Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP493Rows.all (sharedDiskP493Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP493Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP496Params : ChordParams := ⟨⟨(-11510689821132100290911),(-10355301624808752221342),true⟩,⟨2555225414397629106822780,2670299464487544251004438,true⟩,⟨89942327397843234592156,99784335521801628917273,true⟩,⟨132776537394343954343195,146036204709329761181701,true⟩,⟨221664252623913100206067,233924818648527113934798,true⟩,⟨1186121568809684943177318,1188391110619212476356294,true⟩,⟨(-2828364229327828210657529),(-2760230227286597521486000),true⟩,⟨⟨1118810923403192343139829,1258997047512997041427613,true⟩,⟨(-4407),4407,true⟩⟩⟩
theorem sharedDiskP496Params_ok : chordParams (Grid.ofRats (33/50) (27/40)) (Grid.ofRats (58929547351633/109951162777600) (300093324678443/549755813888000))=sharedDiskP496Params := by decide +kernel
def sharedDiskP496Values (i : Fin 13) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-6654905525948790308783911),(-2306455403354938793697176),true⟩,⟨(-1887779235397012501981805),1889426101309230678393367,true⟩⟩
  | 0,1 => ⟨⟨(-6136893410084323203067013),(-2030164546723808420617596),true⟩,⟨(-1905958789128066327167698),1708470052819959340808791,true⟩⟩
  | 0,2 => ⟨⟨(-5740163724017250708010796),(-1833521323403218830306462),true⟩,⟨(-1916165983145651629418847),1540570968043462898031852,true⟩⟩
  | 0,3 => ⟨⟨(-5507534055576283855149532),(-1723456136239634371492185),true⟩,⟨(-1921165185788190963368572),1432247859499244363281997,true⟩⟩
  | 0,4 => ⟨⟨(-7227425944631950146795363),(-2636466327695520423845876),true⟩,⟨(-1861654370955027128760053),2028178055440688843159753,true⟩⟩
  | 0,5 => ⟨⟨(-7772150542645233567300109),(-2972569363854240755641529),true⟩,⟨(-1831953005485665807890256),2089153391260742508283632,true⟩⟩
  | 0,6 => ⟨⟨(-8208164315428788790612598),(-3273378854715277432696362),true⟩,⟨(-1806052501089187221360081),2080991111865313873336736,true⟩⟩
  | 0,7 => ⟨⟨(-8472136155150268844419880),(-3469734996817710930875365),true⟩,⟨(-1790115067602211185885014),2049285088204303393867470,true⟩⟩
  | 1,0 => ⟨⟨(-3960963831633726591619713),(-1061194423492288007626903),true⟩,⟨(-1939238300673293704574260),656509712282631362227739,true⟩⟩
  | 1,1 => ⟨⟨(-3592807082635903878483893),(-917815142312705507297055),true⟩,⟨(-1930995154813646479989196),476789381173891170300637,true⟩⟩
  | 1,2 => ⟨⟨(-3320365605280069060253875),(-813722120664045211875572),true⟩,⟨(-1922040576161081787543799),342418240000773769339394,true⟩⟩
  | 1,3 => ⟨⟨(-3163954154832903151638814),(-754459396074438195338122),true⟩,⟨(-1915814931016914577230228),265218421214483526899749,true⟩⟩
  | 1,4 => ⟨⟨(-4386824227143348112408463),(-1232644991592346494054026),true⟩,⟨(-1943014460149124393562843),858692738056605242869127,true⟩⟩
  | 1,5 => ⟨⟨(-4813814280482489874745775),(-1411833592259936563186219),true⟩,⟨(-1940454394512384367848279),1075634414850868447686931,true⟩⟩
  | 1,6 => ⟨⟨(-5172297213977278829457903),(-1569204227231093817293206),true⟩,⟨(-1932994123922733219460964),1265420942160447270927660,true⟩⟩
  | 1,7 => ⟨⟨(-5396596291424940149966050),(-1671599366482440298358891),true⟩,⟨(-1925614783812570275706430),1378345111414069152377462,true⟩⟩
  | 2,0 => ⟨⟨(-2178922264217409628186611),(-363304956023086911408516),true⟩,⟨(-1875285310347885150942301),(-182756601247539114244257),true⟩⟩
  | 2,1 => ⟨⟨(-1956901667441255769537764),(-266988816537241705550158),true⟩,⟨(-1862386017457726634452143),(-264547536790659433270393),true⟩⟩
  | 2,2 => ⟨⟨(-1792221510995877633503193),(-193787579601099105268202),true⟩,⟨(-1851281696096499096543714),(-322759560857070731699783),true⟩⟩
  | 2,3 => ⟨⟨(-1697301311981889889394412),(-150812492572483793775609),true⟩,⟨(-1844199659947777786003035),(-355201826208760627430445),true⟩⟩
  | 2,4 => ⟨⟨(-2436460331410244083041355),(-472292102291319786610681),true⟩,⟨(-1887760283293545906047418),(-84132694537336639608259),true⟩⟩
  | 2,5 => ⟨⟨(-2709509526420758292913877),(-580226063387402565422956),true⟩,⟨(-1898134122305273898153216),43182690379046785519933,true⟩⟩
  | 2,6 => ⟨⟨(-2942324361879599971519737),(-670807289806925593257443),true⟩,⟨(-1905625627975782614652072),156266619412133330289421,true⟩⟩
  | 2,7 => ⟨⟨(-3090145884053014539078113),(-726573724815942089900623),true⟩,⟨(-1912601037259102133394716),228853646274051207159880,true⟩⟩
  | 3,0 => ⟨⟨(-1077643576101564431194107),150611883941008074927601,true⟩,⟨(-1782194833591332466634066),(-541398159519676953869283),true⟩⟩
  | 3,1 => ⟨⟨(-930556692664303938543249),229627533798598636546035,true⟩,⟨(-1762640978578869811985775),(-576024834061729900989843),true⟩⟩
  | 3,2 => ⟨⟨(-825316333146454822596397),290586687857003372133749,true⟩,⟨(-1747552016741238302821174),(-595154667523177939681496),true⟩⟩
  | 3,3 => ⟨⟨(-764156458827854048610868),326701137035826899548854,true⟩,⟨(-1738143247020723037865058),(-605335071397448454958267),true⟩⟩
  | 3,4 => ⟨⟨(-1248561083270968846663298),63053750666883772202956,true⟩,⟨(-1802449135458280937291040),(-495093422908407274545254),true⟩⟩
  | 3,5 => ⟨⟨(-1418844249694210138182792),(-20970590417449335231812),true⟩,⟨(-1820069827949794703707559),(-444890243464315955986739),true⟩⟩
  | 3,6 => ⟨⟨(-1562087901268830253407665),(-88502807549525884987432),true⟩,⟨(-1833148347935458217331245),(-399839392643827183633792),true⟩⟩
  | 3,7 => ⟨⟨(-1652376520933402119377219),(-130257094149433099365683),true⟩,⟨(-1840658373037473469379527),(-370246352442288590874570),true⟩⟩
  | 4,0 => ⟨⟨476103352882899629428550,1298205089194520282779279,true⟩,⟨(-1420682563526437533925842),(-570750386337894384797894),true⟩⟩
  | 4,1 => ⟨⟨700434418251446956882080,1517526468587771024551081,true⟩,⟨(-1334996276993583622945347),(-515908983356444206634776),true⟩⟩
  | 4,2 => ⟨⟨859854370507391374570147,1675191378911044182892157,true⟩,⟨(-1267536154679148830516702),(-469066432700507746911534),true⟩⟩
  | 4,3 => ⟨⟨949128485119267223121565,1763955378138500974528615,true⟩,⟨(-1227638722811239132761652),(-440317927879701636575852),true⟩⟩
  | 4,4 => ⟨⟨195747871505241463643529,1034909608728113795120946,true⟩,⟨(-1512633575970690791279098),(-617952597497521728692642),true⟩⟩
  | 4,5 => ⟨⟨(-147146993723032435852327),759578543897992470678679,true⟩,⟨(-1612273190288003383953455),(-641767780605982292646504),true⟩⟩
  | 4,6 => ⟨⟨(-470473786430438684992017),517578659030892713207777,true⟩,⟨(-1685706915213984536636333),(-638052713507283894570169),true⟩⟩
  | 4,7 => ⟨⟨(-692166479948305913458152),369872028866843652905091,true⟩,⟨(-1726431677808526929018214),(-616395494109128478933586),true⟩⟩
  | 5,0 => ⟨⟨1843530996967588416620324,2657572249458819198690237,true⟩,⟨(-796689910828405573958044),(-106457424852044105674775),true⟩⟩
  | 5,1 => ⟨⟨2005884937855370099439091,2821334421327035616280359,true⟩,⟨(-739346377475604812303276),(-59272167064275391421835),true⟩⟩
  | 5,2 => ⟨⟨2119821065911947636757303,2939131330703825296502066,true⟩,⟨(-716339548877388922062911),(-38357890428642920326482),true⟩⟩
  | 5,3 => ⟨⟨2184438459636730614648404,3007996950448776857641477,true⟩,⟨(-712742626044289038696242),(-32984908009932991421688),true⟩⟩
  | 5,4 => ⟨⟨1635406790945466532440607,2449743879501837891153160,true⟩,⟨(-891761152498993319290960),(-182383552620235445017881),true⟩⟩
  | 5,5 => ⟨⟨1397337891769696726603403,2211921383682706671840461,true⟩,⟨(-1010534760113455759349792),(-275740493252811895786230),true⟩⟩
  | 5,6 => ⟨⟨1169306613811851608947128,1983778038069714805666462,true⟩,⟨(-1123780719580175073256731),(-362931355327288164990427),true⟩⟩
  | 5,7 => ⟨⟨1011103851269878385782624,1825725790226123401770186,true⟩,⟨(-1199135306701121633736035),(-419405514815119076937878),true⟩⟩
  | 6,0 => ⟨⟨2596481193553495810941066,3739459825193754680659336,true⟩,⟨(-1107229372988579212272536),(-142710498568172227254119),true⟩⟩
  | 6,1 => ⟨⟨2736911088814553120929106,4058324074060122219840031,true⟩,⟨(-1421643127792355319346817),(-280008386609899067204047),true⟩⟩
  | 6,2 => ⟨⟨2857664410241860838173189,4377576114397148774064797,true⟩,⟨(-1803692283248528248233028),(-456820706614503980312234),true⟩⟩
  | 6,3 => ⟨⟨2929423426365306605321122,4604888855618119468655363,true⟩,⟨(-2119622764315765763381837),(-607079949307700005155730),true⟩⟩
  | 6,4 => ⟨⟨2463960863597559334201305,3472425835344414113611410,true⟩,⟨(-900189838321334697239588),(-62733463499606232673795),true⟩⟩
  | 6,5 => ⟨⟨2351799567561588079135776,3268735552150238259003477,true⟩,⟨(-785748980349402067816210),(-29890020276792340530098),true⟩⟩
  | 6,6 => ⟨⟨2265467050171948383596398,3125713743973386538694705,true⟩,⟨(-733774172560417051560455),(-25376182602917347745213),true⟩⟩
  | 6,7 => ⟨⟨2212480251702860706173406,3043718510906862830807510,true⟩,⟨(-715910775325416993546029),(-30459352690767746113056),true⟩⟩
  | 7,0 => ⟨⟨3033931320469376814434750,5156077198351149385791451,true⟩,⟨(-3083027254610347667866173),(-1075411548511091148826303),true⟩⟩
  | 7,1 => ⟨⟨3037056759423671690041789,5310759303555950770085956,true⟩,⟨(-3424338061073230868981902),(-1243023681644754191056651),true⟩⟩
  | 7,2 => ⟨⟨3026654646289739967375282,5434569155987074061572408,true⟩,⟨(-3731442685535677974676275),(-1394104532123117024404548),true⟩⟩
  | 7,3 => ⟨⟨3013261303782065857422183,5508853071371152546040414,true⟩,⟨(-3934289552657913115300120),(-1493947008851026526567876),true⟩⟩
  | 7,4 => ⟨⟨3016201539702112538223393,4995116571723105115597460,true⟩,⟨(-2766518709940032694579845),(-920511972494985712893631),true⟩⟩
  | 7,5 => ⟨⟨2990554144423097641900484,4851474261238966980873049,true⟩,⟨(-2510802564636209206256055),(-795964625116334029371758),true⟩⟩
  | 7,6 => ⟨⟨2966004750922975175347329,4742718833108050938919275,true⟩,⟨(-2331435256485720814934861),(-709057559696080476687379),true⟩⟩
  | 7,7 => ⟨⟨2949908233588976790049594,4679382494139010120812749,true⟩,⟨(-2232057604846508446370016),(-661112610047819710300254),true⟩⟩
  | 8,0 => ⟨⟨2614939405523966750030227,5961133738766648969370398,true⟩,⟨(-5972800537975791433028704),(-2491973050205768146257542),true⟩⟩
  | 8,1 => ⟨⟨2345467404700285518769291,6001583365386072112646803,true⟩,⟨(-6739243697388866895633689),(-2861633857441717496666411),true⟩⟩
  | 8,2 => ⟨⟨2052579204351907096686226,5978094109637911348978735,true⟩,⟨(-7412574229032136511851999),(-3182512954732141265433016),true⟩⟩
  | 8,3 => ⟨⟨1834558693573705551784611,5932210401490975282217244,true⟩,⟨(-7845560130860507124944614),(-3386564680524493614551195),true⟩⟩
  | 8,4 => ⟨⟨2808659399954322510918752,5859563746734750740287242,true⟩,⟨(-5252735883074546179793410),(-2141307168654706782469699),true⟩⟩
  | 8,5 => ⟨⟨2923556200506088817948890,5731616536168337852039169,true⟩,⟨(-4669683578577242278642105),(-1855604955537992191678648),true⟩⟩
  | 8,6 => ⟨⟨2981053020740336953676566,5617007916877890884909373,true⟩,⟨(-4262358306851407021417463),(-1655394073444917570211213),true⟩⟩
  | 8,7 => ⟨⟨3004483037277865851754786,5544569141661848955590723,true⟩,⟨(-4037856593805537407598128),(-1544922974170719608062862),true⟩⟩
  | 9,0 => ⟨⟨554007785031662917258940,5431830693119978400004342,true⟩,⟨(-9689259145831027124563772),(-4211214273792342143575422),true⟩⟩
  | 9,1 => ⟨⟨17104168753816948111914,5178813094604645332691101,true⟩,⟨(-10237384703366261072514297),(-4429000948565641895993663),true⟩⟩
  | 9,2 => ⟨⟨(-472352358662507328788013),4933490357928720445954811,true⟩,⟨(-10668006074631693216625730),(-4592962162446129468619694),true⟩⟩
  | 9,3 => ⟨⟨(-791945877606135321949295),4764672838053079495447324,true⟩,⟨(-10923245364522164359707409),(-4686532339243797262960634),true⟩⟩
  | 9,4 => ⟨⟨1042603329313816494512286,5640748422566643171802353,true⟩,⟨(-9112572197551219180722003),(-3970655470924570128572537),true⟩⟩
  | 9,5 => ⟨⟨1381925669256843833667982,5784921633984508534766617,true⟩,⟨(-8617512864400739171028110),(-3745037276667074278317086),true⟩⟩
  | 9,6 => ⟨⟨1617527697344632650546475,5869087893289459392332415,true⟩,⟨(-8234138847538046183538738),(-3567932172960798675347678),true⟩⟩
  | 9,7 => ⟨⟨1746522756060518616503258,5908471823293199008744853,true⟩,⟨(-8007745912676816872802535),(-3462477987261939869376279),true⟩⟩
  | 10,0 => ⟨⟨(-3754394778628351493144200),2945140280406934842463214,true⟩,⟨(-12507787636123242597234562),(-5148964340612652545131239),true⟩⟩
  | 10,1 => ⟨⟨(-4741081380578674245441066),2252840002100183260878867,true⟩,⟨(-12758889205179738439556141),(-5161420861228261543116587),true⟩⟩
  | 10,2 => ⟨⟨(-5553803233430694081317668),1726190854291979007390506,true⟩,⟨(-12863294792363004229435372),(-5081873991838837117676941),true⟩⟩
  | 10,3 => ⟨⟨(-6051628699426177688733503),1407665201531591099072833,true⟩,⟨(-12879051546692506616394142),(-4999850837630572224891510),true⟩⟩
  | 10,4 => ⟨⟨(-2764031598701465674345078),3598846354194397816390177,true⟩,⟨(-12121263512600270921224271),(-5068134720774261504252602),true⟩⟩
  | 10,5 => ⟨⟨(-1916321197160099800884056),4123861461844224665973445,true⟩,⟨(-11680170839185267282125128),(-4942355067571969936864571),true⟩⟩
  | 10,6 => ⟨⟨(-1300652850229096576712198),4483255194161872881957343,true⟩,⟨(-11291588088445877045261579),(-4815721036781708370593445),true⟩⟩
  | 10,7 => ⟨⟨(-953688163553515376425931),4676824089179975381896068,true⟩,⟨(-11045250271998516312921939),(-4730152724413549826403194),true⟩⟩
  | 11,0 => ⟨⟨(-9519293638026703274627701),(-1111248335511443411988225),true⟩,⟨(-11582175544671254614169131),(-3701065099607720151851456),true⟩⟩
  | 11,1 => ⟨⟨(-10285950870136487561807015),(-1765613783778527740446954),true⟩,⟨(-10726169631440896126608415),(-3077285176326698153364624),true⟩⟩
  | 11,2 => ⟨⟨(-10781382721539432293040577),(-2236340684883804873818869),true⟩,⟨(-9903081920327564542456985),(-2500247448401113655840433),true⟩⟩
  | 11,3 => ⟨⟨(-11004807500800250910391043),(-2493879598945519294685328),true⟩,⟨(-9350894779572106916584783),(-2141636158046966258500294),true⟩⟩
  | 11,4 => ⟨⟨(-8583917954371763371132214),(-364947823994357496998494),true⟩,⟨(-12257621988537568971365206),(-4217694773410362432687019),true⟩⟩
  | 11,5 => ⟨⟨(-7606842716793128845783919),351126210891427804780105,true⟩,⟨(-12659023844206175075594253),(-4602830951820765918562741),true⟩⟩
  | 11,6 => ⟨⟨(-6792604285987658757241238),916820692368148143953825,true⟩,⟨(-12828890499521992300117890),(-4839126518948720462066680),true⟩⟩
  | 11,7 => ⟨⟨(-6294011923332070964667902),1249392516652571401189774,true⟩,⟨(-12872691553557585310283181),(-4952533428238434923338059),true⟩⟩
  | 12,0 => ⟨⟨(-10639554147575433546624177),(-3573750302699637593767469),true⟩,⟨(-4523537378986523854991612),444267631934211719948521,true⟩⟩
  | 12,1 => ⟨⟨(-9939610973336601138161449),(-3589073391429722861169204),true⟩,⟨(-3203885600766721447686007),1178779068498682995749342,true⟩⟩
  | 12,2 => ⟨⟨(-9248955742391501982044529),(-3523420715732403625749212),true⟩,⟨(-2246971621144401802548707),1686074551326792379155021,true⟩⟩
  | 12,3 => ⟨⟨(-8792258537463174837107433),(-3436951852757147589845178),true⟩,⟨(-1718286844144618864485002),1936158992612600586142793,true⟩⟩
  | 12,4 => ⟨⟨(-11119548847046149732371236),(-3420068779418207216880044),true⟩,⟨(-6015553092024447970101604),(-313665052458608625892703),true⟩⟩
  | 12,5 => ⟨⟨(-11292181862598300972230005),(-3142468090548289957971073),true⟩,⟨(-7408212318586286885687670),(-1015192676302082126658312),true⟩⟩
  | 12,6 => ⟨⟨(-11221592197681004822731455),(-2832964896141378729537964),true⟩,⟨(-8465778302957914411238321),(-1604786298390287536641202),true⟩⟩
  | 12,7 => ⟨⟨(-11091165465151879932906532),(-2610678512785211911322329),true⟩,⟨(-9069541791308499543740048),(-1966255155514402578906273),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP496Value0_0 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 0 (0:Fin 8))=sharedDiskP496Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value0_1 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 0 (1:Fin 8))=sharedDiskP496Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value0_2 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 0 (2:Fin 8))=sharedDiskP496Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value0_3 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 0 (3:Fin 8))=sharedDiskP496Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value0_4 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 0 (4:Fin 8))=sharedDiskP496Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value0_5 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 0 (5:Fin 8))=sharedDiskP496Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value0_6 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 0 (6:Fin 8))=sharedDiskP496Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value0_7 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 0 (7:Fin 8))=sharedDiskP496Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP496Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 0 j)=sharedDiskP496Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP496Value0_0
  · exact sharedDiskP496Value0_1
  · exact sharedDiskP496Value0_2
  · exact sharedDiskP496Value0_3
  · exact sharedDiskP496Value0_4
  · exact sharedDiskP496Value0_5
  · exact sharedDiskP496Value0_6
  · exact sharedDiskP496Value0_7
private theorem sharedDiskP496Value1_0 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 1 (0:Fin 8))=sharedDiskP496Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value1_1 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 1 (1:Fin 8))=sharedDiskP496Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value1_2 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 1 (2:Fin 8))=sharedDiskP496Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value1_3 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 1 (3:Fin 8))=sharedDiskP496Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value1_4 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 1 (4:Fin 8))=sharedDiskP496Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value1_5 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 1 (5:Fin 8))=sharedDiskP496Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value1_6 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 1 (6:Fin 8))=sharedDiskP496Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value1_7 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 1 (7:Fin 8))=sharedDiskP496Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP496Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 1 j)=sharedDiskP496Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP496Value1_0
  · exact sharedDiskP496Value1_1
  · exact sharedDiskP496Value1_2
  · exact sharedDiskP496Value1_3
  · exact sharedDiskP496Value1_4
  · exact sharedDiskP496Value1_5
  · exact sharedDiskP496Value1_6
  · exact sharedDiskP496Value1_7
private theorem sharedDiskP496Value2_0 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 2 (0:Fin 8))=sharedDiskP496Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value2_1 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 2 (1:Fin 8))=sharedDiskP496Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value2_2 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 2 (2:Fin 8))=sharedDiskP496Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value2_3 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 2 (3:Fin 8))=sharedDiskP496Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value2_4 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 2 (4:Fin 8))=sharedDiskP496Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value2_5 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 2 (5:Fin 8))=sharedDiskP496Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value2_6 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 2 (6:Fin 8))=sharedDiskP496Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value2_7 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 2 (7:Fin 8))=sharedDiskP496Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP496Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 2 j)=sharedDiskP496Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP496Value2_0
  · exact sharedDiskP496Value2_1
  · exact sharedDiskP496Value2_2
  · exact sharedDiskP496Value2_3
  · exact sharedDiskP496Value2_4
  · exact sharedDiskP496Value2_5
  · exact sharedDiskP496Value2_6
  · exact sharedDiskP496Value2_7
private theorem sharedDiskP496Value3_0 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 3 (0:Fin 8))=sharedDiskP496Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value3_1 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 3 (1:Fin 8))=sharedDiskP496Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value3_2 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 3 (2:Fin 8))=sharedDiskP496Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value3_3 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 3 (3:Fin 8))=sharedDiskP496Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value3_4 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 3 (4:Fin 8))=sharedDiskP496Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value3_5 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 3 (5:Fin 8))=sharedDiskP496Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value3_6 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 3 (6:Fin 8))=sharedDiskP496Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value3_7 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 3 (7:Fin 8))=sharedDiskP496Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP496Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 3 j)=sharedDiskP496Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP496Value3_0
  · exact sharedDiskP496Value3_1
  · exact sharedDiskP496Value3_2
  · exact sharedDiskP496Value3_3
  · exact sharedDiskP496Value3_4
  · exact sharedDiskP496Value3_5
  · exact sharedDiskP496Value3_6
  · exact sharedDiskP496Value3_7
private theorem sharedDiskP496Value4_0 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 4 (0:Fin 8))=sharedDiskP496Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value4_1 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 4 (1:Fin 8))=sharedDiskP496Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value4_2 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 4 (2:Fin 8))=sharedDiskP496Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value4_3 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 4 (3:Fin 8))=sharedDiskP496Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value4_4 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 4 (4:Fin 8))=sharedDiskP496Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value4_5 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 4 (5:Fin 8))=sharedDiskP496Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value4_6 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 4 (6:Fin 8))=sharedDiskP496Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value4_7 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 4 (7:Fin 8))=sharedDiskP496Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP496Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 4 j)=sharedDiskP496Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP496Value4_0
  · exact sharedDiskP496Value4_1
  · exact sharedDiskP496Value4_2
  · exact sharedDiskP496Value4_3
  · exact sharedDiskP496Value4_4
  · exact sharedDiskP496Value4_5
  · exact sharedDiskP496Value4_6
  · exact sharedDiskP496Value4_7
private theorem sharedDiskP496Value5_0 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 5 (0:Fin 8))=sharedDiskP496Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value5_1 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 5 (1:Fin 8))=sharedDiskP496Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value5_2 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 5 (2:Fin 8))=sharedDiskP496Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value5_3 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 5 (3:Fin 8))=sharedDiskP496Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value5_4 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 5 (4:Fin 8))=sharedDiskP496Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value5_5 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 5 (5:Fin 8))=sharedDiskP496Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value5_6 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 5 (6:Fin 8))=sharedDiskP496Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value5_7 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 5 (7:Fin 8))=sharedDiskP496Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP496Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 5 j)=sharedDiskP496Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP496Value5_0
  · exact sharedDiskP496Value5_1
  · exact sharedDiskP496Value5_2
  · exact sharedDiskP496Value5_3
  · exact sharedDiskP496Value5_4
  · exact sharedDiskP496Value5_5
  · exact sharedDiskP496Value5_6
  · exact sharedDiskP496Value5_7
private theorem sharedDiskP496Value6_0 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 6 (0:Fin 8))=sharedDiskP496Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value6_1 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 6 (1:Fin 8))=sharedDiskP496Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value6_2 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 6 (2:Fin 8))=sharedDiskP496Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value6_3 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 6 (3:Fin 8))=sharedDiskP496Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value6_4 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 6 (4:Fin 8))=sharedDiskP496Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value6_5 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 6 (5:Fin 8))=sharedDiskP496Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value6_6 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 6 (6:Fin 8))=sharedDiskP496Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value6_7 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 6 (7:Fin 8))=sharedDiskP496Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP496Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 6 j)=sharedDiskP496Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP496Value6_0
  · exact sharedDiskP496Value6_1
  · exact sharedDiskP496Value6_2
  · exact sharedDiskP496Value6_3
  · exact sharedDiskP496Value6_4
  · exact sharedDiskP496Value6_5
  · exact sharedDiskP496Value6_6
  · exact sharedDiskP496Value6_7
private theorem sharedDiskP496Value7_0 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 7 (0:Fin 8))=sharedDiskP496Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value7_1 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 7 (1:Fin 8))=sharedDiskP496Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value7_2 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 7 (2:Fin 8))=sharedDiskP496Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value7_3 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 7 (3:Fin 8))=sharedDiskP496Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value7_4 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 7 (4:Fin 8))=sharedDiskP496Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value7_5 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 7 (5:Fin 8))=sharedDiskP496Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value7_6 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 7 (6:Fin 8))=sharedDiskP496Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value7_7 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 7 (7:Fin 8))=sharedDiskP496Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP496Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 7 j)=sharedDiskP496Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP496Value7_0
  · exact sharedDiskP496Value7_1
  · exact sharedDiskP496Value7_2
  · exact sharedDiskP496Value7_3
  · exact sharedDiskP496Value7_4
  · exact sharedDiskP496Value7_5
  · exact sharedDiskP496Value7_6
  · exact sharedDiskP496Value7_7
private theorem sharedDiskP496Value8_0 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 8 (0:Fin 8))=sharedDiskP496Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value8_1 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 8 (1:Fin 8))=sharedDiskP496Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value8_2 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 8 (2:Fin 8))=sharedDiskP496Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value8_3 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 8 (3:Fin 8))=sharedDiskP496Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value8_4 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 8 (4:Fin 8))=sharedDiskP496Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value8_5 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 8 (5:Fin 8))=sharedDiskP496Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value8_6 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 8 (6:Fin 8))=sharedDiskP496Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value8_7 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 8 (7:Fin 8))=sharedDiskP496Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP496Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 8 j)=sharedDiskP496Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP496Value8_0
  · exact sharedDiskP496Value8_1
  · exact sharedDiskP496Value8_2
  · exact sharedDiskP496Value8_3
  · exact sharedDiskP496Value8_4
  · exact sharedDiskP496Value8_5
  · exact sharedDiskP496Value8_6
  · exact sharedDiskP496Value8_7
private theorem sharedDiskP496Value9_0 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 9 (0:Fin 8))=sharedDiskP496Values 9 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value9_1 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 9 (1:Fin 8))=sharedDiskP496Values 9 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value9_2 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 9 (2:Fin 8))=sharedDiskP496Values 9 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value9_3 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 9 (3:Fin 8))=sharedDiskP496Values 9 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value9_4 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 9 (4:Fin 8))=sharedDiskP496Values 9 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value9_5 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 9 (5:Fin 8))=sharedDiskP496Values 9 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value9_6 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 9 (6:Fin 8))=sharedDiskP496Values 9 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value9_7 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 9 (7:Fin 8))=sharedDiskP496Values 9 (7:Fin 8) := by decide +kernel
theorem sharedDiskP496Values9_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 9 j)=sharedDiskP496Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP496Value9_0
  · exact sharedDiskP496Value9_1
  · exact sharedDiskP496Value9_2
  · exact sharedDiskP496Value9_3
  · exact sharedDiskP496Value9_4
  · exact sharedDiskP496Value9_5
  · exact sharedDiskP496Value9_6
  · exact sharedDiskP496Value9_7
private theorem sharedDiskP496Value10_0 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 10 (0:Fin 8))=sharedDiskP496Values 10 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value10_1 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 10 (1:Fin 8))=sharedDiskP496Values 10 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value10_2 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 10 (2:Fin 8))=sharedDiskP496Values 10 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value10_3 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 10 (3:Fin 8))=sharedDiskP496Values 10 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value10_4 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 10 (4:Fin 8))=sharedDiskP496Values 10 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value10_5 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 10 (5:Fin 8))=sharedDiskP496Values 10 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value10_6 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 10 (6:Fin 8))=sharedDiskP496Values 10 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value10_7 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 10 (7:Fin 8))=sharedDiskP496Values 10 (7:Fin 8) := by decide +kernel
theorem sharedDiskP496Values10_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 10 j)=sharedDiskP496Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP496Value10_0
  · exact sharedDiskP496Value10_1
  · exact sharedDiskP496Value10_2
  · exact sharedDiskP496Value10_3
  · exact sharedDiskP496Value10_4
  · exact sharedDiskP496Value10_5
  · exact sharedDiskP496Value10_6
  · exact sharedDiskP496Value10_7
private theorem sharedDiskP496Value11_0 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 11 (0:Fin 8))=sharedDiskP496Values 11 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value11_1 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 11 (1:Fin 8))=sharedDiskP496Values 11 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value11_2 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 11 (2:Fin 8))=sharedDiskP496Values 11 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value11_3 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 11 (3:Fin 8))=sharedDiskP496Values 11 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value11_4 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 11 (4:Fin 8))=sharedDiskP496Values 11 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value11_5 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 11 (5:Fin 8))=sharedDiskP496Values 11 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value11_6 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 11 (6:Fin 8))=sharedDiskP496Values 11 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value11_7 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 11 (7:Fin 8))=sharedDiskP496Values 11 (7:Fin 8) := by decide +kernel
theorem sharedDiskP496Values11_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 11 j)=sharedDiskP496Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP496Value11_0
  · exact sharedDiskP496Value11_1
  · exact sharedDiskP496Value11_2
  · exact sharedDiskP496Value11_3
  · exact sharedDiskP496Value11_4
  · exact sharedDiskP496Value11_5
  · exact sharedDiskP496Value11_6
  · exact sharedDiskP496Value11_7
private theorem sharedDiskP496Value12_0 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 12 (0:Fin 8))=sharedDiskP496Values 12 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value12_1 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 12 (1:Fin 8))=sharedDiskP496Values 12 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value12_2 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 12 (2:Fin 8))=sharedDiskP496Values 12 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value12_3 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 12 (3:Fin 8))=sharedDiskP496Values 12 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value12_4 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 12 (4:Fin 8))=sharedDiskP496Values 12 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value12_5 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 12 (5:Fin 8))=sharedDiskP496Values 12 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value12_6 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 12 (6:Fin 8))=sharedDiskP496Values 12 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP496Value12_7 : truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 12 (7:Fin 8))=sharedDiskP496Values 12 (7:Fin 8) := by decide +kernel
theorem sharedDiskP496Values12_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points 12 j)=sharedDiskP496Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP496Value12_0
  · exact sharedDiskP496Value12_1
  · exact sharedDiskP496Value12_2
  · exact sharedDiskP496Value12_3
  · exact sharedDiskP496Value12_4
  · exact sharedDiskP496Value12_5
  · exact sharedDiskP496Value12_6
  · exact sharedDiskP496Value12_7
theorem sharedDiskP496Values_eq : ∀ (i : Fin 13) (j : Fin 8), truncatedChordCell 2 sharedDiskP496Params (sharedChord493Gauss8Points i j)=sharedDiskP496Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP496Values0_eq
  · exact sharedDiskP496Values1_eq
  · exact sharedDiskP496Values2_eq
  · exact sharedDiskP496Values3_eq
  · exact sharedDiskP496Values4_eq
  · exact sharedDiskP496Values5_eq
  · exact sharedDiskP496Values6_eq
  · exact sharedDiskP496Values7_eq
  · exact sharedDiskP496Values8_eq
  · exact sharedDiskP496Values9_eq
  · exact sharedDiskP496Values10_eq
  · exact sharedDiskP496Values11_eq
  · exact sharedDiskP496Values12_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP496Box : HorizontalRectangle := ⟨(33/50),(27/40),(58929547351633/109951162777600),(300093324678443/549755813888000),(299096853509047264186689978889323/649037107316853453566312041152512),(5175338986126647672369822249870973/1298074214633706907132624082305024),(-2928908416006025340073397786463897/649037107316853453566312041152512),(-1072365896716781457803792666238257/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP496Grid : CGrid := momentChordGrid sharedDiskP496Params chordGaussRule8 2 sharedChord493Bd sharedChord493M (23175049/18014398509481984)
theorem sharedDiskP496Columns : containedInReported sharedDiskP496Grid.re sharedDiskP496Box.reLo sharedDiskP496Box.reHi=true ∧ containedInReported sharedDiskP496Grid.im sharedDiskP496Box.imLo sharedDiskP496Box.imHi=true := by
  rw [sharedDiskP496Grid,momentChordGrid_eq_tabulated sharedDiskP496Params chordGaussRule8 2 sharedChord493Bd sharedChord493M (23175049/18014398509481984) sharedChord493Gauss8Points sharedChord493Gauss8Weights sharedDiskP496Values sharedChord493Gauss8Points_eq sharedChord493Gauss8Weights_eq sharedDiskP496Values_eq]
  decide +kernel
theorem sharedDiskP496Sound : sharedDiskP496Box.Sound := by
  intro t a tl tu al au
  change (((33/50):ℚ):ℝ)≤t at tl
  change t≤(((27/40):ℚ):ℝ) at tu
  change (((58929547351633/109951162777600):ℚ):ℝ)≤a at al
  change a≤(((300093324678443/549755813888000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP496Params_ok] at ps
  have band := sharedChord493ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((129/200):ℚ)≤(33/50))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((27/40):ℚ)≤(3/4)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((878940159632233/1649267441664000):ℚ)≤(58929547351633/109951162777600))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((300093324678443/549755813888000):ℚ)≤(929134916903873/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord493Bd (by decide +kernel) (by decide +kernel) sharedChord493M (by decide +kernel) (sharedChord493Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP496Columns.1 sharedDiskP496Columns.2
def sharedDiskP496Rows : List SignRow := [positive_496.toSignRow, positive_497.toSignRow, positive_498.toSignRow]
theorem sharedDiskP496Rows_actual : ∀ r∈sharedDiskP496Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP496Rows.all (sharedDiskP496Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP496Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP499Params : ChordParams := ⟨⟨(-12319961638523602756072),(-11510689821132100290638),true⟩,⟨2506005444313423016254154,2593175913929597829292206,true⟩,⟨94339991204483961963332,101995781443480465240688,true⟩,⟨141523057024523733705814,152104589560046269245772,true⟩,⟨233548495762119539910803,241779214333712043379117,true⟩,⟨1184534464573566287088050,1186121568809684943177856,true⟩,⟨(-2760230227286597521496047),(-2716295453889222659454472),true⟩,⟨⟨1131146980855095044827921,1240920993028329956688587,true⟩,⟨(-8936),8936,true⟩⟩⟩
theorem sharedDiskP499Params_ok : chordParams (Grid.ofRats (27/40) (137/200)) (Grid.ofRats (889155926669671/1649267441664000) (903824955642727/1649267441664000))=sharedDiskP499Params := by decide +kernel
def sharedDiskP499Values (i : Fin 13) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-6694865277589946058284855),(-2145147164071935481127410),true⟩,⟨(-2028859439689732951653511),2169669921565709413683003,true⟩⟩
  | 0,1 => ⟨⟨(-6197243735237426161173986),(-1882930029860986604810227),true⟩,⟨(-2035952041702444646211723),1966871437748155933769877,true⟩⟩
  | 0,2 => ⟨⟨(-5813932644488355947617432),(-1698130107350601791232162),true⟩,⟨(-2035647388756393003907708),1785610523974097239474446,true⟩⟩
  | 0,3 => ⟨⟨(-5588413962989422109140369),(-1595508109225745286540927),true⟩,⟨(-2033287820222772550688790),1670599117979022651338191,true⟩⟩
  | 0,4 => ⟨⟨(-7240223790735442070300757),(-2453241220016814044447563),true⟩,⟨(-2010710881307699016818205),2339343723286874306848915,true⟩⟩
  | 0,5 => ⟨⟨(-7753527365657429403945543),(-2775814317200733502653611),true⟩,⟨(-1983457138012503404318369),2437085645052787818999969,true⟩⟩
  | 0,6 => ⟨⟨(-8159665791687865192482757),(-3068205093084904092995781),true⟩,⟨(-1955172550465924168487178),2463711874597910381483792,true⟩⟩
  | 0,7 => ⟨⟨(-8403215017726802226938664),(-3260840859835813826674218),true⟩,⟨(-1935641629455885604772061),2455343627172908129560981,true⟩⟩
  | 1,0 => ⟨⟨(-4078602991971308569687382),(-993020344543890095677910),true⟩,⟨(-1983753896191624644376641),890650021416809623930449,true⟩⟩
  | 1,1 => ⟨⟨(-3716830150182327686829154),(-863000915441160570466786),true⟩,⟨(-1964928696926544631541552),702969454095261151296441,true⟩⟩
  | 1,2 => ⟨⟨(-3448819547137888611577952),(-768230725246538779392304),true⟩,⟨(-1949606256277869899251439),562661867491450786683669,true⟩⟩
  | 1,3 => ⟨⟨(-3294866865206642226431686),(-714059879551205162074308),true⟩,⟨(-1940305234439956515649576),481986714383016456077039,true⟩⟩
  | 1,4 => ⟨⟨(-4496335250866351769026605),(-1148207394151318928414405),true⟩,⟨(-2002523609760569303989155),1102333137254743718476105,true⟩⟩
  | 1,5 => ⟨⟨(-4913313769086339871860648),(-1310884546566158953412860),true⟩,⟨(-2017603689904691124162712),1305252461794110050181764,true⟩⟩
  | 1,6 => ⟨⟨(-5262561732771380248022001),(-1454282113191999474359083),true⟩,⟨(-2027232302496520171847594),1495373309180929341398406,true⟩⟩
  | 1,7 => ⟨⟨(-5480689315507273660894063),(-1547940154783506018723629),true⟩,⟨(-2031621953796679810708048),1613767015638981772746479,true⟩⟩
  | 2,0 => ⟨⟨(-2312297115563979685529005),(-361441004450604417366480),true⟩,⟨(-1871974492743975471377914),(-19430665363089956799568),true⟩⟩
  | 2,1 => ⟨⟨(-2087695746246833877216454),(-274667467909065966888286),true⟩,⟨(-1853316663133633498061015),(-120012694047144215311568),true⟩⟩
  | 2,2 => ⟨⟨(-1925045665226549351728717),(-208500981852645011277199),true⟩,⟨(-1838560176594363977114032),(-185318583928285581705554),true⟩⟩
  | 2,3 => ⟨⟨(-1831402690688284463732067),(-169555852951406721697907),true⟩,⟨(-1829638343638596501687196),(-221870018457308391525209),true⟩⟩
  | 2,4 => ⟨⟨(-2578094248171656254806326),(-459324546764085607079584),true⟩,⟨(-1892156003473027883248207),112030834411754781976064,true⟩⟩
  | 2,5 => ⟨⟨(-2847355522945573643294207),(-556059801549890802790927),true⟩,⟨(-1911221030192729374568941),249211939147609755129745,true⟩⟩
  | 2,6 => ⟨⟨(-3076645513507791882877282),(-637250434894080028261900),true⟩,⟨(-1926507996103379020888919),367983311779845809234111,true⟩⟩
  | 2,7 => ⟨⟨(-3222202045704569557996296),(-688503705209434376417709),true⟩,⟨(-1935790881872387045299613),443957997693577921346349,true⟩⟩
  | 3,0 => ⟨⟨(-1222406141251884528128279),104328123072490613389320,true⟩,⟨(-1761153242383935962855923),(-435079893510567023337444),true⟩⟩
  | 3,1 => ⟨⟨(-1076062312511186778686309),176687157019691533202909,true⟩,⟨(-1741076352681579461323591),(-478410067553937641149751),true⟩⟩
  | 3,2 => ⟨⟨(-966189628452508771402785),232718464655919175633845,true⟩,⟨(-1724801174161156165323724),(-508509644496990603912517),true⟩⟩
  | 3,3 => ⟨⟨(-902297009363246512722325),265997869033524203428620,true⟩,⟨(-1714817633612171662142243),(-524994092970425761474075),true⟩⟩
  | 3,4 => ⟨⟨(-1389942929009442811302743),24502523196913002104824,true⟩,⟨(-1782164807956682040173000),(-381315382679625557148804),true⟩⟩
  | 3,5 => ⟨⟨(-1557204607693630504188066),(-51390809169364758158694),true⟩,⟨(-1801345896633355760493333),(-323676515023806303862627),true⟩⟩
  | 3,6 => ⟨⟨(-1698157357307002097356300),(-112946654997511289108727),true⟩,⟨(-1816326951497312192880344),(-272382139787356152147046),true⟩⟩
  | 3,7 => ⟨⟨(-1787111811892086994591719),(-150900102029334806021176),true⟩,⟨(-1825297969521423673470578),(-238863867290359889637335),true⟩⟩
  | 4,0 => ⟨⟨349389063485319409800870,1155849747687895711379105,true⟩,⟨(-1410748436627512323984513),(-576276913622579129820051),true⟩⟩
  | 4,1 => ⟨⟨578116013911812262499828,1362896264233673266297112,true⟩,⟨(-1330111364606108157108272),(-535962613742840407335575),true⟩⟩
  | 4,2 => ⟨⟨741158751079651781476860,1513071657586367975342095,true⟩,⟨(-1266350272135228576068066),(-498765288590040063748407),true⟩⟩
  | 4,3 => ⟨⟨832739170035019340541909,1598156793725468679745332,true⟩,⟨(-1228493391157145422495532),(-475164603307180513646864),true⟩⟩
  | 4,4 => ⟨⟨51357514404096383765845,909943860229566939073035,true⟩,⟨(-1505185110003186701641150),(-604210408960675593698991),true⟩⟩
  | 4,5 => ⟨⟨(-290890496696441461321403),655866377060056717781540,true⟩,⟨(-1596198533060248336455542),(-605520935261373385038150),true⟩⟩
  | 4,6 => ⟨⟨(-610334715449967594417101),435303582068903131523253,true⟩,⟨(-1664302822029670811937531),(-579815239573881929731427),true⟩⟩
  | 4,7 => ⟨⟨(-829854741712917118299055),305861137747326186961487,true⟩,⟨(-1703155261921361321757622),(-541046814665069519191119),true⟩⟩
  | 5,0 => ⟨⟨1773310051157962039442502,2487028548015623291026966,true⟩,⟨(-811680829838273897707169),(-182479240501571843858727),true⟩⟩
  | 5,1 => ⟨⟨1951666235627354006256862,2659715155096698237521992,true⟩,⟨(-755303707905975580582188),(-141223520464366132014267),true⟩⟩
  | 5,2 => ⟨⟨2078686743271008150607195,2786128289229735637865849,true⟩,⟨(-732995367830968864818368),(-124706309799134209713625),true⟩⟩
  | 5,3 => ⟨⟨2151324231745332207310934,2860620991537646550725123,true⟩,⟨(-729920923935132934706016),(-122095455674135002198795),true⟩⟩
  | 5,4 => ⟨⟨1549043209758420850772602,2273268288986078964379976,true⟩,⟨(-904869005517121010283770),(-250444178643623036334116),true⟩⟩
  | 5,5 => ⟨⟨1297333814685444402206136,2034827547266427938817714,true⟩,⟨(-1020337037349246605318209),(-333570814012176267310324),true⟩⟩
  | 5,6 => ⟨⟨1059782721744432289762150,1810759503978776719436296,true⟩,⟨(-1129381424727485247998031),(-409674308052049750573462),true⟩⟩
  | 5,7 => ⟨⟨896461642532157612109161,1657613996451191071213100,true⟩,⟨(-1201375495202027543611366),(-457716850383843661103022),true⟩⟩
  | 6,0 => ⟨⟨2644585295785371411753047,3602573854105611802393675,true⟩,⟨(-1118615591494909227853343),(-288106845357646075372955),true⟩⟩
  | 6,1 => ⟨⟨2808726282462463200872903,3913815167783345275648957,true⟩,⟨(-1434806063526725682584089),(-457569167941564515766031),true⟩⟩
  | 6,2 => ⟨⟨2947252452311119211240144,4217375668162463630043173,true⟩,⟨(-1819411278841949554693480),(-670922487934165936498630),true⟩⟩
  | 6,3 => ⟨⟨3028363129449206420259987,4428057750134941707680375,true⟩,⟨(-2136816934254676657324541),(-849954334079463762494124),true⟩⟩
  | 6,4 => ⟨⟨2486773030890311325535276,3336001814953663482407886,true⟩,⟨(-911770369991700488379555),(-184602375839826074834221),true⟩⟩
  | 6,5 => ⟨⟨2351624176346847107960157,3129246409641359934687991,true⟩,⟨(-799068411371448324003861),(-136043245956553241211705),true⟩⟩
  | 6,6 => ⟨⟨2247510160766383073050588,2982732083522213577722913,true⟩,⟨(-749231613410918334897620),(-121649813650712841927536),true⟩⟩
  | 6,7 => ⟨⟨2183982166927023842376409,2898472549243582174694517,true⟩,⟨(-732881967525184684931914),(-121474888210801357983471),true⟩⟩
  | 7,0 => ⟨⟨3143788700775952626429033,4914321813903096768423770,true⟩,⟨(-3097859405172478805493940),(-1399229664727266084937440),true⟩⟩
  | 7,1 => ⟨⟨3146491355286798139512751,5042029177050065085717418,true⟩,⟨(-3435292887810260328724118),(-1593183186641225334937175),true⟩⟩
  | 7,2 => ⟨⟨3134336940217423330527763,5140120795274270453133603,true⟩,⟨(-3737398598476119112141631),(-1766936985191149944089800),true⟩⟩
  | 7,3 => ⟨⟨3119175819549219892402761,5196730858317633208328510,true⟩,⟨(-3936129745195091647739052),(-1881221483146188646060191),true⟩⟩
  | 7,4 => ⟨⟨3124727337519794540773413,4776683909588625847520654,true⟩,⟨(-2783447847715408900616778),(-1218822216318500830232540),true⟩⟩
  | 7,5 => ⟨⟨3096542971253296704427766,4650546272027584176651567,true⟩,⟨(-2528440943560154323335438),(-1072898771380151819017734),true⟩⟩
  | 7,6 => ⟨⟨3069290892614432918033792,4553272355718341177480553,true⟩,⟨(-2349084908114429171271808),(-970581795239769035960759),true⟩⟩
  | 7,7 => ⟨⟨3051322915266568550666882,4495988573680393513973708,true⟩,⟨(-2249553502245403661823714),(-913948629065662180407266),true⟩⟩
  | 8,0 => ⟨⟨2685508844014920592913143,5447230281122939688308791,true⟩,⟨(-5894165039621328115287856),(-3000503426113344820246101),true⟩⟩
  | 8,1 => ⟨⟨2398350426100864759745861,5402997226515247609329733,true⟩,⟨(-6610188437483504543601121),(-3404131714432095049155855),true⟩⟩
  | 8,2 => ⟨⟨2089615924628810982097182,5302195080475122979007123,true⟩,⟨(-7229015490568247927358008),(-3749249803600858755111030),true⟩⟩
  | 8,3 => ⟨⟨1861680566349790342948182,5205397277610828964696339,true⟩,⟨(-7621493903718370428754420),(-3965959235057675291498068),true⟩⟩
  | 8,4 => ⟨⟨2894410768833724510297455,5421323004470090455388119,true⟩,⟨(-5211029682184007201865936),(-2612031138795752794596817),true⟩⟩
  | 8,5 => ⟨⟨3019780442903885863173928,5351355021753655363698954,true⟩,⟨(-4650929753603450212233951),(-2291665249453441023766261),true⟩⟩
  | 8,6 => ⟨⟨3083221849509930262109290,5275236826780132416462585,true⟩,⟨(-4256128965546676603600110),(-2065125841776603075646904),true⟩⟩
  | 8,7 => ⟨⟨3109327134101829519695154,5223225142403430582432739,true⟩,⟨(-4037339949094599403996847),(-1939407192276988671346658),true⟩⟩
  | 9,0 => ⟨⟨551325990410445911979039,4485942862626977940769515,true⟩,⟨(-9239387961518292979922935),(-4814916692893629380820765),true⟩⟩
  | 9,1 => ⟨⟨30056260880558583288912,4171454689522686237606187,true⟩,⟨(-9694191014489412010349447),(-5029492884839194693046872),true⟩⟩
  | 9,2 => ⟨⟨(-436587408500036352764864),3878745435432544472114055,true⟩,⟨(-10042522455067015205994585),(-5187003436781928990441613),true⟩⟩
  | 9,3 => ⟨⟨(-739173709001272467710553),3682405822678672951754559,true⟩,⟨(-10244578950784084292606173),(-5274859279991494608585856),true⟩⟩
  | 9,4 => ⟨⟨1040888934301747538938945,4760961039278854364427550,true⟩,⟨(-8744124150553698202604807),(-4572451035854825496519658),true⟩⟩
  | 9,5 => ⟨⟨1392824001154914344896968,4965481467084949116536619,true⟩,⟨(-8309527536681516345825244),(-4340851972722097145003956),true⟩⟩
  | 9,6 => ⟨⟨1636179911397622549046700,5095912130606549186981034,true⟩,⟨(-7969796951016847044053393),(-4156616457532375675907867),true⟩⟩
  | 9,7 => ⟨⟨1770048279985425186276119,5162378919592867587407391,true⟩,⟨(-7767335711013152730609953),(-4045994412737091720466345),true⟩⟩
  | 10,0 => ⟨⟨(-3471575736834198426654082),1740769570053190387941916,true⟩,⟨(-11364702494681160555620922),(-5634202305327564365285950),true⟩⟩
  | 10,1 => ⟨⟨(-4355157382287629792285542),1131168088004768591883747,true⟩,⟨(-11477414569132747482449067),(-5559753290340859994074421),true⟩⟩
  | 10,2 => ⟨⟨(-5073596021711002812839804),616710944060626961191124,true⟩,⟨(-11476466715223469867200598),(-5443080079177956927378537),true⟩⟩
  | 10,3 => ⟨⟨(-5509531457771263187966324),295711131543001952255423,true⟩,⟨(-11432293500930392015608199),(-5346038646107622802416914),true⟩⟩
  | 10,4 => ⟨⟨(-2571844490939627427673960),2398730458162287614443996,true⟩,⟨(-11126477304811369284381141),(-5602075962699530825375570),true⟩⟩
  | 10,5 => ⟨⟨(-1791033734042698336043982),2964027060608596639846041,true⟩,⟨(-10818366810917329687575527),(-5503097740457136158685508),true⟩⟩
  | 10,6 => ⟨⟨(-1217453673475943592679913),3362314401091642755012264,true⟩,⟨(-10529231346302627440200640),(-5392875479745921182722603),true⟩⟩
  | 10,7 => ⟨⟨(-891681311660012473320796),3581593304474949790663384,true⟩,⟨(-10339839554925939698437667),(-5315188118111725204478968),true⟩⟩
  | 11,0 => ⟨⟨(-8454184963447246867169988),(-2101366786939441797234603),true⟩,⟨(-9881742279048479929046123),(-3950113030357214963792129),true⟩⟩
  | 11,1 => ⟨⟨(-9036823695709955282032374),(-2690682468536221303755719),true⟩,⟨(-9047463361733032221926981),(-3366999896485105655514551),true⟩⟩
  | 11,2 => ⟨⟨(-9415853460122619547527593),(-3100646961742826293588548),true⟩,⟨(-8278148664207096442789363),(-2818363889328089252516431),true⟩⟩
  | 11,3 => ⟨⟨(-9588275424536805649365206),(-3318553985887713458669610),true⟩,⟨(-7774129217670439798748106),(-2470173012288019131085243),true⟩⟩
  | 11,4 => ⟨⟨(-7677016006223697111694462),(-1407458615115557636900401),true⟩,⟨(-10584903797945378872998141),(-4490714132572321512104942),true⟩⟩
  | 11,5 => ⟨⟨(-6850917098150981447533770),(-729850346120770027784684),true⟩,⟨(-11054192406163812634470368),(-4903043905496604706053917),true⟩⟩
  | 11,6 => ⟨⟨(-6152543162203576195880023),(-188280558137567225176900),true⟩,⟨(-11300640620112128710392717),(-5163136187168816793589989),true⟩⟩
  | 11,7 => ⟨⟨(-5720641997947103810478282),137675631061090216017447,true⟩,⟨(-11398193322435126845569459),(-5291431794898575006820771),true⟩⟩
  | 12,0 => ⟨⟨(-9236080446069308718838243),(-4090745426209896218234119),true⟩,⟨(-3582116908128626585619185),13760850945458669560945,true⟩⟩
  | 12,1 => ⟨⟨(-8667418720658728197644507),(-4032180647451280538457923),true⟩,⟨(-2473995542020631518585524),649845452882767844130296,true⟩⟩
  | 12,2 => ⟨⟨(-8109683318011568059490532),(-3914765080437170145167466),true⟩,⟨(-1675462185528614764488409),1128690555368643768469502,true⟩⟩
  | 12,3 => ⟨⟨(-7739294210746564373796363),(-3805789143519961728207844),true⟩,⟨(-1235372680307260357025370),1372314073041753370026186,true⟩⟩
  | 12,4 => ⟨⟨(-9639500057759639987428890),(-4025320519778850542571859),true⟩,⟨(-4849566728913564915631177),(-680611085933743879277501),true⟩⟩
  | 12,5 => ⟨⟨(-9793364146552540236998849),(-3835343770789970077728701),true⟩,⟨(-6051311778924604223625362),(-1372524471662797369915567),true⟩⟩
  | 12,6 => ⟨⟨(-9750402306274408002333567),(-3596143927872828505897224),true⟩,⟨(-6980901028941838745903969),(-1948251504939245791619540),true⟩⟩
  | 12,7 => ⟨⟨(-9653856955150363334369926),(-3415536369363501109261069),true⟩,⟨(-7520213494808391156299672),(-2299808619654433845998816),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP499Value0_0 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 0 (0:Fin 8))=sharedDiskP499Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value0_1 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 0 (1:Fin 8))=sharedDiskP499Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value0_2 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 0 (2:Fin 8))=sharedDiskP499Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value0_3 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 0 (3:Fin 8))=sharedDiskP499Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value0_4 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 0 (4:Fin 8))=sharedDiskP499Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value0_5 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 0 (5:Fin 8))=sharedDiskP499Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value0_6 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 0 (6:Fin 8))=sharedDiskP499Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value0_7 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 0 (7:Fin 8))=sharedDiskP499Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP499Values0_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 0 j)=sharedDiskP499Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP499Value0_0
  · exact sharedDiskP499Value0_1
  · exact sharedDiskP499Value0_2
  · exact sharedDiskP499Value0_3
  · exact sharedDiskP499Value0_4
  · exact sharedDiskP499Value0_5
  · exact sharedDiskP499Value0_6
  · exact sharedDiskP499Value0_7
private theorem sharedDiskP499Value1_0 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 1 (0:Fin 8))=sharedDiskP499Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value1_1 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 1 (1:Fin 8))=sharedDiskP499Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value1_2 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 1 (2:Fin 8))=sharedDiskP499Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value1_3 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 1 (3:Fin 8))=sharedDiskP499Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value1_4 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 1 (4:Fin 8))=sharedDiskP499Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value1_5 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 1 (5:Fin 8))=sharedDiskP499Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value1_6 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 1 (6:Fin 8))=sharedDiskP499Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value1_7 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 1 (7:Fin 8))=sharedDiskP499Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP499Values1_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 1 j)=sharedDiskP499Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP499Value1_0
  · exact sharedDiskP499Value1_1
  · exact sharedDiskP499Value1_2
  · exact sharedDiskP499Value1_3
  · exact sharedDiskP499Value1_4
  · exact sharedDiskP499Value1_5
  · exact sharedDiskP499Value1_6
  · exact sharedDiskP499Value1_7
private theorem sharedDiskP499Value2_0 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 2 (0:Fin 8))=sharedDiskP499Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value2_1 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 2 (1:Fin 8))=sharedDiskP499Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value2_2 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 2 (2:Fin 8))=sharedDiskP499Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value2_3 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 2 (3:Fin 8))=sharedDiskP499Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value2_4 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 2 (4:Fin 8))=sharedDiskP499Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value2_5 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 2 (5:Fin 8))=sharedDiskP499Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value2_6 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 2 (6:Fin 8))=sharedDiskP499Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value2_7 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 2 (7:Fin 8))=sharedDiskP499Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP499Values2_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 2 j)=sharedDiskP499Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP499Value2_0
  · exact sharedDiskP499Value2_1
  · exact sharedDiskP499Value2_2
  · exact sharedDiskP499Value2_3
  · exact sharedDiskP499Value2_4
  · exact sharedDiskP499Value2_5
  · exact sharedDiskP499Value2_6
  · exact sharedDiskP499Value2_7
private theorem sharedDiskP499Value3_0 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 3 (0:Fin 8))=sharedDiskP499Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value3_1 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 3 (1:Fin 8))=sharedDiskP499Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value3_2 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 3 (2:Fin 8))=sharedDiskP499Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value3_3 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 3 (3:Fin 8))=sharedDiskP499Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value3_4 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 3 (4:Fin 8))=sharedDiskP499Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value3_5 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 3 (5:Fin 8))=sharedDiskP499Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value3_6 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 3 (6:Fin 8))=sharedDiskP499Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value3_7 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 3 (7:Fin 8))=sharedDiskP499Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP499Values3_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 3 j)=sharedDiskP499Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP499Value3_0
  · exact sharedDiskP499Value3_1
  · exact sharedDiskP499Value3_2
  · exact sharedDiskP499Value3_3
  · exact sharedDiskP499Value3_4
  · exact sharedDiskP499Value3_5
  · exact sharedDiskP499Value3_6
  · exact sharedDiskP499Value3_7
private theorem sharedDiskP499Value4_0 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 4 (0:Fin 8))=sharedDiskP499Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value4_1 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 4 (1:Fin 8))=sharedDiskP499Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value4_2 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 4 (2:Fin 8))=sharedDiskP499Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value4_3 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 4 (3:Fin 8))=sharedDiskP499Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value4_4 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 4 (4:Fin 8))=sharedDiskP499Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value4_5 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 4 (5:Fin 8))=sharedDiskP499Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value4_6 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 4 (6:Fin 8))=sharedDiskP499Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value4_7 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 4 (7:Fin 8))=sharedDiskP499Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP499Values4_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 4 j)=sharedDiskP499Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP499Value4_0
  · exact sharedDiskP499Value4_1
  · exact sharedDiskP499Value4_2
  · exact sharedDiskP499Value4_3
  · exact sharedDiskP499Value4_4
  · exact sharedDiskP499Value4_5
  · exact sharedDiskP499Value4_6
  · exact sharedDiskP499Value4_7
private theorem sharedDiskP499Value5_0 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 5 (0:Fin 8))=sharedDiskP499Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value5_1 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 5 (1:Fin 8))=sharedDiskP499Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value5_2 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 5 (2:Fin 8))=sharedDiskP499Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value5_3 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 5 (3:Fin 8))=sharedDiskP499Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value5_4 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 5 (4:Fin 8))=sharedDiskP499Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value5_5 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 5 (5:Fin 8))=sharedDiskP499Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value5_6 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 5 (6:Fin 8))=sharedDiskP499Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value5_7 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 5 (7:Fin 8))=sharedDiskP499Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP499Values5_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 5 j)=sharedDiskP499Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP499Value5_0
  · exact sharedDiskP499Value5_1
  · exact sharedDiskP499Value5_2
  · exact sharedDiskP499Value5_3
  · exact sharedDiskP499Value5_4
  · exact sharedDiskP499Value5_5
  · exact sharedDiskP499Value5_6
  · exact sharedDiskP499Value5_7
private theorem sharedDiskP499Value6_0 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 6 (0:Fin 8))=sharedDiskP499Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value6_1 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 6 (1:Fin 8))=sharedDiskP499Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value6_2 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 6 (2:Fin 8))=sharedDiskP499Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value6_3 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 6 (3:Fin 8))=sharedDiskP499Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value6_4 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 6 (4:Fin 8))=sharedDiskP499Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value6_5 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 6 (5:Fin 8))=sharedDiskP499Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value6_6 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 6 (6:Fin 8))=sharedDiskP499Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value6_7 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 6 (7:Fin 8))=sharedDiskP499Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP499Values6_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 6 j)=sharedDiskP499Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP499Value6_0
  · exact sharedDiskP499Value6_1
  · exact sharedDiskP499Value6_2
  · exact sharedDiskP499Value6_3
  · exact sharedDiskP499Value6_4
  · exact sharedDiskP499Value6_5
  · exact sharedDiskP499Value6_6
  · exact sharedDiskP499Value6_7
private theorem sharedDiskP499Value7_0 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 7 (0:Fin 8))=sharedDiskP499Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value7_1 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 7 (1:Fin 8))=sharedDiskP499Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value7_2 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 7 (2:Fin 8))=sharedDiskP499Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value7_3 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 7 (3:Fin 8))=sharedDiskP499Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value7_4 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 7 (4:Fin 8))=sharedDiskP499Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value7_5 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 7 (5:Fin 8))=sharedDiskP499Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value7_6 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 7 (6:Fin 8))=sharedDiskP499Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value7_7 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 7 (7:Fin 8))=sharedDiskP499Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP499Values7_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 7 j)=sharedDiskP499Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP499Value7_0
  · exact sharedDiskP499Value7_1
  · exact sharedDiskP499Value7_2
  · exact sharedDiskP499Value7_3
  · exact sharedDiskP499Value7_4
  · exact sharedDiskP499Value7_5
  · exact sharedDiskP499Value7_6
  · exact sharedDiskP499Value7_7
private theorem sharedDiskP499Value8_0 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 8 (0:Fin 8))=sharedDiskP499Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value8_1 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 8 (1:Fin 8))=sharedDiskP499Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value8_2 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 8 (2:Fin 8))=sharedDiskP499Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value8_3 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 8 (3:Fin 8))=sharedDiskP499Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value8_4 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 8 (4:Fin 8))=sharedDiskP499Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value8_5 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 8 (5:Fin 8))=sharedDiskP499Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value8_6 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 8 (6:Fin 8))=sharedDiskP499Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value8_7 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 8 (7:Fin 8))=sharedDiskP499Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP499Values8_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 8 j)=sharedDiskP499Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP499Value8_0
  · exact sharedDiskP499Value8_1
  · exact sharedDiskP499Value8_2
  · exact sharedDiskP499Value8_3
  · exact sharedDiskP499Value8_4
  · exact sharedDiskP499Value8_5
  · exact sharedDiskP499Value8_6
  · exact sharedDiskP499Value8_7
private theorem sharedDiskP499Value9_0 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 9 (0:Fin 8))=sharedDiskP499Values 9 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value9_1 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 9 (1:Fin 8))=sharedDiskP499Values 9 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value9_2 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 9 (2:Fin 8))=sharedDiskP499Values 9 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value9_3 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 9 (3:Fin 8))=sharedDiskP499Values 9 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value9_4 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 9 (4:Fin 8))=sharedDiskP499Values 9 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value9_5 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 9 (5:Fin 8))=sharedDiskP499Values 9 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value9_6 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 9 (6:Fin 8))=sharedDiskP499Values 9 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value9_7 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 9 (7:Fin 8))=sharedDiskP499Values 9 (7:Fin 8) := by decide +kernel
theorem sharedDiskP499Values9_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 9 j)=sharedDiskP499Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP499Value9_0
  · exact sharedDiskP499Value9_1
  · exact sharedDiskP499Value9_2
  · exact sharedDiskP499Value9_3
  · exact sharedDiskP499Value9_4
  · exact sharedDiskP499Value9_5
  · exact sharedDiskP499Value9_6
  · exact sharedDiskP499Value9_7
private theorem sharedDiskP499Value10_0 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 10 (0:Fin 8))=sharedDiskP499Values 10 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value10_1 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 10 (1:Fin 8))=sharedDiskP499Values 10 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value10_2 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 10 (2:Fin 8))=sharedDiskP499Values 10 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value10_3 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 10 (3:Fin 8))=sharedDiskP499Values 10 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value10_4 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 10 (4:Fin 8))=sharedDiskP499Values 10 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value10_5 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 10 (5:Fin 8))=sharedDiskP499Values 10 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value10_6 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 10 (6:Fin 8))=sharedDiskP499Values 10 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value10_7 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 10 (7:Fin 8))=sharedDiskP499Values 10 (7:Fin 8) := by decide +kernel
theorem sharedDiskP499Values10_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 10 j)=sharedDiskP499Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP499Value10_0
  · exact sharedDiskP499Value10_1
  · exact sharedDiskP499Value10_2
  · exact sharedDiskP499Value10_3
  · exact sharedDiskP499Value10_4
  · exact sharedDiskP499Value10_5
  · exact sharedDiskP499Value10_6
  · exact sharedDiskP499Value10_7
private theorem sharedDiskP499Value11_0 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 11 (0:Fin 8))=sharedDiskP499Values 11 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value11_1 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 11 (1:Fin 8))=sharedDiskP499Values 11 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value11_2 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 11 (2:Fin 8))=sharedDiskP499Values 11 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value11_3 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 11 (3:Fin 8))=sharedDiskP499Values 11 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value11_4 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 11 (4:Fin 8))=sharedDiskP499Values 11 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value11_5 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 11 (5:Fin 8))=sharedDiskP499Values 11 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value11_6 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 11 (6:Fin 8))=sharedDiskP499Values 11 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value11_7 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 11 (7:Fin 8))=sharedDiskP499Values 11 (7:Fin 8) := by decide +kernel
theorem sharedDiskP499Values11_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 11 j)=sharedDiskP499Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP499Value11_0
  · exact sharedDiskP499Value11_1
  · exact sharedDiskP499Value11_2
  · exact sharedDiskP499Value11_3
  · exact sharedDiskP499Value11_4
  · exact sharedDiskP499Value11_5
  · exact sharedDiskP499Value11_6
  · exact sharedDiskP499Value11_7
private theorem sharedDiskP499Value12_0 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 12 (0:Fin 8))=sharedDiskP499Values 12 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value12_1 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 12 (1:Fin 8))=sharedDiskP499Values 12 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value12_2 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 12 (2:Fin 8))=sharedDiskP499Values 12 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value12_3 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 12 (3:Fin 8))=sharedDiskP499Values 12 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value12_4 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 12 (4:Fin 8))=sharedDiskP499Values 12 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value12_5 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 12 (5:Fin 8))=sharedDiskP499Values 12 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value12_6 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 12 (6:Fin 8))=sharedDiskP499Values 12 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP499Value12_7 : truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 12 (7:Fin 8))=sharedDiskP499Values 12 (7:Fin 8) := by decide +kernel
theorem sharedDiskP499Values12_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points 12 j)=sharedDiskP499Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP499Value12_0
  · exact sharedDiskP499Value12_1
  · exact sharedDiskP499Value12_2
  · exact sharedDiskP499Value12_3
  · exact sharedDiskP499Value12_4
  · exact sharedDiskP499Value12_5
  · exact sharedDiskP499Value12_6
  · exact sharedDiskP499Value12_7
theorem sharedDiskP499Values_eq : ∀ (i : Fin 13) (j : Fin 8), truncatedChordCell 1 sharedDiskP499Params (sharedChord493Gauss8Points i j)=sharedDiskP499Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP499Values0_eq
  · exact sharedDiskP499Values1_eq
  · exact sharedDiskP499Values2_eq
  · exact sharedDiskP499Values3_eq
  · exact sharedDiskP499Values4_eq
  · exact sharedDiskP499Values5_eq
  · exact sharedDiskP499Values6_eq
  · exact sharedDiskP499Values7_eq
  · exact sharedDiskP499Values8_eq
  · exact sharedDiskP499Values9_eq
  · exact sharedDiskP499Values10_eq
  · exact sharedDiskP499Values11_eq
  · exact sharedDiskP499Values12_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP499Box : HorizontalRectangle := ⟨(27/40),(137/200),(889155926669671/1649267441664000),(903824955642727/1649267441664000),(261263841357636960053985719592751/649037107316853453566312041152512),(1225983875149485001881445932591903/324518553658426726783156020576256),(-181318919265855587442881111554947/40564819207303340847894502572032),(-39254863554604650160027308948355/40564819207303340847894502572032),true,[]⟩
noncomputable def sharedDiskP499Grid : CGrid := momentChordGrid sharedDiskP499Params chordGaussRule8 1 sharedChord493Bd sharedChord493M (23175049/18014398509481984)
theorem sharedDiskP499Columns : containedInReported sharedDiskP499Grid.re sharedDiskP499Box.reLo sharedDiskP499Box.reHi=true ∧ containedInReported sharedDiskP499Grid.im sharedDiskP499Box.imLo sharedDiskP499Box.imHi=true := by
  rw [sharedDiskP499Grid,momentChordGrid_eq_tabulated sharedDiskP499Params chordGaussRule8 1 sharedChord493Bd sharedChord493M (23175049/18014398509481984) sharedChord493Gauss8Points sharedChord493Gauss8Weights sharedDiskP499Values sharedChord493Gauss8Points_eq sharedChord493Gauss8Weights_eq sharedDiskP499Values_eq]
  decide +kernel
theorem sharedDiskP499Sound : sharedDiskP499Box.Sound := by
  intro t a tl tu al au
  change (((27/40):ℚ):ℝ)≤t at tl
  change t≤(((137/200):ℚ):ℝ) at tu
  change (((889155926669671/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((903824955642727/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP499Params_ok] at ps
  have band := sharedChord493ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((129/200):ℚ)≤(27/40))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((137/200):ℚ)≤(3/4)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((878940159632233/1649267441664000):ℚ)≤(889155926669671/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((903824955642727/1649267441664000):ℚ)≤(929134916903873/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 1 sharedChord493Bd (by decide +kernel) (by decide +kernel) sharedChord493M (by decide +kernel) (sharedChord493Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP499Columns.1 sharedDiskP499Columns.2
def sharedDiskP499Rows : List SignRow := [positive_499.toSignRow, positive_500.toSignRow]
theorem sharedDiskP499Rows_actual : ∀ r∈sharedDiskP499Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP499Rows.all (sharedDiskP499Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP499Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP501Params : ChordParams := ⟨⟨(-13160373309931296877270),(-12319961638523602755782),true⟩,⟨2457893514652086529027505,2543245469880284892969223,true⟩,⟨96933319911205113796696,104654477923875464335204,true⟩,⟨147490555949996519466409,158280001956881308316976,true⟩,⟨241452838681871430176768,249724126807341270871183,true⟩,⟨1182888515237481524075416,1184534464573566287088620,true⟩,⟨(-2716295453889222659464433),(-2673491992435834643451524),true⟩,⟨⟨1128723417181398199331159,1240005414777716658022636,true⟩,⟨(-18027),18027,true⟩⟩⟩
theorem sharedDiskP501Params_ok : chordParams (Grid.ofRats (137/200) (139/200)) (Grid.ofRats (892747446892277/1649267441664000) (907463002306829/1649267441664000))=sharedDiskP501Params := by decide +kernel
def sharedDiskP501Values (i : Fin 13) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-6706216222101847220391961),(-2104012250806608525019671),true⟩,⟨(-2045172756558673705098077),2218157739349563977057563,true⟩⟩
  | 0,1 => ⟨⟨(-6226666869381840985849654),(-1852219292610393642727417),true⟩,⟨(-2050044918604434389264619),2024158161547760431600797,true⟩⟩
  | 0,2 => ⟨⟨(-5856171147681252824113653),(-1674384755620093960943889),true⟩,⟨(-2048087470110208044800588),1850084360647365232766116,true⟩⟩
  | 0,3 => ⟨⟨(-5637707392920245177139227),(-1575496088460929398645925),true⟩,⟨(-2044764907937055466850020),1739264761004366903566657,true⟩⟩
  | 0,4 => ⟨⟨(-7230088941063825455171697),(-2395728321800365229923377),true⟩,⟨(-2029594394728812959217573),2380034477461681035209693,true⟩⟩
  | 0,5 => ⟨⟨(-7721733062016307858229379),(-2703855310560160980027214),true⟩,⟨(-2004859469409383509539507),2473458199933861126204215,true⟩⟩
  | 0,6 => ⟨⟨(-8109832199149077248638030),(-2982641904726396226022538),true⟩,⟨(-1978543776727355835434898),2499552868554482235501218,true⟩⟩
  | 0,7 => ⟨⟨(-8342611692588159719330275),(-3166122316140595064920428),true⟩,⟨(-1960122718807898564364299),2492344511222548731757847,true⟩⟩
  | 1,0 => ⟨⟨(-4164445327943133863536913),(-993621425590983720146670),true⟩,⟨(-1988269285667656035486347),971491460545240576175815,true⟩⟩
  | 1,1 => ⟨⟨(-3808557831381955954129734),(-867986418414517576388833),true⟩,⟨(-1967598864334240645150831),786737707629073624413112,true⟩⟩
  | 1,2 => ⟨⟨(-3544147786986468912200167),(-776485609495942572480239),true⟩,⟨(-1950873101810736596142240),647801557670666860585912,true⟩⟩
  | 1,3 => ⟨⟨(-3391974093615785564550969),(-724222490915022085617821),true⟩,⟨(-1940760928020025903419714),567577668423390418236152,true⟩⟩
  | 1,4 => ⟨⟨(-4573925528269228027716077),(-1143639352919828644654015),true⟩,⟨(-2009070179165336410099316),1178482527675887763982186,true⟩⟩
  | 1,5 => ⟨⟨(-4981212978915364539738884),(-1300842183612368810405381),true⟩,⟨(-2026089939762421189592383),1378002134199536389130732,true⟩⟩
  | 1,6 => ⟨⟨(-5321375477645828208678938),(-1439262108350223228074007),true⟩,⟨(-2037311965774009129841105),1569839257103723609276260,true⟩⟩
  | 1,7 => ⟨⟨(-5533219943756889969991214),(-1529627588040848532719171),true⟩,⟨(-2042638720610645277694266),1684393044502955398391436,true⟩⟩
  | 2,0 => ⟨⟨(-2416161120928390476974384),(-384899866612930604900855),true⟩,⟨(-1867721463629095000981492),62236739047232118643849,true⟩⟩
  | 2,1 => ⟨⟨(-2188412512669157827986285),(-301619099474129251354072),true⟩,⟨(-1848294770787924718796067),(-48794038921373027007921),true⟩⟩
  | 2,2 => ⟨⟨(-2023840479750139174463617),(-238155057769088983840943),true⟩,⟨(-1833119273141423280400888),(-120403879439916793593642),true⟩⟩
  | 2,3 => ⟨⟨(-1930460077261556115058839),(-200811611006449920964383),true⟩,⟨(-1824026177815645240414752),(-158122429256280320972391),true⟩⟩
  | 2,4 => ⟨⟨(-2680851197236772042123874),(-478936561862676329658851),true⟩,⟨(-1889015700365360786764630),196152778846284040902552,true⟩⟩
  | 2,5 => ⟨⟨(-2948476146864630984828564),(-571985338776464582547948),true⟩,⟨(-1909366252048909497371340),334603864400711802211320,true⟩⟩
  | 2,6 => ⟨⟨(-3175920493904140122337825),(-650175539456873721947280),true⟩,⟨(-1925821506552845356475468),453766351912144039350407,true⟩⟩
  | 2,7 => ⟨⟨(-3320076714501455797364925),(-699577631537342227954495),true⟩,⟨(-1935864493155020533482939),529672345192961823449944,true⟩⟩
  | 3,0 => ⟨⟨(-1322840040504144972046748),61163253825045775373527,true⟩,⟨(-1756085304272236261098819),(-381337189393280612204280),true⟩⟩
  | 3,1 => ⟨⟨(-1176857367902529524105796),130586359731556578107028,true⟩,⟨(-1736668416812875223120146),(-427656762318769087899660),true⟩⟩
  | 3,2 => ⟨⟨(-1067293047983411538375641),184376082838299311814781,true⟩,⟨(-1721046295887280084704593),(-460134139030485645477429),true⟩⟩
  | 3,3 => ⟨⟨(-1003598223158537782414381),216339514763091502308038,true⟩,⟨(-1711507080023808170404753),(-478050822909403876693186),true⟩⟩
  | 3,4 => ⟨⟨(-1490006752828861445657229),(-15140277003897696455427),true⟩,⟨(-1776616792968790474464745),(-324416299706568607067486),true⟩⟩
  | 3,5 => ⟨⟨(-1656911683485416947501928),(-87528915517553253654582),true⟩,⟨(-1795585436137945535295259),(-263925668087731935984184),true⟩⟩
  | 3,6 => ⟨⟨(-1797547638791034609976651),(-146539392877227953234503),true⟩,⟨(-1810572169110734483891094),(-210469714514463759363199),true⟩⟩
  | 3,7 => ⟨⟨(-1886284537296366788731217),(-182925137141317831380795),true⟩,⟨(-1819624618622405296674588),(-175703632107438851242113),true⟩⟩
  | 4,0 => ⟨⟨257616853545989711430665,1072317937364129789321945,true⟩,⟨(-1419820115383984069520634),(-572181606284989201290117),true⟩⟩
  | 4,1 => ⟨⟨484438559573445847083741,1275272815481665483191189,true⟩,⟨(-1344937796018047814008630),(-538848097161459652856235),true⟩⟩
  | 4,2 => ⟨⟨646430317794039141705882,1423263722175537390339882,true⟩,⟨(-1285340458713649047337903),(-506352528231867269641628),true⟩⟩
  | 4,3 => ⟨⟨737588748344544381438288,1507447658175993596815597,true⟩,⟨(-1249813954889595842655979),(-485266929457355123348939),true⟩⟩
  | 4,4 => ⟨⟨(-47705617544516302925372),832624014850363292337085,true⟩,⟨(-1513349897221155938002986),(-591198177100788832124536),true⟩⟩
  | 4,5 => ⟨⟨(-388584136594785738118316),586212118675223151268356,true⟩,⟨(-1598428581538351279954965),(-582800057726188513943192),true⟩⟩
  | 4,6 => ⟨⟨(-706531441304042775946321),377366597241312134971765,true⟩,⟨(-1662331498075891834953368),(-546093060141490519394782),true⟩⟩
  | 4,7 => ⟨⟨(-928607388788431287254267),254643182595226761361686,true⟩,⟨(-1699811805971302898641641),(-498191590924035996956980),true⟩⟩
  | 5,0 => ⟨⟨1688609201907719573173700,2409204437337032978339950,true⟩,⟨(-854720029431470566484849),(-211279076755175336588356),true⟩⟩
  | 5,1 => ⟨⟨1873936820233485306885074,2591276692941128656805208,true⟩,⟨(-802312758390090807883518),(-172111569786109898956815),true⟩⟩
  | 5,2 => ⟨⟨2007104059493420339055874,2726108001964967949134008,true⟩,⟨(-783240135958962203179237),(-157056253113030517993124),true⟩⟩
  | 5,3 => ⟨⟨2083608759148559303744533,2806003606623812561403086,true⟩,⟨(-782312082783085872883829),(-155371092364142971704945),true⟩⟩
  | 5,4 => ⟨⟨1458362708557075403856432,2187489277425498761739350,true⟩,⟨(-943121908207539880466568),(-276081760504713651475996),true⟩⟩
  | 5,5 => ⟨⟨1203031743984956605391002,1944354983371078647124752,true⟩,⟨(-1052979632698208297651701),(-354678676646715222171807),true⟩⟩
  | 5,6 => ⟨⟨964308620596411400927687,1719037890679935559438478,true⟩,⟨(-1156370594473982800764635),(-425550823873162751760102),true⟩⟩
  | 5,7 => ⟨⟨801106552073870857388563,1566434408385852374889449,true⟩,⟨(-1224306178968377088377588),(-469509197397108452126662),true⟩⟩
  | 6,0 => ⟨⟨2605371463341760879451683,3590273760854999220511258,true⟩,⟨(-1201988786129085742540023),(-337437022324167575236267),true⟩⟩
  | 6,1 => ⟨⟨2772699273629525751926786,3912335060326493750629258,true⟩,⟨(-1537719734977449217243665),(-517723573260970095945924),true⟩⟩
  | 6,2 => ⟨⟨2908937500511449215037314,4221722306664059967034664,true⟩,⟨(-1944435835750797932894028),(-743585713274379013061243),true⟩⟩
  | 6,3 => ⟨⟨2985040979124143923914357,4433379278692729617741808,true⟩,⟨(-2278825203559994355813575),(-932294669903087148097355),true⟩⟩
  | 6,4 => ⟨⟨2440444178672103133420053,3310748585719272876323258,true⟩,⟨(-981286343308611667397996),(-226532810873424683869491),true⟩⟩
  | 6,5 => ⟨⟨2297087296047629514599290,3091876690419278631074466,true⟩,⟨(-859932820825666687159282),(-173546717643586811744385),true⟩⟩
  | 6,6 => ⟨⟨2186019068781472432855793,2936091256320549139570822,true⟩,⟨(-805138201386248770147654),(-156671847762174085637762),true⟩⟩
  | 6,7 => ⟨⟨2118241301542871112438546,2846459956082936595853726,true⟩,⟨(-786355435357249972800940),(-155262517991553684141803),true⟩⟩
  | 7,0 => ⟨⟨3074772138321987323045763,4908841073945855169841837,true⟩,⟨(-3284081359056524754461891),(-1506612688884006204807406),true⟩⟩
  | 7,1 => ⟨⟨3065867049909260975690616,5029123876988773372985024,true⟩,⟨(-3634350716327974689122881),(-1707689197387836426814093),true⟩⟩
  | 7,2 => ⟨⟨3042500119278655799048294,5119307814530763092968459,true⟩,⟨(-3946713478192668733368427),(-1887038074122936241907111),true⟩⟩
  | 7,3 => ⟨⟨3019602624472008359489218,5170130918492619439993023,true⟩,⟨(-4151542433309961730144449),(-2004590436800836780566618),true⟩⟩
  | 7,4 => ⟨⟨3065482085568672036356772,4776600068740406226777417,true⟩,⟨(-2956430654185233501824046),(-1318764405350525170755843),true⟩⟩
  | 7,5 => ⟨⟨3044334787317492174235891,4653603530739833835111943,true⟩,⟨(-2689801080625619977552549),(-1166257302740600423974517),true⟩⟩
  | 7,6 => ⟨⟨3021471909856929249774784,4557785010970708798695900,true⟩,⟨(-2501805337944651755818117),(-1059026688644275757586692),true⟩⟩
  | 7,7 => ⟨⟨3005713478133004636772327,4501011297520249615529460,true⟩,⟨(-2397316264581523831375466),(-999569325653581813051168),true⟩⟩
  | 8,0 => ⟨⟨2500133665118012486730747,5344436115550889128494687,true⟩,⟨(-6140215674862893389553894),(-3137426562608698263449143),true⟩⟩
  | 8,1 => ⟨⟨2179719796673822064169588,5265888479207429108406279,true⟩,⟨(-6852805653413248733470653),(-3536864365870500165430963),true⟩⟩
  | 8,2 => ⟨⟨1842565414745548913022105,5133557129794672483981434,true⟩,⟨(-7461437870932565613740168),(-3873939073282188683907297),true⟩⟩
  | 8,3 => ⟨⟨1597072930995494647607649,5016078012131747774797513,true⟩,⟨(-7843622807541419501934853),(-4083237294468473542004799),true⟩⟩
  | 8,4 => ⟨⟨2740336121534377980304424,5348489690740265813225016,true⟩,⟨(-5452725275274164615139101),(-2748215887501248811362836),true⟩⟩
  | 8,5 => ⟨⟨2890499677703464079077986,5300591027874857247875276,true⟩,⟨(-4883881412886792957919927),(-2423995245352325671740584),true⟩⟩
  | 8,6 => ⟨⟨2970676741019778841264476,5238430933291784003482190,true⟩,⟨(-4480254882369750949713286),(-2193053703396955150044799),true⟩⟩
  | 8,7 => ⟨⟨3005715882706930656637611,5193511707270901950145352,true⟩,⟨(-4255657075328047106676049),(-2064312540913985099120819),true⟩⟩
  | 9,0 => ⟨⟨177554944080322486479532,4210925576699915336402392,true⟩,⟨(-9409232841202636902557316),(-4880277494534757184844840),true⟩⟩
  | 9,1 => ⟨⟨(-364303692150029518733669),3874250463110417458391946,true⟩,⟨(-9831292973516907058758928),(-5073408690737882696634362),true⟩⟩
  | 9,2 => ⟨⟨(-840220944762446423064866),3565432581373026635460310,true⟩,⟨(-10149216543393924307736394),(-5211588336368750552166398),true⟩⟩
  | 9,3 => ⟨⟨(-1146453790343900208045367),3360278071832060187573527,true⟩,⟨(-10331003497914736997743173),(-5286816796308099380536463),true⟩⟩
  | 9,4 => ⟨⟨686455966814837790610115,4510956483344171428375502,true⟩,⟨(-8942401650034879008334502),(-4657152352064206358524503),true⟩⟩
  | 9,5 => ⟨⟨1099015664125800025562445,4739056089714343111607484,true⟩,⟨(-8505501176217412841259754),(-4440315482208204207315134),true⟩⟩
  | 9,6 => ⟨⟨1356482562914063099997267,4887911436507162923693537,true⟩,⟨(-8180057411899784312983536),(-4265686845612237336007024),true⟩⟩
  | 9,7 => ⟨⟨1499056531451037196691170,4965269219930212524038557,true⟩,⟨(-7984821187203013612689838),(-4160029390369016587160816),true⟩⟩
  | 10,0 => ⟨⟨(-3848689142347941087374670),1434656900113902389536042,true⟩,⟨(-11260508207217212364233788),(-5512690716825274155113199),true⟩⟩
  | 10,1 => ⟨⟨(-4700477333497044417081554),834021470164215665531888,true⟩,⟨(-11313019138264725358567294),(-5406550964938488885604314),true⟩⟩
  | 10,2 => ⟨⟨(-5385460759586883682073521),332660160872011819461865,true⟩,⟨(-11265279693464624824619825),(-5266851630920328686705734),true⟩⟩
  | 10,3 => ⟨⟨(-5797728594610727290034165),22214855920011804782389,true⟩,⟨(-11194043318601225649938966),(-5157280928259398215048929),true⟩⟩
  | 10,4 => ⟨⟨(-2970626317421723198498618),2048133914234377360562302,true⟩,⟨(-11085261624983866302468158),(-5538344531210413000490595),true⟩⟩
  | 10,5 => ⟨⟨(-2199537991119819458903384),2620514492249336681761043,true⟩,⟨(-10832109780976381758802138),(-5471204977320897947616437),true⟩⟩
  | 10,6 => ⟨⟨(-1627422781798921164358145),3028724045543451615576369,true⟩,⟨(-10582941086106037557310381),(-5384834644519488805924184),true⟩⟩
  | 10,7 => ⟨⟨(-1300219213571070825423346),3255487129409917689591806,true⟩,⟨(-10415911676392541359398386),(-5320768246062106276753054),true⟩⟩
  | 11,0 => ⟨⟨(-8504802124961494180495892),(-2238845369688014762025952),true⟩,⟨(-9513973604015219567181788),(-3723347451733070341121843),true⟩⟩
  | 11,1 => ⟨⟨(-9019292096306658016201155),(-2781346952439155549677302),true⟩,⟨(-8679491626978526862427863),(-3148515982779112651932874),true⟩⟩
  | 11,2 => ⟨⟨(-9353188405968229998414687),(-3154740665042072137838264),true⟩,⟨(-7923547994649016908088170),(-2608020465213732116690069),true⟩⟩
  | 11,3 => ⟨⟨(-9495276588694570135866024),(-3351734521851364367310692),true⟩,⟨(-7432993548426919266119067),(-2274874464907775383582366),true⟩⟩
  | 11,4 => ⟨⟨(-7806016191062866007556751),(-1592566947856964790213038),true⟩,⟨(-10237516378340618691356086),(-4262811720574883362174226),true⟩⟩
  | 11,5 => ⟨⟨(-7049431455661424237748681),(-954062939753489976821999),true⟩,⟨(-10741913224945055657191887),(-4684503587502915781859658),true⟩⟩
  | 11,6 => ⟨⟨(-6401036446555812240639476),(-438467331934284123514779),true⟩,⟨(-11024874021245399619708464),(-4958257588796337347262113),true⟩⟩
  | 11,7 => ⟨⟨(-5996443888084420033314435),(-127930307069142096636023),true⟩,⟨(-11147279742910655894393993),(-5097051071853613188616528),true⟩⟩
  | 12,0 => ⟨⟨(-9046370453250497583065923),(-4025492795623272421675745),true⟩,⟨(-3432311002262332304882412),75840867314259494638757,true⟩⟩
  | 12,1 => ⟨⟨(-8493729310950877932556534),(-3962487193181917172579018),true⟩,⟨(-2384777903566119342991017),680148534832596725546065,true⟩⟩
  | 12,2 => ⟨⟨(-7959313650912541809786307),(-3848004328832620813635503),true⟩,⟨(-1629129789280663507312078),1129060506992443438188741,true⟩⟩
  | 12,3 => ⟨⟨(-7606250077946824507290493),(-3742371880623946905060260),true⟩,⟨(-1211737932125899652365092),1358261692208385930410837,true⟩⟩
  | 12,4 => ⟨⟨(-9451541538703813336573144),(-3976347238422631369189295),true⟩,⟨(-4632510036986382671192175),(-583569696344688406358709),true⟩⟩
  | 12,5 => ⟨⟨(-9628810227693488967040454),(-3812466261300656522439073),true⟩,⟨(-5776136862244457415915406),(-1234199662034063893848105),true⟩⟩
  | 12,6 => ⟨⟨(-9618599552047889911230629),(-3600676378543304102421443),true⟩,⟨(-6666892330260713450615041),(-1778452085991610449413915),true⟩⟩
  | 12,7 => ⟨⟨(-9547290919990209527858939),(-3438996578963921558975424),true⟩,⟨(-7187046392327234505269807),(-2112472120909486734579825),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP501Value0_0 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 0 (0:Fin 8))=sharedDiskP501Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value0_1 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 0 (1:Fin 8))=sharedDiskP501Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value0_2 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 0 (2:Fin 8))=sharedDiskP501Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value0_3 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 0 (3:Fin 8))=sharedDiskP501Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value0_4 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 0 (4:Fin 8))=sharedDiskP501Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value0_5 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 0 (5:Fin 8))=sharedDiskP501Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value0_6 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 0 (6:Fin 8))=sharedDiskP501Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value0_7 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 0 (7:Fin 8))=sharedDiskP501Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP501Values0_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 0 j)=sharedDiskP501Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP501Value0_0
  · exact sharedDiskP501Value0_1
  · exact sharedDiskP501Value0_2
  · exact sharedDiskP501Value0_3
  · exact sharedDiskP501Value0_4
  · exact sharedDiskP501Value0_5
  · exact sharedDiskP501Value0_6
  · exact sharedDiskP501Value0_7
private theorem sharedDiskP501Value1_0 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 1 (0:Fin 8))=sharedDiskP501Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value1_1 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 1 (1:Fin 8))=sharedDiskP501Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value1_2 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 1 (2:Fin 8))=sharedDiskP501Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value1_3 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 1 (3:Fin 8))=sharedDiskP501Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value1_4 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 1 (4:Fin 8))=sharedDiskP501Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value1_5 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 1 (5:Fin 8))=sharedDiskP501Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value1_6 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 1 (6:Fin 8))=sharedDiskP501Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value1_7 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 1 (7:Fin 8))=sharedDiskP501Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP501Values1_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 1 j)=sharedDiskP501Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP501Value1_0
  · exact sharedDiskP501Value1_1
  · exact sharedDiskP501Value1_2
  · exact sharedDiskP501Value1_3
  · exact sharedDiskP501Value1_4
  · exact sharedDiskP501Value1_5
  · exact sharedDiskP501Value1_6
  · exact sharedDiskP501Value1_7
private theorem sharedDiskP501Value2_0 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 2 (0:Fin 8))=sharedDiskP501Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value2_1 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 2 (1:Fin 8))=sharedDiskP501Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value2_2 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 2 (2:Fin 8))=sharedDiskP501Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value2_3 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 2 (3:Fin 8))=sharedDiskP501Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value2_4 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 2 (4:Fin 8))=sharedDiskP501Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value2_5 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 2 (5:Fin 8))=sharedDiskP501Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value2_6 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 2 (6:Fin 8))=sharedDiskP501Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value2_7 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 2 (7:Fin 8))=sharedDiskP501Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP501Values2_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 2 j)=sharedDiskP501Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP501Value2_0
  · exact sharedDiskP501Value2_1
  · exact sharedDiskP501Value2_2
  · exact sharedDiskP501Value2_3
  · exact sharedDiskP501Value2_4
  · exact sharedDiskP501Value2_5
  · exact sharedDiskP501Value2_6
  · exact sharedDiskP501Value2_7
private theorem sharedDiskP501Value3_0 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 3 (0:Fin 8))=sharedDiskP501Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value3_1 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 3 (1:Fin 8))=sharedDiskP501Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value3_2 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 3 (2:Fin 8))=sharedDiskP501Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value3_3 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 3 (3:Fin 8))=sharedDiskP501Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value3_4 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 3 (4:Fin 8))=sharedDiskP501Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value3_5 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 3 (5:Fin 8))=sharedDiskP501Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value3_6 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 3 (6:Fin 8))=sharedDiskP501Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value3_7 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 3 (7:Fin 8))=sharedDiskP501Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP501Values3_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 3 j)=sharedDiskP501Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP501Value3_0
  · exact sharedDiskP501Value3_1
  · exact sharedDiskP501Value3_2
  · exact sharedDiskP501Value3_3
  · exact sharedDiskP501Value3_4
  · exact sharedDiskP501Value3_5
  · exact sharedDiskP501Value3_6
  · exact sharedDiskP501Value3_7
private theorem sharedDiskP501Value4_0 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 4 (0:Fin 8))=sharedDiskP501Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value4_1 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 4 (1:Fin 8))=sharedDiskP501Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value4_2 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 4 (2:Fin 8))=sharedDiskP501Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value4_3 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 4 (3:Fin 8))=sharedDiskP501Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value4_4 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 4 (4:Fin 8))=sharedDiskP501Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value4_5 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 4 (5:Fin 8))=sharedDiskP501Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value4_6 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 4 (6:Fin 8))=sharedDiskP501Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value4_7 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 4 (7:Fin 8))=sharedDiskP501Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP501Values4_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 4 j)=sharedDiskP501Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP501Value4_0
  · exact sharedDiskP501Value4_1
  · exact sharedDiskP501Value4_2
  · exact sharedDiskP501Value4_3
  · exact sharedDiskP501Value4_4
  · exact sharedDiskP501Value4_5
  · exact sharedDiskP501Value4_6
  · exact sharedDiskP501Value4_7
private theorem sharedDiskP501Value5_0 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 5 (0:Fin 8))=sharedDiskP501Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value5_1 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 5 (1:Fin 8))=sharedDiskP501Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value5_2 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 5 (2:Fin 8))=sharedDiskP501Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value5_3 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 5 (3:Fin 8))=sharedDiskP501Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value5_4 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 5 (4:Fin 8))=sharedDiskP501Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value5_5 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 5 (5:Fin 8))=sharedDiskP501Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value5_6 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 5 (6:Fin 8))=sharedDiskP501Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value5_7 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 5 (7:Fin 8))=sharedDiskP501Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP501Values5_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 5 j)=sharedDiskP501Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP501Value5_0
  · exact sharedDiskP501Value5_1
  · exact sharedDiskP501Value5_2
  · exact sharedDiskP501Value5_3
  · exact sharedDiskP501Value5_4
  · exact sharedDiskP501Value5_5
  · exact sharedDiskP501Value5_6
  · exact sharedDiskP501Value5_7
private theorem sharedDiskP501Value6_0 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 6 (0:Fin 8))=sharedDiskP501Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value6_1 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 6 (1:Fin 8))=sharedDiskP501Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value6_2 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 6 (2:Fin 8))=sharedDiskP501Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value6_3 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 6 (3:Fin 8))=sharedDiskP501Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value6_4 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 6 (4:Fin 8))=sharedDiskP501Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value6_5 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 6 (5:Fin 8))=sharedDiskP501Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value6_6 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 6 (6:Fin 8))=sharedDiskP501Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value6_7 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 6 (7:Fin 8))=sharedDiskP501Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP501Values6_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 6 j)=sharedDiskP501Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP501Value6_0
  · exact sharedDiskP501Value6_1
  · exact sharedDiskP501Value6_2
  · exact sharedDiskP501Value6_3
  · exact sharedDiskP501Value6_4
  · exact sharedDiskP501Value6_5
  · exact sharedDiskP501Value6_6
  · exact sharedDiskP501Value6_7
private theorem sharedDiskP501Value7_0 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 7 (0:Fin 8))=sharedDiskP501Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value7_1 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 7 (1:Fin 8))=sharedDiskP501Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value7_2 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 7 (2:Fin 8))=sharedDiskP501Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value7_3 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 7 (3:Fin 8))=sharedDiskP501Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value7_4 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 7 (4:Fin 8))=sharedDiskP501Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value7_5 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 7 (5:Fin 8))=sharedDiskP501Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value7_6 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 7 (6:Fin 8))=sharedDiskP501Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value7_7 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 7 (7:Fin 8))=sharedDiskP501Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP501Values7_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 7 j)=sharedDiskP501Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP501Value7_0
  · exact sharedDiskP501Value7_1
  · exact sharedDiskP501Value7_2
  · exact sharedDiskP501Value7_3
  · exact sharedDiskP501Value7_4
  · exact sharedDiskP501Value7_5
  · exact sharedDiskP501Value7_6
  · exact sharedDiskP501Value7_7
private theorem sharedDiskP501Value8_0 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 8 (0:Fin 8))=sharedDiskP501Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value8_1 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 8 (1:Fin 8))=sharedDiskP501Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value8_2 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 8 (2:Fin 8))=sharedDiskP501Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value8_3 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 8 (3:Fin 8))=sharedDiskP501Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value8_4 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 8 (4:Fin 8))=sharedDiskP501Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value8_5 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 8 (5:Fin 8))=sharedDiskP501Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value8_6 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 8 (6:Fin 8))=sharedDiskP501Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value8_7 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 8 (7:Fin 8))=sharedDiskP501Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP501Values8_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 8 j)=sharedDiskP501Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP501Value8_0
  · exact sharedDiskP501Value8_1
  · exact sharedDiskP501Value8_2
  · exact sharedDiskP501Value8_3
  · exact sharedDiskP501Value8_4
  · exact sharedDiskP501Value8_5
  · exact sharedDiskP501Value8_6
  · exact sharedDiskP501Value8_7
private theorem sharedDiskP501Value9_0 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 9 (0:Fin 8))=sharedDiskP501Values 9 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value9_1 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 9 (1:Fin 8))=sharedDiskP501Values 9 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value9_2 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 9 (2:Fin 8))=sharedDiskP501Values 9 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value9_3 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 9 (3:Fin 8))=sharedDiskP501Values 9 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value9_4 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 9 (4:Fin 8))=sharedDiskP501Values 9 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value9_5 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 9 (5:Fin 8))=sharedDiskP501Values 9 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value9_6 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 9 (6:Fin 8))=sharedDiskP501Values 9 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value9_7 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 9 (7:Fin 8))=sharedDiskP501Values 9 (7:Fin 8) := by decide +kernel
theorem sharedDiskP501Values9_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 9 j)=sharedDiskP501Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP501Value9_0
  · exact sharedDiskP501Value9_1
  · exact sharedDiskP501Value9_2
  · exact sharedDiskP501Value9_3
  · exact sharedDiskP501Value9_4
  · exact sharedDiskP501Value9_5
  · exact sharedDiskP501Value9_6
  · exact sharedDiskP501Value9_7
private theorem sharedDiskP501Value10_0 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 10 (0:Fin 8))=sharedDiskP501Values 10 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value10_1 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 10 (1:Fin 8))=sharedDiskP501Values 10 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value10_2 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 10 (2:Fin 8))=sharedDiskP501Values 10 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value10_3 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 10 (3:Fin 8))=sharedDiskP501Values 10 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value10_4 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 10 (4:Fin 8))=sharedDiskP501Values 10 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value10_5 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 10 (5:Fin 8))=sharedDiskP501Values 10 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value10_6 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 10 (6:Fin 8))=sharedDiskP501Values 10 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value10_7 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 10 (7:Fin 8))=sharedDiskP501Values 10 (7:Fin 8) := by decide +kernel
theorem sharedDiskP501Values10_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 10 j)=sharedDiskP501Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP501Value10_0
  · exact sharedDiskP501Value10_1
  · exact sharedDiskP501Value10_2
  · exact sharedDiskP501Value10_3
  · exact sharedDiskP501Value10_4
  · exact sharedDiskP501Value10_5
  · exact sharedDiskP501Value10_6
  · exact sharedDiskP501Value10_7
private theorem sharedDiskP501Value11_0 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 11 (0:Fin 8))=sharedDiskP501Values 11 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value11_1 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 11 (1:Fin 8))=sharedDiskP501Values 11 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value11_2 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 11 (2:Fin 8))=sharedDiskP501Values 11 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value11_3 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 11 (3:Fin 8))=sharedDiskP501Values 11 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value11_4 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 11 (4:Fin 8))=sharedDiskP501Values 11 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value11_5 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 11 (5:Fin 8))=sharedDiskP501Values 11 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value11_6 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 11 (6:Fin 8))=sharedDiskP501Values 11 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value11_7 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 11 (7:Fin 8))=sharedDiskP501Values 11 (7:Fin 8) := by decide +kernel
theorem sharedDiskP501Values11_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 11 j)=sharedDiskP501Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP501Value11_0
  · exact sharedDiskP501Value11_1
  · exact sharedDiskP501Value11_2
  · exact sharedDiskP501Value11_3
  · exact sharedDiskP501Value11_4
  · exact sharedDiskP501Value11_5
  · exact sharedDiskP501Value11_6
  · exact sharedDiskP501Value11_7
private theorem sharedDiskP501Value12_0 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 12 (0:Fin 8))=sharedDiskP501Values 12 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value12_1 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 12 (1:Fin 8))=sharedDiskP501Values 12 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value12_2 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 12 (2:Fin 8))=sharedDiskP501Values 12 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value12_3 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 12 (3:Fin 8))=sharedDiskP501Values 12 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value12_4 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 12 (4:Fin 8))=sharedDiskP501Values 12 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value12_5 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 12 (5:Fin 8))=sharedDiskP501Values 12 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value12_6 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 12 (6:Fin 8))=sharedDiskP501Values 12 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP501Value12_7 : truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 12 (7:Fin 8))=sharedDiskP501Values 12 (7:Fin 8) := by decide +kernel
theorem sharedDiskP501Values12_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points 12 j)=sharedDiskP501Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP501Value12_0
  · exact sharedDiskP501Value12_1
  · exact sharedDiskP501Value12_2
  · exact sharedDiskP501Value12_3
  · exact sharedDiskP501Value12_4
  · exact sharedDiskP501Value12_5
  · exact sharedDiskP501Value12_6
  · exact sharedDiskP501Value12_7
theorem sharedDiskP501Values_eq : ∀ (i : Fin 13) (j : Fin 8), truncatedChordCell 1 sharedDiskP501Params (sharedChord493Gauss8Points i j)=sharedDiskP501Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP501Values0_eq
  · exact sharedDiskP501Values1_eq
  · exact sharedDiskP501Values2_eq
  · exact sharedDiskP501Values3_eq
  · exact sharedDiskP501Values4_eq
  · exact sharedDiskP501Values5_eq
  · exact sharedDiskP501Values6_eq
  · exact sharedDiskP501Values7_eq
  · exact sharedDiskP501Values8_eq
  · exact sharedDiskP501Values9_eq
  · exact sharedDiskP501Values10_eq
  · exact sharedDiskP501Values11_eq
  · exact sharedDiskP501Values12_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP501Box : HorizontalRectangle := ⟨(137/200),(139/200),(892747446892277/1649267441664000),(907463002306829/1649267441664000),(58202678931913346387429948157509/162259276829213363391578010288128),(4644237458412361875482338354283599/1298074214633706907132624082305024),(-2876969801126533332060685453652763/649037107316853453566312041152512),(-1423987780793526928350811283318325/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP501Grid : CGrid := momentChordGrid sharedDiskP501Params chordGaussRule8 1 sharedChord493Bd sharedChord493M (23175049/18014398509481984)
theorem sharedDiskP501Columns : containedInReported sharedDiskP501Grid.re sharedDiskP501Box.reLo sharedDiskP501Box.reHi=true ∧ containedInReported sharedDiskP501Grid.im sharedDiskP501Box.imLo sharedDiskP501Box.imHi=true := by
  rw [sharedDiskP501Grid,momentChordGrid_eq_tabulated sharedDiskP501Params chordGaussRule8 1 sharedChord493Bd sharedChord493M (23175049/18014398509481984) sharedChord493Gauss8Points sharedChord493Gauss8Weights sharedDiskP501Values sharedChord493Gauss8Points_eq sharedChord493Gauss8Weights_eq sharedDiskP501Values_eq]
  decide +kernel
theorem sharedDiskP501Sound : sharedDiskP501Box.Sound := by
  intro t a tl tu al au
  change (((137/200):ℚ):ℝ)≤t at tl
  change t≤(((139/200):ℚ):ℝ) at tu
  change (((892747446892277/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((907463002306829/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP501Params_ok] at ps
  have band := sharedChord493ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((129/200):ℚ)≤(137/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((139/200):ℚ)≤(3/4)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((878940159632233/1649267441664000):ℚ)≤(892747446892277/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((907463002306829/1649267441664000):ℚ)≤(929134916903873/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 1 sharedChord493Bd (by decide +kernel) (by decide +kernel) sharedChord493M (by decide +kernel) (sharedChord493Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP501Columns.1 sharedDiskP501Columns.2
def sharedDiskP501Rows : List SignRow := [positive_501.toSignRow, positive_502.toSignRow]
theorem sharedDiskP501Rows_actual : ∀ r∈sharedDiskP501Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP501Rows.all (sharedDiskP501Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP501Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP493Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP496Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP499Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP501Rows_actual
