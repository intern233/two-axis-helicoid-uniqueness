import TwoAxisHelicoid.PdfSharedChord493Gauss8
import TwoAxisHelicoid.PdfSharedChord493Disks

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP511Params : ChordParams := ⟨⟨(-17824690469704283574356),(-16830820727356637357067),true⟩,⟨2232395231149340950528736,2309601533881102355345696,true⟩,⟨109391102439941406737584,117377881461020545755924,true⟩,⟨178936300677778329425740,190736603524458606417889,true⟩,⟨281142093978289381110631,289558433984650254576014,true⟩,⟨1173794424341790943773734,1175726384958611901710092,true⟩,⟨(-2512689369807932198387860),(-2474888550561631412510287),true⟩,⟨⟨1115935732543800965696843,1233993117924849132653183,true⟩,⟨(-459013),459013,true⟩⟩⟩
theorem sharedDiskP511Params_ok : chordParams (Grid.ofRats (147/200) (149/200)) (Grid.ofRats (912100318056157/1649267441664000) (309016142189677/549755813888000))=sharedDiskP511Params := by decide +kernel
def sharedDiskP511Values (i : Fin 13) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-5311890796355041203743613),(-2715324447070800631139412),true⟩,⟨(-1033417051016409181151672),1005938544186654113882279,true⟩⟩
  | 0,1 => ⟨⟨(-4971022124386967511084472),(-2483946668779532856118739),true⟩,⟨(-1062880352984424187728652),937186032542053883861154,true⟩⟩
  | 0,2 => ⟨⟨(-4710167202855046695395377),(-2312764357586632730973341),true⟩,⟨(-1089514783353594619241530),868610518751873043808349,true⟩⟩
  | 0,3 => ⟨⟨(-4556977387221149219370321),(-2214776458883351645862128),true⟩,⟨(-1104861083556026355048321),822381202479256701371969,true⟩⟩
  | 0,4 => ⟨⟨(-5690582811645704497791381),(-2983092606179362550835985),true⟩,⟨(-1014463120188892146100411),1052146355941631087566085,true⟩⟩
  | 0,5 => ⟨⟨(-6054287635020087195167223),(-3251092322061714600447600),true⟩,⟨(-1000737453809876188722981),1064314533237580757112680,true⟩⟩
  | 0,6 => ⟨⟨(-6348601791128178002486857),(-3478442456130292923095709),true⟩,⟨(-993489567859802690372147),1049761073804762901018665,true⟩⟩
  | 0,7 => ⟨⟨(-6528868308416067596778102),(-3622686316594018992046313),true⟩,⟨(-991021224910434309020181),1029769768963613553918040,true⟩⟩
  | 1,0 => ⟨⟨(-3521583381802144547074093),(-1595047173721907268402110),true⟩,⟨(-1200983088687002913828422),453993856742568573987131,true⟩⟩
  | 1,1 => ⟨⟨(-3267247014577798871677542),(-1452508839647533529246299),true⟩,⟨(-1222097745765496141065220),352703336132383212226813,true⟩⟩
  | 1,2 => ⟨⟨(-3076285112531240522668468),(-1347509005087934722649308),true⟩,⟨(-1237161495988818080459231),273107881549121254299957,true⟩⟩
  | 1,3 => ⟨⟨(-2965476386723971457418973),(-1287269918554749231007151),true⟩,⟨(-1245569744425589082493020),225758337679777686964677,true⟩⟩
  | 1,4 => ⟨⟨(-3811280683854446414593754),(-1761738561657680865675135),true⟩,⟨(-1175583854198044213012205),561465735575590762687505,true⟩⟩
  | 1,5 => ⟨⟨(-4097412317664460367108479),(-1931430050182327313645905),true⟩,⟨(-1149233130265730655635465),660045417878839615451137,true⟩⟩
  | 1,6 => ⟨⟨(-4335549940525831127069945),(-2076325800916070177525333),true⟩,⟨(-1126577681846092323514726),748356745691429888052824,true⟩⟩
  | 1,7 => ⟨⟨(-4483806861692122749443749),(-2168615857424117533480561),true⟩,⟨(-1112101582692174191782648),798833293848494952993368,true⟩⟩
  | 2,0 => ⟨⟨(-2235216051110062397274550),(-898613359954502312591019),true⟩,⟨(-1293669489672305331970591),(-97221876771309654643242),true⟩⟩
  | 2,1 => ⟨⟨(-2063344433099671314281853),(-805707130858667725976127),true⟩,⟨(-1302884782490970712609248),(-166971827750749242073401),true⟩⟩
  | 2,2 => ⟨⟨(-1935188197945918281362496),(-735961605736663681495885),true⟩,⟨(-1308984733760619695722354),(-217660408581568239772293),true⟩⟩
  | 2,3 => ⟨⟨(-1860824666750721533159896),(-695384055355948247041899),true⟩,⟨(-1312167315738747831449388),(-246807256545103612558237),true⟩⟩
  | 2,4 => ⟨⟨(-2437065126068147065693491),(-1005110225103874909483743),true⟩,⟨(-1281819239396696215767553),(-7795278222341554574108),true⟩⟩
  | 2,5 => ⟨⟨(-2638155011520843685709691),(-1111700999927246595378484),true⟩,⟨(-1268836459408692563030368),82122008764856255360384,true⟩⟩
  | 2,6 => ⟨⟨(-2806880608326602412145539),(-1201808683832424681397653),true⟩,⟨(-1257149627768429789956663),156764092036144760709053,true⟩⟩
  | 2,7 => ⟨⟨(-2912871339120363052875054),(-1258830359697115602297341),true⟩,⟨(-1249471546267992092440404),203020773380129491739561,true⟩⟩
  | 3,0 => ⟨⟨(-1367088012718569231926282),(-416224069184529962176137),true⟩,⟨(-1332051101352894737158669),(-430491156196715047022995),true⟩⟩
  | 3,1 => ⟨⟨(-1245970371566232314659115),(-343868186767127134879127),true⟩,⟨(-1336415965067293385182369),(-471583802037295925052349),true⟩⟩
  | 3,2 => ⟨⟨(-1154464990760165925688101),(-288396757584837915920218),true⟩,⟨(-1338798564825021654501501),(-501279380068538188878989),true⟩⟩
  | 3,3 => ⟨⟨(-1101038039207714835664020),(-255666177674065693147962),true⟩,⟨(-1339788611504401011695137),(-518026442471156403876446),true⟩⟩
  | 3,4 => ⟨⟨(-1504616773836639795413659),(-497049716993262733057315),true⟩,⟨(-1325633610908095783921317),(-381684568003867241286047),true⟩⟩
  | 3,5 => ⟨⟨(-1640656782673062604426291),(-574490717192836084974256),true⟩,⟨(-1319814209964830161647245),(-331391196588739748409802),true⟩⟩
  | 3,6 => ⟨⟨(-1754283464027421037517639),(-637047660869606771976100),true⟩,⟨(-1316220137140339532800794),(-288104601222472178836494),true⟩⟩
  | 3,7 => ⟨⟨(-1825505016210250069699392),(-676074029982949996421572),true⟩,⟨(-1313579521944876539697631),(-260563847619528069500613),true⟩⟩
  | 4,0 => ⟨⟨4573005315929575458412,549296318400199690752324,true⟩,⟨(-1270494033033302016808753),(-688877046824336692830938),true⟩⟩
  | 4,1 => ⟨⟨225582588418191098851077,748157688944907364472256,true⟩,⟨(-1227977733957261905674571),(-674159085517716349464541),true⟩⟩
  | 4,2 => ⟨⟨375971152094094645258331,894522270932172173582366,true⟩,⟨(-1196898351275611610895966),(-655353533007352065938757),true⟩⟩
  | 4,3 => ⟨⟨459840336709775022901513,978568916811108378511559,true⟩,⟨(-1178224362966861829108760),(-641933010395964649938448),true⟩⟩
  | 4,4 => ⟨⟨(-269276628978264286195808),320121773965239212683937,true⟩,⟨(-1308124922231682792744019),(-684690930549678669991976),true⟩⟩
  | 4,5 => ⟨⟨(-565982085879558556944400),98284195522831010467862,true⟩,⟨(-1331586704868962160305431),(-648024799303958036530594),true⟩⟩
  | 4,6 => ⟨⟨(-842109234254519807817901),(-93147624108347132942011),true⟩,⟨(-1339787551403942968742473),(-592170521799310186617768),true⟩⟩
  | 4,7 => ⟨⟨(-1037924361185450528626801),(-216660429953149243238541),true⟩,⟨(-1340548909173871583142883),(-537208417053591336147353),true⟩⟩
  | 5,0 => ⟨⟨1395079902879184880140697,1952653226754122576956657,true⟩,⟨(-946737011703030185969505),(-432458346078078929167564),true⟩⟩
  | 5,1 => ⟨⟨1597722038802348015762614,2174159817008156554972210,true⟩,⟨(-925214133246625793709318),(-402632891115263947344012),true⟩⟩
  | 5,2 => ⟨⟨1748623258743101526345575,2343381579129567467268777,true⟩,⟨(-929570363474135408226109),(-395267311440987163379964),true⟩⟩
  | 5,3 => ⟨⟨1837084404460144048807866,2444883446496998621252429,true⟩,⟨(-943000385483664587182635),(-398952116335678244009407),true⟩⟩
  | 5,4 => ⟨⟨1154766131357488868824622,1695914126554400940726158,true⟩,⟨(-997322712190088342555724),(-485000569987970512946883),true⟩⟩
  | 5,5 => ⟨⟨900485240190657477506624,1429361191413337913724185,true⟩,⟨(-1064209430716822786558058),(-547432516434700302160609),true⟩⟩
  | 5,6 => ⟨⟨671516514842083861369019,1193294591946832240395640,true⟩,⟨(-1125848187795631433086176),(-600645707377848089852593),true⟩⟩
  | 5,7 => ⟨⟨518669427880984437857374,1037883141030873857366682,true⟩,⟨(-1164350158564636998786353),(-631451950644014062369845),true⟩⟩
  | 6,0 => ⟨⟨2452489839928233128074051,3370826584134038829499162,true⟩,⟨(-1519749144654984547650388),(-680396145749155531190430),true⟩⟩
  | 6,1 => ⟨⟨2624043786062173366971108,3707863896101928366339446,true⟩,⟨(-1937285464452330464315153),(-925457346664660575966704),true⟩⟩
  | 6,2 => ⟨⟨2740008495327110378332108,4002188496895520522399510,true⟩,⟨(-2428528589061552187147830),(-1223265737750851369091993),true⟩⟩
  | 6,3 => ⟨⟨2786428696612087091125462,4184098828407212063819560,true⟩,⟨(-2822241011873686977082655),(-1465563771615386817371735),true⟩⟩
  | 6,4 => ⟨⟨2265169032892761695614989,3055548006832531204787117,true⟩,⟨(-1235597030198403328482183),(-523734652813231968802324),true⟩⟩
  | 6,5 => ⟨⟨2094078851017048727271834,2795812257863762262824590,true⟩,⟨(-1070512979668120997850667),(-442882637884964559214167),true⟩⟩
  | 6,6 => ⟨⟨1959733700450856436412897,2605943720376629767697313,true⟩,⟨(-987844904831859187282208),(-410610163834675937933018),true⟩⟩
  | 6,7 => ⟨⟨1878106178617153224786322,2495724964022194701801221,true⟩,⟨(-954106782677398941964646),(-401874698282008862028063),true⟩⟩
  | 7,0 => ⟨⟨2745185701398289479044497,4510569658069429188309636,true⟩,⟨(-3953969983340565135348247),(-2169205653011929544725064),true⟩⟩
  | 7,1 => ⟨⟨2681411174296060132126019,4564273294317948326365369,true⟩,⟨(-4330407680426207285647178),(-2403929734838427751317761),true⟩⟩
  | 7,2 => ⟨⟨2606662595845563986098341,4590458115398154045877784,true⟩,⟨(-4658376035047832216813513),(-2608287385919149295146896),true⟩⟩
  | 7,3 => ⟨⟨2549132187523742951415002,4597290719844993076869098,true⟩,⟨(-4869487365630977684947440),(-2739682487892720212724316),true⟩⟩
  | 7,4 => ⟨⟨2783709227070463196705690,4434664108499930144117959,true⟩,⟨(-3593512006332720002852289),(-1944523643361487363912847),true⟩⟩
  | 7,5 => ⟨⟨2798230951812587146157985,4352442602324622162263234,true⟩,⟨(-3294206418620455439583934),(-1758232799960931472296652),true⟩⟩
  | 7,6 => ⟨⟨2798364428167209101679645,4282175468857503622324971,true⟩,⟨(-3079921529142433623218418),(-1625139741267309722888616),true⟩⟩
  | 7,7 => ⟨⟨2794491757109264041757608,4238313941017657580481044,true⟩,⟨(-2959649759864146633980400),(-1550583036654227118298296),true⟩⟩
  | 8,0 => ⟨⟨1683784149118309536634406,4291695258098046806487168,true⟩,⟨(-6754746858373451890484129),(-3901442964667947476717926),true⟩⟩
  | 8,1 => ⟨⟨1247930297502106078562743,4030456195675001901563226,true⟩,⟨(-7354974939943327680845111),(-4263845260460855727648026),true⟩⟩
  | 8,2 => ⟨⟨789373368933704239663206,3743021502628628852620675,true⟩,⟨(-7852271718192452986635963),(-4548347478034567790874414),true⟩⟩
  | 8,3 => ⟨⟨460011933460287196910768,3529993844422398580143262,true⟩,⟨(-8154907033690713536579475),(-4714172566626678191574965),true⟩⟩
  | 8,4 => ⟨⟨2042349284810897068082869,4469245519014973868896099,true⟩,⟨(-6137155179628083932967509),(-3523962120227970402563630),true⟩⟩
  | 8,5 => ⟨⟨2292593935662175631323451,4560010343067206638340794,true⟩,⟨(-5598649006197189479931914),(-3192029196433015950916934),true⟩⟩
  | 8,6 => ⟨⟨2443514980081019742336637,4592121608983443749262805,true⟩,⟨(-5201738127926024821110742),(-2946131123826995169513615),true⟩⟩
  | 8,7 => ⟨⟨2517417253649625310898630,4597762608207760006720223,true⟩,⟨(-4975595667033460818166693),(-2805665021901936987065801),true⟩⟩
  | 9,0 => ⟨⟨(-1161952914535164853188377),2384465181662218911188972,true⟩,⟨(-9206782441135104889773440),(-5247728080219847106627640),true⟩⟩
  | 9,1 => ⟨⟨(-1696514699150811202078273),1978438627478136668438086,true⟩,⟨(-9428394388025582636635722),(-5342661175070466482468993),true⟩⟩
  | 9,2 => ⟨⟨(-2146188466351997382594147),1642203988164521759178899,true⟩,⟨(-9573489469540415518750017),(-5387787294578519365910726),true⟩⟩
  | 9,3 => ⟨⟨(-2427742093222994211783867),1441591960880446926441240,true⟩,⟨(-9645675635176349396543525),(-5396482549462557662076801),true⟩⟩
  | 9,4 => ⟨⟨(-632152631823768999287989),2773538551155785968335738,true⟩,⟨(-8931291796927101490978569),(-5117450889120343555312959),true⟩⟩
  | 9,5 => ⟨⟨(-179939022275103184742812),3093885001209467200119695,true⟩,⟨(-8648125304713822107825015),(-4975081375061095997472657),true⟩⟩
  | 9,6 => ⟨⟨147512609708625823737549,3319709864357727366423953,true⟩,⟨(-8410775805464597943583713),(-4851212102018595706584354),true⟩⟩
  | 9,7 => ⟨⟨331562704588895184332807,3444452798182826101084078,true⟩,⟨(-8263538147186829484985528),(-4772747214327275363538953),true⟩⟩
  | 10,0 => ⟨⟨(-4691137457908653472436677),(-262355158723518306361893),true⟩,⟨(-9695686331675309986377282),(-5118700859821623698990417),true⟩⟩
  | 10,1 => ⟨⟨(-5333277346588053117053108),(-773417298840165656139496),true⟩,⟨(-9516720365798799711354094),(-4914671928509574759065531),true⟩⟩
  | 10,2 => ⟨⟨(-5827130389572758933872483),(-1179677783009855536912277),true⟩,⟨(-9304673354649393923046306),(-4710137424907515000328282),true⟩⟩
  | 10,3 => ⟨⟨(-6114774851738378079886387),(-1422735408671910005056397),true⟩,⟨(-9145581068066477684759816),(-4568366157265456053607642),true⟩⟩
  | 10,4 => ⟨⟨(-3995382503478899333563765),277276979521945347895961,true⟩,⟨(-9785229435977544776163386),(-5272469447297579414813101),true⟩⟩
  | 10,5 => ⟨⟨(-3354140721021331657966355),763278945468899038514621,true⟩,⟨(-9782722497335488366806113),(-5358937146835563216010307),true⟩⟩
  | 10,6 => ⟨⟨(-2858554513197248279237090),1129608833102012449690219,true⟩,⟨(-9728621984131357116915239),(-5391649857662989062385373),true⟩⟩
  | 10,7 => ⟨⟨(-2566947155772534745233371),1341443093742154530384102,true⟩,⟨(-9676111549841653593392506),(-5397314633141749175032895),true⟩⟩
  | 11,0 => ⟨⟨(-7803325089208327654842593),(-3039032122038257015158538),true⟩,⟨(-7224934242573546612217112),(-3116215430310258145639859),true⟩⟩
  | 11,1 => ⟨⟨(-8067030719218106447943755),(-3378384087418875008389507),true⟩,⟨(-6486843975352547928439001),(-2612742940223600197618070),true⟩⟩
  | 11,2 => ⟨⟨(-8214506124604409051761234),(-3597828713197686585615199),true⟩,⟨(-5859000882957927922214395),(-2171698864860781621250535),true⟩⟩
  | 11,3 => ⟨⟨(-8263585566990852315657717),(-3707551589074296174093529),true⟩,⟨(-5466287293487204830811899),(-1905082757148766074101468),true⟩⟩
  | 11,4 => ⟨⟨(-7406517599435659990493019),(-2608921962360154742802381),true⟩,⟨(-7929541308782479875124880),(-3615686221667045670263308),true⟩⟩
  | 11,5 => ⟨⟨(-6942661546741929249444804),(-2158845099933707120163794),true⟩,⟨(-8491274474045960023869244),(-4036251551541381995498139),true⟩⟩
  | 11,6 => ⟨⟨(-6522553481682770932621635),(-1777371723118932160955554),true⟩,⟨(-8865416748444775348888540),(-4332804342450708291439785),true⟩⟩
  | 11,7 => ⟨⟨(-6250830282787848136373934),(-1539630334963354568712911),true⟩,⟨(-9059805949388979329107329),(-4494637959220284826856212),true⟩⟩
  | 12,0 => ⟨⟨(-7692991918928639848669996),(-3959752601376030822341271),true⟩,⟨(-2489123459010570952630017),(-83084378003432025678990),true⟩⟩
  | 12,1 => ⟨⟨(-7280318680016922916372155),(-3863571028895421990326683),true⟩,⟨(-1737316161254816594822698),374111472594621104645111,true⟩⟩
  | 12,2 => ⟨⟨(-6895096926382986460807230),(-3745921582783894840866588),true⟩,⟨(-1192715139914644384523260),732449978971493966316582,true⟩⟩
  | 12,3 => ⟨⟨(-6643394317045729848848276),(-3657844218257511803000892),true⟩,⟨(-889271328537917220573441),922031094070715173709864,true⟩⟩
  | 12,4 => ⟨⟨(-8027107529209276071550932),(-3987475202446466742747107),true⟩,⟨(-3356172002922746689387510),(-583280156170883430484538),true⟩⟩
  | 12,5 => ⟨⟨(-8218922679744116835527712),(-3935228026803710861705666),true⟩,⟨(-4197670314176283773685362),(-1088529867952186816896536),true⟩⟩
  | 12,6 => ⟨⟨(-8279973487023947132755878),(-3837583851451397691465163),true⟩,⟨(-4870362204519550638391932),(-1513209262558940708742892),true⟩⟩
  | 12,7 => ⟨⟨(-8276387354777707691007002),(-3754422245487808967919528),true⟩,⟨(-5272887612990949057516841),(-1776258140438302284822280),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP511Value0_0 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 0 (0:Fin 8))=sharedDiskP511Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value0_1 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 0 (1:Fin 8))=sharedDiskP511Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value0_2 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 0 (2:Fin 8))=sharedDiskP511Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value0_3 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 0 (3:Fin 8))=sharedDiskP511Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value0_4 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 0 (4:Fin 8))=sharedDiskP511Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value0_5 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 0 (5:Fin 8))=sharedDiskP511Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value0_6 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 0 (6:Fin 8))=sharedDiskP511Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value0_7 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 0 (7:Fin 8))=sharedDiskP511Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP511Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 0 j)=sharedDiskP511Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP511Value0_0
  · exact sharedDiskP511Value0_1
  · exact sharedDiskP511Value0_2
  · exact sharedDiskP511Value0_3
  · exact sharedDiskP511Value0_4
  · exact sharedDiskP511Value0_5
  · exact sharedDiskP511Value0_6
  · exact sharedDiskP511Value0_7
private theorem sharedDiskP511Value1_0 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 1 (0:Fin 8))=sharedDiskP511Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value1_1 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 1 (1:Fin 8))=sharedDiskP511Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value1_2 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 1 (2:Fin 8))=sharedDiskP511Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value1_3 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 1 (3:Fin 8))=sharedDiskP511Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value1_4 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 1 (4:Fin 8))=sharedDiskP511Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value1_5 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 1 (5:Fin 8))=sharedDiskP511Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value1_6 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 1 (6:Fin 8))=sharedDiskP511Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value1_7 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 1 (7:Fin 8))=sharedDiskP511Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP511Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 1 j)=sharedDiskP511Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP511Value1_0
  · exact sharedDiskP511Value1_1
  · exact sharedDiskP511Value1_2
  · exact sharedDiskP511Value1_3
  · exact sharedDiskP511Value1_4
  · exact sharedDiskP511Value1_5
  · exact sharedDiskP511Value1_6
  · exact sharedDiskP511Value1_7
private theorem sharedDiskP511Value2_0 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 2 (0:Fin 8))=sharedDiskP511Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value2_1 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 2 (1:Fin 8))=sharedDiskP511Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value2_2 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 2 (2:Fin 8))=sharedDiskP511Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value2_3 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 2 (3:Fin 8))=sharedDiskP511Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value2_4 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 2 (4:Fin 8))=sharedDiskP511Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value2_5 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 2 (5:Fin 8))=sharedDiskP511Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value2_6 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 2 (6:Fin 8))=sharedDiskP511Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value2_7 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 2 (7:Fin 8))=sharedDiskP511Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP511Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 2 j)=sharedDiskP511Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP511Value2_0
  · exact sharedDiskP511Value2_1
  · exact sharedDiskP511Value2_2
  · exact sharedDiskP511Value2_3
  · exact sharedDiskP511Value2_4
  · exact sharedDiskP511Value2_5
  · exact sharedDiskP511Value2_6
  · exact sharedDiskP511Value2_7
private theorem sharedDiskP511Value3_0 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 3 (0:Fin 8))=sharedDiskP511Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value3_1 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 3 (1:Fin 8))=sharedDiskP511Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value3_2 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 3 (2:Fin 8))=sharedDiskP511Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value3_3 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 3 (3:Fin 8))=sharedDiskP511Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value3_4 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 3 (4:Fin 8))=sharedDiskP511Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value3_5 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 3 (5:Fin 8))=sharedDiskP511Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value3_6 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 3 (6:Fin 8))=sharedDiskP511Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value3_7 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 3 (7:Fin 8))=sharedDiskP511Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP511Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 3 j)=sharedDiskP511Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP511Value3_0
  · exact sharedDiskP511Value3_1
  · exact sharedDiskP511Value3_2
  · exact sharedDiskP511Value3_3
  · exact sharedDiskP511Value3_4
  · exact sharedDiskP511Value3_5
  · exact sharedDiskP511Value3_6
  · exact sharedDiskP511Value3_7
private theorem sharedDiskP511Value4_0 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 4 (0:Fin 8))=sharedDiskP511Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value4_1 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 4 (1:Fin 8))=sharedDiskP511Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value4_2 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 4 (2:Fin 8))=sharedDiskP511Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value4_3 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 4 (3:Fin 8))=sharedDiskP511Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value4_4 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 4 (4:Fin 8))=sharedDiskP511Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value4_5 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 4 (5:Fin 8))=sharedDiskP511Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value4_6 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 4 (6:Fin 8))=sharedDiskP511Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value4_7 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 4 (7:Fin 8))=sharedDiskP511Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP511Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 4 j)=sharedDiskP511Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP511Value4_0
  · exact sharedDiskP511Value4_1
  · exact sharedDiskP511Value4_2
  · exact sharedDiskP511Value4_3
  · exact sharedDiskP511Value4_4
  · exact sharedDiskP511Value4_5
  · exact sharedDiskP511Value4_6
  · exact sharedDiskP511Value4_7
private theorem sharedDiskP511Value5_0 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 5 (0:Fin 8))=sharedDiskP511Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value5_1 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 5 (1:Fin 8))=sharedDiskP511Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value5_2 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 5 (2:Fin 8))=sharedDiskP511Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value5_3 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 5 (3:Fin 8))=sharedDiskP511Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value5_4 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 5 (4:Fin 8))=sharedDiskP511Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value5_5 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 5 (5:Fin 8))=sharedDiskP511Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value5_6 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 5 (6:Fin 8))=sharedDiskP511Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value5_7 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 5 (7:Fin 8))=sharedDiskP511Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP511Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 5 j)=sharedDiskP511Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP511Value5_0
  · exact sharedDiskP511Value5_1
  · exact sharedDiskP511Value5_2
  · exact sharedDiskP511Value5_3
  · exact sharedDiskP511Value5_4
  · exact sharedDiskP511Value5_5
  · exact sharedDiskP511Value5_6
  · exact sharedDiskP511Value5_7
private theorem sharedDiskP511Value6_0 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 6 (0:Fin 8))=sharedDiskP511Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value6_1 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 6 (1:Fin 8))=sharedDiskP511Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value6_2 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 6 (2:Fin 8))=sharedDiskP511Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value6_3 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 6 (3:Fin 8))=sharedDiskP511Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value6_4 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 6 (4:Fin 8))=sharedDiskP511Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value6_5 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 6 (5:Fin 8))=sharedDiskP511Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value6_6 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 6 (6:Fin 8))=sharedDiskP511Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value6_7 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 6 (7:Fin 8))=sharedDiskP511Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP511Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 6 j)=sharedDiskP511Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP511Value6_0
  · exact sharedDiskP511Value6_1
  · exact sharedDiskP511Value6_2
  · exact sharedDiskP511Value6_3
  · exact sharedDiskP511Value6_4
  · exact sharedDiskP511Value6_5
  · exact sharedDiskP511Value6_6
  · exact sharedDiskP511Value6_7
private theorem sharedDiskP511Value7_0 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 7 (0:Fin 8))=sharedDiskP511Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value7_1 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 7 (1:Fin 8))=sharedDiskP511Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value7_2 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 7 (2:Fin 8))=sharedDiskP511Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value7_3 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 7 (3:Fin 8))=sharedDiskP511Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value7_4 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 7 (4:Fin 8))=sharedDiskP511Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value7_5 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 7 (5:Fin 8))=sharedDiskP511Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value7_6 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 7 (6:Fin 8))=sharedDiskP511Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value7_7 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 7 (7:Fin 8))=sharedDiskP511Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP511Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 7 j)=sharedDiskP511Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP511Value7_0
  · exact sharedDiskP511Value7_1
  · exact sharedDiskP511Value7_2
  · exact sharedDiskP511Value7_3
  · exact sharedDiskP511Value7_4
  · exact sharedDiskP511Value7_5
  · exact sharedDiskP511Value7_6
  · exact sharedDiskP511Value7_7
private theorem sharedDiskP511Value8_0 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 8 (0:Fin 8))=sharedDiskP511Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value8_1 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 8 (1:Fin 8))=sharedDiskP511Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value8_2 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 8 (2:Fin 8))=sharedDiskP511Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value8_3 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 8 (3:Fin 8))=sharedDiskP511Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value8_4 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 8 (4:Fin 8))=sharedDiskP511Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value8_5 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 8 (5:Fin 8))=sharedDiskP511Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value8_6 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 8 (6:Fin 8))=sharedDiskP511Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value8_7 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 8 (7:Fin 8))=sharedDiskP511Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP511Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 8 j)=sharedDiskP511Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP511Value8_0
  · exact sharedDiskP511Value8_1
  · exact sharedDiskP511Value8_2
  · exact sharedDiskP511Value8_3
  · exact sharedDiskP511Value8_4
  · exact sharedDiskP511Value8_5
  · exact sharedDiskP511Value8_6
  · exact sharedDiskP511Value8_7
private theorem sharedDiskP511Value9_0 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 9 (0:Fin 8))=sharedDiskP511Values 9 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value9_1 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 9 (1:Fin 8))=sharedDiskP511Values 9 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value9_2 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 9 (2:Fin 8))=sharedDiskP511Values 9 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value9_3 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 9 (3:Fin 8))=sharedDiskP511Values 9 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value9_4 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 9 (4:Fin 8))=sharedDiskP511Values 9 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value9_5 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 9 (5:Fin 8))=sharedDiskP511Values 9 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value9_6 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 9 (6:Fin 8))=sharedDiskP511Values 9 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value9_7 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 9 (7:Fin 8))=sharedDiskP511Values 9 (7:Fin 8) := by decide +kernel
theorem sharedDiskP511Values9_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 9 j)=sharedDiskP511Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP511Value9_0
  · exact sharedDiskP511Value9_1
  · exact sharedDiskP511Value9_2
  · exact sharedDiskP511Value9_3
  · exact sharedDiskP511Value9_4
  · exact sharedDiskP511Value9_5
  · exact sharedDiskP511Value9_6
  · exact sharedDiskP511Value9_7
private theorem sharedDiskP511Value10_0 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 10 (0:Fin 8))=sharedDiskP511Values 10 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value10_1 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 10 (1:Fin 8))=sharedDiskP511Values 10 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value10_2 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 10 (2:Fin 8))=sharedDiskP511Values 10 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value10_3 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 10 (3:Fin 8))=sharedDiskP511Values 10 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value10_4 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 10 (4:Fin 8))=sharedDiskP511Values 10 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value10_5 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 10 (5:Fin 8))=sharedDiskP511Values 10 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value10_6 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 10 (6:Fin 8))=sharedDiskP511Values 10 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value10_7 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 10 (7:Fin 8))=sharedDiskP511Values 10 (7:Fin 8) := by decide +kernel
theorem sharedDiskP511Values10_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 10 j)=sharedDiskP511Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP511Value10_0
  · exact sharedDiskP511Value10_1
  · exact sharedDiskP511Value10_2
  · exact sharedDiskP511Value10_3
  · exact sharedDiskP511Value10_4
  · exact sharedDiskP511Value10_5
  · exact sharedDiskP511Value10_6
  · exact sharedDiskP511Value10_7
private theorem sharedDiskP511Value11_0 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 11 (0:Fin 8))=sharedDiskP511Values 11 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value11_1 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 11 (1:Fin 8))=sharedDiskP511Values 11 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value11_2 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 11 (2:Fin 8))=sharedDiskP511Values 11 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value11_3 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 11 (3:Fin 8))=sharedDiskP511Values 11 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value11_4 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 11 (4:Fin 8))=sharedDiskP511Values 11 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value11_5 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 11 (5:Fin 8))=sharedDiskP511Values 11 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value11_6 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 11 (6:Fin 8))=sharedDiskP511Values 11 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value11_7 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 11 (7:Fin 8))=sharedDiskP511Values 11 (7:Fin 8) := by decide +kernel
theorem sharedDiskP511Values11_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 11 j)=sharedDiskP511Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP511Value11_0
  · exact sharedDiskP511Value11_1
  · exact sharedDiskP511Value11_2
  · exact sharedDiskP511Value11_3
  · exact sharedDiskP511Value11_4
  · exact sharedDiskP511Value11_5
  · exact sharedDiskP511Value11_6
  · exact sharedDiskP511Value11_7
private theorem sharedDiskP511Value12_0 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 12 (0:Fin 8))=sharedDiskP511Values 12 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value12_1 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 12 (1:Fin 8))=sharedDiskP511Values 12 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value12_2 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 12 (2:Fin 8))=sharedDiskP511Values 12 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value12_3 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 12 (3:Fin 8))=sharedDiskP511Values 12 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value12_4 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 12 (4:Fin 8))=sharedDiskP511Values 12 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value12_5 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 12 (5:Fin 8))=sharedDiskP511Values 12 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value12_6 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 12 (6:Fin 8))=sharedDiskP511Values 12 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP511Value12_7 : truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 12 (7:Fin 8))=sharedDiskP511Values 12 (7:Fin 8) := by decide +kernel
theorem sharedDiskP511Values12_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points 12 j)=sharedDiskP511Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP511Value12_0
  · exact sharedDiskP511Value12_1
  · exact sharedDiskP511Value12_2
  · exact sharedDiskP511Value12_3
  · exact sharedDiskP511Value12_4
  · exact sharedDiskP511Value12_5
  · exact sharedDiskP511Value12_6
  · exact sharedDiskP511Value12_7
theorem sharedDiskP511Values_eq : ∀ (i : Fin 13) (j : Fin 8), truncatedChordCell 2 sharedDiskP511Params (sharedChord493Gauss8Points i j)=sharedDiskP511Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP511Values0_eq
  · exact sharedDiskP511Values1_eq
  · exact sharedDiskP511Values2_eq
  · exact sharedDiskP511Values3_eq
  · exact sharedDiskP511Values4_eq
  · exact sharedDiskP511Values5_eq
  · exact sharedDiskP511Values6_eq
  · exact sharedDiskP511Values7_eq
  · exact sharedDiskP511Values8_eq
  · exact sharedDiskP511Values9_eq
  · exact sharedDiskP511Values10_eq
  · exact sharedDiskP511Values11_eq
  · exact sharedDiskP511Values12_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP511Box : HorizontalRectangle := ⟨(147/200),(149/200),(912100318056157/1649267441664000),(309016142189677/549755813888000),(184159880680978477856025199137781/2596148429267413814265248164610048),(108667510645714933575909259436007/40564819207303340847894502572032),(-174160209711896096480894077132111/40564819207303340847894502572032),(-64633865192799824005108182834511/40564819207303340847894502572032),true,[]⟩
noncomputable def sharedDiskP511Grid : CGrid := momentChordGrid sharedDiskP511Params chordGaussRule8 2 sharedChord493Bd sharedChord493M (23175049/18014398509481984)
theorem sharedDiskP511Columns : containedInReported sharedDiskP511Grid.re sharedDiskP511Box.reLo sharedDiskP511Box.reHi=true ∧ containedInReported sharedDiskP511Grid.im sharedDiskP511Box.imLo sharedDiskP511Box.imHi=true := by
  rw [sharedDiskP511Grid,momentChordGrid_eq_tabulated sharedDiskP511Params chordGaussRule8 2 sharedChord493Bd sharedChord493M (23175049/18014398509481984) sharedChord493Gauss8Points sharedChord493Gauss8Weights sharedDiskP511Values sharedChord493Gauss8Points_eq sharedChord493Gauss8Weights_eq sharedDiskP511Values_eq]
  decide +kernel
theorem sharedDiskP511Sound : sharedDiskP511Box.Sound := by
  intro t a tl tu al au
  change (((147/200):ℚ):ℝ)≤t at tl
  change t≤(((149/200):ℚ):ℝ) at tu
  change (((912100318056157/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((309016142189677/549755813888000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP511Params_ok] at ps
  have band := sharedChord493ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((129/200):ℚ)≤(147/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((149/200):ℚ)≤(3/4)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((878940159632233/1649267441664000):ℚ)≤(912100318056157/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((309016142189677/549755813888000):ℚ)≤(929134916903873/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord493Bd (by decide +kernel) (by decide +kernel) sharedChord493M (by decide +kernel) (sharedChord493Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP511Columns.1 sharedDiskP511Columns.2
def sharedDiskP511Rows : List SignRow := [positive_511.toSignRow, positive_512.toSignRow]
theorem sharedDiskP511Rows_actual : ∀ r∈sharedDiskP511Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP511Rows.all (sharedDiskP511Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP511Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP513Params : ChordParams := ⟨⟨(-18332900498891248935737),(-17824690469704283573961),true⟩,⟨2211106203611825492752785,2265773364307587939238053,true⟩,⟨112375264527108631831735,117967173434776341231016,true⟩,⟨185542449200059910457324,194125199274925000072743,true⟩,⟨289204034493135252925072,293419396002970489385806,true⟩,⟨1172807735630698749477372,1173794424341790943774504,true⟩,⟨(-2474888550561631412519796),(-2456322777553789056735310),true⟩,⟨⟨1131032750273107575614713,1214164522978400892699626,true⟩,⟨(-610206),610206,true⟩⟩⟩
theorem sharedDiskP513Params_ok : chordParams (Grid.ofRats (149/200) (3/4)) (Grid.ofRats (916250015015873/1649267441664000) (929134916903873/1649267441664000))=sharedDiskP513Params := by decide +kernel
def sharedDiskP513Values (i : Fin 13) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-5940737981420293457879372),(-2216119306741935089730846),true⟩,⟨(-1609426129321296478098574),1857507205795457040593530,true⟩⟩
  | 0,1 => ⟨⟨(-5582352899314604966821668),(-2002449528079863326746075),true⟩,⟨(-1614542755537133172877243),1730497915532877634251169,true⟩⟩
  | 0,2 => ⟨⟨(-5304354279256246459905927),(-1848349502821323770279599),true⟩,⟨(-1616005337708782443516724),1615764430390901646116399,true⟩⟩
  | 0,3 => ⟨⟨(-5139752636470422526877326),(-1761513429106369981407064),true⟩,⟨(-1615894344419577129970634),1541994744895420015543559,true⟩⟩
  | 0,4 => ⟨⟨(-6331507659918859881957639),(-2455027796072619686652829),true⟩,⟨(-1599504428934930650774440),1964574595984847193721724,true⟩⟩
  | 0,5 => ⟨⟨(-6706296577399533524750689),(-2709229138800242317390239),true⟩,⟨(-1586001897126157946488884),2030177572269340795536776,true⟩⟩
  | 0,6 => ⟨⟨(-7000432759407861923499154),(-2933595690147780316500495),true⟩,⟨(-1572538768506410124976370),2054505833387791441895018,true⟩⟩
  | 0,7 => ⟨⟨(-7175534457343970432067801),(-3079056525724808422005859),true⟩,⟨(-1563365188617846837020068),2056102074378088347695730,true⟩⟩
  | 1,0 => ⟨⟨(-4007488351992799802226369),(-1233875348620604839581825),true⟩,⟨(-1598766519946530155397325),1016764167317293991737737,true⟩⟩
  | 1,1 => ⟨⟨(-3725764361053590168769073),(-1116963612288332595825856),true⟩,⟨(-1590934023944085591436277),877190327074903465020155,true⟩⟩
  | 1,2 => ⟨⟨(-3513861605566493892636841),(-1031530924798072340144462),true⟩,⟨(-1584355193384933598434148),769334971725721671872210,true⟩⟩
  | 1,3 => ⟨⟨(-3390830977073897101286795),(-982707855837943137214612),true⟩,⟨(-1580301900523675575194541),705809502933211491470798,true⟩⟩
  | 1,4 => ⟨⟨(-4327206096938996553651714),(-1372378986560142585160960),true⟩,⟨(-1606150689971084829933209),1168537984070356201895099,true⟩⟩
  | 1,5 => ⟨⟨(-4641127879043145931934200),(-1515772674098097299217495),true⟩,⟨(-1611561957241726637166792),1309183316369307053780626,true⟩⟩
  | 1,6 => ⟨⟨(-4900261581750193066246482),(-1640489894023854640764354),true⟩,⟨(-1614510418788554652427921),1427817148716322842952386,true⟩⟩
  | 1,7 => ⟨⟨(-5060809189566497285816010),(-1720947920163072600781495),true⟩,⟨(-1615594471794736735840779),1505213128443723759741117,true⟩⟩
  | 2,0 => ⟨⟨(-2581456401939174034488312),(-668001460691430835631368),true⟩,⟨(-1550328507885749167362527),279934788634336018096950,true⟩⟩
  | 2,1 => ⟨⟨(-2387244133267019513420826),(-591943442219484431970421),true⟩,⟨(-1542389856909215064760090),178200896068390073633734,true⟩⟩
  | 2,2 => ⟨⟨(-2242248629650712910095831),(-534381613626236935794578),true⟩,⟨(-1536245972803943683874236),103118434206091564397762,true⟩⟩
  | 2,3 => ⟨⟨(-2158361592602724959175629),(-500672247386456850943266),true⟩,⟨(-1532590829030359218779688),60147106926513124691099,true⟩⟩
  | 2,4 => ⟨⟨(-2804626591429710477485034),(-754553262464906915374342),true⟩,⟨(-1559096055443035967627881),397732767873326366031734,true⟩⟩
  | 2,5 => ⟨⟨(-3027489368705974423570553),(-840789375846438347799004),true⟩,⟨(-1567487950824328170513448),515500248750542967353617,true⟩⟩
  | 2,6 => ⟨⟨(-3214735971365155730911011),(-913592118060698156071327),true⟩,⟨(-1574237636892655018656781),613981357562746159294717,true⟩⟩
  | 2,7 => ⟨⟨(-3332418510407871121315312),(-959692599612060316682248),true⟩,⟨(-1578323061789003691929283),675455024111640075322374,true⟩⟩
  | 3,0 => ⟨⟨(-1613158994935244233502334),(-268021924424230498133134),true⟩,⟨(-1505712917874644094456028),(-196220422859619535246967),true⟩⟩
  | 3,1 => ⟨⟨(-1482925531161831127323565),(-207790121319208421722012),true⟩,⟨(-1498046207776681161451167),(-250297058542256712698590),true⟩⟩
  | 3,2 => ⟨⟨(-1384980027624268500401903),(-161247649510332696449891),true⟩,⟨(-1491833607133568989348393),(-289495637487883924149770),true⟩⟩
  | 3,3 => ⟨⟨(-1327976086808899339980850),(-133631073627512005863119),true⟩,⟨(-1488012371010673372429553),(-311666156863629439163804),true⟩⟩
  | 3,4 => ⟨⟨(-1761817471390746624769012),(-334705939871230085269357),true⟩,⟨(-1513792885704296204891150),(-132130593215460613326872),true⟩⟩
  | 3,5 => ⟨⟨(-1911236854495658062471234),(-399109142301083848127818),true⟩,⟨(-1521273294894100417703591),(-63298207527249489271050),true⟩⟩
  | 3,6 => ⟨⟨(-2038530817898764037098068),(-451888309143587304563464),true⟩,⟨(-1527217269601105221127481),(-493543237426717277029),true⟩⟩
  | 3,7 => ⟨⟨(-2118588251871673287020217),(-484567890941105055848211),true⟩,⟨(-1530828462554469932995563),39915101038122037548053,true⟩⟩
  | 4,0 => ⟨⟨(-152532397945205088084906),578184079990434702560034,true⟩,⟨(-1348620554552511926811023),(-594578665095480917573619),true⟩⟩
  | 4,1 => ⟨⟨79213686247984543491059,758815838674510900293133,true⟩,⟨(-1299995322827170940555055),(-598910060448504579681305),true⟩⟩
  | 4,2 => ⟨⟨244067461047450442262455,893357989364102136729200,true⟩,⟨(-1260227285000661475310683),(-592729096890870854718550),true⟩⟩
  | 4,3 => ⟨⟨333031193392388816390254,971157584323046647338152,true⟩,⟨(-1238825472627249991942030),(-586098042336801713352274),true⟩⟩
  | 4,4 => ⟨⟨(-438106601774789868686660),369670577317095720886327,true⟩,⟨(-1396980437660043503373300),(-567339886174871519951629),true⟩⟩
  | 4,5 => ⟨⟨(-751149995941657687696196),172572070432384722548510,true⟩,⟨(-1437054263009914305055306),(-502654712163441621275389),true⟩⟩
  | 4,6 => ⟨⟨(-1053683673117897069178978),5286025426370112310159,true⟩,⟨(-1466990846757847506652062),(-410748921245296577024165),true⟩⟩
  | 4,7 => ⟨⟨(-1260814110458518322591659),(-100566994044881790475208),true⟩,⟨(-1483292659040130520418556),(-337134116421121426776566),true⟩⟩
  | 5,0 => ⟨⟨1317156009425042529912156,1896245560293508131474145,true⟩,⟨(-989560850626678204398513),(-438774056635283895565380),true⟩⟩
  | 5,1 => ⟨⟨1532221854675299571518745,2112116675696701231118006,true⟩,⟨(-964448543014903706681818),(-420334472448854907568246),true⟩⟩
  | 5,2 => ⟨⟨1692694293557383527934014,2278277864693034235761805,true⟩,⟨(-966362080591380703302771),(-421306262936624189455176),true⟩⟩
  | 5,3 => ⟨⟨1786705460622263676879627,2378414074562714126400882,true⟩,⟨(-978641357050113513351763),(-429871554125838831901166),true⟩⟩
  | 5,4 => ⟨⟨1063147514662500668090428,1648535419046464096405810,true⟩,⟨(-1044416242055908802307479),(-477172176347008894438508),true⟩⟩
  | 5,5 => ⟨⟨795539623805640683979369,1394241454685941852079877,true⟩,⟨(-1115784672496313598309207),(-523485586701293691141355),true⟩⟩
  | 5,6 => ⟨⟨555198945916577613078865,1171532954388899769230549,true⟩,⟨(-1181737032002183956849662),(-560854588013989582329064),true⟩⟩
  | 5,7 => ⟨⟨394806019258719375739587,1026283845901834208268267,true⟩,⟨(-1223538566864646280378836),(-580226439507031457244749),true⟩⟩
  | 6,0 => ⟨⟨2455883724363574628864719,3272098899553338104724838,true⟩,⟨(-1535135657850992100781939),(-772717810428977606417573),true⟩⟩
  | 6,1 => ⟨⟨2640970144882727980953975,3590520375141342874404921,true⟩,⟨(-1946261664502092325518990),(-1045592874374758677767141),true⟩⟩
  | 6,2 => ⟨⟨2765375666111869438304527,3861777604304977644882602,true⟩,⟨(-2430373575400455400868141),(-1371945236792693752425683),true⟩⟩
  | 6,3 => ⟨⟨2815033325464023041643041,4024053094270087273588085,true⟩,⟨(-2817674547098028788027267),(-1634942755657139500180787),true⟩⟩
  | 6,4 => ⟨⟨2252624846018266461754909,2969727469760258363176486,true⟩,⟨(-1257022868470704314561560),(-593277177524405552568583),true⟩⟩
  | 6,5 => ⟨⟨2066287082128206810497875,2718740446522971102593380,true⟩,⟨(-1097594331686439521297783),(-495332830385882382775288),true⟩⟩
  | 6,6 => ⟨⟨1919824400139814081135629,2534824643691467807352303,true⟩,⟨(-1019582813799612264207845),(-451179613946644347336520),true⟩⟩
  | 6,7 => ⟨⟨1830880729328243628081021,2428163867184633607853573,true⟩,⟨(-988775505904061812602343),(-435599090758602028874517),true⟩⟩
  | 7,0 => ⟨⟨2772595603610322664008596,4288687545302456914598215,true⟩,⟨(-3924424423634490071745418),(-2389614967515465181259967),true⟩⟩
  | 7,1 => ⟨⟨2706113394138249215426098,4320245840435796550874134,true⟩,⟨(-4289853783919815606053822),(-2638743396852163979406346),true⟩⟩
  | 7,2 => ⟨⟨2628360843757406596127920,4326577167260661538644222,true⟩,⟨(-4606968303256526695450168),(-2854615150013571105219500),true⟩⟩
  | 7,3 => ⟨⟨2568634234210094919912303,4320374448811913605241789,true⟩,⟨(-4810433252780164631293439),(-2992903960519898285514287),true⟩⟩
  | 7,4 => ⟨⟨2812797695201390026253828,4233289150376877967100318,true⟩,⟨(-3573158884236577697178529),(-2149955191976082388375139),true⟩⟩
  | 7,5 => ⟨⟨2827882096941326197153646,4167536670302852062332105,true⟩,⟨(-3280564147330076325052916),(-1950336639952636944390579),true⟩⟩
  | 7,6 => ⟨⟨2827866799227006726696297,4108730179411085511904171,true⟩,⟨(-3070613123055127109943668),(-1807192182067766649744119),true⟩⟩
  | 7,7 => ⟨⟨2823680245566444538723362,4071175718608204087164613,true⟩,⟨(-2952615080171752962412722),(-1726801725859326579033402),true⟩⟩
  | 8,0 => ⟨⟨1678907716806446924803285,3891337783313795697282984,true⟩,⟨(-6600349356472301687968749),(-4196410140038374659009093),true⟩⟩
  | 8,1 => ⟨⟨1235375352128272235562613,3589011103483328830710397,true⟩,⟨(-7157467963630423235688804),(-4563118944903836302663729),true⟩⟩
  | 8,2 => ⟨⟨773888927104254288544165,3268651280992626412149136,true⟩,⟨(-7612461441563120512058115),(-4846811517952750616031584),true⟩⟩
  | 8,3 => ⟨⟨449593552038829565087035,3036216352194595464348795,true⟩,⟨(-7883154430486454429618767),(-5009917631173374377160393),true⟩⟩
  | 8,4 => ⟨⟨2045892003675552139477704,4110487545052779146093337,true⟩,⟨(-6019950024716706860024339),(-3809503259016089655416804),true⟩⟩
  | 8,5 => ⟨⟨2303335303037891560129204,4236695058840496425833856,true⟩,⟨(-5508874388262720716095728),(-3465821247932254468477636),true⟩⟩
  | 8,6 => ⟨⟨2459219198104424250710241,4294314190566849521559014,true⟩,⟨(-5129544176278496453877265),(-3209361326142803078851118),true⟩⟩
  | 8,7 => ⟨⟨2535748311203617939796938,4314223024676640082350672,true⟩,⟨(-4912495127396823224555389),(-3062195766994172695243911),true⟩⟩
  | 9,0 => ⟨⟨(-1120703339059807640468118),1827981316160579277239965,true⟩,⟨(-8787782434231445369230207),(-5513308212059141248260357),true⟩⟩
  | 9,1 => ⟨⟨(-1631128469175027446244400),1430429353717319173251994,true⟩,⟨(-8964375141145208622744408),(-5583841973691209869153966),true⟩⟩
  | 9,2 => ⟨⟨(-2058341305450255405480133),1103015736218958833686000,true⟩,⟨(-9073059161113168050843907),(-5608473042216288863146484),true⟩⟩
  | 9,3 => ⟨⟨(-2324845970490381360576612),895751851732786696328442,true⟩,⟨(-9123186388352839176267943),(-5611218785089494156325446),true⟩⟩
  | 9,4 => ⟨⟨(-611994411706962156563945),2232257797189278189789037,true⟩,⟨(-8558604143948718321723370),(-5395337999676331039516833),true⟩⟩
  | 9,5 => ⟨⟨(-175466229834781147310734),2569374153938019189026590,true⟩,⟨(-8316199262376455966280301),(-5261733522836589122866892),true⟩⟩
  | 9,6 => ⟨⟨143124232424962718491604,2809808297296161910402120,true⟩,⟨(-8109246537146725466749929),(-5143063829304451401886184),true⟩⟩
  | 9,7 => ⟨⟨323482111676556765010192,2943790915166024120593172,true⟩,⟨(-7979484024403855389849910),(-5067034645299288976519945),true⟩⟩
  | 10,0 => ⟨⟨(-4440056644914889650383591),(-826111942971762825803799),true⟩,⟨(-9022333950805735967752120),(-5278976540745517803539976),true⟩⟩
  | 10,1 => ⟨⟨(-5031141174071755640895916),(-1335328923588109404332097),true⟩,⟨(-8812211852613613915310932),(-5058004263440352889825250),true⟩⟩
  | 10,2 => ⟨⟨(-5482799059958044197866998),(-1736185149248644639050651),true⟩,⟨(-8581353933135828675422233),(-4840103718125871136303536),true⟩⟩
  | 10,3 => ⟨⟨(-5744610715405952695909328),(-1974267160095066138298540),true⟩,⟨(-8413873484577553731115261),(-4690409241423248689129310),true⟩⟩
  | 10,4 => ⟨⟨(-3795025848782084113420780),(-286786029393356423494433),true⟩,⟨(-9152377808769452297161926),(-5450484206105834220015123),true⟩⟩
  | 10,5 => ⟨⟨(-3196445129080186047481277),201970448531460827914599,true⟩,⟨(-9192201213212123456480055),(-5552604819300634057858022),true⟩⟩
  | 10,6 => ⟨⟨(-2731178842852398482538948),575355069859495921443004,true⟩,⟨(-9173578550958356874277039),(-5596848336016322217689786),true⟩⟩
  | 10,7 => ⟨⟨(-2456332713393806346922069),792651883314996651731082,true⟩,⟨(-9142939715497641895546173),(-5609023425212242885993502),true⟩⟩
  | 11,0 => ⟨⟨(-7256656641187704039141004),(-3515557935589060870955768),true⟩,⟨(-6518683640662910464224415),(-3187348550953125899822572),true⟩⟩
  | 11,1 => ⟨⟨(-7482160508027816658529731),(-3824541429520186428912822),true⟩,⟨(-5817981792388817849348045),(-2677644768198512892049812),true⟩⟩
  | 11,2 => ⟨⟨(-7593673642688057518490766),(-4018520783863566237067217),true⟩,⟨(-5228159122461746140035346),(-2250857220619382073062693),true⟩⟩
  | 11,3 => ⟨⟨(-7632673001492740094785334),(-4112254532656722904988404),true⟩,⟨(-4861990758596644227035600),(-1984195711659340582601257),true⟩⟩
  | 11,4 => ⟨⟨(-6906470035784463218861678),(-3114259086257524034955372),true⟩,⟨(-7197957945013487309514825),(-3700120998809968565154278),true⟩⟩
  | 11,5 => ⟨⟨(-6492279947704375308171042),(-2686509561574479894423006),true⟩,⟨(-7750110097868806380688027),(-4134742487341792062759159),true⟩⟩
  | 11,6 => ⟨⟨(-6114044882783232400860149),(-2319149750962991187585100),true⟩,⟨(-8125868977451703304910580),(-4443411612701258143780588),true⟩⟩
  | 11,7 => ⟨⟨(-5868105228785683606223751),(-2088283318145136694951045),true⟩,⟨(-8324906850581962419252345),(-4612894254938870949110327),true⟩⟩
  | 12,0 => ⟨⟨(-7096531756557293790984059),(-4245488756312121601436837),true⟩,⟨(-2131908785817666478858405),(-155487948501527850122018),true⟩⟩
  | 12,1 => ⟨⟨(-6723542975057373394731243),(-4119330955977123040006524),true⟩,⟨(-1451646977567560332212231),282896380266254108160637,true⟩⟩
  | 12,2 => ⟨⟨(-6377561100313507137141606),(-3979590862037480521483445),true⟩,⟨(-960485317010329845378426),618137481786529234884965,true⟩⟩
  | 12,3 => ⟨⟨(-6152031011774458250225419),(-3872384186218147503500901),true⟩,⟨(-687299776343744519969707),796641103924913058376479,true⟩⟩
  | 12,4 => ⟨⟨(-7400756961711134250552668),(-4307575943491612251362724),true⟩,⟨(-2920223351912940677336669),(-658100878398616027681427),true⟩⟩
  | 12,5 => ⟨⟨(-7579137408427895536707854),(-4288820381053874572299309),true⟩,⟨(-3690075744409600503504537),(-1166243205239223480125584),true⟩⟩
  | 12,6 => ⟨⟨(-7640483166210515591390525),(-4218173293878799253545535),true⟩,⟨(-4309583603858367503108686),(-1591986953584279462185361),true⟩⟩
  | 12,7 => ⟨⟨(-7641817931820315096859851),(-4151279040728202144977011),true⟩,⟨(-4682309121002636886602466),(-1855307588772775159860630),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP513Value0_0 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 0 (0:Fin 8))=sharedDiskP513Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value0_1 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 0 (1:Fin 8))=sharedDiskP513Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value0_2 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 0 (2:Fin 8))=sharedDiskP513Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value0_3 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 0 (3:Fin 8))=sharedDiskP513Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value0_4 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 0 (4:Fin 8))=sharedDiskP513Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value0_5 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 0 (5:Fin 8))=sharedDiskP513Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value0_6 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 0 (6:Fin 8))=sharedDiskP513Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value0_7 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 0 (7:Fin 8))=sharedDiskP513Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP513Values0_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 0 j)=sharedDiskP513Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP513Value0_0
  · exact sharedDiskP513Value0_1
  · exact sharedDiskP513Value0_2
  · exact sharedDiskP513Value0_3
  · exact sharedDiskP513Value0_4
  · exact sharedDiskP513Value0_5
  · exact sharedDiskP513Value0_6
  · exact sharedDiskP513Value0_7
private theorem sharedDiskP513Value1_0 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 1 (0:Fin 8))=sharedDiskP513Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value1_1 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 1 (1:Fin 8))=sharedDiskP513Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value1_2 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 1 (2:Fin 8))=sharedDiskP513Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value1_3 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 1 (3:Fin 8))=sharedDiskP513Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value1_4 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 1 (4:Fin 8))=sharedDiskP513Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value1_5 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 1 (5:Fin 8))=sharedDiskP513Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value1_6 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 1 (6:Fin 8))=sharedDiskP513Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value1_7 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 1 (7:Fin 8))=sharedDiskP513Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP513Values1_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 1 j)=sharedDiskP513Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP513Value1_0
  · exact sharedDiskP513Value1_1
  · exact sharedDiskP513Value1_2
  · exact sharedDiskP513Value1_3
  · exact sharedDiskP513Value1_4
  · exact sharedDiskP513Value1_5
  · exact sharedDiskP513Value1_6
  · exact sharedDiskP513Value1_7
private theorem sharedDiskP513Value2_0 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 2 (0:Fin 8))=sharedDiskP513Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value2_1 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 2 (1:Fin 8))=sharedDiskP513Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value2_2 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 2 (2:Fin 8))=sharedDiskP513Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value2_3 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 2 (3:Fin 8))=sharedDiskP513Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value2_4 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 2 (4:Fin 8))=sharedDiskP513Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value2_5 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 2 (5:Fin 8))=sharedDiskP513Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value2_6 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 2 (6:Fin 8))=sharedDiskP513Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value2_7 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 2 (7:Fin 8))=sharedDiskP513Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP513Values2_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 2 j)=sharedDiskP513Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP513Value2_0
  · exact sharedDiskP513Value2_1
  · exact sharedDiskP513Value2_2
  · exact sharedDiskP513Value2_3
  · exact sharedDiskP513Value2_4
  · exact sharedDiskP513Value2_5
  · exact sharedDiskP513Value2_6
  · exact sharedDiskP513Value2_7
private theorem sharedDiskP513Value3_0 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 3 (0:Fin 8))=sharedDiskP513Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value3_1 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 3 (1:Fin 8))=sharedDiskP513Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value3_2 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 3 (2:Fin 8))=sharedDiskP513Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value3_3 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 3 (3:Fin 8))=sharedDiskP513Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value3_4 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 3 (4:Fin 8))=sharedDiskP513Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value3_5 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 3 (5:Fin 8))=sharedDiskP513Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value3_6 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 3 (6:Fin 8))=sharedDiskP513Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value3_7 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 3 (7:Fin 8))=sharedDiskP513Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP513Values3_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 3 j)=sharedDiskP513Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP513Value3_0
  · exact sharedDiskP513Value3_1
  · exact sharedDiskP513Value3_2
  · exact sharedDiskP513Value3_3
  · exact sharedDiskP513Value3_4
  · exact sharedDiskP513Value3_5
  · exact sharedDiskP513Value3_6
  · exact sharedDiskP513Value3_7
private theorem sharedDiskP513Value4_0 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 4 (0:Fin 8))=sharedDiskP513Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value4_1 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 4 (1:Fin 8))=sharedDiskP513Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value4_2 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 4 (2:Fin 8))=sharedDiskP513Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value4_3 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 4 (3:Fin 8))=sharedDiskP513Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value4_4 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 4 (4:Fin 8))=sharedDiskP513Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value4_5 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 4 (5:Fin 8))=sharedDiskP513Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value4_6 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 4 (6:Fin 8))=sharedDiskP513Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value4_7 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 4 (7:Fin 8))=sharedDiskP513Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP513Values4_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 4 j)=sharedDiskP513Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP513Value4_0
  · exact sharedDiskP513Value4_1
  · exact sharedDiskP513Value4_2
  · exact sharedDiskP513Value4_3
  · exact sharedDiskP513Value4_4
  · exact sharedDiskP513Value4_5
  · exact sharedDiskP513Value4_6
  · exact sharedDiskP513Value4_7
private theorem sharedDiskP513Value5_0 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 5 (0:Fin 8))=sharedDiskP513Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value5_1 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 5 (1:Fin 8))=sharedDiskP513Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value5_2 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 5 (2:Fin 8))=sharedDiskP513Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value5_3 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 5 (3:Fin 8))=sharedDiskP513Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value5_4 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 5 (4:Fin 8))=sharedDiskP513Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value5_5 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 5 (5:Fin 8))=sharedDiskP513Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value5_6 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 5 (6:Fin 8))=sharedDiskP513Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value5_7 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 5 (7:Fin 8))=sharedDiskP513Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP513Values5_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 5 j)=sharedDiskP513Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP513Value5_0
  · exact sharedDiskP513Value5_1
  · exact sharedDiskP513Value5_2
  · exact sharedDiskP513Value5_3
  · exact sharedDiskP513Value5_4
  · exact sharedDiskP513Value5_5
  · exact sharedDiskP513Value5_6
  · exact sharedDiskP513Value5_7
private theorem sharedDiskP513Value6_0 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 6 (0:Fin 8))=sharedDiskP513Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value6_1 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 6 (1:Fin 8))=sharedDiskP513Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value6_2 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 6 (2:Fin 8))=sharedDiskP513Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value6_3 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 6 (3:Fin 8))=sharedDiskP513Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value6_4 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 6 (4:Fin 8))=sharedDiskP513Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value6_5 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 6 (5:Fin 8))=sharedDiskP513Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value6_6 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 6 (6:Fin 8))=sharedDiskP513Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value6_7 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 6 (7:Fin 8))=sharedDiskP513Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP513Values6_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 6 j)=sharedDiskP513Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP513Value6_0
  · exact sharedDiskP513Value6_1
  · exact sharedDiskP513Value6_2
  · exact sharedDiskP513Value6_3
  · exact sharedDiskP513Value6_4
  · exact sharedDiskP513Value6_5
  · exact sharedDiskP513Value6_6
  · exact sharedDiskP513Value6_7
private theorem sharedDiskP513Value7_0 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 7 (0:Fin 8))=sharedDiskP513Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value7_1 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 7 (1:Fin 8))=sharedDiskP513Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value7_2 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 7 (2:Fin 8))=sharedDiskP513Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value7_3 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 7 (3:Fin 8))=sharedDiskP513Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value7_4 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 7 (4:Fin 8))=sharedDiskP513Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value7_5 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 7 (5:Fin 8))=sharedDiskP513Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value7_6 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 7 (6:Fin 8))=sharedDiskP513Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value7_7 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 7 (7:Fin 8))=sharedDiskP513Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP513Values7_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 7 j)=sharedDiskP513Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP513Value7_0
  · exact sharedDiskP513Value7_1
  · exact sharedDiskP513Value7_2
  · exact sharedDiskP513Value7_3
  · exact sharedDiskP513Value7_4
  · exact sharedDiskP513Value7_5
  · exact sharedDiskP513Value7_6
  · exact sharedDiskP513Value7_7
private theorem sharedDiskP513Value8_0 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 8 (0:Fin 8))=sharedDiskP513Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value8_1 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 8 (1:Fin 8))=sharedDiskP513Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value8_2 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 8 (2:Fin 8))=sharedDiskP513Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value8_3 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 8 (3:Fin 8))=sharedDiskP513Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value8_4 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 8 (4:Fin 8))=sharedDiskP513Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value8_5 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 8 (5:Fin 8))=sharedDiskP513Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value8_6 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 8 (6:Fin 8))=sharedDiskP513Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value8_7 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 8 (7:Fin 8))=sharedDiskP513Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP513Values8_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 8 j)=sharedDiskP513Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP513Value8_0
  · exact sharedDiskP513Value8_1
  · exact sharedDiskP513Value8_2
  · exact sharedDiskP513Value8_3
  · exact sharedDiskP513Value8_4
  · exact sharedDiskP513Value8_5
  · exact sharedDiskP513Value8_6
  · exact sharedDiskP513Value8_7
private theorem sharedDiskP513Value9_0 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 9 (0:Fin 8))=sharedDiskP513Values 9 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value9_1 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 9 (1:Fin 8))=sharedDiskP513Values 9 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value9_2 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 9 (2:Fin 8))=sharedDiskP513Values 9 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value9_3 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 9 (3:Fin 8))=sharedDiskP513Values 9 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value9_4 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 9 (4:Fin 8))=sharedDiskP513Values 9 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value9_5 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 9 (5:Fin 8))=sharedDiskP513Values 9 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value9_6 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 9 (6:Fin 8))=sharedDiskP513Values 9 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value9_7 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 9 (7:Fin 8))=sharedDiskP513Values 9 (7:Fin 8) := by decide +kernel
theorem sharedDiskP513Values9_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 9 j)=sharedDiskP513Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP513Value9_0
  · exact sharedDiskP513Value9_1
  · exact sharedDiskP513Value9_2
  · exact sharedDiskP513Value9_3
  · exact sharedDiskP513Value9_4
  · exact sharedDiskP513Value9_5
  · exact sharedDiskP513Value9_6
  · exact sharedDiskP513Value9_7
private theorem sharedDiskP513Value10_0 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 10 (0:Fin 8))=sharedDiskP513Values 10 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value10_1 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 10 (1:Fin 8))=sharedDiskP513Values 10 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value10_2 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 10 (2:Fin 8))=sharedDiskP513Values 10 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value10_3 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 10 (3:Fin 8))=sharedDiskP513Values 10 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value10_4 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 10 (4:Fin 8))=sharedDiskP513Values 10 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value10_5 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 10 (5:Fin 8))=sharedDiskP513Values 10 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value10_6 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 10 (6:Fin 8))=sharedDiskP513Values 10 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value10_7 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 10 (7:Fin 8))=sharedDiskP513Values 10 (7:Fin 8) := by decide +kernel
theorem sharedDiskP513Values10_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 10 j)=sharedDiskP513Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP513Value10_0
  · exact sharedDiskP513Value10_1
  · exact sharedDiskP513Value10_2
  · exact sharedDiskP513Value10_3
  · exact sharedDiskP513Value10_4
  · exact sharedDiskP513Value10_5
  · exact sharedDiskP513Value10_6
  · exact sharedDiskP513Value10_7
private theorem sharedDiskP513Value11_0 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 11 (0:Fin 8))=sharedDiskP513Values 11 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value11_1 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 11 (1:Fin 8))=sharedDiskP513Values 11 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value11_2 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 11 (2:Fin 8))=sharedDiskP513Values 11 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value11_3 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 11 (3:Fin 8))=sharedDiskP513Values 11 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value11_4 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 11 (4:Fin 8))=sharedDiskP513Values 11 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value11_5 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 11 (5:Fin 8))=sharedDiskP513Values 11 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value11_6 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 11 (6:Fin 8))=sharedDiskP513Values 11 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value11_7 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 11 (7:Fin 8))=sharedDiskP513Values 11 (7:Fin 8) := by decide +kernel
theorem sharedDiskP513Values11_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 11 j)=sharedDiskP513Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP513Value11_0
  · exact sharedDiskP513Value11_1
  · exact sharedDiskP513Value11_2
  · exact sharedDiskP513Value11_3
  · exact sharedDiskP513Value11_4
  · exact sharedDiskP513Value11_5
  · exact sharedDiskP513Value11_6
  · exact sharedDiskP513Value11_7
private theorem sharedDiskP513Value12_0 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 12 (0:Fin 8))=sharedDiskP513Values 12 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value12_1 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 12 (1:Fin 8))=sharedDiskP513Values 12 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value12_2 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 12 (2:Fin 8))=sharedDiskP513Values 12 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value12_3 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 12 (3:Fin 8))=sharedDiskP513Values 12 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value12_4 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 12 (4:Fin 8))=sharedDiskP513Values 12 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value12_5 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 12 (5:Fin 8))=sharedDiskP513Values 12 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value12_6 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 12 (6:Fin 8))=sharedDiskP513Values 12 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP513Value12_7 : truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 12 (7:Fin 8))=sharedDiskP513Values 12 (7:Fin 8) := by decide +kernel
theorem sharedDiskP513Values12_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points 12 j)=sharedDiskP513Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP513Value12_0
  · exact sharedDiskP513Value12_1
  · exact sharedDiskP513Value12_2
  · exact sharedDiskP513Value12_3
  · exact sharedDiskP513Value12_4
  · exact sharedDiskP513Value12_5
  · exact sharedDiskP513Value12_6
  · exact sharedDiskP513Value12_7
theorem sharedDiskP513Values_eq : ∀ (i : Fin 13) (j : Fin 8), truncatedChordCell 1 sharedDiskP513Params (sharedChord493Gauss8Points i j)=sharedDiskP513Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP513Values0_eq
  · exact sharedDiskP513Values1_eq
  · exact sharedDiskP513Values2_eq
  · exact sharedDiskP513Values3_eq
  · exact sharedDiskP513Values4_eq
  · exact sharedDiskP513Values5_eq
  · exact sharedDiskP513Values6_eq
  · exact sharedDiskP513Values7_eq
  · exact sharedDiskP513Values8_eq
  · exact sharedDiskP513Values9_eq
  · exact sharedDiskP513Values10_eq
  · exact sharedDiskP513Values11_eq
  · exact sharedDiskP513Values12_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP513Box : HorizontalRectangle := ⟨(149/200),(3/4),(916250015015873/1649267441664000),(929134916903873/1649267441664000),(8296050646274921784132304694371/1298074214633706907132624082305024),(3367688403210460817234782255901795/1298074214633706907132624082305024),(-1388790778859483355253879193831217/324518553658426726783156020576256),(-529946192539518719342450094737201/324518553658426726783156020576256),true,[]⟩
noncomputable def sharedDiskP513Grid : CGrid := momentChordGrid sharedDiskP513Params chordGaussRule8 1 sharedChord493Bd sharedChord493M (23175049/18014398509481984)
theorem sharedDiskP513Columns : containedInReported sharedDiskP513Grid.re sharedDiskP513Box.reLo sharedDiskP513Box.reHi=true ∧ containedInReported sharedDiskP513Grid.im sharedDiskP513Box.imLo sharedDiskP513Box.imHi=true := by
  rw [sharedDiskP513Grid,momentChordGrid_eq_tabulated sharedDiskP513Params chordGaussRule8 1 sharedChord493Bd sharedChord493M (23175049/18014398509481984) sharedChord493Gauss8Points sharedChord493Gauss8Weights sharedDiskP513Values sharedChord493Gauss8Points_eq sharedChord493Gauss8Weights_eq sharedDiskP513Values_eq]
  decide +kernel
theorem sharedDiskP513Sound : sharedDiskP513Box.Sound := by
  intro t a tl tu al au
  change (((149/200):ℚ):ℝ)≤t at tl
  change t≤(((3/4):ℚ):ℝ) at tu
  change (((916250015015873/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((929134916903873/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP513Params_ok] at ps
  have band := sharedChord493ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((129/200):ℚ)≤(149/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3/4):ℚ)≤(3/4)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((878940159632233/1649267441664000):ℚ)≤(916250015015873/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((929134916903873/1649267441664000):ℚ)≤(929134916903873/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 1 sharedChord493Bd (by decide +kernel) (by decide +kernel) sharedChord493M (by decide +kernel) (sharedChord493Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP513Columns.1 sharedDiskP513Columns.2
def sharedDiskP513Rows : List SignRow := [positive_513.toSignRow]
theorem sharedDiskP513Rows_actual : ∀ r∈sharedDiskP513Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP513Rows.all (sharedDiskP513Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP513Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP511Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP513Rows_actual
