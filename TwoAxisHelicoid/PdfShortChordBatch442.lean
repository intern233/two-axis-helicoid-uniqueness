import TwoAxisHelicoid.PdfSharedChord442Gauss6
import TwoAxisHelicoid.PdfSharedChord442Disks
import TwoAxisHelicoid.PdfSharedChord442Gauss8

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP442Params : ChordParams := ⟨⟨(-469308876484190916311),(-446690082326940401689),true⟩,⟨4699349087847602069849231,4731237407873395470866695,true⟩,⟨22326360568803090251809,22934304230729401453249,true⟩,⟨24140710186863035632459,24785951845600044422548,true⟩,⟨46458417823547367689845,47621028093782873594230,true⟩,⟨1207987566094683331415998,1208032769426104318445316,true⟩,⟨(-4773769652484002405656719),(-4743756079088589943705566),true⟩,⟨⟨1204213696791183038877322,1211818503962328011601241,true⟩,⟨(-46),46,true⟩⟩⟩
theorem sharedDiskP442Params_ok : chordParams (Grid.ofRats (159/400) (2/5)) (Grid.ofRats (1110112793673/2199023255552) (1110649664585/2199023255552))=sharedDiskP442Params := by decide +kernel
def sharedDiskP442Values (i : Fin 20) (j : Fin 6) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-9073163328409025039855308),(-7173707108279070059438175),true⟩,⟨(-808232027982950513579254),710160223366368532589906,true⟩⟩
  | 0,1 => ⟨⟨(-8593572723420022622071298),(-6728605213017514272865849),true⟩,⟨(-882026652378048448898133),645412900319419695222518,true⟩⟩
  | 0,2 => ⟨⟨(-8292853956410701435521851),(-6453640348578718158803466),true⟩,⟨(-933071012504984459865889),591359773608504670732269,true⟩⟩
  | 0,3 => ⟨⟨(-9629379987800259371766998),(-7699482502600599058341020),true⟩,⟨(-735116731890426202025137),751219803616224587830664,true⟩⟩
  | 0,4 => ⟨⟨(-10132917876025584225812533),(-8182517960066871109928986),true⟩,⟨(-688621278515514691427167),756169439272714963758864,true⟩⟩
  | 0,5 => ⟨⟨(-10460642685291203267075183),(-8501031828224881839343335),true⟩,⟨(-667914009380101178339582),742781866747619097335440,true⟩⟩
  | 1,0 => ⟨⟨(-6932978654224378477988499),(-5251798204194878065286751),true⟩,⟨(-1205597851187524028174505),233031408072094906112786,true⟩⟩
  | 1,1 => ⟨⟨(-6526530504982351948575969),(-4905782412248759598907941),true⟩,⟨(-1299077688387452742842263),95415069404087684240357,true⟩⟩
  | 1,2 => ⟨⟨(-6274539088384550266659270),(-4694189452399080144716136),true⟩,⟨(-1359520266417968334749739),3373555879651490263892,true⟩⟩
  | 1,3 => ⟨⟨(-7412073078265617030641066),(-5667434610186976564508039),true⟩,⟨(-1102196557568923651531007),376589053697985608999494,true⟩⟩
  | 1,4 => ⟨⟨(-7853668352470010757126052),(-6058000144542004330119757),true⟩,⟨(-1013868792152443519546698),494476970883553307003538,true⟩⟩
  | 1,5 => ⟨⟨(-8145333578329270965012830),(-6319952934327604494539270),true⟩,⟨(-959399965369605994206700),561154528139039952438578,true⟩⟩
  | 2,0 => ⟨⟨(-5164350409379571156706305),(-3780412179488154006864066),true⟩,⟨(-1647423779775027555898028),(-435793863826887875987965),true⟩⟩
  | 2,1 => ⟨⟨(-4838266659769204430676063),(-3517949708880387983640300),true⟩,⟨(-1737167699912758148657000),(-576039625406578425302809),true⟩⟩
  | 2,2 => ⟨⟨(-4636890628273694007826010),(-3356930012551607525411508),true⟩,⟨(-1793420810236614716018889),(-664499430991797242739619),true⟩⟩
  | 2,3 => ⟨⟨(-5551449082335986253184934),(-4095291976756520198479168),true⟩,⟨(-1543569530508023590225310),(-275416830038017706978251),true⟩⟩
  | 2,4 => ⟨⟨(-5911531792036456183013528),(-4391940676437337232335486),true⟩,⟨(-1450073514278961419003044),(-133545986326052085749553),true⟩⟩
  | 2,5 => ⟨⟨(-6151671870804274647408624),(-4591802872525177069139093),true⟩,⟨(-1389646750466204951932903),(-42971283374402927565885),true⟩⟩
  | 3,0 => ⟨⟨(-3747099094953097207145368),(-2651735719769158720336337),true⟩,⟨(-2045854075673798301549808),(-1064220838831380178594961),true⟩⟩
  | 3,1 => ⟨⟨(-3484864844412814716561954),(-2444705556662680515795741),true⟩,⟨(-2120065724376636793192219),(-1182123526036842962802521),true⟩⟩
  | 3,2 => ⟨⟨(-3322445065928435497614190),(-2316387919119320568591327),true⟩,⟨(-2165618196159821063923038),(-1254533266520081237724652),true⟩⟩
  | 3,3 => ⟨⟨(-4057659674672786919375064),(-2897087623602666347858465),true⟩,⟨(-1957472032311324412748030),(-923948831481364785752377),true⟩⟩
  | 3,4 => ⟨⟨(-4346361159080394801389425),(-3125777909408100808489962),true⟩,⟨(-1875407827812871427861670),(-793954356607321743587280),true⟩⟩
  | 3,5 => ⟨⟨(-4538865446073510243336496),(-3278800758926309657075705),true⟩,⟨(-1820989102114901752124790),(-707968964639762681767141),true⟩⟩
  | 4,0 => ⟨⟨(-1983508801727518411402572),(-1243457626560689876829820),true⟩,⟨(-2517985137447516393635111),(-1806561617664720837810615),true⟩⟩
  | 4,1 => ⟨⟨(-1598100820055618751031978),(-925205237089816680478282),true⟩,⟨(-2604980407168344135881227),(-1937879709758580295476147),true⟩⟩
  | 4,2 => ⟨⟨(-1362463973008275014531662),(-728151173745667060680423),true⟩,⟨(-2652859259797108792870803),(-2010573975072912823894890),true⟩⟩
  | 4,3 => ⟨⟨(-2451146434936363847019463),(-1622856703549221669826972),true⟩,⟨(-2400564040453464727812635),(-1626075680145577930762897),true⟩⟩
  | 4,4 => ⟨⟨(-2898097594725064409043654),(-1980166682398661531679926),true⟩,⟨(-2282119092622695925887221),(-1439902880115855452937450),true⟩⟩
  | 4,5 => ⟨⟨(-3203996911911631833686601),(-2222710701878699173805892),true⟩,⟨(-2198554264948518301677834),(-1306907857975365877877839),true⟩⟩
  | 5,0 => ⟨⟨(-325185949409155364103574),162216172187624705389768,true⟩,⟨(-2806676496349981932106266),(-2259057002905825470259457),true⟩⟩
  | 5,1 => ⟨⟨(-16427136410421027915751),440131568297405647331721,true⟩,⟨(-2833142474073553848111307),(-2307974691879683337793470),true⟩⟩
  | 5,2 => ⟨⟨175206714165076811418629,618198844959002398455080,true⟩,⟨(-2845097801722912831251511),(-2332111764303332744782242),true⟩⟩
  | 5,3 => ⟨⟨(-688039393256587429334247),(-153949104043678842009608),true⟩,⟨(-2764037410161068337889575),(-2185908740085509506914019),true⟩⟩
  | 5,4 => ⟨⟨(-1024036043151498846411219),(-441918100357315714509137),true⟩,⟨(-2713661867799176441963183),(-2104824711727413370070573),true⟩⟩
  | 5,5 => ⟨⟨(-1248141839132999418441685),(-631888945215936500056554),true⟩,⟨(-2674483671367381193672318),(-2043785087631177115181394),true⟩⟩
  | 6,0 => ⟨⟨1764611741430191476725654,2177307036236180325436491,true⟩,⟨(-2830347305795882314480050),(-2385819915119475371873380),true⟩⟩
  | 6,1 => ⟨⟨2244997385265113780891782,2657194837124044057357594,true⟩,⟨(-2785307173761048220748685),(-2356379484058315504338626),true⟩⟩
  | 6,2 => ⟨⟨2543024220283096102442785,2956160585601781776920013,true⟩,⟨(-2749589548347220942059689),(-2329551666281525434773273),true⟩⟩
  | 6,3 => ⟨⟨1196535331777836060576807,1613818430498069537329193,true⟩,⟨(-2861095953030627541990219),(-2395633094486013841756948),true⟩⟩
  | 6,4 => ⟨⟨667785076401413994526610,1094278778512148360822597,true⟩,⟨(-2864766351881048699055201),(-2376766599565842177080572),true⟩⟩
  | 6,5 => ⟨⟨313566125517505047968834,749466326510234507118603,true⟩,⟨(-2852344066888473427806961),(-2347243258352315061855850),true⟩⟩
  | 7,0 => ⟨⟨3874095446724665475228050,4299540750746286718499496,true⟩,⟨(-2529735691553347190966506),(-2144073416227333648114082),true⟩⟩
  | 7,1 => ⟨⟨4269876629424241049612700,4700701121304182598619854,true⟩,⟨(-2448339457071244963019277),(-2071699520449661339073512),true⟩⟩
  | 7,2 => ⟨⟨4515306987374912231543455,4949712388070653100449894,true⟩,⟨(-2394693091364726514347965),(-2023459058438372614488772),true⟩⟩
  | 7,3 => ⟨⟨3407029593804916035266200,3826953504519619051540827,true⟩,⟨(-2617006775425189412228538),(-2220097686193419044139110),true⟩⟩
  | 7,4 => ⟨⟨2975125396674421031511511,3390998199796587625925575,true⟩,⟨(-2688332912065325511147673),(-2280297591250006801949254),true⟩⟩
  | 7,5 => ⟨⟨2688527573788973880669630,3102417841369189294043684,true⟩,⟨(-2730164136796309646845859),(-2314276967911431222171033),true⟩⟩
  | 8,0 => ⟨⟨7954618505374733708416823,8441011853794276914958157,true⟩,⟨(-1416868514862774867487897),(-1117164306840983489501533),true⟩⟩
  | 8,1 => ⟨⟨8701582166665922481924758,9194456949050925767211833,true⟩,⟨(-1138304770350295468815328),(-856602162525566570727385),true⟩⟩
  | 8,2 => ⟨⟨9090407754019194096685220,9584549915378604726145477,true⟩,⟨(-976392119827565077542095),(-705430188972218291244089),true⟩⟩
  | 8,3 => ⟨⟨6879104844242936167108842,7351061752193754478975717,true⟩,⟨(-1768594898296463061491398),(-1445965198881932575669110),true⟩⟩
  | 8,4 => ⟨⟨5695977107579060310266515,6149088482297599685057167,true⟩,⟨(-2105863160848947236417949),(-1759291848463649773705504),true⟩⟩
  | 8,5 => ⟨⟨4811555121524497329295650,5250473446139138856456621,true⟩,⟨(-2326886518926414679324873),(-1962019960080699552474123),true⟩⟩
  | 9,0 => ⟨⟨10284414696200987342754464,10716857470396211392884799,true⟩,⟨(-2876292968626325853757),187048303549627820477048,true⟩⟩
  | 9,1 => ⟨⟨10054289819430565689945289,10450913962659624962768473,true⟩,⟨157985241188430584590350,327848260941758969354376,true⟩⟩
  | 9,2 => ⟨⟨9816126107567105398825449,10188583964179694395568501,true⟩,⟨233079140679415859372835,390901230395320657290699,true⟩⟩
  | 9,3 => ⟨⟨10249511889080247076836893,10716429786683218658588402,true⟩,⟨(-268003706798014857208234),(-51572185171478453042143),true⟩⟩
  | 9,4 => ⟨⟨9844945972341733301859808,10332656071173842099859833,true⟩,⟨(-596553820054473514166221),(-352674705770811332330380),true⟩⟩
  | 9,5 => ⟨⟨9338707516211985511899801,9832452308471995187396448,true⟩,⟨(-863918444121423351814304),(-600641088963698710912206),true⟩⟩
  | 10,0 => ⟨⟨6460950514429069249164871,6633842740097607010237263,true⟩,⟨379784491211632693879746,455034545675339128618965,true⟩⟩
  | 10,1 => ⟨⟨5416305264436556084148272,5544348379679217648080521,true⟩,⟨337027157804021152531731,395341693310029464900622,true⟩⟩
  | 10,2 => ⟨⟨4822077180923295526051144,4926870096193397933637460,true⟩,⟨304458933620349963637949,354020681402961966161106,true⟩⟩
  | 10,3 => ⟨⟨7770299902232110456276084,8007668423825021818242049,true⟩,⟨398100930606741339422845,498221190264767758512966,true⟩⟩
  | 10,4 => ⟨⟨8939154633626104938341983,9245282199832319932010941,true⟩,⟨356047939596276560174616,484132031531604741923999,true⟩⟩
  | 10,5 => ⟨⟨9604239290358772817087414,9958471161988569639014483,true⟩,⟨277339442663445036734875,426592153241718534270944,true⟩⟩
  | 11,0 => ⟨⟨2796319983451430661271729,2881104449358004671498201,true⟩,⟨145257800707069633524546,180757570386272088298041,true⟩⟩
  | 11,1 => ⟨⟨2419380067212650940492192,2501374315453030771433768,true⟩,⟨99414800499293988065991,133347743209193991254499,true⟩⟩
  | 11,2 => ⟨⟨2242964218059649887224427,2324626920472300917666639,true⟩,⟨68947688779140987365883,102878812662104580653618,true⟩⟩
  | 11,3 => ⟨⟨3377040922276403984272902,3466977940520158288288434,true⟩,⟨199717049935506668012739,238699777848556360721227,true⟩⟩
  | 11,4 => ⟨⟨4041214942850729276419584,4136528139141563339117764,true⟩,⟨252048763366434710705918,295382366086730141520244,true⟩⟩
  | 11,5 => ⟨⟨4547757154465003566646636,4646538616779704045094430,true⟩,⟨287267234811264860383974,333970533170090188861026,true⟩⟩
  | 12,0 => ⟨⟨2060084170954298508478863,2151530116745163640285184,true⟩,⟨(-40788832318988981815994),322188389147352031416,true⟩⟩
  | 12,1 => ⟨⟨2114029160671088387535054,2215155103036824700495072,true⟩,⟨(-106071034736919746088011),(-57439322066087495757817),true⟩⟩
  | 12,2 => ⟨⟨2195739488464313474672698,2306819973308991637730392,true⟩,⟨(-170051537224399425923727),(-113511159928025110675172),true⟩⟩
  | 12,3 => ⟨⟨2073191512383982138113264,2158670291596503723611070,true⟩,⟨7542676560174514977415,44289645501155704526692,true⟩⟩
  | 12,4 => ⟨⟨2132734320457720407017562,2215536949183752068836249,true⟩,⟨39281625454980182600793,74134234882172382351740,true⟩⟩
  | 12,5 => ⟨⟨2190610126127815553721303,2272564829824037570491338,true⟩,⟨56779837619926927688501,90979609223468547176800,true⟩⟩
  | 13,0 => ⟨⟨2710590369803931456464909,2878751209277359929730747,true⟩,⟨(-557774752302797034449280),(-451456425312823239302253),true⟩⟩
  | 13,1 => ⟨⟨3032330609481918261587235,3240726361873489695597233,true⟩,⟨(-858284884629596364076415),(-713009254894727533435928),true⟩⟩
  | 13,2 => ⟨⟨3307019373374044517081986,3554996178285809277130225,true⟩,⟨(-1169676418885712674950595),(-983662613015327967100212),true⟩⟩
  | 13,3 => ⟨⟨2461542259063822305773794,2601639263915117020479203,true⟩,⟨(-360998514721003940761312),(-280063325133943381507906),true⟩⟩
  | 13,4 => ⟨⟨2310751127174031783270984,2434517138827396099288885,true⟩,⟨(-252118157564176698626818),(-185159999955261021293288),true⟩⟩
  | 13,5 => ⟨⟨2239063165121458971931287,2355001600421679682732905,true⟩,⟨(-201286471353708216070320),(-140802694624830611041714),true⟩⟩
  | 14,0 => ⟨⟨3792038619861191877102590,4129165681716207465643407,true⟩,⟨(-1905745820151423528820953),(-1621319083591495786912723),true⟩⟩
  | 14,1 => ⟨⟨3945296399199167724243042,4319118471868106595898561,true⟩,⟨(-2216735663470220692411835),(-1889702055310224065809660),true⟩⟩
  | 14,2 => ⟨⟨4044727319455867977640359,4446079267649443423947561,true⟩,⟨(-2451664223838166536314604),(-2092012947157221922089038),true⟩⟩
  | 14,3 => ⟨⟨3626267586242643069779555,3929236784929819219771448,true⟩,⟨(-1619609796058565610367900),(-1373829337013950194949735),true⟩⟩
  | 14,4 => ⟨⟨3488566491129857802678660,3766359256752902106523620,true⟩,⟨(-1411640143463936050029609),(-1193630425199760364229679),true⟩⟩
  | 14,5 => ⟨⟨3405188325652560552549173,3668862772237266835410886,true⟩,⟨(-1296404782985795102180187),(-1093673559464286987767000),true⟩⟩
  | 15,0 => ⟨⟨4434293680442096068608636,5034408799922541731047527,true⟩,⟨(-4152682032551483628155678),(-3545179056028621690285534),true⟩⟩
  | 15,1 => ⟨⟨4451238317318252735620589,5151311315127251413436830,true⟩,⟨(-4993163270239266399883112),(-4255231040245004860734577),true⟩⟩
  | 15,2 => ⟨⟨4395881479365141073563000,5173771235228356634269426,true⟩,⟨(-5634585005774296644083005),(-4793345866444407700250976),true⟩⟩
  | 15,3 => ⟨⟨4325857965927967848354780,4837557956266880596311394,true⟩,⟨(-3398109104555067198571168),(-2903142712648462842850590),true⟩⟩
  | 15,4 => ⟨⟨4190074913257371400237777,4639881471257796228764055,true⟩,⟨(-2866962000025794668654340),(-2448716714017742253209291),true⟩⟩
  | 15,5 => ⟨⟨4093846307835680374641824,4510265115024458809096035,true⟩,⟨(-2580623590258416796091339),(-2202906344090506505156864),true⟩⟩
  | 16,0 => ⟨⟨3838720754310638263007420,4876186644936938097671646,true⟩,⟨(-7667953927490969147684478),(-6475379619357745338899470),true⟩⟩
  | 16,1 => ⟨⟨3480776122482233786740276,4619873677461314156326459,true⟩,⟨(-8411636162808875980601856),(-7080187124180706953167175),true⟩⟩
  | 16,2 => ⟨⟨3185915475463187774135157,4396309144208807919870681,true⟩,⟨(-8913326067388475941978418),(-7484452419852624223348331),true⟩⟩
  | 16,3 => ⟨⟨4120724689679454732824279,5056510590548788170430329,true⟩,⟨(-6892901643709435569057692),(-5838808895555350692223115),true⟩⟩
  | 16,4 => ⟨⟨4285052787223485695904902,5141414618009825193993035,true⟩,⟨(-6267730873414426666210105),(-5321144938618307189561090),true⟩⟩
  | 16,5 => ⟨⟨4356748839310578851728261,5166903021267239453673906,true⟩,⟨(-5896670234413634550624855),(-5012240681261045581982054),true⟩⟩
  | 17,0 => ⟨⟨811756305688248534277839,2429580827430651261262138,true⟩,⟨(-11399840307023402290678223),(-9423761148413516370677360),true⟩⟩
  | 17,1 => ⟨⟨(-419508092602700344634817),1393206586012177041822301,true⟩,⟨(-12113772937718348099420261),(-9932890871334684961505085),true⟩⟩
  | 17,2 => ⟨⟨(-1343809990532491489072028),619913280154052653868480,true⟩,⟨(-12496269750063967286551856),(-10180829405767886915230962),true⟩⟩
  | 17,3 => ⟨⟨1888046275173434474188484,3345766820434082355368750,true⟩,⟨(-10508693270946536216545048),(-8744534591828457385009400),true⟩⟩
  | 17,4 => ⟨⟨2631478468745648940364136,3957682354481686602941970,true⟩,⟨(-9690024729406084921415750),(-8103395255829440053816343),true⟩⟩
  | 17,5 => ⟨⟨3017520970300718870457870,4265213132578280019482451,true⟩,⟨(-9168805705678630599389566),(-7689031447180875333086925),true⟩⟩
  | 18,0 => ⟨⟨(-6871329548535349217595275),(-4000417563560951567159892),true⟩,⟨(-12625687286023923356450408),(-9787243925997387483761140),true⟩⟩
  | 18,1 => ⟨⟨(-8737429966547066001832652),(-5628647914671696276117121),true⟩,⟨(-11752895416341238050226271),(-8883998730285803050615751),true⟩⟩
  | 18,2 => ⟨⟨(-9824252116510319363906955),(-6605025040649828318090873),true⟩,⟨(-10908893695254275425364196),(-8077491539730083192831138),true⟩⟩
  | 18,3 => ⟨⟨(-4710582927352953691516226),(-2164211328222253909008084),true⟩,⟨(-13005313495359255839459475),(-10304149813461667949596269),true⟩⟩
  | 18,4 => ⟨⟨(-2903388751535970398862022),(-659900612829491125342778),true⟩,⟨(-12896105347339960708512111),(-10376901738365395606677038),true⟩⟩
  | 18,5 => ⟨⟨(-1839834045605409965003148),213909818510249888998349,true⟩,⟨(-12655411983279696451151577),(-10270343560552586097866384),true⟩⟩
  | 19,0 => ⟨⟨(-12184573025590532771511573),(-9160425898505370156761099),true⟩,⟨(-4497192298132381943264487),(-2484497908507664275749122),true⟩⟩
  | 19,1 => ⟨⟨(-11614510000581703473033415),(-8937156397314434317607104),true⟩,⟨(-2232156859486382115610132),(-638577433603981072747091),true⟩⟩
  | 19,2 => ⟨⟨(-10944890057977385590024868),(-8541091116468599224198358),true⟩,⟨(-930164795537080275540066),439830779723510895398855,true⟩⟩
  | 19,3 => ⟨⟨(-12012616690360271065259381),(-8761626861264187705165184),true⟩,⟨(-7131513794765697285810613),(-4714291240699274286849274),true⟩⟩
  | 19,4 => ⟨⟨(-11155848363413848382870035),(-7857544129964870400279835),true⟩,⟨(-9252309857348884531902810),(-6570095191441058944165259),true⟩⟩
  | 19,5 => ⟨⟨(-10312858509308923263786802),(-7054732507653194346462769),true⟩,⟨(-10407860398959951420092842),(-7613462022738233629469296),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP442Value0_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 0 (0:Fin 6))=sharedDiskP442Values 0 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value0_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 0 (1:Fin 6))=sharedDiskP442Values 0 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value0_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 0 (2:Fin 6))=sharedDiskP442Values 0 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value0_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 0 (3:Fin 6))=sharedDiskP442Values 0 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value0_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 0 (4:Fin 6))=sharedDiskP442Values 0 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value0_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 0 (5:Fin 6))=sharedDiskP442Values 0 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values0_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 0 j)=sharedDiskP442Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value0_0
  · exact sharedDiskP442Value0_1
  · exact sharedDiskP442Value0_2
  · exact sharedDiskP442Value0_3
  · exact sharedDiskP442Value0_4
  · exact sharedDiskP442Value0_5
private theorem sharedDiskP442Value1_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 1 (0:Fin 6))=sharedDiskP442Values 1 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value1_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 1 (1:Fin 6))=sharedDiskP442Values 1 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value1_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 1 (2:Fin 6))=sharedDiskP442Values 1 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value1_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 1 (3:Fin 6))=sharedDiskP442Values 1 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value1_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 1 (4:Fin 6))=sharedDiskP442Values 1 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value1_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 1 (5:Fin 6))=sharedDiskP442Values 1 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values1_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 1 j)=sharedDiskP442Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value1_0
  · exact sharedDiskP442Value1_1
  · exact sharedDiskP442Value1_2
  · exact sharedDiskP442Value1_3
  · exact sharedDiskP442Value1_4
  · exact sharedDiskP442Value1_5
private theorem sharedDiskP442Value2_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 2 (0:Fin 6))=sharedDiskP442Values 2 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value2_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 2 (1:Fin 6))=sharedDiskP442Values 2 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value2_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 2 (2:Fin 6))=sharedDiskP442Values 2 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value2_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 2 (3:Fin 6))=sharedDiskP442Values 2 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value2_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 2 (4:Fin 6))=sharedDiskP442Values 2 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value2_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 2 (5:Fin 6))=sharedDiskP442Values 2 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values2_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 2 j)=sharedDiskP442Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value2_0
  · exact sharedDiskP442Value2_1
  · exact sharedDiskP442Value2_2
  · exact sharedDiskP442Value2_3
  · exact sharedDiskP442Value2_4
  · exact sharedDiskP442Value2_5
private theorem sharedDiskP442Value3_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 3 (0:Fin 6))=sharedDiskP442Values 3 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value3_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 3 (1:Fin 6))=sharedDiskP442Values 3 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value3_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 3 (2:Fin 6))=sharedDiskP442Values 3 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value3_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 3 (3:Fin 6))=sharedDiskP442Values 3 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value3_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 3 (4:Fin 6))=sharedDiskP442Values 3 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value3_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 3 (5:Fin 6))=sharedDiskP442Values 3 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values3_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 3 j)=sharedDiskP442Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value3_0
  · exact sharedDiskP442Value3_1
  · exact sharedDiskP442Value3_2
  · exact sharedDiskP442Value3_3
  · exact sharedDiskP442Value3_4
  · exact sharedDiskP442Value3_5
private theorem sharedDiskP442Value4_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 4 (0:Fin 6))=sharedDiskP442Values 4 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value4_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 4 (1:Fin 6))=sharedDiskP442Values 4 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value4_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 4 (2:Fin 6))=sharedDiskP442Values 4 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value4_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 4 (3:Fin 6))=sharedDiskP442Values 4 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value4_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 4 (4:Fin 6))=sharedDiskP442Values 4 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value4_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 4 (5:Fin 6))=sharedDiskP442Values 4 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values4_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 4 j)=sharedDiskP442Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value4_0
  · exact sharedDiskP442Value4_1
  · exact sharedDiskP442Value4_2
  · exact sharedDiskP442Value4_3
  · exact sharedDiskP442Value4_4
  · exact sharedDiskP442Value4_5
private theorem sharedDiskP442Value5_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 5 (0:Fin 6))=sharedDiskP442Values 5 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value5_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 5 (1:Fin 6))=sharedDiskP442Values 5 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value5_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 5 (2:Fin 6))=sharedDiskP442Values 5 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value5_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 5 (3:Fin 6))=sharedDiskP442Values 5 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value5_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 5 (4:Fin 6))=sharedDiskP442Values 5 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value5_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 5 (5:Fin 6))=sharedDiskP442Values 5 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values5_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 5 j)=sharedDiskP442Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value5_0
  · exact sharedDiskP442Value5_1
  · exact sharedDiskP442Value5_2
  · exact sharedDiskP442Value5_3
  · exact sharedDiskP442Value5_4
  · exact sharedDiskP442Value5_5
private theorem sharedDiskP442Value6_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 6 (0:Fin 6))=sharedDiskP442Values 6 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value6_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 6 (1:Fin 6))=sharedDiskP442Values 6 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value6_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 6 (2:Fin 6))=sharedDiskP442Values 6 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value6_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 6 (3:Fin 6))=sharedDiskP442Values 6 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value6_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 6 (4:Fin 6))=sharedDiskP442Values 6 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value6_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 6 (5:Fin 6))=sharedDiskP442Values 6 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values6_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 6 j)=sharedDiskP442Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value6_0
  · exact sharedDiskP442Value6_1
  · exact sharedDiskP442Value6_2
  · exact sharedDiskP442Value6_3
  · exact sharedDiskP442Value6_4
  · exact sharedDiskP442Value6_5
private theorem sharedDiskP442Value7_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 7 (0:Fin 6))=sharedDiskP442Values 7 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value7_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 7 (1:Fin 6))=sharedDiskP442Values 7 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value7_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 7 (2:Fin 6))=sharedDiskP442Values 7 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value7_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 7 (3:Fin 6))=sharedDiskP442Values 7 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value7_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 7 (4:Fin 6))=sharedDiskP442Values 7 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value7_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 7 (5:Fin 6))=sharedDiskP442Values 7 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values7_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 7 j)=sharedDiskP442Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value7_0
  · exact sharedDiskP442Value7_1
  · exact sharedDiskP442Value7_2
  · exact sharedDiskP442Value7_3
  · exact sharedDiskP442Value7_4
  · exact sharedDiskP442Value7_5
private theorem sharedDiskP442Value8_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 8 (0:Fin 6))=sharedDiskP442Values 8 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value8_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 8 (1:Fin 6))=sharedDiskP442Values 8 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value8_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 8 (2:Fin 6))=sharedDiskP442Values 8 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value8_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 8 (3:Fin 6))=sharedDiskP442Values 8 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value8_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 8 (4:Fin 6))=sharedDiskP442Values 8 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value8_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 8 (5:Fin 6))=sharedDiskP442Values 8 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values8_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 8 j)=sharedDiskP442Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value8_0
  · exact sharedDiskP442Value8_1
  · exact sharedDiskP442Value8_2
  · exact sharedDiskP442Value8_3
  · exact sharedDiskP442Value8_4
  · exact sharedDiskP442Value8_5
private theorem sharedDiskP442Value9_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 9 (0:Fin 6))=sharedDiskP442Values 9 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value9_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 9 (1:Fin 6))=sharedDiskP442Values 9 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value9_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 9 (2:Fin 6))=sharedDiskP442Values 9 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value9_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 9 (3:Fin 6))=sharedDiskP442Values 9 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value9_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 9 (4:Fin 6))=sharedDiskP442Values 9 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value9_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 9 (5:Fin 6))=sharedDiskP442Values 9 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values9_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 9 j)=sharedDiskP442Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value9_0
  · exact sharedDiskP442Value9_1
  · exact sharedDiskP442Value9_2
  · exact sharedDiskP442Value9_3
  · exact sharedDiskP442Value9_4
  · exact sharedDiskP442Value9_5
private theorem sharedDiskP442Value10_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 10 (0:Fin 6))=sharedDiskP442Values 10 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value10_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 10 (1:Fin 6))=sharedDiskP442Values 10 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value10_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 10 (2:Fin 6))=sharedDiskP442Values 10 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value10_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 10 (3:Fin 6))=sharedDiskP442Values 10 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value10_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 10 (4:Fin 6))=sharedDiskP442Values 10 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value10_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 10 (5:Fin 6))=sharedDiskP442Values 10 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values10_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 10 j)=sharedDiskP442Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value10_0
  · exact sharedDiskP442Value10_1
  · exact sharedDiskP442Value10_2
  · exact sharedDiskP442Value10_3
  · exact sharedDiskP442Value10_4
  · exact sharedDiskP442Value10_5
private theorem sharedDiskP442Value11_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 11 (0:Fin 6))=sharedDiskP442Values 11 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value11_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 11 (1:Fin 6))=sharedDiskP442Values 11 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value11_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 11 (2:Fin 6))=sharedDiskP442Values 11 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value11_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 11 (3:Fin 6))=sharedDiskP442Values 11 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value11_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 11 (4:Fin 6))=sharedDiskP442Values 11 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value11_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 11 (5:Fin 6))=sharedDiskP442Values 11 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values11_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 11 j)=sharedDiskP442Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value11_0
  · exact sharedDiskP442Value11_1
  · exact sharedDiskP442Value11_2
  · exact sharedDiskP442Value11_3
  · exact sharedDiskP442Value11_4
  · exact sharedDiskP442Value11_5
private theorem sharedDiskP442Value12_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 12 (0:Fin 6))=sharedDiskP442Values 12 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value12_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 12 (1:Fin 6))=sharedDiskP442Values 12 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value12_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 12 (2:Fin 6))=sharedDiskP442Values 12 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value12_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 12 (3:Fin 6))=sharedDiskP442Values 12 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value12_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 12 (4:Fin 6))=sharedDiskP442Values 12 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value12_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 12 (5:Fin 6))=sharedDiskP442Values 12 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values12_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 12 j)=sharedDiskP442Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value12_0
  · exact sharedDiskP442Value12_1
  · exact sharedDiskP442Value12_2
  · exact sharedDiskP442Value12_3
  · exact sharedDiskP442Value12_4
  · exact sharedDiskP442Value12_5
private theorem sharedDiskP442Value13_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 13 (0:Fin 6))=sharedDiskP442Values 13 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value13_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 13 (1:Fin 6))=sharedDiskP442Values 13 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value13_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 13 (2:Fin 6))=sharedDiskP442Values 13 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value13_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 13 (3:Fin 6))=sharedDiskP442Values 13 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value13_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 13 (4:Fin 6))=sharedDiskP442Values 13 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value13_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 13 (5:Fin 6))=sharedDiskP442Values 13 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values13_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 13 j)=sharedDiskP442Values 13 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value13_0
  · exact sharedDiskP442Value13_1
  · exact sharedDiskP442Value13_2
  · exact sharedDiskP442Value13_3
  · exact sharedDiskP442Value13_4
  · exact sharedDiskP442Value13_5
private theorem sharedDiskP442Value14_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 14 (0:Fin 6))=sharedDiskP442Values 14 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value14_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 14 (1:Fin 6))=sharedDiskP442Values 14 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value14_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 14 (2:Fin 6))=sharedDiskP442Values 14 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value14_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 14 (3:Fin 6))=sharedDiskP442Values 14 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value14_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 14 (4:Fin 6))=sharedDiskP442Values 14 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value14_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 14 (5:Fin 6))=sharedDiskP442Values 14 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values14_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 14 j)=sharedDiskP442Values 14 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value14_0
  · exact sharedDiskP442Value14_1
  · exact sharedDiskP442Value14_2
  · exact sharedDiskP442Value14_3
  · exact sharedDiskP442Value14_4
  · exact sharedDiskP442Value14_5
private theorem sharedDiskP442Value15_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 15 (0:Fin 6))=sharedDiskP442Values 15 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value15_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 15 (1:Fin 6))=sharedDiskP442Values 15 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value15_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 15 (2:Fin 6))=sharedDiskP442Values 15 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value15_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 15 (3:Fin 6))=sharedDiskP442Values 15 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value15_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 15 (4:Fin 6))=sharedDiskP442Values 15 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value15_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 15 (5:Fin 6))=sharedDiskP442Values 15 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values15_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 15 j)=sharedDiskP442Values 15 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value15_0
  · exact sharedDiskP442Value15_1
  · exact sharedDiskP442Value15_2
  · exact sharedDiskP442Value15_3
  · exact sharedDiskP442Value15_4
  · exact sharedDiskP442Value15_5
private theorem sharedDiskP442Value16_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 16 (0:Fin 6))=sharedDiskP442Values 16 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value16_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 16 (1:Fin 6))=sharedDiskP442Values 16 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value16_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 16 (2:Fin 6))=sharedDiskP442Values 16 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value16_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 16 (3:Fin 6))=sharedDiskP442Values 16 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value16_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 16 (4:Fin 6))=sharedDiskP442Values 16 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value16_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 16 (5:Fin 6))=sharedDiskP442Values 16 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values16_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 16 j)=sharedDiskP442Values 16 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value16_0
  · exact sharedDiskP442Value16_1
  · exact sharedDiskP442Value16_2
  · exact sharedDiskP442Value16_3
  · exact sharedDiskP442Value16_4
  · exact sharedDiskP442Value16_5
private theorem sharedDiskP442Value17_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 17 (0:Fin 6))=sharedDiskP442Values 17 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value17_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 17 (1:Fin 6))=sharedDiskP442Values 17 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value17_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 17 (2:Fin 6))=sharedDiskP442Values 17 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value17_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 17 (3:Fin 6))=sharedDiskP442Values 17 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value17_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 17 (4:Fin 6))=sharedDiskP442Values 17 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value17_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 17 (5:Fin 6))=sharedDiskP442Values 17 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values17_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 17 j)=sharedDiskP442Values 17 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value17_0
  · exact sharedDiskP442Value17_1
  · exact sharedDiskP442Value17_2
  · exact sharedDiskP442Value17_3
  · exact sharedDiskP442Value17_4
  · exact sharedDiskP442Value17_5
private theorem sharedDiskP442Value18_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 18 (0:Fin 6))=sharedDiskP442Values 18 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value18_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 18 (1:Fin 6))=sharedDiskP442Values 18 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value18_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 18 (2:Fin 6))=sharedDiskP442Values 18 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value18_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 18 (3:Fin 6))=sharedDiskP442Values 18 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value18_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 18 (4:Fin 6))=sharedDiskP442Values 18 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value18_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 18 (5:Fin 6))=sharedDiskP442Values 18 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values18_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 18 j)=sharedDiskP442Values 18 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value18_0
  · exact sharedDiskP442Value18_1
  · exact sharedDiskP442Value18_2
  · exact sharedDiskP442Value18_3
  · exact sharedDiskP442Value18_4
  · exact sharedDiskP442Value18_5
private theorem sharedDiskP442Value19_0 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 19 (0:Fin 6))=sharedDiskP442Values 19 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value19_1 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 19 (1:Fin 6))=sharedDiskP442Values 19 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value19_2 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 19 (2:Fin 6))=sharedDiskP442Values 19 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value19_3 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 19 (3:Fin 6))=sharedDiskP442Values 19 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value19_4 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 19 (4:Fin 6))=sharedDiskP442Values 19 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP442Value19_5 : truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 19 (5:Fin 6))=sharedDiskP442Values 19 (5:Fin 6) := by decide +kernel
theorem sharedDiskP442Values19_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points 19 j)=sharedDiskP442Values 19 j := by
  intro j
  fin_cases j
  · exact sharedDiskP442Value19_0
  · exact sharedDiskP442Value19_1
  · exact sharedDiskP442Value19_2
  · exact sharedDiskP442Value19_3
  · exact sharedDiskP442Value19_4
  · exact sharedDiskP442Value19_5
theorem sharedDiskP442Values_eq : ∀ (i : Fin 20) (j : Fin 6), truncatedChordCell 1 sharedDiskP442Params (sharedChord442Gauss6Points i j)=sharedDiskP442Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP442Values0_eq
  · exact sharedDiskP442Values1_eq
  · exact sharedDiskP442Values2_eq
  · exact sharedDiskP442Values3_eq
  · exact sharedDiskP442Values4_eq
  · exact sharedDiskP442Values5_eq
  · exact sharedDiskP442Values6_eq
  · exact sharedDiskP442Values7_eq
  · exact sharedDiskP442Values8_eq
  · exact sharedDiskP442Values9_eq
  · exact sharedDiskP442Values10_eq
  · exact sharedDiskP442Values11_eq
  · exact sharedDiskP442Values12_eq
  · exact sharedDiskP442Values13_eq
  · exact sharedDiskP442Values14_eq
  · exact sharedDiskP442Values15_eq
  · exact sharedDiskP442Values16_eq
  · exact sharedDiskP442Values17_eq
  · exact sharedDiskP442Values18_eq
  · exact sharedDiskP442Values19_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP442Box : HorizontalRectangle := ⟨(159/400),(2/5),(1110112793673/2199023255552),(1110649664585/2199023255552),(1373804484388511206155655418132579/324518553658426726783156020576256),(3849639939089418140761807111764067/324518553658426726783156020576256),(-3061741392600206847342433918655059/649037107316853453566312041152512),(4204114508978614864790024746158939/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP442Grid : CGrid := momentChordGrid sharedDiskP442Params chordGaussRule6 1 sharedChord442Bd sharedChord442M (995300573/4503599627370496)
theorem sharedDiskP442Columns : containedInReported sharedDiskP442Grid.re sharedDiskP442Box.reLo sharedDiskP442Box.reHi=true ∧ containedInReported sharedDiskP442Grid.im sharedDiskP442Box.imLo sharedDiskP442Box.imHi=true := by
  rw [sharedDiskP442Grid,momentChordGrid_eq_tabulated sharedDiskP442Params chordGaussRule6 1 sharedChord442Bd sharedChord442M (995300573/4503599627370496) sharedChord442Gauss6Points sharedChord442Gauss6Weights sharedDiskP442Values sharedChord442Gauss6Points_eq sharedChord442Gauss6Weights_eq sharedDiskP442Values_eq]
  decide +kernel
theorem sharedDiskP442Sound : sharedDiskP442Box.Sound := by
  intro t a tl tu al au
  change (((159/400):ℚ):ℝ)≤t at tl
  change t≤(((2/5):ℚ):ℝ) at tu
  change (((1110112793673/2199023255552):ℚ):ℝ)≤a at al
  change a≤(((1110649664585/2199023255552):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP442Params_ok] at ps
  have band := sharedChord442ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((159/400):ℚ)≤(159/400))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((2/5):ℚ)≤(21/40)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((1110112793673/2199023255552):ℚ)≤(1110112793673/2199023255552))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((1110649664585/2199023255552):ℚ)≤(3410681265479/6597069766656)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule6 chordGaussRule6_nodes chordGaussRule6_half_disk 1 sharedChord442Bd (by decide +kernel) (by decide +kernel) sharedChord442M (by decide +kernel) (sharedChord442Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP442Columns.1 sharedDiskP442Columns.2
def sharedDiskP442Rows : List SignRow := [positive_442.toSignRow]
theorem sharedDiskP442Rows_actual : ∀ r∈sharedDiskP442Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP442Rows.all (sharedDiskP442Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP442Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP461Params : ChordParams := ⟨⟨(-2553594301324183689965),(-1858885037832424105321),true⟩,⟨3610632031508911252244533,3822136247555748490703054,true⟩,⟨42973018636351843750044,51630813439536575596102,true⟩,⟨51207729600283872904071,60998097575100401410434,true⟩,⟨94610579471127164672469,110952859523340989289248,true⟩,⟨1203829396104281761159498,1205213757330895624622130,true⟩,⟨(-3903392459831024236296412),(-3707785869584949843904183),true⟩,⟨⟨1149363078699149665012408,1262544566857519386680603,true⟩,⟨(-47),47,true⟩⟩⟩
theorem sharedDiskP461Params_ok : chordParams (Grid.ofRats (97/200) (51/100)) (Grid.ofRats (3377117349125/6597069766656) (3398506407779/6597069766656))=sharedDiskP461Params := by decide +kernel
def sharedDiskP461Values (i : Fin 20) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-17021732000957655887950125),(-2002733195433421622499197),true⟩,⟨(-5693816875062457777700078),8875634133169092109208720,true⟩⟩
  | 0,1 => ⟨⟨(-16830342365167610148533047),(-1882171253726055390341060),true⟩,⟨(-5752777996439467802026142),8879143611838149625588027,true⟩⟩
  | 0,2 => ⟨⟨(-16673875051552724213022857),(-1791848971880701048586821),true⟩,⟨(-5795855551715342619812792),8867768385748865108792862,true⟩⟩
  | 0,3 => ⟨⟨(-16577424778302327956848382),(-1739563223320319776400549),true⟩,⟨(-5820258818163053560998516),8854977139296623488818784,true⟩⟩
  | 0,4 => ⟨⟨(-17219459406667744389008157),(-2140236132590072489124303),true⟩,⟨(-5625049980039683402823209),8849220772586970608936802,true⟩⟩
  | 0,5 => ⟨⟨(-17396834485934857917797568),(-2276089389655160489732572),true⟩,⟨(-5555983702524243415417347),8803084709157609901050819,true⟩⟩
  | 0,6 => ⟨⟨(-17532656153981656743358362),(-2388946558303982843249062),true⟩,⟨(-5498023889360703321333100),8751608205867978930656813,true⟩⟩
  | 0,7 => ⟨⟨(-17612609833146019155442754),(-2459245671498538794907180),true⟩,⟨(-5461732837283958779923779),8714130511186470047456624,true⟩⟩
  | 1,0 => ⟨⟨(-15810009367472425968674763),(-1400124871959611077169211),true⟩,⟨(-5963848588080781630317585),8626359115792271136366518,true⟩⟩
  | 1,1 => ⟨⟨(-15581608718600320566842390),(-1320678812759923702396755),true⟩,⟨(-5991695307127887758840964),8523649735331255337050941,true⟩⟩
  | 1,2 => ⟨⟨(-15396688736948903134445739),(-1262214812975720559935933),true⟩,⟨(-6009993337478028500675027),8431402202322897173494381,true⟩⟩
  | 1,3 => ⟨⟨(-15283506219926073365633335),(-1228793485195381312951353),true⟩,⟨(-6019442838309647019909907),8371328201019577967266856,true⟩⟩
  | 1,4 => ⟨⟨(-16048507967530086212102461),(-1492644265096979447276906),true⟩,⟨(-5928017784736682418728833),8718502087571401472301632,true⟩⟩
  | 1,5 => ⟨⟨(-16264598894198900300795614),(-1585990451942759805285337),true⟩,⟨(-5889010995013267859254239),8786659198736816580715044,true⟩⟩
  | 1,6 => ⟨⟨(-16431379988266845616798930),(-1664957411963882459060874),true⟩,⟨(-5854265141164293335850598),8827922401673589888579793,true⟩⟩
  | 1,7 => ⟨⟨(-16530064864933941616565045),(-1714783541199429318384594),true⟩,⟨(-5831667033714533489934708),8847186471410464436925318,true⟩⟩
  | 2,0 => ⟨⟨(-14404256135421843411215165),(-1019644426851728456819395),true⟩,⟨(-6053662638571911212031303),7829809941192717437795162,true⟩⟩
  | 2,1 => ⟨⟨(-14149544026981740923375127),(-972703268804785596689051),true⟩,⟨(-6052394088324216251520911),7653423486173978814915382,true⟩⟩
  | 2,2 => ⟨⟨(-13945523752480290984932142),(-938647421709047560379617),true⟩,⟨(-6048278537311690048087212),7507298595552488586809776,true⟩⟩
  | 2,3 => ⟨⟨(-13821593441508837017769717),(-919361508354159870118628),true⟩,⟨(-6044516115925661782863084),7416661049726722402354288,true⟩⟩
  | 2,4 => ⟨⟨(-14673555888432431441751546),(-1075279986545924772030258),true⟩,⟨(-6049931758644832757030345),8007889568481568341347047,true⟩⟩
  | 2,5 => ⟨⟨(-14920592153246323841392546),(-1132463765051225019379760),true⟩,⟨(-6041497701798850693177142),8162431556272156229359364,true⟩⟩
  | 2,6 => ⟨⟨(-15113287596838248432512545),(-1181651008493032952968205),true⟩,⟨(-6031297404709290613795902),8276269722857298373127755,true⟩⟩
  | 2,7 => ⟨⟨(-15228154321040724675359357),(-1213063860581115538180876),true⟩,⟨(-6023601766548665836966466),8341017600119086776872387,true⟩⟩
  | 3,0 => ⟨⟨(-12881550055492748566251780),(-801344060225117828719040),true⟩,⟨(-5988723635624263324286362),6693093944288964880838736,true⟩⟩
  | 3,1 => ⟨⟨(-12616172078526479009159817),(-766863846200670190395662),true⟩,⟨(-5965352386544976500270423),6480118512016870492658809,true⟩⟩
  | 3,2 => ⟨⟨(-12405671830931180013610700),(-720128157414086550953354),true⟩,⟨(-5944742140498349567424626),6309248230862895483424419,true⟩⟩
  | 3,3 => ⟨⟨(-12278668043405876668458614),(-692732407404994109048724),true⟩,⟨(-5931469956547440755967548),6205448239986821286122688,true⟩⟩
  | 3,4 => ⟨⟨(-13165387328248063574105630),(-832350537560358444769030),true⟩,⟨(-6010250305610325809511736),6917258219069123351254687,true⟩⟩
  | 3,5 => ⟨⟨(-13428856151858064136348686),(-864480380012270790628901),true⟩,⟨(-6026754219857172062371676),7121306113874756056021493,true⟩⟩
  | 3,6 => ⟨⟨(-13636521375699638788926543),(-892376382262666962759810),true⟩,⟨(-6037216258101101285018177),7278923316126664435796592,true⟩⟩
  | 3,7 => ⟨⟨(-13761240529633853822433879),(-910329586611919529818114),true⟩,⟨(-6042352567942295098768276),7372046362202184723074207,true⟩⟩
  | 4,0 => ⟨⟨(-10442593723522094027967370),(-350602639137335053340044),true⟩,⟨(-5681467259613217639119407),4675108077383615009459235,true⟩⟩
  | 4,1 => ⟨⟨(-9941297820481611287497751),(-270587848643795235284961),true⟩,⟨(-5597979462023431929330696),4256449523141122902859004,true⟩⟩
  | 4,2 => ⟨⟨(-9553245466619636030857989),(-211449636518340723610183),true⟩,⟨(-5529829402491854005328277),3934470526396683562724700,true⟩⟩
  | 4,3 => ⟨⟨(-9323389989911496192122198),(-177402665850001404514333),true⟩,⟨(-5488143505235357984540562),3744951397825770193216545,true⟩⟩
  | 4,4 => ⟨⟨(-10992614279586263841791134),(-444034257950307077992662),true⟩,⟨(-5766396992256362785257507),5136080641384700603238410,true⟩⟩
  | 4,5 => ⟨⟨(-11514613893279358679391163),(-539259964731113036145939),true⟩,⟨(-5839603256475738560122811),5572867102670050742250237,true⟩⟩
  | 4,6 => ⟨⟨(-11932734574605373942050793),(-620957168211529518538570),true⟩,⟨(-5892320687994309824035198),5920500509466558719919359,true⟩⟩
  | 4,7 => ⟨⟨(-12186247585682763259043122),(-673158797342411309115285),true⟩,⟨(-5921431431874283918242082),6129617179104015979780624,true⟩⟩
  | 5,0 => ⟨⟨(-7720658379079265467326586),48781615376578084726400,true⟩,⟨(-5174691443234346844208310),2460610509709642534685910,true⟩⟩
  | 5,1 => ⟨⟨(-7311107468176238372974966),106912500573349578576559,true⟩,⟨(-5089255137028838321396628),2146117273697099179462019,true⟩⟩
  | 5,2 => ⟨⟨(-6998771119802909695684431),151263197957891430885483,true⟩,⟨(-5022881874344531077026349),1910925852184946419103629,true⟩⟩
  | 5,3 => ⟨⟨(-6815494886899836209445877),177392746354310830399320,true⟩,⟨(-4983474180408575810228987),1774933138387763603266901,true⟩⟩
  | 5,4 => ⟨⟨(-8179005659085796131445043),(-15935568291318799408149),true⟩,⟨(-5267963677011127993891770),2819975884838453683167881,true⟩⟩
  | 5,5 => ⟨⟨(-8623980171278642252867127),(-77419330481158637166678),true⟩,⟨(-5355891001965755631808684),3175428007554301839713541,true⟩⟩
  | 5,6 => ⟨⟨(-8988342709977432140948272),(-128897105575732103295985),true⟩,⟨(-5425757933380274394845345),3470652818770227615013190,true⟩⟩
  | 5,7 => ⟨⟨(-9213052084643760482519640),(-161290315319715865291131),true⟩,⟨(-5467805207814809089366457),3654347341668557350408828,true⟩⟩
  | 6,0 => ⟨⟨(-4547179514271426356142736),529698529182415641174973,true⟩,⟨(-4474456648614189448219742),434543567475692670405909,true⟩⟩
  | 6,1 => ⟨⟨(-4027659251314859063594051),624617808446987466295910,true⟩,⟨(-4351650955270640369968697),163568420671208730795608,true⟩⟩
  | 6,2 => ⟨⟨(-3652157822481001875465849),709458170486834214889981,true⟩,⟨(-4260230598821128733662361),(-11814094984754982107639),true⟩⟩
  | 6,3 => ⟨⟨(-3450665411401679697905925),771457294856010349904249,true⟩,⟨(-4207356498121330755317169),(-72840344396162460680354),true⟩⟩
  | 6,4 => ⟨⟨(-5161031020172802648841098),426469040660932752648519,true⟩,⟨(-4616387788721933100625425),770949567949113048139679,true⟩⟩
  | 6,5 => ⟨⟨(-5792163676329923474255865),327723414639973007503836,true⟩,⟨(-4759018133519372666797551),1132472969937183174476848,true⟩⟩
  | 6,6 => ⟨⟨(-6336115843716922651314553),246691078763303485189311,true⟩,⟨(-4879280333534943403427939),1454862053688074915960150,true⟩⟩
  | 6,7 => ⟨⟨(-6684505237877572423510752),196147265490268192890390,true⟩,⟨(-4955108563956068040798321),1678696035763406694045010,true⟩⟩
  | 7,0 => ⟨⟨(-2160308834627128289866244),1223437981113112672330039,true⟩,⟨(-3855546097348617669057986),(-414485924376207474877876),true⟩⟩
  | 7,1 => ⟨⟨(-1855005588816351889223811),1347074334064890213224374,true⟩,⟨(-3767634725503079322590794),(-480317490182372424927580),true⟩⟩
  | 7,2 => ⟨⟨(-1637639172064134216920731),1444276229909865551215666,true⟩,⟨(-3702333454919042532461051),(-512710701866824424786325),true⟩⟩
  | 7,3 => ⟨⟨(-1512753192152064595726267),1502590830010366076569044,true⟩,⟨(-3664015221283848058024894),(-528715851847013359166992),true⟩⟩
  | 7,4 => ⟨⟨(-2511954185735840600705248),1089611091847205462803273,true⟩,⟨(-3954211719892137342305969),(-330893665793619584973406),true⟩⟩
  | 7,5 => ⟨⟨(-2865478442566241004318768),963584299474696743573665,true⟩,⟨(-4051070804000307922940778),(-239239295349223102956529),true⟩⟩
  | 7,6 => ⟨⟨(-3165404757856378658670031),862731261077139730282370,true⟩,⟨(-4131726009364955753587767),(-156081821913394390690755),true⟩⟩
  | 7,7 => ⟨⟨(-3355656225097630605106157),801383559309651975741956,true⟩,⟨(-4182273373921256732582059),(-100989812139657486951543),true⟩⟩
  | 8,0 => ⟨⟨830113859989143907897873,3049241042833885691907372,true⟩,⟨(-2798634493118907221204773),(-544462726458473180743243),true⟩⟩
  | 8,1 => ⟨⟨1220350812594913176640453,3423457741257520790725426,true⟩,⟨(-2609707943690163680903935),(-471833574592800966510873),true⟩⟩
  | 8,2 => ⟨⟨1498917087069965354531973,3695664455022281670276157,true⟩,⟨(-2464133784406972009120233),(-406513040476389883598953),true⟩⟩
  | 8,3 => ⟨⟨1655226515921159474047941,3849474175245491378018538,true⟩,⟨(-2378446273000911153581210),(-365301677248803473281141),true⟩⟩
  | 8,4 => ⟨⟨354912566262138166633817,2610918888431152378574888,true⟩,⟨(-3005346651783043175093150),(-600049890555744411436703),true⟩⟩
  | 8,5 => ⟨⟨(-267327895551864523612450),2170316314765736677118741,true⟩,⟨(-3247218990693502512630038),(-615524669496564040770007),true⟩⟩
  | 8,6 => ⟨⟨(-917128389839213869483172),1802090832611784347302308,true⟩,⟨(-3473292656451091020056704),(-587566381639540995556414),true⟩⟩
  | 8,7 => ⟨⟨(-1366152931053005898828969),1572993288480672594061299,true⟩,⟨(-3618343746406438766822913),(-545942503657128303530238),true⟩⟩
  | 9,0 => ⟨⟨3174461342417843110864464,5287976013704731237820362,true⟩,⟨(-1349255201237434944849942),198628099638054552839463,true⟩⟩
  | 9,1 => ⟨⟨3404740123711027644324902,5465075014555573872952077,true⟩,⟨(-1134739707635796880103182),316520028715607104833868,true⟩⟩
  | 9,2 => ⟨⟨3541009425738050837324220,5550944733923864430796063,true⟩,⟨(-986080593367980374823805),393738951192345003956243,true⟩⟩
  | 9,3 => ⟨⟨3605951855124762867515934,5582540428713328924588136,true⟩,⟨(-904753903988594607781748),433856822549201116002602,true⟩⟩
  | 9,4 => ⟨⟨2842211474876529836663748,4997472659451347483199168,true⟩,⟨(-1616027891089117226522042),45733725613280390318009,true⟩⟩
  | 9,5 => ⟨⟨2437792338231065308373542,4616724864886657613184273,true⟩,⟨(-1901692490653488604121533),(-114180480774820411213610),true⟩⟩
  | 9,6 => ⟨⟨2040866056476614158995982,4229624019457456751588463,true⟩,⟨(-2154087681683799022516551),(-250556121246475291634646),true⟩⟩
  | 9,7 => ⟨⟨1763806800512688986949120,3956538820741736056778363,true⟩,⟨(-2317181120608420630572732),(-334835911385972847812665),true⟩⟩
  | 10,0 => ⟨⟨3637183464029036731097648,5029674160958163810119726,true⟩,⟨(-230473873775124635362058),631892686110875523148088,true⟩⟩
  | 10,1 => ⟨⟨3487688172340130505745171,4724219823905355562010161,true⟩,⟨(-155570304863096439686078),609841204248599068235462,true⟩⟩
  | 10,2 => ⟨⟨3355520810264967192566830,4479694354867220341276261,true⟩,⟨(-118142479136597345845903),581279759159516330491411,true⟩⟩
  | 10,3 => ⟨⟨3273974676870471629918917,4335761146252280497249965,true⟩,⟨(-103303396972524992795420),560764786437991149023005,true⟩⟩
  | 10,4 => ⟨⟨3751661885239364466174319,5324334995678910962158685,true⟩,⟨(-355251257872964216663732),628966020252478148213338,true⟩⟩
  | 10,5 => ⟨⟨3782521688155229766878071,5527537460564017582743343,true⟩,⟨(-526723632466494277951512),588830348368531835222916,true⟩⟩
  | 10,6 => ⟨⟨3726461316044528330100294,5603441604062500330621149,true⟩,⟨(-711804287970828825623269),520880479637946538478303,true⟩⟩
  | 10,7 => ⟨⟨3645812157949289383881839,5596937772241864636566344,true⟩,⟨(-849262236257600823832796),460178068649762911512930,true⟩⟩
  | 11,0 => ⟨⟨2620780763564797814086321,3694383678666966398424988,true⟩,⟨(-216290557224527649072275),446238014694866048133045,true⟩⟩
  | 11,1 => ⟨⟨2512589335079771518887375,3634458129848115758954170,true⟩,⟨(-300398559866531557822097),402529966122126247292219,true⟩⟩
  | 11,2 => ⟨⟨2461932736541283199911014,3649213106661757692726390,true⟩,⟨(-397881865204642138239389),361648649185100281465868,true⟩⟩
  | 11,3 => ⟨⟨2449530025163759179776369,3693641347383720302219587,true⟩,⟨(-477211619199265698976959),332409601045290231551948,true⟩⟩
  | 11,4 => ⟨⟨2781098329642577082695259,3829809479595964352960318,true⟩,⟨(-156593305538079955706391),487121005888047670859556,true⟩⟩
  | 11,5 => ⟨⟨2963447839855493104664727,4004892378328016870901594,true⟩,⟨(-121234130373463802548041),520279772433499709109986,true⟩⟩
  | 11,6 => ⟨⟨3125200478067000154554957,4168158570675504510317328,true⟩,⟨(-105308996141263619649806),542270978531367647935597,true⟩⟩
  | 11,7 => ⟨⟨3228128907122432462982109,4274233527583319958814950,true⟩,⟨(-100916711098315668893240),553088766686033863938402,true⟩⟩
  | 12,0 => ⟨⟨2577340605336124380381661,4294799882318155146100047,true⟩,⟨(-1117090265233521635463499),132638006449847354479805,true⟩⟩
  | 12,1 => ⟨⟨2672888974402284704355642,4665190389155880473801237,true⟩,⟨(-1501863584635345473526879),18855887651121747464179,true⟩⟩
  | 12,2 => ⟨⟨2765093422711586353573252,5072630645219644227969346,true⟩,⟨(-1958433901948340410381903),(-109659297854612622958690),true⟩⟩
  | 12,3 => ⟨⟨2822558981493683240288299,5383402725797479717782979,true⟩,⟨(-2335715484139077767501259),(-214697082796579110696082),true⟩⟩
  | 12,4 => ⟨⟨2506030158131064892870800,4023233221193618465922229,true⟩,⟨(-844623509225838561588650),214391707837537513901822,true⟩⟩
  | 12,5 => ⟨⟨2466658258291820203751311,3852676701999754206644761,true⟩,⟨(-668693649653058655161076),268857840256815247366047,true⟩⟩
  | 12,6 => ⟨⟨2451726620036441862802960,3759617611218322879186327,true⟩,⟨(-563854764986979351349032),302790568430575288564663,true⟩⟩
  | 12,7 => ⟨⟨2448898854144660648372510,3717985005071915601051366,true⟩,⟨(-511335193031612826420483),320518944396209230944361,true⟩⟩
  | 13,0 => ⟨⟨2808018381451424030536239,7249690853740527800372786,true⟩,⟨(-5325337407271570676299527),(-1021657344401600455269819),true⟩⟩
  | 13,1 => ⟨⟨2537651073928201754198294,7965678389002052245613287,true⟩,⟨(-6968072002133213610894477),(-1437748255660298682417641),true⟩⟩
  | 13,2 => ⟨⟨2086164588859792001411209,8560621159561147722787977,true⟩,⟨(-8735495126034183470148281),(-1860083938245813020884780),true⟩⟩
  | 13,3 => ⟨⟨1650388210035368096775034,8900870237184522648816377,true⟩,⟨(-10053430779921143341483337),(-2156853912425963040025544),true⟩⟩
  | 13,4 => ⟨⟨2900936629539046587787512,6579474294706342384462284,true⟩,⟨(-4081873875400012306350017),(-692852293894827959728404),true⟩⟩
  | 13,5 => ⟨⟨2898449709652990998145791,6054194557236710800828437,true⟩,⟨(-3251170545630085045718179),(-467384903348454700177677),true⟩⟩
  | 13,6 => ⟨⟨2867404466745543617277301,5700581093006862573718338,true⟩,⟨(-2750181743232957949149489),(-329552438176469350672868),true⟩⟩
  | 13,7 => ⟨⟨2842400895409046842812604,5511082507089883768516245,true⟩,⟨(-2498813990305022874276908),(-259970922124640952923527),true⟩⟩
  | 14,0 => ⟨⟨40030960673581708257446,9397099231642136415057700,true⟩,⟨(-13488867367825246769907177),(-2840559789266411823659184),true⟩⟩
  | 14,1 => ⟨⟨(-776299433114871184651827),9437071194404465637791637,true⟩,⟨(-14598853768139001824343199),(-3019323580903971016929692),true⟩⟩
  | 14,2 => ⟨⟨(-1526467017785162698004550),9429088650343191489382329,true⟩,⟨(-15527537234978185117005719),(-3157167928520292838669037),true⟩⟩
  | 14,3 => ⟨⟨(-2026645348856353502670234),9404128125823326926733501,true⟩,⟨(-16106801868895745333497533),(-3237402638153272161668066),true⟩⟩
  | 14,4 => ⟨⟨660300433353339333957284,9305100106838859180146397,true⟩,⟨(-12419385592028108200750316),(-2647700984624440296086116),true⟩⟩
  | 14,5 => ⟨⟨1062820906618844864576146,9184474203157674998939957,true⟩,⟨(-11533229600522978263982541),(-2470449494144717070570350),true⟩⟩
  | 14,6 => ⟨⟨1337369337376328186413316,9070856968331695278108950,true⟩,⟨(-10874237689207312194681941),(-2333443140641935493653780),true⟩⟩
  | 14,7 => ⟨⟨1485937154344800542584766,8996269408843759255816827,true⟩,⟨(-10495066280703763917451241),(-2252673350635157562508757),true⟩⟩
  | 15,0 => ⟨⟨(-7073475536495507860203062),8546679151045812613422778,true⟩,⟨(-20650851340576721723643845),(-3673199635253759295434223),true⟩⟩
  | 15,1 => ⟨⟨(-8927381933329631666546514),8027508252452109524899093,true⟩,⟨(-21854215481615980029985811),(-3703363644622472020645564),true⟩⟩
  | 15,2 => ⟨⟨(-10525637720969008137587523),7508459071675124398164167,true⟩,⟨(-22718660237147018602783034),(-3683105416900169523582980),true⟩⟩
  | 15,3 => ⟨⟨(-11574915636992864984449401),7146778555062598835331337,true⟩,⟨(-23186314528645880469089437),(-3648663435612243929572016),true⟩⟩
  | 15,4 => ⟨⟨(-5302196685831796587924563),8951397603091279137859349,true⟩,⟨(-19286877411054468832096792),(-3585609305123721548524162),true⟩⟩
  | 15,5 => ⟨⟨(-3853971605904364906223728),9205592956022670771090313,true⟩,⟨(-17998067214168484990606867),(-3465247787585283219586117),true⟩⟩
  | 15,6 => ⟨⟨(-2840314666056151882967848),9334822410156332308022601,true⟩,⟨(-16989505580549797690823815),(-3350579853445947296542835),true⟩⟩
  | 15,7 => ⟨⟨(-2283015264603801900700540),9385927385635582894860187,true⟩,⟨(-16392535105054533045952240),(-3275272454118998141208957),true⟩⟩
  | 16,0 => ⟨⟨(-16232949915018649797091858),5400986946204041253171384,true⟩,⟨(-24419576017931828670715315),(-3176031141549907624183441),true⟩⟩
  | 16,1 => ⟨⟨(-17524878374714713549276072),4835463425525327062350418,true⟩,⟨(-24541743886977255577248141),(-2803392783695476675489927),true⟩⟩
  | 16,2 => ⟨⟨(-18538238918562367622628417),4362010341651232465002243,true⟩,⟨(-24558616304867910568046709),(-2478997895626491121242559),true⟩⟩
  | 16,3 => ⟨⟨(-19140994643635271565891179),4066355253361153259206383,true⟩,⟨(-24531961601065731128626482),(-2271264743107854643914481),true⟩⟩
  | 16,4 => ⟨⟨(-14848636198989505579721631),5964971635745276601761551,true⟩,⟨(-24176233227246444350895260),(-3455574120538261976734535),true⟩⟩
  | 16,5 => ⟨⟨(-13574354502223671804691838),6449629907079613205498652,true⟩,⟨(-23858061713785432447300602),(-3547047842777213239560091),true⟩⟩
  | 16,6 => ⟨⟨(-12583797654547159323830284),6804474612848814074456814,true⟩,⟨(-23551115224904105396912623),(-3603707860466988459212981),true⟩⟩
  | 16,7 => ⟨⟨(-11996664924666813026890389),7006008585760573044612531,true⟩,⟨(-23345169991712807242645220),(-3631430767819627072249401),true⟩⟩
  | 17,0 => ⟨⟨(-23188400563149381182207855),2017911616504403329739148,true⟩,⟨(-23343706205347085568967034),(-479083378128581392331382),true⟩⟩
  | 17,1 => ⟨⟨(-24087168485174478945141920),1529910796799614580994979,true⟩,⟨(-22674747511684791250568040),78741124097399230425416,true⟩⟩
  | 17,2 => ⟨⟨(-24697459172027374751951746),1143735047896219501913259,true⟩,⟨(-22037361028374750112565284),547536117060099035061773,true⟩⟩
  | 17,3 => ⟨⟨(-25044940682008724619298184),912311769520960341014204,true⟩,⟨(-21610860236952960327148025),901556089603238637602769,true⟩⟩
  | 17,4 => ⟨⟨(-22089482337727773671769268),2536177635347067258096025,true⟩,⟨(-23893500292415342530345882),(-1053968432335413004398013),true⟩⟩
  | 17,5 => ⟨⟨(-20963899839484560765530716),3095241847387913078328299,true⟩,⟨(-24253453122636934328054734),(-1564285295764126205152204),true⟩⟩
  | 17,6 => ⟨⟨(-20018503568083187120378932),3614671546220412777219719,true⟩,⟨(-24438215499054125020169181),(-1946899290545217611191524),true⟩⟩
  | 17,7 => ⟨⟨(-19430356373162829379629724),3920337813145757234769299,true⟩,⟨(-24508581637327871741975744),(-2167303258201270182584879),true⟩⟩
  | 18,0 => ⟨⟨(-26263298722041593311040393),(-671447470550300173944097),true⟩,⟨(-17450344667191461229818541),4127582246733398865784211,true⟩⟩
  | 18,1 => ⟨⟨(-26095937582733079183085950),(-1046708891365363449755171),true⟩,⟨(-16035859210534003709636516),5154716174811135647616760,true⟩⟩
  | 18,2 => ⟨⟨(-25800084333377393717538571),(-1320705438888060209450777),true⟩,⟨(-14863415263032305008791778),5913381698645453436253852,true⟩⟩
  | 18,3 => ⟨⟨(-25553027851281181242064616),(-1475109776570574409975759),true⟩,⟨(-14139713049233135045705841),6342997108994921817494132,true⟩⟩
  | 18,4 => ⟨⟨(-26187693527939636541442006),(-237333715886715930587838),true⟩,⟨(-18862383768768240257099186),2961954703659393039641951,true⟩⟩
  | 18,5 => ⟨⟨(-25886447679173891387386396),201530549174562402893729,true⟩,⟨(-20060277321975890451723671),2083364865812676527723999,true⟩⟩
  | 18,6 => ⟨⟨(-25498010480591069891129691),572532579341571696614880,true⟩,⟨(-20917374623516185124030862),1462587539386679887588288,true⟩⟩
  | 18,7 => ⟨⟨(-25203435988646127844474014),800677397186723740711959,true⟩,⟨(-21392257037886320759778372),1085016522946052442106410,true⟩⟩
  | 19,0 => ⟨⟨(-22257456579943193241002685),(-2209514762000440735911878),true⟩,⟨(-8662309736459987798098135),8706265065447954188263966,true⟩⟩
  | 19,1 => ⟨⟨(-20972650177445036956785158),(-2157580910864119969255761),true⟩,⟨(-7211521078741349666419593),9065149701121330435984237,true⟩⟩
  | 19,2 => ⟨⟨(-19960049805243479108490386),(-2107263102692115339603836),true⟩,⟨(-6117133890974388114555570),9253025018952817133844703,true⟩⟩
  | 19,3 => ⟨⟨(-19369955350309752862690367),(-2073840443213337702570729),true⟩,⟨(-5484818353885921997554889),9326130206051936452302071,true⟩⟩
  | 19,4 => ⟨⟨(-23485161627416741230335129),(-2135109993662232902034924),true⟩,⟨(-10281345553714557123750310),8169523617394666439663690,true⟩⟩
  | 19,5 => ⟨⟨(-24458099513404970220043528),(-1902330433797982355452597),true⟩,⟨(-11823486705799797361466726),7531422629792851622664874,true⟩⟩
  | 19,6 => ⟨⟨(-25093938871719165864615013),(-1688312207289584465681661),true⟩,⟨(-13049751473228385094176437),6937008635175046032652124,true⟩⟩
  | 19,7 => ⟨⟨(-25414941241545928952684595),(-1546940843966888616347518),true⟩,⟨(-13785155635885702875239500),6543122077993130090211559,true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP461Value0_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 0 (0:Fin 8))=sharedDiskP461Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value0_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 0 (1:Fin 8))=sharedDiskP461Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value0_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 0 (2:Fin 8))=sharedDiskP461Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value0_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 0 (3:Fin 8))=sharedDiskP461Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value0_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 0 (4:Fin 8))=sharedDiskP461Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value0_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 0 (5:Fin 8))=sharedDiskP461Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value0_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 0 (6:Fin 8))=sharedDiskP461Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value0_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 0 (7:Fin 8))=sharedDiskP461Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values0_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 0 j)=sharedDiskP461Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value0_0
  · exact sharedDiskP461Value0_1
  · exact sharedDiskP461Value0_2
  · exact sharedDiskP461Value0_3
  · exact sharedDiskP461Value0_4
  · exact sharedDiskP461Value0_5
  · exact sharedDiskP461Value0_6
  · exact sharedDiskP461Value0_7
private theorem sharedDiskP461Value1_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 1 (0:Fin 8))=sharedDiskP461Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value1_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 1 (1:Fin 8))=sharedDiskP461Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value1_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 1 (2:Fin 8))=sharedDiskP461Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value1_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 1 (3:Fin 8))=sharedDiskP461Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value1_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 1 (4:Fin 8))=sharedDiskP461Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value1_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 1 (5:Fin 8))=sharedDiskP461Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value1_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 1 (6:Fin 8))=sharedDiskP461Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value1_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 1 (7:Fin 8))=sharedDiskP461Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values1_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 1 j)=sharedDiskP461Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value1_0
  · exact sharedDiskP461Value1_1
  · exact sharedDiskP461Value1_2
  · exact sharedDiskP461Value1_3
  · exact sharedDiskP461Value1_4
  · exact sharedDiskP461Value1_5
  · exact sharedDiskP461Value1_6
  · exact sharedDiskP461Value1_7
private theorem sharedDiskP461Value2_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 2 (0:Fin 8))=sharedDiskP461Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value2_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 2 (1:Fin 8))=sharedDiskP461Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value2_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 2 (2:Fin 8))=sharedDiskP461Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value2_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 2 (3:Fin 8))=sharedDiskP461Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value2_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 2 (4:Fin 8))=sharedDiskP461Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value2_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 2 (5:Fin 8))=sharedDiskP461Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value2_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 2 (6:Fin 8))=sharedDiskP461Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value2_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 2 (7:Fin 8))=sharedDiskP461Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values2_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 2 j)=sharedDiskP461Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value2_0
  · exact sharedDiskP461Value2_1
  · exact sharedDiskP461Value2_2
  · exact sharedDiskP461Value2_3
  · exact sharedDiskP461Value2_4
  · exact sharedDiskP461Value2_5
  · exact sharedDiskP461Value2_6
  · exact sharedDiskP461Value2_7
private theorem sharedDiskP461Value3_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 3 (0:Fin 8))=sharedDiskP461Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value3_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 3 (1:Fin 8))=sharedDiskP461Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value3_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 3 (2:Fin 8))=sharedDiskP461Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value3_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 3 (3:Fin 8))=sharedDiskP461Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value3_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 3 (4:Fin 8))=sharedDiskP461Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value3_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 3 (5:Fin 8))=sharedDiskP461Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value3_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 3 (6:Fin 8))=sharedDiskP461Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value3_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 3 (7:Fin 8))=sharedDiskP461Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values3_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 3 j)=sharedDiskP461Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value3_0
  · exact sharedDiskP461Value3_1
  · exact sharedDiskP461Value3_2
  · exact sharedDiskP461Value3_3
  · exact sharedDiskP461Value3_4
  · exact sharedDiskP461Value3_5
  · exact sharedDiskP461Value3_6
  · exact sharedDiskP461Value3_7
private theorem sharedDiskP461Value4_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 4 (0:Fin 8))=sharedDiskP461Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value4_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 4 (1:Fin 8))=sharedDiskP461Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value4_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 4 (2:Fin 8))=sharedDiskP461Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value4_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 4 (3:Fin 8))=sharedDiskP461Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value4_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 4 (4:Fin 8))=sharedDiskP461Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value4_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 4 (5:Fin 8))=sharedDiskP461Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value4_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 4 (6:Fin 8))=sharedDiskP461Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value4_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 4 (7:Fin 8))=sharedDiskP461Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values4_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 4 j)=sharedDiskP461Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value4_0
  · exact sharedDiskP461Value4_1
  · exact sharedDiskP461Value4_2
  · exact sharedDiskP461Value4_3
  · exact sharedDiskP461Value4_4
  · exact sharedDiskP461Value4_5
  · exact sharedDiskP461Value4_6
  · exact sharedDiskP461Value4_7
private theorem sharedDiskP461Value5_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 5 (0:Fin 8))=sharedDiskP461Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value5_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 5 (1:Fin 8))=sharedDiskP461Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value5_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 5 (2:Fin 8))=sharedDiskP461Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value5_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 5 (3:Fin 8))=sharedDiskP461Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value5_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 5 (4:Fin 8))=sharedDiskP461Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value5_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 5 (5:Fin 8))=sharedDiskP461Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value5_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 5 (6:Fin 8))=sharedDiskP461Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value5_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 5 (7:Fin 8))=sharedDiskP461Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values5_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 5 j)=sharedDiskP461Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value5_0
  · exact sharedDiskP461Value5_1
  · exact sharedDiskP461Value5_2
  · exact sharedDiskP461Value5_3
  · exact sharedDiskP461Value5_4
  · exact sharedDiskP461Value5_5
  · exact sharedDiskP461Value5_6
  · exact sharedDiskP461Value5_7
private theorem sharedDiskP461Value6_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 6 (0:Fin 8))=sharedDiskP461Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value6_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 6 (1:Fin 8))=sharedDiskP461Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value6_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 6 (2:Fin 8))=sharedDiskP461Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value6_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 6 (3:Fin 8))=sharedDiskP461Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value6_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 6 (4:Fin 8))=sharedDiskP461Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value6_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 6 (5:Fin 8))=sharedDiskP461Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value6_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 6 (6:Fin 8))=sharedDiskP461Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value6_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 6 (7:Fin 8))=sharedDiskP461Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values6_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 6 j)=sharedDiskP461Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value6_0
  · exact sharedDiskP461Value6_1
  · exact sharedDiskP461Value6_2
  · exact sharedDiskP461Value6_3
  · exact sharedDiskP461Value6_4
  · exact sharedDiskP461Value6_5
  · exact sharedDiskP461Value6_6
  · exact sharedDiskP461Value6_7
private theorem sharedDiskP461Value7_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 7 (0:Fin 8))=sharedDiskP461Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value7_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 7 (1:Fin 8))=sharedDiskP461Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value7_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 7 (2:Fin 8))=sharedDiskP461Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value7_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 7 (3:Fin 8))=sharedDiskP461Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value7_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 7 (4:Fin 8))=sharedDiskP461Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value7_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 7 (5:Fin 8))=sharedDiskP461Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value7_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 7 (6:Fin 8))=sharedDiskP461Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value7_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 7 (7:Fin 8))=sharedDiskP461Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values7_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 7 j)=sharedDiskP461Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value7_0
  · exact sharedDiskP461Value7_1
  · exact sharedDiskP461Value7_2
  · exact sharedDiskP461Value7_3
  · exact sharedDiskP461Value7_4
  · exact sharedDiskP461Value7_5
  · exact sharedDiskP461Value7_6
  · exact sharedDiskP461Value7_7
private theorem sharedDiskP461Value8_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 8 (0:Fin 8))=sharedDiskP461Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value8_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 8 (1:Fin 8))=sharedDiskP461Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value8_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 8 (2:Fin 8))=sharedDiskP461Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value8_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 8 (3:Fin 8))=sharedDiskP461Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value8_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 8 (4:Fin 8))=sharedDiskP461Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value8_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 8 (5:Fin 8))=sharedDiskP461Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value8_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 8 (6:Fin 8))=sharedDiskP461Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value8_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 8 (7:Fin 8))=sharedDiskP461Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values8_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 8 j)=sharedDiskP461Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value8_0
  · exact sharedDiskP461Value8_1
  · exact sharedDiskP461Value8_2
  · exact sharedDiskP461Value8_3
  · exact sharedDiskP461Value8_4
  · exact sharedDiskP461Value8_5
  · exact sharedDiskP461Value8_6
  · exact sharedDiskP461Value8_7
private theorem sharedDiskP461Value9_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 9 (0:Fin 8))=sharedDiskP461Values 9 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value9_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 9 (1:Fin 8))=sharedDiskP461Values 9 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value9_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 9 (2:Fin 8))=sharedDiskP461Values 9 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value9_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 9 (3:Fin 8))=sharedDiskP461Values 9 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value9_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 9 (4:Fin 8))=sharedDiskP461Values 9 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value9_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 9 (5:Fin 8))=sharedDiskP461Values 9 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value9_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 9 (6:Fin 8))=sharedDiskP461Values 9 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value9_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 9 (7:Fin 8))=sharedDiskP461Values 9 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values9_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 9 j)=sharedDiskP461Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value9_0
  · exact sharedDiskP461Value9_1
  · exact sharedDiskP461Value9_2
  · exact sharedDiskP461Value9_3
  · exact sharedDiskP461Value9_4
  · exact sharedDiskP461Value9_5
  · exact sharedDiskP461Value9_6
  · exact sharedDiskP461Value9_7
private theorem sharedDiskP461Value10_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 10 (0:Fin 8))=sharedDiskP461Values 10 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value10_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 10 (1:Fin 8))=sharedDiskP461Values 10 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value10_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 10 (2:Fin 8))=sharedDiskP461Values 10 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value10_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 10 (3:Fin 8))=sharedDiskP461Values 10 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value10_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 10 (4:Fin 8))=sharedDiskP461Values 10 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value10_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 10 (5:Fin 8))=sharedDiskP461Values 10 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value10_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 10 (6:Fin 8))=sharedDiskP461Values 10 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value10_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 10 (7:Fin 8))=sharedDiskP461Values 10 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values10_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 10 j)=sharedDiskP461Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value10_0
  · exact sharedDiskP461Value10_1
  · exact sharedDiskP461Value10_2
  · exact sharedDiskP461Value10_3
  · exact sharedDiskP461Value10_4
  · exact sharedDiskP461Value10_5
  · exact sharedDiskP461Value10_6
  · exact sharedDiskP461Value10_7
private theorem sharedDiskP461Value11_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 11 (0:Fin 8))=sharedDiskP461Values 11 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value11_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 11 (1:Fin 8))=sharedDiskP461Values 11 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value11_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 11 (2:Fin 8))=sharedDiskP461Values 11 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value11_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 11 (3:Fin 8))=sharedDiskP461Values 11 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value11_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 11 (4:Fin 8))=sharedDiskP461Values 11 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value11_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 11 (5:Fin 8))=sharedDiskP461Values 11 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value11_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 11 (6:Fin 8))=sharedDiskP461Values 11 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value11_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 11 (7:Fin 8))=sharedDiskP461Values 11 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values11_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 11 j)=sharedDiskP461Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value11_0
  · exact sharedDiskP461Value11_1
  · exact sharedDiskP461Value11_2
  · exact sharedDiskP461Value11_3
  · exact sharedDiskP461Value11_4
  · exact sharedDiskP461Value11_5
  · exact sharedDiskP461Value11_6
  · exact sharedDiskP461Value11_7
private theorem sharedDiskP461Value12_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 12 (0:Fin 8))=sharedDiskP461Values 12 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value12_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 12 (1:Fin 8))=sharedDiskP461Values 12 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value12_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 12 (2:Fin 8))=sharedDiskP461Values 12 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value12_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 12 (3:Fin 8))=sharedDiskP461Values 12 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value12_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 12 (4:Fin 8))=sharedDiskP461Values 12 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value12_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 12 (5:Fin 8))=sharedDiskP461Values 12 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value12_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 12 (6:Fin 8))=sharedDiskP461Values 12 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value12_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 12 (7:Fin 8))=sharedDiskP461Values 12 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values12_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 12 j)=sharedDiskP461Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value12_0
  · exact sharedDiskP461Value12_1
  · exact sharedDiskP461Value12_2
  · exact sharedDiskP461Value12_3
  · exact sharedDiskP461Value12_4
  · exact sharedDiskP461Value12_5
  · exact sharedDiskP461Value12_6
  · exact sharedDiskP461Value12_7
private theorem sharedDiskP461Value13_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 13 (0:Fin 8))=sharedDiskP461Values 13 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value13_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 13 (1:Fin 8))=sharedDiskP461Values 13 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value13_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 13 (2:Fin 8))=sharedDiskP461Values 13 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value13_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 13 (3:Fin 8))=sharedDiskP461Values 13 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value13_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 13 (4:Fin 8))=sharedDiskP461Values 13 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value13_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 13 (5:Fin 8))=sharedDiskP461Values 13 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value13_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 13 (6:Fin 8))=sharedDiskP461Values 13 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value13_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 13 (7:Fin 8))=sharedDiskP461Values 13 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values13_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 13 j)=sharedDiskP461Values 13 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value13_0
  · exact sharedDiskP461Value13_1
  · exact sharedDiskP461Value13_2
  · exact sharedDiskP461Value13_3
  · exact sharedDiskP461Value13_4
  · exact sharedDiskP461Value13_5
  · exact sharedDiskP461Value13_6
  · exact sharedDiskP461Value13_7
private theorem sharedDiskP461Value14_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 14 (0:Fin 8))=sharedDiskP461Values 14 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value14_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 14 (1:Fin 8))=sharedDiskP461Values 14 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value14_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 14 (2:Fin 8))=sharedDiskP461Values 14 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value14_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 14 (3:Fin 8))=sharedDiskP461Values 14 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value14_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 14 (4:Fin 8))=sharedDiskP461Values 14 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value14_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 14 (5:Fin 8))=sharedDiskP461Values 14 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value14_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 14 (6:Fin 8))=sharedDiskP461Values 14 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value14_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 14 (7:Fin 8))=sharedDiskP461Values 14 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values14_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 14 j)=sharedDiskP461Values 14 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value14_0
  · exact sharedDiskP461Value14_1
  · exact sharedDiskP461Value14_2
  · exact sharedDiskP461Value14_3
  · exact sharedDiskP461Value14_4
  · exact sharedDiskP461Value14_5
  · exact sharedDiskP461Value14_6
  · exact sharedDiskP461Value14_7
private theorem sharedDiskP461Value15_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 15 (0:Fin 8))=sharedDiskP461Values 15 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value15_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 15 (1:Fin 8))=sharedDiskP461Values 15 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value15_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 15 (2:Fin 8))=sharedDiskP461Values 15 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value15_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 15 (3:Fin 8))=sharedDiskP461Values 15 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value15_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 15 (4:Fin 8))=sharedDiskP461Values 15 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value15_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 15 (5:Fin 8))=sharedDiskP461Values 15 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value15_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 15 (6:Fin 8))=sharedDiskP461Values 15 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value15_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 15 (7:Fin 8))=sharedDiskP461Values 15 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values15_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 15 j)=sharedDiskP461Values 15 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value15_0
  · exact sharedDiskP461Value15_1
  · exact sharedDiskP461Value15_2
  · exact sharedDiskP461Value15_3
  · exact sharedDiskP461Value15_4
  · exact sharedDiskP461Value15_5
  · exact sharedDiskP461Value15_6
  · exact sharedDiskP461Value15_7
private theorem sharedDiskP461Value16_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 16 (0:Fin 8))=sharedDiskP461Values 16 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value16_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 16 (1:Fin 8))=sharedDiskP461Values 16 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value16_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 16 (2:Fin 8))=sharedDiskP461Values 16 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value16_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 16 (3:Fin 8))=sharedDiskP461Values 16 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value16_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 16 (4:Fin 8))=sharedDiskP461Values 16 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value16_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 16 (5:Fin 8))=sharedDiskP461Values 16 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value16_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 16 (6:Fin 8))=sharedDiskP461Values 16 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value16_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 16 (7:Fin 8))=sharedDiskP461Values 16 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values16_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 16 j)=sharedDiskP461Values 16 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value16_0
  · exact sharedDiskP461Value16_1
  · exact sharedDiskP461Value16_2
  · exact sharedDiskP461Value16_3
  · exact sharedDiskP461Value16_4
  · exact sharedDiskP461Value16_5
  · exact sharedDiskP461Value16_6
  · exact sharedDiskP461Value16_7
private theorem sharedDiskP461Value17_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 17 (0:Fin 8))=sharedDiskP461Values 17 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value17_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 17 (1:Fin 8))=sharedDiskP461Values 17 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value17_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 17 (2:Fin 8))=sharedDiskP461Values 17 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value17_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 17 (3:Fin 8))=sharedDiskP461Values 17 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value17_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 17 (4:Fin 8))=sharedDiskP461Values 17 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value17_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 17 (5:Fin 8))=sharedDiskP461Values 17 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value17_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 17 (6:Fin 8))=sharedDiskP461Values 17 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value17_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 17 (7:Fin 8))=sharedDiskP461Values 17 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values17_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 17 j)=sharedDiskP461Values 17 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value17_0
  · exact sharedDiskP461Value17_1
  · exact sharedDiskP461Value17_2
  · exact sharedDiskP461Value17_3
  · exact sharedDiskP461Value17_4
  · exact sharedDiskP461Value17_5
  · exact sharedDiskP461Value17_6
  · exact sharedDiskP461Value17_7
private theorem sharedDiskP461Value18_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 18 (0:Fin 8))=sharedDiskP461Values 18 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value18_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 18 (1:Fin 8))=sharedDiskP461Values 18 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value18_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 18 (2:Fin 8))=sharedDiskP461Values 18 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value18_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 18 (3:Fin 8))=sharedDiskP461Values 18 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value18_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 18 (4:Fin 8))=sharedDiskP461Values 18 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value18_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 18 (5:Fin 8))=sharedDiskP461Values 18 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value18_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 18 (6:Fin 8))=sharedDiskP461Values 18 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value18_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 18 (7:Fin 8))=sharedDiskP461Values 18 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values18_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 18 j)=sharedDiskP461Values 18 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value18_0
  · exact sharedDiskP461Value18_1
  · exact sharedDiskP461Value18_2
  · exact sharedDiskP461Value18_3
  · exact sharedDiskP461Value18_4
  · exact sharedDiskP461Value18_5
  · exact sharedDiskP461Value18_6
  · exact sharedDiskP461Value18_7
private theorem sharedDiskP461Value19_0 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 19 (0:Fin 8))=sharedDiskP461Values 19 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value19_1 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 19 (1:Fin 8))=sharedDiskP461Values 19 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value19_2 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 19 (2:Fin 8))=sharedDiskP461Values 19 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value19_3 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 19 (3:Fin 8))=sharedDiskP461Values 19 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value19_4 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 19 (4:Fin 8))=sharedDiskP461Values 19 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value19_5 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 19 (5:Fin 8))=sharedDiskP461Values 19 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value19_6 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 19 (6:Fin 8))=sharedDiskP461Values 19 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP461Value19_7 : truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 19 (7:Fin 8))=sharedDiskP461Values 19 (7:Fin 8) := by decide +kernel
theorem sharedDiskP461Values19_eq : ∀ j : Fin 8, truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points 19 j)=sharedDiskP461Values 19 j := by
  intro j
  fin_cases j
  · exact sharedDiskP461Value19_0
  · exact sharedDiskP461Value19_1
  · exact sharedDiskP461Value19_2
  · exact sharedDiskP461Value19_3
  · exact sharedDiskP461Value19_4
  · exact sharedDiskP461Value19_5
  · exact sharedDiskP461Value19_6
  · exact sharedDiskP461Value19_7
theorem sharedDiskP461Values_eq : ∀ (i : Fin 20) (j : Fin 8), truncatedChordCell 1 sharedDiskP461Params (sharedChord442Gauss8Points i j)=sharedDiskP461Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP461Values0_eq
  · exact sharedDiskP461Values1_eq
  · exact sharedDiskP461Values2_eq
  · exact sharedDiskP461Values3_eq
  · exact sharedDiskP461Values4_eq
  · exact sharedDiskP461Values5_eq
  · exact sharedDiskP461Values6_eq
  · exact sharedDiskP461Values7_eq
  · exact sharedDiskP461Values8_eq
  · exact sharedDiskP461Values9_eq
  · exact sharedDiskP461Values10_eq
  · exact sharedDiskP461Values11_eq
  · exact sharedDiskP461Values12_eq
  · exact sharedDiskP461Values13_eq
  · exact sharedDiskP461Values14_eq
  · exact sharedDiskP461Values15_eq
  · exact sharedDiskP461Values16_eq
  · exact sharedDiskP461Values17_eq
  · exact sharedDiskP461Values18_eq
  · exact sharedDiskP461Values19_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP461Box : HorizontalRectangle := ⟨(97/200),(51/100),(3377117349125/6597069766656),(3398506407779/6597069766656),(1127805296683780874797695114414217/649037107316853453566312041152512),(4775534760128584941688939923638409/649037107316853453566312041152512),(-1462515395384376855688362627566351/324518553658426726783156020576256),(3762696634554179007457269558257545/2596148429267413814265248164610048),true,[]⟩
noncomputable def sharedDiskP461Grid : CGrid := momentChordGrid sharedDiskP461Params chordGaussRule8 1 sharedChord442Bd sharedChord442M (23175049/18014398509481984)
theorem sharedDiskP461Columns : containedInReported sharedDiskP461Grid.re sharedDiskP461Box.reLo sharedDiskP461Box.reHi=true ∧ containedInReported sharedDiskP461Grid.im sharedDiskP461Box.imLo sharedDiskP461Box.imHi=true := by
  rw [sharedDiskP461Grid,momentChordGrid_eq_tabulated sharedDiskP461Params chordGaussRule8 1 sharedChord442Bd sharedChord442M (23175049/18014398509481984) sharedChord442Gauss8Points sharedChord442Gauss8Weights sharedDiskP461Values sharedChord442Gauss8Points_eq sharedChord442Gauss8Weights_eq sharedDiskP461Values_eq]
  decide +kernel
theorem sharedDiskP461Sound : sharedDiskP461Box.Sound := by
  intro t a tl tu al au
  change (((97/200):ℚ):ℝ)≤t at tl
  change t≤(((51/100):ℚ):ℝ) at tu
  change (((3377117349125/6597069766656):ℚ):ℝ)≤a at al
  change a≤(((3398506407779/6597069766656):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP461Params_ok] at ps
  have band := sharedChord442ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((159/400):ℚ)≤(97/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((51/100):ℚ)≤(21/40)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((1110112793673/2199023255552):ℚ)≤(3377117349125/6597069766656))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3398506407779/6597069766656):ℚ)≤(3410681265479/6597069766656)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 1 sharedChord442Bd (by decide +kernel) (by decide +kernel) sharedChord442M (by decide +kernel) (sharedChord442Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP461Columns.1 sharedDiskP461Columns.2
def sharedDiskP461Rows : List SignRow := [positive_461.toSignRow, positive_463.toSignRow, positive_464.toSignRow, positive_465.toSignRow]
theorem sharedDiskP461Rows_actual : ∀ r∈sharedDiskP461Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP461Rows.all (sharedDiskP461Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP461Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP466Params : ChordParams := ⟨⟨(-3045001778040279689751),(-2553594301324183689892),true⟩,⟨3494120446995233693228528,3613427514022004551824179,true⟩,⟨50037788552278563105058,55537579118036420113906,true⟩,⟨60857210423331651092096,67169468080344912019757,true⟩,⟨110844273539477664132128,121089702401322736362532,true⟩,⟨1202851116816066216313016,1203829396104281761159644,true⟩,⟨(-3707785869584949843916445),(-3598922125668220793431094),true⟩,⟨⟨1167622080594119730482577,1240192941794659101192513,true⟩,⟨(-46),46,true⟩⟩⟩
theorem sharedDiskP466Params_ok : chordParams (Grid.ofRats (51/100) (21/40)) (Grid.ofRats (1132009987935/2199023255552) (3410681265479/6597069766656))=sharedDiskP466Params := by decide +kernel
def sharedDiskP466Values (i : Fin 20) (j : Fin 6) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-11366544168862253296190313),(-3794285939551580656111147),true⟩,⟨(-2890140079271345884237039),3769047982260549551519539,true⟩⟩
  | 0,1 => ⟨⟨(-11169361787777201128855391),(-3648921172621433351769488),true⟩,⟨(-2918342260062161450345341),3769728069608532366175694,true⟩⟩
  | 0,2 => ⟨⟨(-11042066033176739926012229),(-3558698447145737107008252),true⟩,⟨(-2935573102094157235343070),3764070538641990602357402,true⟩⟩
  | 0,3 => ⟨⟨(-11587453539393282329073990),(-3965456165286979162119305),true⟩,⟨(-2856443269299815110992619),3753980401786938830571771,true⟩⟩
  | 0,4 => ⟨⟨(-11781400749229499926460366),(-4123154228484444141082408),true⟩,⟨(-2825136539065705972675754),3727651887071052660191726,true⟩⟩
  | 0,5 => ⟨⟨(-11905037110167175149366779),(-4227361342130277142627423),true⟩,⟨(-2804398431211249037772849),3704214660894750984330826,true⟩⟩
  | 1,0 => ⟨⟨(-10422417205302814063401742),(-3157841626185280489726629),true⟩,⟨(-3008151806287466854928637),3674164648250104253266304,true⟩⟩
  | 1,1 => ⟨⟨(-10220075513817307744656232),(-3039817660564207678005108),true⟩,⟨(-3027758769159229759283897),3624532628391580118373870,true⟩⟩
  | 1,2 => ⟨⟨(-10089863567857348874382248),(-2966968638940959587930720),true⟩,⟨(-3039321519568272966103633),3587861068267579125293648,true⟩⟩
  | 1,3 => ⟨⟨(-10649965049435964803219716),(-3297912662985036733619972),true⟩,⟨(-2983696571328469374488836),3718571023456426388639490,true⟩⟩
  | 1,4 => ⟨⟨(-10850413059802584307655230),(-3428066017419061394884765),true⟩,⟨(-2960037075175924736971239),3746959215770219827496111,true⟩⟩
  | 1,5 => ⟨⟨(-10978486090769498756992785),(-3514676495266565637636625),true⟩,⟨(-2943887134045428348169417),3759517465009029664915957,true⟩⟩
  | 2,0 => ⟨⟨(-9461143624577914729294502),(-2646542016879998806662134),true⟩,⟨(-3083881396554450337467073),3364403022058314797142590,true⟩⟩
  | 2,1 => ⟨⟨(-9257814543631840581664434),(-2540899248419360628244560),true⟩,⟨(-3094463192268528362286850),3277623347084926328629162,true⟩⟩
  | 2,2 => ⟨⟨(-9127506842634667283493466),(-2474137839436396781413115),true⟩,⟨(-3100311073292076925210981),3218749484557119819627587,true⟩⟩
  | 2,3 => ⟨⟨(-9690991367102355820597989),(-2757969454421057652608575),true⟩,⟨(-3069710713974485436759500),3454419514782094897353536,true⟩⟩
  | 2,4 => ⟨⟨(-9894471160947856531039826),(-2862002072051957530104137),true⟩,⟨(-3055144699580543428720555),3526309222397026223449693,true⟩⟩
  | 2,5 => ⟨⟨(-10024954635033653016064085),(-2931530406022206353307030),true⟩,⟨(-3044780025758333456807461),3568261353160285004249744,true⟩⟩
  | 3,0 => ⟨⟨(-8504419553005520557428524),(-2174816682522636863606712),true⟩,⟨(-3118802787325108878222324),2906657517026177735832986,true⟩⟩
  | 3,1 => ⟨⟨(-8305095073531028122633737),(-2085421821610097767742916),true⟩,⟨(-3121632545065411256060523),2797640821261712070829491,true⟩⟩
  | 3,2 => ⟨⟨(-8177913841243464197399688),(-2029848034610016059633266),true⟩,⟨(-3122713416172004642971143),2726110684678058010679022,true⟩⟩
  | 3,3 => ⟨⟨(-8731027292557254660527311),(-2280047796296052688602351),true⟩,⟨(-3113823826032896806438596),3025547262252019286369069,true⟩⟩
  | 3,4 => ⟨⟨(-8932776980847539114802742),(-2377160459707964315254328),true⟩,⟨(-3107735274301307518936955),3126376456604489500086866,true⟩⟩
  | 3,5 => ⟨⟨(-9062710135750083551056251),(-2441503848433078491247870),true⟩,⟨(-3102954138132263086908195),3188579608977209711605143,true⟩⟩
  | 4,0 => ⟨⟨(-7023812430599907326592508),(-1570231681926959009736247),true⟩,⟨(-3109838950489260180227848),2024203964946426841397626,true⟩⟩
  | 4,1 => ⟨⟨(-6659909166742658713243965),(-1439045809923804657793750),true⟩,⟨(-3098544851841176565186090),1789657159411011991065399,true⟩⟩
  | 4,2 => ⟨⟨(-6432271373686326151914250),(-1359598347284562362077160),true⟩,⟨(-3090014671273782541752883),1641238343595739288609717,true⟩⟩
  | 4,3 => ⟨⟨(-7447310072686871901370895),(-1730418617984699409646889),true⟩,⟨(-3118938527335595013605939),2290838554707157206487807,true⟩⟩
  | 4,4 => ⟨⟨(-7832135784444523152584571),(-1884140626693519821073677),true⟩,⟨(-3122957037625272141099713),2524787566227928372756164,true⟩⟩
  | 4,5 => ⟨⟨(-8083357608420225462718232),(-1989238960642522069978787),true⟩,⟨(-3123163911416931009680570),2672009076257268218406859,true⟩⟩
  | 5,0 => ⟨⟨(-5407692044413429494711470),(-1020176165814134928585395),true⟩,⟨(-3040217990245728946601666),1001857003220497623880865,true⟩⟩
  | 5,1 => ⟨⟨(-5102686706818244438403183),(-922862782611946629175355),true⟩,⟨(-3022453336830005900262594),830604439112979879781130,true⟩⟩
  | 5,2 => ⟨⟨(-4913646742789154928045586),(-863028143606950787212776),true⟩,⟨(-3010826595079463429085803),724743769737069876935299,true⟩⟩
  | 5,3 => ⟨⟨(-5767554921778955561802562),(-1136866387617975748001605),true⟩,⟨(-3059476889239716786267298),1204701031750635379728528,true⟩⟩
  | 5,4 => ⟨⟨(-6100483520534512750590354),(-1246886267493851119539067),true⟩,⟨(-3075756462901835307978017),1423582047891671523775267,true⟩⟩
  | 5,5 => ⟨⟨(-6320741713776847502204309),(-1321327423621126885712830),true⟩,⟨(-3085454380449228954477021),1568202244404464182385248,true⟩⟩
  | 6,0 => ⟨⟨(-3387931580219734026818321),(-373525237748877942162050),true⟩,⟨(-2900484133684065762323627),(-89226685453711118346945),true⟩⟩
  | 6,1 => ⟨⟨(-2986765591126352382961943),(-230391014176429749667688),true⟩,⟨(-2864391085296963962842492),(-252477247779554651790124),true⟩⟩
  | 6,2 => ⟨⟨(-2746808673213812023780533),(-141826321866796264798210),true⟩,⟨(-2841295475868855175172558),(-346112063513386907568106),true⟩⟩
  | 6,3 => ⟨⟨(-3908150780600197350566108),(-544788504353959205541677),true⟩,⟨(-2941651204226186730801570),172816675818924152161720,true⟩⟩
  | 6,4 => ⟨⟨(-4421109759563606082978014),(-707745708746157968717442),true⟩,⟨(-2978459178225969879418753),451302835120268274459992,true⟩⟩
  | 6,5 => ⟨⟨(-4775876170553037168144327),(-819558278641455578023118),true⟩,⟨(-3002069827520133049290152),647845327431250298438535,true⟩⟩
  | 7,0 => ⟨⟨(-1751204158624588975506862),266668367089493983089837,true⟩,⟨(-2728071936532337386672473),(-691196433229958494876087),true⟩⟩
  | 7,1 => ⟨⟨(-1475576623266423279093914),393117840983317548885097,true⟩,⟨(-2689854512152400344119939),(-771165549173350459919896),true⟩⟩
  | 7,2 => ⟨⟨(-1313336529010104279749646),472812295342023916226558,true⟩,⟨(-2665576704891629288804914),(-809388082094796611362868),true⟩⟩
  | 7,3 => ⟨⟨(-2087488131597908306300999),120125595700576586935851,true⟩,⟨(-2770115196287043448281615),(-583652147584138324711802),true⟩⟩
  | 7,4 => ⟨⟨(-2410592904782497418879733),(-13105198632115594099979),true⟩,⟨(-2806599752799870362823229),(-471224660829872174775959),true⟩⟩
  | 7,5 => ⟨⟨(-2632079154506423740000585),(-98552439298963044954882),true⟩,⟨(-2829786724806182677368988),(-389654440880938847816527),true⟩⟩
  | 8,0 => ⟨⟨729292437014777146096054,1970087881050906022832595,true⟩,⟨(-2186645531017138341349096),(-883782339722692852313313),true⟩⟩
  | 8,1 => ⟨⟨1162111144153207451510297,2380845186234060235575370,true⟩,⟨(-2028448587069954622154527),(-806723492684863496261577),true⟩⟩
  | 8,2 => ⟨⟨1411185938813876148713733,2621338907345690628467596,true⟩,⟨(-1925011800848858003779925),(-747632564876681603909523),true⟩⟩
  | 8,3 => ⟨⟨150702727742000225725848,1451492398649568902147259,true⟩,⟨(-2357147447344186704950004),(-930618516978356307903243),true⟩⟩
  | 8,4 => ⟨⟨(-568376751662858779772860),941249871673187641433957,true⟩,⟨(-2531586583037803906520853),(-907865701992245997527743),true⟩⟩
  | 8,5 => ⟨⟨(-1122195110475779580456051),585918141816598586886421,true⟩,⟨(-2634941692559489917235287),(-842054071025352203324229),true⟩⟩
  | 9,0 => ⟨⟨2950030702813264881243445,4104188976227834456383998,true⟩,⟨(-1065827312538261634371516),(-170534155648216349697174),true⟩⟩
  | 9,1 => ⟨⟨3223676062814830399312608,4345638287036061997024485,true⟩,⟨(-850423312785378204162900),(-23215224104652006079089),true⟩⟩
  | 9,2 => ⟨⟨3353936600604494826864516,4451173239262332270910953,true⟩,⟨(-730564553572123989272873),58294065080447405875285,true⟩⟩
  | 9,3 => ⟨⟨2516497020274784895822388,3696643490614173355784537,true⟩,⟨(-1353401801764057235623108),(-370241202889666826122661),true⟩⟩
  | 9,4 => ⟨⟨1997598523195212490601555,3193171303030148630794300,true⟩,⟨(-1645774626330743839147499),(-569939813458795255410119),true⟩⟩
  | 9,5 => ⟨⟨1584119585382956203736583,2789468114281466459888366,true⟩,⟨(-1847914260477194916051285),(-700694587596240072393016),true⟩⟩
  | 10,0 => ⟨⟨3541402344369676239515350,4342059826764241045760575,true⟩,⟨(-123344425855204053688021),395642300386015612242810,true⟩⟩
  | 10,1 => ⟨⟨3403324907953306824657821,4110213826638343899855318,true⟩,⟨(-56656595937758815058181),400432996010622719252122,true⟩⟩
  | 10,2 => ⟨⟨3301220034260809753752835,3954220506697623300635368,true⟩,⟨(-35197193087686977686470),388848305649255891213115,true⟩⟩
  | 10,3 => ⟨⟨3622621902269032313836704,4538353815605704539655665,true⟩,⟨(-263280017329650856868363),341405167608205113363156,true⟩⟩
  | 10,4 => ⟨⟨3567070878448116141050275,4584460567331457116485358,true⟩,⟨(-466880575736690333942961),228659208322158426445949,true⟩⟩
  | 10,5 => ⟨⟨3431216165249198768045418,4508251595491999594634597,true⟩,⟨(-649795531893751370129393),112317107950722352835246,true⟩⟩
  | 11,0 => ⟨⟨2808403369837624389070101,3493724899902495735730782,true⟩,⟨(-161921110348990934962227),281535803899863025638414,true⟩⟩
  | 11,1 => ⟨⟨2751400514046304836393140,3495169174652297046002768,true⟩,⟨(-285749237564360316567633),207612713624188373014289,true⟩⟩
  | 11,2 => ⟨⟨2762663847731336930572259,3570246802075824231413872,true⟩,⟨(-410955261834442165357402),139032031280010938695482,true⟩⟩
  | 11,3 => ⟨⟨2950122124582668945866652,3603561611636328539595274,true⟩,⟨(-80740690748092898950738),337974956427757473296448,true⟩⟩
  | 11,4 => ⟨⟨3120914718791983335410781,3763194899437887082893832,true⟩,⟨(-42608428116856786494466),370675050364641918599593,true⟩⟩
  | 11,5 => ⟨⟨3243701578887297991289880,3884108094723352410283313,true⟩,⟨(-32699097610854049409973),382769498296015808414527,true⟩⟩
  | 12,0 => ⟨⟨3055986972717789582545995,4251647142915840064689857,true⟩,⟨(-1167715425141960636040076),(-241060162394892320718471),true⟩⟩
  | 12,1 => ⟨⟨3247326363445220532110911,4722066569740542018682865,true⟩,⟨(-1741681662056858957339977),(-521416081775440737756823),true⟩⟩
  | 12,2 => ⟨⟨3384494914707557621649039,5132476552052961317790618,true⟩,⟨(-2324816475580126600777864),(-804678534859971673875036),true⟩⟩
  | 12,3 => ⟨⟨2900463518386138411476621,3902801242068129083936987,true⟩,⟨(-785718539132622668828067),(-53346604080999835932830),true⟩⟩
  | 12,4 => ⟨⟨2813683012874353020095747,3705328599480717698659001,true⟩,⟨(-572335899574738771794609),54381318107669023791064,true⟩⟩
  | 12,5 => ⟨⟨2779168735909048882724243,3618668484130123091304093,true⟩,⟨(-472378113237721889916639),106485433492992186477492,true⟩⟩
  | 13,0 => ⟨⟨3365799286321498035825215,6553162697345824045083554,true⟩,⟨(-5573422892791418652805580),(-2334040940333058155659174),true⟩⟩
  | 13,1 => ⟨⟨2850072658147463820443760,6908371686388131264720412,true⟩,⟨(-7584048546651430116786432),(-3226144442949661404747835),true⟩⟩
  | 13,2 => ⟨⟨2152938122000070267968630,6944275138284994963389516,true⟩,⟨(-9263192515703308982454199),(-3932394747446866624770982),true⟩⟩
  | 13,3 => ⟨⟨3517063495872949430023250,6023642944724599109184886,true⟩,⟨(-4013380276837673305031566),(-1611590261191275210591773),true⟩⟩
  | 13,4 => ⟨⟨3486399813163808853317963,5572347495561223050326272,true⟩,⟨(-3067234746647591498708654),(-1162239787274375287119039),true⟩⟩
  | 13,5 => ⟨⟨3432497193031829589014826,5311083246161137854022534,true⟩,⟨(-2609350027886374695927678),(-942170814807464947425281),true⟩⟩
  | 14,0 => ⟨⟨296622704303395408895615,6415700743465110845905437,true⟩,⟨(-12086853213419586517948404),(-5005484409463645781152326),true⟩⟩
  | 14,1 => ⟨⟨(-614209126218848577330452),6074140507666731085505407,true⟩,⟨(-12988411444549979718941394),(-5288525230692410994120394),true⟩⟩
  | 14,2 => ⟨⟨(-1287343753310892169692139),5795709635322006105430759,true⟩,⟨(-13565598792368247621552939),(-5455332379914867662473569),true⟩⟩
  | 14,3 => ⟨⟨1060274534680624215373382,6684600913060227539167402,true⟩,⟨(-11129626656114397201444643),(-4667141810874474327489874),true⟩⟩
  | 14,4 => ⟨⟨1569025609129528699028444,6836837219259984359112184,true⟩,⟨(-10338120215684891621404397),(-4362848310842527730550262),true⟩⟩
  | 14,5 => ⟨⟨1849302000675488730110098,6899173723604443944634872,true⟩,⟨(-9848549875358282634705159),(-4169097132913108070412239),true⟩⟩
  | 15,0 => ⟨⟨(-5475029121928760799961697),3677729585087931003974915,true⟩,⟨(-15975012038720625545854410),(-5924962287526906868331941),true⟩⟩
  | 15,1 => ⟨⟨(-7125749141156948254551745),2693630827438440240967012,true⟩,⟨(-16445732547293532578133075),(-5885158626964007717260364),true⟩⟩
  | 15,2 => ⟨⟨(-8231258260421033701083108),1997920518251714653921390,true⟩,⟨(-16611325564211692466848639),(-5786044606781038373529986),true⟩⟩
  | 15,3 => ⟨⟨(-3767306276484508031508619),4611413794399717123770647,true⟩,⟨(-15212813325846380592076245),(-5838235797685159363090633),true⟩⟩
  | 15,4 => ⟨⟨(-2422791282204125869242322),5281481447799847606891077,true⟩,⟨(-14405978047645580575828832),(-5672071472690911074571475),true⟩⟩
  | 15,5 => ⟨⟨(-1647648136704367248240753),5638204157411261172586625,true⟩,⟨(-13849410820065940846952260),(-5532399620119953894028105),true⟩⟩
  | 16,0 => ⟨⟨(-11043390073864130228535245),406763803032857916396791,true⟩,⟨(-16404296382725383174454239),(-5072096564927571640467594),true⟩⟩
  | 16,1 => ⟨⟨(-11937946310755115838733744),(-104159879134261568520574),true⟩,⟨(-16129841432102503343024568),(-4684379668088345137502520),true⟩⟩
  | 16,2 => ⟨⟨(-12487630802709305004105620),(-425449613656715737151307),true⟩,⟨(-15895477027983556378165083),(-4411198795463885496711930),true⟩⟩
  | 16,3 => ⟨⟨(-10078987195459331440523643),978074341181753192905601,true⟩,⟨(-16589872406827352082796854),(-5373502793339131653731402),true⟩⟩
  | 16,4 => ⟨⟨(-9209500052572235490717449),1469354783318361424048440,true⟩,⟨(-16649894391389593953947315),(-5591940011327693326749102),true⟩⟩
  | 16,5 => ⟨⟨(-8648959076277686195158820),1775161266681080171518156,true⟩,⟨(-16640762128709392066815565),(-5709505894535355592438538),true⟩⟩
  | 17,0 => ⟨⟨(-14700999984296849370156434),(-1919266729012521946653931),true⟩,⟨(-14112507349085537745431793),(-2872867934413273177980624),true⟩⟩
  | 17,1 => ⟨⟨(-15205963653253004094436684),(-2359429478698131382490759),true⟩,⟨(-13311239859988963211298172),(-2318701277508530827486875),true⟩⟩
  | 17,2 => ⟨⟨(-15462493620981499810596777),(-2624519320682085283066386),true⟩,⟨(-12745104187407362834408088),(-1955820191163319301026710),true⟩⟩
  | 17,3 => ⟨⟨(-13993025398079087086799702),(-1390828633290194015285663),true⟩,⟨(-14889014824054043407517251),(-3471792627719141539282420),true⟩⟩
  | 17,4 => ⟨⟨(-13263097486393432405033477),(-903622672679621876692523),true⟩,⟨(-15457036782905113176385458),(-3969041864794811477208408),true⟩⟩
  | 17,5 => ⟨⟨(-12752372606290112269641081),(-585037990275939207708555),true⟩,⟨(-15761438897983304178627925),(-4268458105133155812635864),true⟩⟩
  | 18,0 => ⟨⟨(-15859896204045602381309405),(-3651895632453756211058988),true⟩,⟨(-9574062990866597747030949),(-227491885554713083685562),true⟩⟩
  | 18,1 => ⟨⟨(-15694900375331812043961414),(-3879983328368116266916751),true⟩,⟨(-8449488087593991778669396),400405627342328815332578,true⟩⟩
  | 18,2 => ⟨⟨(-15507092384235436014917564),(-3996947619071579031335434),true⟩,⟨(-7718874216369900616888631),788848403871688679715804,true⟩⟩
  | 18,3 => ⟨⟨(-15882308664078796025894375),(-3329747366864748969226736),true⟩,⟨(-10802220553301211163406890),(-844769156582596564944103),true⟩⟩
  | 18,4 => ⟨⟨(-15739235489808929861723428),(-2991546414763534063290164),true⟩,⟨(-11828970534470554788284737),(-1408791914313934770030290),true⟩⟩
  | 18,5 => ⟨⟨(-15569151971857687545883351),(-2750734267592187648443192),true⟩,⟨(-12449200178078974423737795),(-1774094368957815270144803),true⟩⟩
  | 19,0 => ⟨⟨(-13805926438279355479765721),(-4238485950170490282544722),true⟩,⟨(-4304339348783595224482936),2725103923787110530579976,true⟩⟩
  | 19,1 => ⟨⟨(-13031272059341447503262637),(-4198887405454380756621719),true⟩,⟨(-3301351058293701081440493),3202976498512986943195081,true⟩⟩
  | 19,2 => ⟨⟨(-12507356254520781699628743),(-4097478885830810748884221),true⟩,⟨(-2697766630953753700133137),3459643961544267725649980,true⟩⟩
  | 19,3 => ⟨⟨(-14565031692945550874224396),(-4210493888052073125121981),true⟩,⟨(-5511676059354576715863395),2074850463860311981653388,true⟩⟩
  | 19,4 => ⟨⟨(-15111089295356315596805472),(-4128534045063080551306484),true⟩,⟨(-6626512927106048916815048),1408635742035992563550497,true⟩⟩
  | 19,5 => ⟨⟨(-15390334693644999317963408),(-4046490305326797724764060),true⟩,⟨(-7354771173670002649458414),974558376578750755230577,true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP466Value0_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 0 (0:Fin 6))=sharedDiskP466Values 0 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value0_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 0 (1:Fin 6))=sharedDiskP466Values 0 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value0_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 0 (2:Fin 6))=sharedDiskP466Values 0 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value0_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 0 (3:Fin 6))=sharedDiskP466Values 0 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value0_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 0 (4:Fin 6))=sharedDiskP466Values 0 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value0_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 0 (5:Fin 6))=sharedDiskP466Values 0 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values0_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 0 j)=sharedDiskP466Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value0_0
  · exact sharedDiskP466Value0_1
  · exact sharedDiskP466Value0_2
  · exact sharedDiskP466Value0_3
  · exact sharedDiskP466Value0_4
  · exact sharedDiskP466Value0_5
private theorem sharedDiskP466Value1_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 1 (0:Fin 6))=sharedDiskP466Values 1 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value1_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 1 (1:Fin 6))=sharedDiskP466Values 1 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value1_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 1 (2:Fin 6))=sharedDiskP466Values 1 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value1_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 1 (3:Fin 6))=sharedDiskP466Values 1 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value1_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 1 (4:Fin 6))=sharedDiskP466Values 1 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value1_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 1 (5:Fin 6))=sharedDiskP466Values 1 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values1_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 1 j)=sharedDiskP466Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value1_0
  · exact sharedDiskP466Value1_1
  · exact sharedDiskP466Value1_2
  · exact sharedDiskP466Value1_3
  · exact sharedDiskP466Value1_4
  · exact sharedDiskP466Value1_5
private theorem sharedDiskP466Value2_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 2 (0:Fin 6))=sharedDiskP466Values 2 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value2_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 2 (1:Fin 6))=sharedDiskP466Values 2 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value2_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 2 (2:Fin 6))=sharedDiskP466Values 2 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value2_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 2 (3:Fin 6))=sharedDiskP466Values 2 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value2_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 2 (4:Fin 6))=sharedDiskP466Values 2 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value2_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 2 (5:Fin 6))=sharedDiskP466Values 2 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values2_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 2 j)=sharedDiskP466Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value2_0
  · exact sharedDiskP466Value2_1
  · exact sharedDiskP466Value2_2
  · exact sharedDiskP466Value2_3
  · exact sharedDiskP466Value2_4
  · exact sharedDiskP466Value2_5
private theorem sharedDiskP466Value3_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 3 (0:Fin 6))=sharedDiskP466Values 3 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value3_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 3 (1:Fin 6))=sharedDiskP466Values 3 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value3_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 3 (2:Fin 6))=sharedDiskP466Values 3 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value3_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 3 (3:Fin 6))=sharedDiskP466Values 3 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value3_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 3 (4:Fin 6))=sharedDiskP466Values 3 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value3_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 3 (5:Fin 6))=sharedDiskP466Values 3 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values3_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 3 j)=sharedDiskP466Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value3_0
  · exact sharedDiskP466Value3_1
  · exact sharedDiskP466Value3_2
  · exact sharedDiskP466Value3_3
  · exact sharedDiskP466Value3_4
  · exact sharedDiskP466Value3_5
private theorem sharedDiskP466Value4_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 4 (0:Fin 6))=sharedDiskP466Values 4 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value4_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 4 (1:Fin 6))=sharedDiskP466Values 4 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value4_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 4 (2:Fin 6))=sharedDiskP466Values 4 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value4_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 4 (3:Fin 6))=sharedDiskP466Values 4 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value4_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 4 (4:Fin 6))=sharedDiskP466Values 4 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value4_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 4 (5:Fin 6))=sharedDiskP466Values 4 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values4_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 4 j)=sharedDiskP466Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value4_0
  · exact sharedDiskP466Value4_1
  · exact sharedDiskP466Value4_2
  · exact sharedDiskP466Value4_3
  · exact sharedDiskP466Value4_4
  · exact sharedDiskP466Value4_5
private theorem sharedDiskP466Value5_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 5 (0:Fin 6))=sharedDiskP466Values 5 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value5_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 5 (1:Fin 6))=sharedDiskP466Values 5 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value5_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 5 (2:Fin 6))=sharedDiskP466Values 5 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value5_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 5 (3:Fin 6))=sharedDiskP466Values 5 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value5_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 5 (4:Fin 6))=sharedDiskP466Values 5 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value5_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 5 (5:Fin 6))=sharedDiskP466Values 5 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values5_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 5 j)=sharedDiskP466Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value5_0
  · exact sharedDiskP466Value5_1
  · exact sharedDiskP466Value5_2
  · exact sharedDiskP466Value5_3
  · exact sharedDiskP466Value5_4
  · exact sharedDiskP466Value5_5
private theorem sharedDiskP466Value6_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 6 (0:Fin 6))=sharedDiskP466Values 6 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value6_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 6 (1:Fin 6))=sharedDiskP466Values 6 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value6_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 6 (2:Fin 6))=sharedDiskP466Values 6 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value6_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 6 (3:Fin 6))=sharedDiskP466Values 6 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value6_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 6 (4:Fin 6))=sharedDiskP466Values 6 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value6_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 6 (5:Fin 6))=sharedDiskP466Values 6 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values6_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 6 j)=sharedDiskP466Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value6_0
  · exact sharedDiskP466Value6_1
  · exact sharedDiskP466Value6_2
  · exact sharedDiskP466Value6_3
  · exact sharedDiskP466Value6_4
  · exact sharedDiskP466Value6_5
private theorem sharedDiskP466Value7_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 7 (0:Fin 6))=sharedDiskP466Values 7 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value7_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 7 (1:Fin 6))=sharedDiskP466Values 7 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value7_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 7 (2:Fin 6))=sharedDiskP466Values 7 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value7_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 7 (3:Fin 6))=sharedDiskP466Values 7 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value7_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 7 (4:Fin 6))=sharedDiskP466Values 7 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value7_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 7 (5:Fin 6))=sharedDiskP466Values 7 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values7_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 7 j)=sharedDiskP466Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value7_0
  · exact sharedDiskP466Value7_1
  · exact sharedDiskP466Value7_2
  · exact sharedDiskP466Value7_3
  · exact sharedDiskP466Value7_4
  · exact sharedDiskP466Value7_5
private theorem sharedDiskP466Value8_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 8 (0:Fin 6))=sharedDiskP466Values 8 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value8_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 8 (1:Fin 6))=sharedDiskP466Values 8 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value8_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 8 (2:Fin 6))=sharedDiskP466Values 8 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value8_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 8 (3:Fin 6))=sharedDiskP466Values 8 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value8_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 8 (4:Fin 6))=sharedDiskP466Values 8 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value8_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 8 (5:Fin 6))=sharedDiskP466Values 8 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values8_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 8 j)=sharedDiskP466Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value8_0
  · exact sharedDiskP466Value8_1
  · exact sharedDiskP466Value8_2
  · exact sharedDiskP466Value8_3
  · exact sharedDiskP466Value8_4
  · exact sharedDiskP466Value8_5
private theorem sharedDiskP466Value9_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 9 (0:Fin 6))=sharedDiskP466Values 9 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value9_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 9 (1:Fin 6))=sharedDiskP466Values 9 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value9_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 9 (2:Fin 6))=sharedDiskP466Values 9 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value9_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 9 (3:Fin 6))=sharedDiskP466Values 9 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value9_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 9 (4:Fin 6))=sharedDiskP466Values 9 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value9_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 9 (5:Fin 6))=sharedDiskP466Values 9 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values9_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 9 j)=sharedDiskP466Values 9 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value9_0
  · exact sharedDiskP466Value9_1
  · exact sharedDiskP466Value9_2
  · exact sharedDiskP466Value9_3
  · exact sharedDiskP466Value9_4
  · exact sharedDiskP466Value9_5
private theorem sharedDiskP466Value10_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 10 (0:Fin 6))=sharedDiskP466Values 10 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value10_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 10 (1:Fin 6))=sharedDiskP466Values 10 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value10_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 10 (2:Fin 6))=sharedDiskP466Values 10 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value10_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 10 (3:Fin 6))=sharedDiskP466Values 10 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value10_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 10 (4:Fin 6))=sharedDiskP466Values 10 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value10_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 10 (5:Fin 6))=sharedDiskP466Values 10 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values10_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 10 j)=sharedDiskP466Values 10 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value10_0
  · exact sharedDiskP466Value10_1
  · exact sharedDiskP466Value10_2
  · exact sharedDiskP466Value10_3
  · exact sharedDiskP466Value10_4
  · exact sharedDiskP466Value10_5
private theorem sharedDiskP466Value11_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 11 (0:Fin 6))=sharedDiskP466Values 11 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value11_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 11 (1:Fin 6))=sharedDiskP466Values 11 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value11_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 11 (2:Fin 6))=sharedDiskP466Values 11 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value11_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 11 (3:Fin 6))=sharedDiskP466Values 11 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value11_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 11 (4:Fin 6))=sharedDiskP466Values 11 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value11_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 11 (5:Fin 6))=sharedDiskP466Values 11 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values11_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 11 j)=sharedDiskP466Values 11 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value11_0
  · exact sharedDiskP466Value11_1
  · exact sharedDiskP466Value11_2
  · exact sharedDiskP466Value11_3
  · exact sharedDiskP466Value11_4
  · exact sharedDiskP466Value11_5
private theorem sharedDiskP466Value12_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 12 (0:Fin 6))=sharedDiskP466Values 12 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value12_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 12 (1:Fin 6))=sharedDiskP466Values 12 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value12_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 12 (2:Fin 6))=sharedDiskP466Values 12 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value12_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 12 (3:Fin 6))=sharedDiskP466Values 12 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value12_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 12 (4:Fin 6))=sharedDiskP466Values 12 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value12_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 12 (5:Fin 6))=sharedDiskP466Values 12 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values12_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 12 j)=sharedDiskP466Values 12 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value12_0
  · exact sharedDiskP466Value12_1
  · exact sharedDiskP466Value12_2
  · exact sharedDiskP466Value12_3
  · exact sharedDiskP466Value12_4
  · exact sharedDiskP466Value12_5
private theorem sharedDiskP466Value13_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 13 (0:Fin 6))=sharedDiskP466Values 13 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value13_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 13 (1:Fin 6))=sharedDiskP466Values 13 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value13_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 13 (2:Fin 6))=sharedDiskP466Values 13 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value13_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 13 (3:Fin 6))=sharedDiskP466Values 13 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value13_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 13 (4:Fin 6))=sharedDiskP466Values 13 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value13_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 13 (5:Fin 6))=sharedDiskP466Values 13 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values13_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 13 j)=sharedDiskP466Values 13 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value13_0
  · exact sharedDiskP466Value13_1
  · exact sharedDiskP466Value13_2
  · exact sharedDiskP466Value13_3
  · exact sharedDiskP466Value13_4
  · exact sharedDiskP466Value13_5
private theorem sharedDiskP466Value14_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 14 (0:Fin 6))=sharedDiskP466Values 14 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value14_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 14 (1:Fin 6))=sharedDiskP466Values 14 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value14_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 14 (2:Fin 6))=sharedDiskP466Values 14 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value14_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 14 (3:Fin 6))=sharedDiskP466Values 14 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value14_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 14 (4:Fin 6))=sharedDiskP466Values 14 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value14_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 14 (5:Fin 6))=sharedDiskP466Values 14 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values14_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 14 j)=sharedDiskP466Values 14 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value14_0
  · exact sharedDiskP466Value14_1
  · exact sharedDiskP466Value14_2
  · exact sharedDiskP466Value14_3
  · exact sharedDiskP466Value14_4
  · exact sharedDiskP466Value14_5
private theorem sharedDiskP466Value15_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 15 (0:Fin 6))=sharedDiskP466Values 15 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value15_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 15 (1:Fin 6))=sharedDiskP466Values 15 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value15_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 15 (2:Fin 6))=sharedDiskP466Values 15 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value15_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 15 (3:Fin 6))=sharedDiskP466Values 15 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value15_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 15 (4:Fin 6))=sharedDiskP466Values 15 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value15_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 15 (5:Fin 6))=sharedDiskP466Values 15 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values15_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 15 j)=sharedDiskP466Values 15 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value15_0
  · exact sharedDiskP466Value15_1
  · exact sharedDiskP466Value15_2
  · exact sharedDiskP466Value15_3
  · exact sharedDiskP466Value15_4
  · exact sharedDiskP466Value15_5
private theorem sharedDiskP466Value16_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 16 (0:Fin 6))=sharedDiskP466Values 16 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value16_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 16 (1:Fin 6))=sharedDiskP466Values 16 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value16_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 16 (2:Fin 6))=sharedDiskP466Values 16 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value16_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 16 (3:Fin 6))=sharedDiskP466Values 16 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value16_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 16 (4:Fin 6))=sharedDiskP466Values 16 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value16_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 16 (5:Fin 6))=sharedDiskP466Values 16 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values16_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 16 j)=sharedDiskP466Values 16 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value16_0
  · exact sharedDiskP466Value16_1
  · exact sharedDiskP466Value16_2
  · exact sharedDiskP466Value16_3
  · exact sharedDiskP466Value16_4
  · exact sharedDiskP466Value16_5
private theorem sharedDiskP466Value17_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 17 (0:Fin 6))=sharedDiskP466Values 17 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value17_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 17 (1:Fin 6))=sharedDiskP466Values 17 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value17_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 17 (2:Fin 6))=sharedDiskP466Values 17 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value17_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 17 (3:Fin 6))=sharedDiskP466Values 17 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value17_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 17 (4:Fin 6))=sharedDiskP466Values 17 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value17_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 17 (5:Fin 6))=sharedDiskP466Values 17 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values17_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 17 j)=sharedDiskP466Values 17 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value17_0
  · exact sharedDiskP466Value17_1
  · exact sharedDiskP466Value17_2
  · exact sharedDiskP466Value17_3
  · exact sharedDiskP466Value17_4
  · exact sharedDiskP466Value17_5
private theorem sharedDiskP466Value18_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 18 (0:Fin 6))=sharedDiskP466Values 18 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value18_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 18 (1:Fin 6))=sharedDiskP466Values 18 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value18_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 18 (2:Fin 6))=sharedDiskP466Values 18 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value18_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 18 (3:Fin 6))=sharedDiskP466Values 18 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value18_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 18 (4:Fin 6))=sharedDiskP466Values 18 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value18_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 18 (5:Fin 6))=sharedDiskP466Values 18 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values18_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 18 j)=sharedDiskP466Values 18 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value18_0
  · exact sharedDiskP466Value18_1
  · exact sharedDiskP466Value18_2
  · exact sharedDiskP466Value18_3
  · exact sharedDiskP466Value18_4
  · exact sharedDiskP466Value18_5
private theorem sharedDiskP466Value19_0 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 19 (0:Fin 6))=sharedDiskP466Values 19 (0:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value19_1 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 19 (1:Fin 6))=sharedDiskP466Values 19 (1:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value19_2 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 19 (2:Fin 6))=sharedDiskP466Values 19 (2:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value19_3 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 19 (3:Fin 6))=sharedDiskP466Values 19 (3:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value19_4 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 19 (4:Fin 6))=sharedDiskP466Values 19 (4:Fin 6) := by decide +kernel
private theorem sharedDiskP466Value19_5 : truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 19 (5:Fin 6))=sharedDiskP466Values 19 (5:Fin 6) := by decide +kernel
theorem sharedDiskP466Values19_eq : ∀ j : Fin 6, truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points 19 j)=sharedDiskP466Values 19 j := by
  intro j
  fin_cases j
  · exact sharedDiskP466Value19_0
  · exact sharedDiskP466Value19_1
  · exact sharedDiskP466Value19_2
  · exact sharedDiskP466Value19_3
  · exact sharedDiskP466Value19_4
  · exact sharedDiskP466Value19_5
theorem sharedDiskP466Values_eq : ∀ (i : Fin 20) (j : Fin 6), truncatedChordCell 1 sharedDiskP466Params (sharedChord442Gauss6Points i j)=sharedDiskP466Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP466Values0_eq
  · exact sharedDiskP466Values1_eq
  · exact sharedDiskP466Values2_eq
  · exact sharedDiskP466Values3_eq
  · exact sharedDiskP466Values4_eq
  · exact sharedDiskP466Values5_eq
  · exact sharedDiskP466Values6_eq
  · exact sharedDiskP466Values7_eq
  · exact sharedDiskP466Values8_eq
  · exact sharedDiskP466Values9_eq
  · exact sharedDiskP466Values10_eq
  · exact sharedDiskP466Values11_eq
  · exact sharedDiskP466Values12_eq
  · exact sharedDiskP466Values13_eq
  · exact sharedDiskP466Values14_eq
  · exact sharedDiskP466Values15_eq
  · exact sharedDiskP466Values16_eq
  · exact sharedDiskP466Values17_eq
  · exact sharedDiskP466Values18_eq
  · exact sharedDiskP466Values19_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP466Box : HorizontalRectangle := ⟨(51/100),(21/40),(1132009987935/2199023255552),(3410681265479/6597069766656),(1141115282748496767585287546320027/649037107316853453566312041152512),(4408302011966897887182158460859547/649037107316853453566312041152512),(-1398619963987052343911950016643473/324518553658426726783156020576256),(330667244020739207385411581050479/324518553658426726783156020576256),true,[]⟩
noncomputable def sharedDiskP466Grid : CGrid := momentChordGrid sharedDiskP466Params chordGaussRule6 1 sharedChord442Bd sharedChord442M (995300573/4503599627370496)
theorem sharedDiskP466Columns : containedInReported sharedDiskP466Grid.re sharedDiskP466Box.reLo sharedDiskP466Box.reHi=true ∧ containedInReported sharedDiskP466Grid.im sharedDiskP466Box.imLo sharedDiskP466Box.imHi=true := by
  rw [sharedDiskP466Grid,momentChordGrid_eq_tabulated sharedDiskP466Params chordGaussRule6 1 sharedChord442Bd sharedChord442M (995300573/4503599627370496) sharedChord442Gauss6Points sharedChord442Gauss6Weights sharedDiskP466Values sharedChord442Gauss6Points_eq sharedChord442Gauss6Weights_eq sharedDiskP466Values_eq]
  decide +kernel
theorem sharedDiskP466Sound : sharedDiskP466Box.Sound := by
  intro t a tl tu al au
  change (((51/100):ℚ):ℝ)≤t at tl
  change t≤(((21/40):ℚ):ℝ) at tu
  change (((1132009987935/2199023255552):ℚ):ℝ)≤a at al
  change a≤(((3410681265479/6597069766656):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP466Params_ok] at ps
  have band := sharedChord442ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((159/400):ℚ)≤(51/100))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((21/40):ℚ)≤(21/40)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((1110112793673/2199023255552):ℚ)≤(1132009987935/2199023255552))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3410681265479/6597069766656):ℚ)≤(3410681265479/6597069766656)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule6 chordGaussRule6_nodes chordGaussRule6_half_disk 1 sharedChord442Bd (by decide +kernel) (by decide +kernel) sharedChord442M (by decide +kernel) (sharedChord442Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP466Columns.1 sharedDiskP466Columns.2
def sharedDiskP466Rows : List SignRow := [positive_466.toSignRow, positive_467.toSignRow, positive_468.toSignRow]
theorem sharedDiskP466Rows_actual : ∀ r∈sharedDiskP466Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP466Rows.all (sharedDiskP466Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP466Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP442Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP461Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP466Rows_actual
