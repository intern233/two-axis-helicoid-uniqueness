import TwoAxisHelicoid.PdfSharedChord514Gauss8
import TwoAxisHelicoid.PdfSharedChord514Disks

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP514Params : ChordParams := ⟨⟨(-18589809117529908670412),(-18332900498891248935331),true⟩,⟨2208782363760718149720946,2235925974106776473668729,true⟩,⟨114646036959398423327431,117446579037660596295417,true⟩,⟨190180358094918304144331,194498712455155106350909,true⟩,⟨293236505743766636996737,295345809957283662686887,true⟩,⟨1172309258981342023762642,1172807735630698749478162,true⟩,⟨(-2456322777553789056744789),(-2447121698173474046687117),true⟩,⟨⟨1150370969844533202953556,1192078225456367851296763,true⟩,⟨(-691384),691384,true⟩⟩⟩
theorem sharedDiskP514Params_ok : chordParams (Grid.ofRats (3/4) (301/400)) (Grid.ofRats (921051395650439/1649267441664000) (927493846594439/1649267441664000))=sharedDiskP514Params := by decide +kernel
def sharedDiskP514Values (i : Fin 8) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3266885681718582887467557),(-2626786280079196133151757),true⟩,⟨(-455743564435411651579136),51101538834413464274963,true⟩⟩
  | 0,1 => ⟨⟨(-2818683531401306090754306),(-2242196135962164170903697),true⟩,⟨(-544135527851297965674026),(-70138649654560892902998),true⟩⟩
  | 0,2 => ⟨⟨(-2503222784628087241609152),(-1974427752520589714023385),true⟩,⟨(-613698860828575602760428),(-168157781363149341335668),true⟩⟩
  | 0,3 => ⟨⟨(-2328568366782730847431108),(-1826918100508145070109782),true⟩,⟨(-654274741828511595383849),(-225830373669766988336246),true⟩⟩
  | 0,4 => ⟨⟨(-3812964781931726114720657),(-3104371511486633037584302),true⟩,⟨(-367881690397128513212426),161046237182358696223422,true⟩⟩
  | 0,5 => ⟨⟨(-4384686478132641321001906),(-3614994663484150644265093),true⟩,⟨(-302771146170527903103926),230172033705551506751929,true⟩⟩
  | 0,6 => ⟨⟨(-4878626059546919800631024),(-4064676689046918353897123),true⟩,⟨(-270768613795298645965024),248284986126256110572612,true⟩⟩
  | 0,7 => ⟨⟨(-5192724157924771218581364),(-4354220339798736275497407),true⟩,⟨(-269944603489332215989311),237511806089695144683547,true⟩⟩
  | 1,0 => ⟨⟨(-1311673156372728246964875),(-975942074281229659071099),true⟩,⟨(-894847698085987664351171),(-585631935356304886995944),true⟩⟩
  | 1,1 => ⟨⟨(-1095759288341840984614467),(-794842795162867653860927),true⟩,⟨(-939354912552048472311004),(-657057087661163809854834),true⟩⟩
  | 1,2 => ⟨⟨(-939817162157441767258134),(-663400353755348471321930),true⟩,⟨(-967852394810004098021077),(-704721872548612771218446),true⟩⟩
  | 1,3 => ⟨⟨(-851363574643960524909279),(-588336357969080664965270),true⟩,⟨(-982542763998505737355261),(-729864843875279835785737),true⟩⟩
  | 1,4 => ⟨⟨(-1571525045116515886600769),(-1193082074555505892985690),true⟩,⟨(-835936214699285258830304),(-494334984581046073855926),true⟩⟩
  | 1,5 => ⟨⟨(-1845605376753550291271422),(-1421921281690519064205272),true⟩,⟨(-770424911684714457318733),(-395557373761937007796917),true⟩⟩
  | 1,6 => ⟨⟨(-2088569988360125495604011),(-1625228406357963382969993),true⟩,⟨(-711591333689336011897293),(-308757433419818510407071),true⟩⟩
  | 1,7 => ⟨⟨(-2247677502239134952587207),(-1758820549357464060415169),true⟩,⟨(-673430658561659657213898),(-253362344224554747359521),true⟩⟩
  | 2,0 => ⟨⟨111897825529485037351427,283489329444115109427940,true⟩,⟨(-1042044361487269909995549),(-858588385142614694185855),true⟩⟩
  | 2,1 => ⟨⟨315438565015146998268611,480262925106977682749172,true⟩,⟨(-1021988380383784660407983),(-846600164966596117702396),true⟩⟩
  | 2,2 => ⟨⟨460597162414020283598724,625255926611153409618063,true⟩,⟨(-1002427720750585525847023),(-829909508501375449240105),true⟩⟩
  | 2,3 => ⟨⟨543491260527487631563338,708345336699957413998772,true⟩,⟨(-988986303735669229720502),(-817884892854246832876055),true⟩⟩
  | 2,4 => ⟨⟨(-133300529669982457059382),54514445116623002323387,true⟩,⟨(-1050706254461656081936056),(-853166325302524403923763),true⟩⟩
  | 2,5 => ⟨⟨(-394060542067428949855973),(-183772224000554965713809),true⟩,⟨(-1040801647240342641087124),(-826259759110662790059671),true⟩⟩
  | 2,6 => ⟨⟨(-629560213196516675022791),(-395067393166937338111208),true⟩,⟨(-1016197540633785177460367),(-784499168731512931916856),true⟩⟩
  | 2,7 => ⟨⟨(-789391531853681591701046),(-534791954384009702046726),true⟩,⟨(-992855615142112989362452),(-746429071594752251143158),true⟩⟩
  | 3,0 => ⟨⟨1491808882612414620296165,1670873918008901236366156,true⟩,⟨(-798547781900694348301622),(-631869124254837241397321),true⟩⟩
  | 3,1 => ⟨⟨1704678651908380937067284,1890192905767597283397786,true⟩,⟨(-780258833448570087417965),(-610464178014658164930817),true⟩⟩
  | 3,2 => ⟨⟨1865480947142226515380833,2057148128913256216040570,true⟩,⟨(-785118213646279003041435),(-611274312726914665460866),true⟩⟩
  | 3,3 => ⟨⟨1960778039344188458380174,2156756377149395946969098,true⟩,⟨(-797920188340743437051718),(-620825968134075060420347),true⟩⟩
  | 3,4 => ⟨⟨1243331148728314024210975,1416648154003916449600006,true⟩,⟨(-842174946912129230605105),(-676729323918468648686895),true⟩⟩
  | 3,5 => ⟨⟨984352668429868273303410,1153242617214776498028720,true⟩,⟨(-898713133992606399491790),(-732539532868832161171756),true⟩⟩
  | 3,6 => ⟨⟨754114047363977305103239,920309840167440339985963,true⟩,⟨(-948845466381171848154660),(-780644193105062630007476),true⟩⟩
  | 3,7 => ⟨⟨601822681368891982835382,766931303520997944566461,true⟩,⟨(-978655811471712408224603),(-808457273711867159233917),true⟩⟩
  | 4,0 => ⟨⟨2687311019343343763611842,2983718294808138815946781,true⟩,⟨(-1300997838127907810332241),(-1027774054320844897997491),true⟩⟩
  | 4,1 => ⟨⟨2907528850466302425185762,3256284165838131390189358,true⟩,⟨(-1671667552871374032587139),(-1343573695800548291970120),true⟩⟩
  | 4,2 => ⟨⟨3070279298285517776883350,3474592487665178674735504,true⟩,⟨(-2107298051798295318919313),(-1718535801933167063389148),true⟩⟩
  | 4,3 => ⟨⟨3149071463953240254938633,3595002126427694939017982,true⟩,⟨(-2454973780226842455277679),(-2019315634694482801602698),true⟩⟩
  | 4,4 => ⟨⟨2457971985025668717487486,2713358022766074657355439,true⟩,⟨(-1050015101949879147519497),(-817883083765742336584711),true⟩⟩
  | 4,5 => ⟨⟨2255003219551123876371765,2481687989796302954177844,true⟩,⟨(-906082233757847490400700),(-701397472871316601063912),true⟩⟩
  | 4,6 => ⟨⟨2099371984475492665771805,2307964437173443929815321,true⟩,⟨(-835579705991628835230274),(-647460176916901983909800),true⟩⟩
  | 4,7 => ⟨⟨2006365350194079236434766,2205589923833120184729416,true⟩,⟨(-807617917545318221269541),(-627788240406637418115043),true⟩⟩
  | 5,0 => ⟨⟨2879685079403073283125573,3567122220597537503627803,true⟩,⟨(-4707808350401192447932392),(-3977738254071762383220529),true⟩⟩
  | 5,1 => ⟨⟨2403589869642064614225488,3180168942358113100561413,true⟩,⟨(-5607554146412201179229496),(-4758794896606286007508560),true⟩⟩
  | 5,2 => ⟨⟨1777684358362143948946911,2627468865333984996547792,true⟩,⟨(-6363002672179592736174486),(-5411689811581347875981321),true⟩⟩
  | 5,3 => ⟨⟨1263556989825379710550653,2157005605944937806014626,true⟩,⟨(-6804621307382732137038398),(-5790474005972455313605744),true⟩⟩
  | 5,4 => ⟨⟨3124331791709734843342551,3726590278786341233838110,true⟩,⟨(-3876801284719974329354288),(-3254873111386157097518693),true⟩⟩
  | 5,5 => ⟨⟨3198326858502256356836824,3732612674117239711195749,true⟩,⟨(-3239430407934682045563688),(-2700414224210759819886066),true⟩⟩
  | 5,6 => ⟨⟨3192493697689685943941783,3680428205634567378231817,true⟩,⟨(-2820868419180152305163477),(-2336703155579873068290565),true⟩⟩
  | 5,7 => ⟨⟨3170948194227584090681766,3633839296162396487021364,true⟩,⟨(-2601044010208936724108579),(-2145938847260659992750633),true⟩⟩
  | 6,0 => ⟨⟨(-1903313608775521111074394),(-721241878104157764190088),true⟩,⟨(-7791118507660128104187461),(-6522380603167231418035230),true⟩⟩
  | 6,1 => ⟨⟨(-2993593517508689003017509),(-1735763853633601131838168),true⟩,⟨(-7619590410486784376097485),(-6321504290406543673576071),true⟩⟩
  | 6,2 => ⟨⟨(-3856824435024892413934812),(-2552167957253538792557076),true⟩,⟨(-7281315972294253835261748),(-5985388115917663709808685),true⟩⟩
  | 6,3 => ⟨⟨(-4355540277710919361398698),(-3030597795925348453579357),true⟩,⟨(-6983845483694238877183414),(-5702254312189358275477181),true⟩⟩
  | 6,4 => ⟨⟨(-809381885286103475401580),281226361525300431852073,true⟩,⟨(-7711023287726366106558618),(-6502603270665569984967798),true⟩⟩
  | 6,5 => ⟨⟨92592483901013130536403,1097157567944488973166037,true⟩,⟨(-7452684628832544113116209),(-6317150064612939637678047),true⟩⟩
  | 6,6 => ⟨⟨710493839965264352125287,1654764890728451999472183,true⟩,⟨(-7161124924308649255079175),(-6086642720416384353542642),true⟩⟩
  | 6,7 => ⟨⟨1041766232822276781198236,1956666148861285934913521,true⟩,⟨(-6959790632918451340832860),(-5919967178281660697663882),true⟩⟩
  | 7,0 => ⟨⟨(-6330010022909943865087439),(-5143231140470806444786655),true⟩,⟨(-2959141674571101683362279),(-2119369477269115587392690),true⟩⟩
  | 7,1 => ⟨⟨(-6086499680861307943791514),(-5034314779688617696909094),true⟩,⟨(-1667124812172630221596980),(-1016499897355357022860800),true⟩⟩
  | 7,2 => ⟨⟨(-5668426445196095169674903),(-4743747972511741510690464),true⟩,⟨(-761999595735086681387688),(-259390308143337677985112),true⟩⟩
  | 7,3 => ⟨⟨(-5342867935341533518879735),(-4500998702601288797914930),true⟩,⟨(-290267764112176288341995),137745841999377560692744,true⟩⟩
  | 7,4 => ⟨⟨(-6180542333461595884745264),(-4891741878028830269768971),true⟩,⟨(-4386662145261782140988739),(-3359138448587747510289533),true⟩⟩
  | 7,5 => ⟨⟨(-5661909658687055609724950),(-4326122979560857232932849),true⟩,⟨(-5604667784843014370114090),(-4439891764413463905463205),true⟩⟩
  | 7,6 => ⟨⟨(-5034931289319915208808449),(-3693812635780961327846629),true⟩,⟨(-6412145406030411873385872),(-5171879842380695679978153),true⟩⟩
  | 7,7 => ⟨⟨(-4587110894091246124838664),(-3254915211822670831374380),true⟩,⟨(-6813876294835471615604623),(-5543089644803273359675211),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP514Value0_0 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 0 (0:Fin 8))=sharedDiskP514Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value0_1 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 0 (1:Fin 8))=sharedDiskP514Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value0_2 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 0 (2:Fin 8))=sharedDiskP514Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value0_3 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 0 (3:Fin 8))=sharedDiskP514Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value0_4 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 0 (4:Fin 8))=sharedDiskP514Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value0_5 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 0 (5:Fin 8))=sharedDiskP514Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value0_6 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 0 (6:Fin 8))=sharedDiskP514Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value0_7 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 0 (7:Fin 8))=sharedDiskP514Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP514Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 0 j)=sharedDiskP514Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP514Value0_0
  · exact sharedDiskP514Value0_1
  · exact sharedDiskP514Value0_2
  · exact sharedDiskP514Value0_3
  · exact sharedDiskP514Value0_4
  · exact sharedDiskP514Value0_5
  · exact sharedDiskP514Value0_6
  · exact sharedDiskP514Value0_7
private theorem sharedDiskP514Value1_0 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 1 (0:Fin 8))=sharedDiskP514Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value1_1 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 1 (1:Fin 8))=sharedDiskP514Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value1_2 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 1 (2:Fin 8))=sharedDiskP514Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value1_3 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 1 (3:Fin 8))=sharedDiskP514Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value1_4 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 1 (4:Fin 8))=sharedDiskP514Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value1_5 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 1 (5:Fin 8))=sharedDiskP514Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value1_6 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 1 (6:Fin 8))=sharedDiskP514Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value1_7 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 1 (7:Fin 8))=sharedDiskP514Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP514Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 1 j)=sharedDiskP514Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP514Value1_0
  · exact sharedDiskP514Value1_1
  · exact sharedDiskP514Value1_2
  · exact sharedDiskP514Value1_3
  · exact sharedDiskP514Value1_4
  · exact sharedDiskP514Value1_5
  · exact sharedDiskP514Value1_6
  · exact sharedDiskP514Value1_7
private theorem sharedDiskP514Value2_0 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 2 (0:Fin 8))=sharedDiskP514Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value2_1 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 2 (1:Fin 8))=sharedDiskP514Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value2_2 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 2 (2:Fin 8))=sharedDiskP514Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value2_3 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 2 (3:Fin 8))=sharedDiskP514Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value2_4 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 2 (4:Fin 8))=sharedDiskP514Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value2_5 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 2 (5:Fin 8))=sharedDiskP514Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value2_6 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 2 (6:Fin 8))=sharedDiskP514Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value2_7 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 2 (7:Fin 8))=sharedDiskP514Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP514Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 2 j)=sharedDiskP514Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP514Value2_0
  · exact sharedDiskP514Value2_1
  · exact sharedDiskP514Value2_2
  · exact sharedDiskP514Value2_3
  · exact sharedDiskP514Value2_4
  · exact sharedDiskP514Value2_5
  · exact sharedDiskP514Value2_6
  · exact sharedDiskP514Value2_7
private theorem sharedDiskP514Value3_0 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 3 (0:Fin 8))=sharedDiskP514Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value3_1 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 3 (1:Fin 8))=sharedDiskP514Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value3_2 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 3 (2:Fin 8))=sharedDiskP514Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value3_3 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 3 (3:Fin 8))=sharedDiskP514Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value3_4 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 3 (4:Fin 8))=sharedDiskP514Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value3_5 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 3 (5:Fin 8))=sharedDiskP514Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value3_6 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 3 (6:Fin 8))=sharedDiskP514Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value3_7 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 3 (7:Fin 8))=sharedDiskP514Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP514Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 3 j)=sharedDiskP514Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP514Value3_0
  · exact sharedDiskP514Value3_1
  · exact sharedDiskP514Value3_2
  · exact sharedDiskP514Value3_3
  · exact sharedDiskP514Value3_4
  · exact sharedDiskP514Value3_5
  · exact sharedDiskP514Value3_6
  · exact sharedDiskP514Value3_7
private theorem sharedDiskP514Value4_0 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 4 (0:Fin 8))=sharedDiskP514Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value4_1 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 4 (1:Fin 8))=sharedDiskP514Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value4_2 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 4 (2:Fin 8))=sharedDiskP514Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value4_3 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 4 (3:Fin 8))=sharedDiskP514Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value4_4 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 4 (4:Fin 8))=sharedDiskP514Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value4_5 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 4 (5:Fin 8))=sharedDiskP514Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value4_6 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 4 (6:Fin 8))=sharedDiskP514Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value4_7 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 4 (7:Fin 8))=sharedDiskP514Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP514Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 4 j)=sharedDiskP514Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP514Value4_0
  · exact sharedDiskP514Value4_1
  · exact sharedDiskP514Value4_2
  · exact sharedDiskP514Value4_3
  · exact sharedDiskP514Value4_4
  · exact sharedDiskP514Value4_5
  · exact sharedDiskP514Value4_6
  · exact sharedDiskP514Value4_7
private theorem sharedDiskP514Value5_0 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 5 (0:Fin 8))=sharedDiskP514Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value5_1 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 5 (1:Fin 8))=sharedDiskP514Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value5_2 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 5 (2:Fin 8))=sharedDiskP514Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value5_3 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 5 (3:Fin 8))=sharedDiskP514Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value5_4 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 5 (4:Fin 8))=sharedDiskP514Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value5_5 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 5 (5:Fin 8))=sharedDiskP514Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value5_6 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 5 (6:Fin 8))=sharedDiskP514Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value5_7 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 5 (7:Fin 8))=sharedDiskP514Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP514Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 5 j)=sharedDiskP514Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP514Value5_0
  · exact sharedDiskP514Value5_1
  · exact sharedDiskP514Value5_2
  · exact sharedDiskP514Value5_3
  · exact sharedDiskP514Value5_4
  · exact sharedDiskP514Value5_5
  · exact sharedDiskP514Value5_6
  · exact sharedDiskP514Value5_7
private theorem sharedDiskP514Value6_0 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 6 (0:Fin 8))=sharedDiskP514Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value6_1 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 6 (1:Fin 8))=sharedDiskP514Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value6_2 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 6 (2:Fin 8))=sharedDiskP514Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value6_3 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 6 (3:Fin 8))=sharedDiskP514Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value6_4 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 6 (4:Fin 8))=sharedDiskP514Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value6_5 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 6 (5:Fin 8))=sharedDiskP514Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value6_6 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 6 (6:Fin 8))=sharedDiskP514Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value6_7 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 6 (7:Fin 8))=sharedDiskP514Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP514Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 6 j)=sharedDiskP514Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP514Value6_0
  · exact sharedDiskP514Value6_1
  · exact sharedDiskP514Value6_2
  · exact sharedDiskP514Value6_3
  · exact sharedDiskP514Value6_4
  · exact sharedDiskP514Value6_5
  · exact sharedDiskP514Value6_6
  · exact sharedDiskP514Value6_7
private theorem sharedDiskP514Value7_0 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 7 (0:Fin 8))=sharedDiskP514Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value7_1 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 7 (1:Fin 8))=sharedDiskP514Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value7_2 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 7 (2:Fin 8))=sharedDiskP514Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value7_3 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 7 (3:Fin 8))=sharedDiskP514Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value7_4 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 7 (4:Fin 8))=sharedDiskP514Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value7_5 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 7 (5:Fin 8))=sharedDiskP514Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value7_6 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 7 (6:Fin 8))=sharedDiskP514Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP514Value7_7 : truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 7 (7:Fin 8))=sharedDiskP514Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP514Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points 7 j)=sharedDiskP514Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP514Value7_0
  · exact sharedDiskP514Value7_1
  · exact sharedDiskP514Value7_2
  · exact sharedDiskP514Value7_3
  · exact sharedDiskP514Value7_4
  · exact sharedDiskP514Value7_5
  · exact sharedDiskP514Value7_6
  · exact sharedDiskP514Value7_7
theorem sharedDiskP514Values_eq : ∀ (i : Fin 8) (j : Fin 8), truncatedChordCell 2 sharedDiskP514Params (sharedChord514Gauss8Points i j)=sharedDiskP514Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP514Values0_eq
  · exact sharedDiskP514Values1_eq
  · exact sharedDiskP514Values2_eq
  · exact sharedDiskP514Values3_eq
  · exact sharedDiskP514Values4_eq
  · exact sharedDiskP514Values5_eq
  · exact sharedDiskP514Values6_eq
  · exact sharedDiskP514Values7_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP514Box : HorizontalRectangle := ⟨(3/4),(301/400),(921051395650439/1649267441664000),(927493846594439/1649267441664000),(849827551552802675209193522178031/1298074214633706907132624082305024),(2416768609321983355862482723776495/1298074214633706907132624082305024),(-2325982852391133697316739725372557/649037107316853453566312041152512),(-1523832867332744951057024382643341/649037107316853453566312041152512),true,[]⟩
noncomputable def sharedDiskP514Grid : CGrid := momentChordGrid sharedDiskP514Params chordGaussRule8 2 sharedChord514Bd sharedChord514M (23175049/18014398509481984)
theorem sharedDiskP514Columns : containedInReported sharedDiskP514Grid.re sharedDiskP514Box.reLo sharedDiskP514Box.reHi=true ∧ containedInReported sharedDiskP514Grid.im sharedDiskP514Box.imLo sharedDiskP514Box.imHi=true := by
  rw [sharedDiskP514Grid,momentChordGrid_eq_tabulated sharedDiskP514Params chordGaussRule8 2 sharedChord514Bd sharedChord514M (23175049/18014398509481984) sharedChord514Gauss8Points sharedChord514Gauss8Weights sharedDiskP514Values sharedChord514Gauss8Points_eq sharedChord514Gauss8Weights_eq sharedDiskP514Values_eq]
  decide +kernel
theorem sharedDiskP514Sound : sharedDiskP514Box.Sound := by
  intro t a tl tu al au
  change (((3/4):ℚ):ℝ)≤t at tl
  change t≤(((301/400):ℚ):ℝ) at tu
  change (((921051395650439/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((927493846594439/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP514Params_ok] at ps
  have band := sharedChord514ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3/4):ℚ)≤(3/4))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((301/400):ℚ)≤(77/100)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((921051395650439/1649267441664000):ℚ)≤(921051395650439/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((927493846594439/1649267441664000):ℚ)≤(311497591431881/549755813888000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord514Bd (by decide +kernel) (by decide +kernel) sharedChord514M (by decide +kernel) (sharedChord514Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP514Columns.1 sharedDiskP514Columns.2
def sharedDiskP514Rows : List SignRow := [positive_514.toSignRow]
theorem sharedDiskP514Rows_actual : ∀ r∈sharedDiskP514Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP514Rows.all (sharedDiskP514Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP514Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP515Params : ChordParams := ⟨⟨(-18848580756296183300627),(-18589809117529908670000),true⟩,⟨2198233232649125425927693,2225251617940507168321509,true⟩,⟨115236948307584317287392,118040481901925363225610,true⟩,⟨191867013785039139702483,196203341878001540682660,true⟩,⟨295221761106569534744533,297332082331203149815367,true⟩,⟨1171807378421371187092526,1172309258981342023763444,true⟩,⟨(-2447121698173474046696587),(-2437974471172777833196178),true⟩,⟨⟨1149778038957783142144852,1191583299425262468947518,true⟩,⟨(-801401),801401,true⟩⟩⟩
theorem sharedDiskP515Params_ok : chordParams (Grid.ofRats (301/400) (151/200)) (Grid.ofRats (307370705156169/549755813888000) (309518188804169/549755813888000))=sharedDiskP515Params := by decide +kernel
def sharedDiskP515Values (i : Fin 8) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3266367194603022110827439),(-2627360547632633627139734),true⟩,⟨(-451245262884966370087505),54264444786203796114234,true⟩⟩
  | 0,1 => ⟨⟨(-2821591153125477931141958),(-2245574195022919303549645),true⟩,⟨(-538481324599307850236904),(-65247105726779257250576),true⟩⟩
  | 0,2 => ⟨⟨(-2508153573230025929716953),(-1979504275546506235097150),true⟩,⟨(-607317439616696280172014),(-162322751617719455216829),true⟩⟩
  | 0,3 => ⟨⟨(-2334558445705264574490593),(-1832844982862654942300264),true⟩,⟨(-647544777633899936686274),(-219443345470411134585471),true⟩⟩
  | 0,4 => ⟨⟨(-3807642233273378970725436),(-3100880213789031146068938),true⟩,⟨(-364811731378581962375029),162215734766186930300245,true⟩⟩
  | 0,5 => ⟨⟨(-4373680767914994544733693),(-3606518855375629731796802),true⟩,⟨(-301010961237317629939934),229762229732868432372818,true⟩⟩
  | 0,6 => ⟨⟨(-4862260809920333046932418),(-4051369064794760328753843),true⟩,⟨(-269843430541168412160737),247026580772708940386496,true⟩⟩
  | 0,7 => ⟨⟨(-5172787211764411456193936),(-4337626844813531769429131),true⟩,⟨(-269383837828726692976371),236078053620530232901492,true⟩⟩
  | 1,0 => ⟨⟨(-1322551068913676039202902),(-985871858473763008674391),true⟩,⟨(-887499916564214223378477),(-577773916572174579904030),true⟩⟩
  | 1,1 => ⟨⟨(-1107472771919195499865548),(-805515055940585118999756),true⟩,⟨(-932322667132349674865186),(-649432589448889052354299),true⟩⟩
  | 1,2 => ⟨⟨(-952113652372149412235339),(-674608571204566548663908),true⟩,⟨(-961170941393123616450198),(-697408104722371888546459),true⟩⟩
  | 1,3 => ⟨⟨(-863986304136385031350299),(-600049702954364258515813),true⟩,⟨(-975889651432289765073905),(-722812681791895965821807),true⟩⟩
  | 1,4 => ⟨⟨(-1581328404044476257982769),(-1202095978056837388537368),true⟩,⟨(-828449471358924856218603),(-486484219654141508431742),true⟩⟩
  | 1,5 => ⟨⟨(-1854161378881362906957608),(-1429909583767194229185456),true⟩,⟨(-763038876353678064365747),(-388019645261094335544442),true⟩⟩
  | 1,6 => ⟨⟨(-2095899061484215438358891),(-1632227892454766230868765),true⟩,⟨(-704470262388105236608413),(-301717579693286004572208),true⟩⟩
  | 1,7 => ⟨⟨(-2254133666909616131142070),(-1765120742097828523245395),true⟩,⟨(-666556377533152761885266),(-246739977563570423943113),true⟩⟩
  | 2,0 => ⟨⟨96132369429240957479441,267995012176414583139805,true⟩,⟨(-1040128453043585432365124),(-856584695533243868020538),true⟩⟩
  | 2,1 => ⟨⟨299337296391690024794118,463672429938930904505995,true⟩,⟨(-1021228675999926198263171),(-846169722102504875444397),true⟩⟩
  | 2,2 => ⟨⟨444040744505030215037132,608179886914815741378956,true⟩,⟨(-1002690389309631864032102),(-830483675162137222899387),true⟩⟩
  | 2,3 => ⟨⟨526698881971326560349788,691021227433220760291638,true⟩,⟨(-989834700867802664984031),(-819031066871166078804168),true⟩⟩
  | 2,4 => ⟨⟨(-148240007190651517125183),39962747727419986245160,true⟩,⟨(-1047239399867517418390524),(-849639639842607339951938),true⟩⟩
  | 2,5 => ⟨⟨(-408051131245461629352133),(-197253290758563824842726),true⟩,⟨(-1035892888811789110818700),(-821306539547984991623973),true⟩⟩
  | 2,6 => ⟨⟨(-642707003398406708384094),(-407642864095159688098354),true⟩,⟨(-1010222955248536083490645),(-778487941293114699210326),true⟩⟩
  | 2,7 => ⟨⟨(-802241749511651182337739),(-546772170753080431666191),true⟩,⟨(-986352889035437659951619),(-739570938996282547301166),true⟩⟩
  | 3,0 => ⟨⟨1474630961461457626283651,1653366962262350282561706,true⟩,⟨(-805605410695666417888781),(-638853332308417008350115),true⟩⟩
  | 3,1 => ⟨⟨1688196519110736073793680,1873527760125725640463859,true⟩,⟨(-788597159129506225467284),(-618581171753745737519516),true⟩⟩
  | 3,2 => ⟨⟨1849692385310003858555347,2041312443006454276349111,true⟩,⟨(-794463427788763114694345),(-620267716976063083724733),true⟩⟩
  | 3,3 => ⟨⟨1945445305716673262048657,2141466897291107969604674,true⟩,⟨(-807899143394529249428762),(-630367876874542626520280),true⟩⟩
  | 3,4 => ⟨⟨1225728869003692390421064,1398595833502979613842080,true⟩,⟨(-847719221603546878439245),(-682339731111110043690414),true⟩⟩
  | 3,5 => ⟨⟨966747117876506101219796,1135115043180435419029402,true⟩,⟨(-902595429143363797065097),(-736599412859420856817271),true⟩⟩
  | 3,6 => ⟨⟨736826414531453766874324,902478691610163524684682,true⟩,⟨(-951168364959772900755105),(-783217694916739955411315),true⟩⟩
  | 3,7 => ⟨⟨584876929523479596142310,749447749858334290738714,true⟩,⟨(-979915384541655637592613),(-810003355458518909566021),true⟩⟩
  | 4,0 => ⟨⟨2674513681538219501561076,2971601091190118310550090,true⟩,⟨(-1318201085507897641567650),(-1043745748559706965695515),true⟩⟩
  | 4,1 => ⟨⟨2893800284392394340781582,3243504438205372260454093,true⟩,⟨(-1692468866019342796791077),(-1362780066305300921725495),true⟩⟩
  | 4,2 => ⟨⟨3054289099827345963023863,3459774188052367119182412,true⟩,⟨(-2131588579399844406003860),(-1740901159021706097991340),true⟩⟩
  | 4,3 => ⟨⟨3130662868028091546665167,3577884148712480321052452,true⟩,⟨(-2481524425403830555661671),(-2043741042426870004652842),true⟩⟩
  | 4,4 => ⟨⟨2444921583320725454447822,2700745265160498746311674,true⟩,⟨(-1064320090774611882695630),(-831266758705745927720172),true⟩⟩
  | 4,5 => ⟨⟨2241168527881750610409820,2468109675570489232567715,true⟩,⟨(-918358764019110748317389),(-712978429031927467663411),true⟩⟩
  | 4,6 => ⟨⟨2084759500473405743786781,2293491801465034891855215,true⟩,⟨(-846564424458660326992958),(-657893889709981649400059),true⟩⟩
  | 4,7 => ⟨⟨1991263954056676675688187,2190568207493899580036581,true⟩,⟨(-817914903634606234655622),(-637609581549807858440105),true⟩⟩
  | 5,0 => ⟨⟨2838806074827182216396565,3527168368326644386551237,true⟩,⟨(-4737059268897305718563921),(-4004909005044047369415184),true⟩⟩
  | 5,1 => ⟨⟨2352573563219923708246388,3129335727159695178628047,true⟩,⟨(-5630926872874911247169834),(-4780891184176760869952354),true⟩⟩
  | 5,2 => ⟨⟨1718759277817538568348986,2567744217171980625543234,true⟩,⟨(-6377037547537302628671151),(-5425646152990644718888142),true⟩⟩
  | 5,3 => ⟨⟨1198891138096616373501175,2092634727096319233833251,true⟩,⟨(-6811524571644644261645300),(-5797310458538601135213573),true⟩⟩
  | 5,4 => ⟨⟨3092618762452905023711580,3696166593851624756617859,true⟩,⟨(-3907635198671677652524256),(-3283323445117218880567226),true⟩⟩
  | 5,5 => ⟨⟨3173098537916288094390761,3708768990082596442146951,true⟩,⟨(-3269362439734900947647088),(-2727965394069652413860619),true⟩⟩
  | 5,6 => ⟨⟨3171103048188556623089311,3660401241781485901066141,true⟩,⟨(-2849296915662120239496512),(-2362853480355122953663456),true⟩⟩
  | 5,7 => ⟨⟨3151396872800206519635481,3615613988204266338122650,true⟩,⟨(-2628406333336680280689807),(-2171107847952621461015630),true⟩⟩
  | 6,0 => ⟨⟨(-1961688596596654282330705),(-781586296670173690864531),true⟩,⟨(-7751069028929941348439332),(-6487702908926706746249482),true⟩⟩
  | 6,1 => ⟨⟨(-3040462579279919994635999),(-1786570953126911597686582),true⟩,⟨(-7566788512784999741511446),(-6276247900251531341417524),true⟩⟩
  | 6,2 => ⟨⟨(-3891455168804276258821469),(-2592375855331598602045231),true⟩,⟨(-7220848912722201510315378),(-5934019669456253359332757),true⟩⟩
  | 6,3 => ⟨⟨(-4381756528750878644776137),(-3063356400280374814823577),true⟩,⟨(-6920338284578533960751137),(-5648624265373500281373760),true⟩⟩
  | 6,4 => ⟨⟨(-874861021444075112845476),215346580426907720143065,true⟩,⟨(-7686085166656574715235973),(-6480759967980500073408179),true⟩⟩
  | 6,5 => ⟨⟨25108871806996980395075,1030356144816299363791641,true⟩,⟨(-7441312657902640358415816),(-6307005235002456015697519),true⟩⟩
  | 6,6 => ⟨⟨643593474754682103460293,1587415288808353357613046,true⟩,⟨(-7159380983975273599991576),(-6085915525373286480792831),true⟩⟩
  | 6,7 => ⟨⟨975991608972014052746629,1890891403792465108557067,true⟩,⟨(-6963234276306744621839383),(-5923773995705069908992719),true⟩⟩
  | 7,0 => ⟨⟨(-6302174223239511471044891),(-5124703559749282758767042),true⟩,⟨(-2921783387076870268609298),(-2090511249191393347794968),true⟩⟩
  | 7,1 => ⟨⟨(-6056879869302384262686770),(-5012565531494791228950878),true⟩,⟨(-1646517788962490606400317),(-1001891529525237808413732),true⟩⟩
  | 7,2 => ⟨⟨(-5642218267424068517071084),(-4723777716826584220390408),true⟩,⟨(-753274892782977680127003),(-254669988203652081308770),true⟩⟩
  | 7,3 => ⟨⟨(-5320275347998587242732047),(-4483509899088835808152220),true⟩,⟨(-287412893741166357872458),137747811266764543698821,true⟩⟩
  | 7,4 => ⟨⟨(-6162975239202563651540038),(-4883878543914615653513294),true⟩,⟨(-4333259472783937831977531),(-3316129890560405821470503),true⟩⟩
  | 7,5 => ⟨⟨(-5660134378616656737197923),(-4333344127831613636078950),true⟩,⟨(-5541800469210074446529130),(-4388052679396774053813415),true⟩⟩
  | 7,6 => ⟨⟨(-5047864415742850593614160),(-3714598080246046484476731),true⟩,⟨(-6346881697420728836148276),(-5117320036435891804930135),true⟩⟩
  | 7,7 => ⟨⟨(-4609053074275125915926086),(-3283848711185284314263867),true⟩,⟨(-6749410739445437350070538),(-5488819705690359934446906),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP515Value0_0 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 0 (0:Fin 8))=sharedDiskP515Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value0_1 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 0 (1:Fin 8))=sharedDiskP515Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value0_2 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 0 (2:Fin 8))=sharedDiskP515Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value0_3 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 0 (3:Fin 8))=sharedDiskP515Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value0_4 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 0 (4:Fin 8))=sharedDiskP515Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value0_5 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 0 (5:Fin 8))=sharedDiskP515Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value0_6 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 0 (6:Fin 8))=sharedDiskP515Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value0_7 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 0 (7:Fin 8))=sharedDiskP515Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP515Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 0 j)=sharedDiskP515Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP515Value0_0
  · exact sharedDiskP515Value0_1
  · exact sharedDiskP515Value0_2
  · exact sharedDiskP515Value0_3
  · exact sharedDiskP515Value0_4
  · exact sharedDiskP515Value0_5
  · exact sharedDiskP515Value0_6
  · exact sharedDiskP515Value0_7
private theorem sharedDiskP515Value1_0 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 1 (0:Fin 8))=sharedDiskP515Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value1_1 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 1 (1:Fin 8))=sharedDiskP515Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value1_2 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 1 (2:Fin 8))=sharedDiskP515Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value1_3 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 1 (3:Fin 8))=sharedDiskP515Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value1_4 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 1 (4:Fin 8))=sharedDiskP515Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value1_5 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 1 (5:Fin 8))=sharedDiskP515Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value1_6 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 1 (6:Fin 8))=sharedDiskP515Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value1_7 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 1 (7:Fin 8))=sharedDiskP515Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP515Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 1 j)=sharedDiskP515Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP515Value1_0
  · exact sharedDiskP515Value1_1
  · exact sharedDiskP515Value1_2
  · exact sharedDiskP515Value1_3
  · exact sharedDiskP515Value1_4
  · exact sharedDiskP515Value1_5
  · exact sharedDiskP515Value1_6
  · exact sharedDiskP515Value1_7
private theorem sharedDiskP515Value2_0 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 2 (0:Fin 8))=sharedDiskP515Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value2_1 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 2 (1:Fin 8))=sharedDiskP515Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value2_2 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 2 (2:Fin 8))=sharedDiskP515Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value2_3 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 2 (3:Fin 8))=sharedDiskP515Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value2_4 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 2 (4:Fin 8))=sharedDiskP515Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value2_5 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 2 (5:Fin 8))=sharedDiskP515Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value2_6 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 2 (6:Fin 8))=sharedDiskP515Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value2_7 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 2 (7:Fin 8))=sharedDiskP515Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP515Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 2 j)=sharedDiskP515Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP515Value2_0
  · exact sharedDiskP515Value2_1
  · exact sharedDiskP515Value2_2
  · exact sharedDiskP515Value2_3
  · exact sharedDiskP515Value2_4
  · exact sharedDiskP515Value2_5
  · exact sharedDiskP515Value2_6
  · exact sharedDiskP515Value2_7
private theorem sharedDiskP515Value3_0 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 3 (0:Fin 8))=sharedDiskP515Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value3_1 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 3 (1:Fin 8))=sharedDiskP515Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value3_2 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 3 (2:Fin 8))=sharedDiskP515Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value3_3 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 3 (3:Fin 8))=sharedDiskP515Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value3_4 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 3 (4:Fin 8))=sharedDiskP515Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value3_5 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 3 (5:Fin 8))=sharedDiskP515Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value3_6 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 3 (6:Fin 8))=sharedDiskP515Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value3_7 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 3 (7:Fin 8))=sharedDiskP515Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP515Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 3 j)=sharedDiskP515Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP515Value3_0
  · exact sharedDiskP515Value3_1
  · exact sharedDiskP515Value3_2
  · exact sharedDiskP515Value3_3
  · exact sharedDiskP515Value3_4
  · exact sharedDiskP515Value3_5
  · exact sharedDiskP515Value3_6
  · exact sharedDiskP515Value3_7
private theorem sharedDiskP515Value4_0 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 4 (0:Fin 8))=sharedDiskP515Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value4_1 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 4 (1:Fin 8))=sharedDiskP515Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value4_2 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 4 (2:Fin 8))=sharedDiskP515Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value4_3 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 4 (3:Fin 8))=sharedDiskP515Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value4_4 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 4 (4:Fin 8))=sharedDiskP515Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value4_5 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 4 (5:Fin 8))=sharedDiskP515Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value4_6 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 4 (6:Fin 8))=sharedDiskP515Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value4_7 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 4 (7:Fin 8))=sharedDiskP515Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP515Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 4 j)=sharedDiskP515Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP515Value4_0
  · exact sharedDiskP515Value4_1
  · exact sharedDiskP515Value4_2
  · exact sharedDiskP515Value4_3
  · exact sharedDiskP515Value4_4
  · exact sharedDiskP515Value4_5
  · exact sharedDiskP515Value4_6
  · exact sharedDiskP515Value4_7
private theorem sharedDiskP515Value5_0 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 5 (0:Fin 8))=sharedDiskP515Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value5_1 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 5 (1:Fin 8))=sharedDiskP515Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value5_2 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 5 (2:Fin 8))=sharedDiskP515Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value5_3 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 5 (3:Fin 8))=sharedDiskP515Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value5_4 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 5 (4:Fin 8))=sharedDiskP515Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value5_5 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 5 (5:Fin 8))=sharedDiskP515Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value5_6 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 5 (6:Fin 8))=sharedDiskP515Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value5_7 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 5 (7:Fin 8))=sharedDiskP515Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP515Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 5 j)=sharedDiskP515Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP515Value5_0
  · exact sharedDiskP515Value5_1
  · exact sharedDiskP515Value5_2
  · exact sharedDiskP515Value5_3
  · exact sharedDiskP515Value5_4
  · exact sharedDiskP515Value5_5
  · exact sharedDiskP515Value5_6
  · exact sharedDiskP515Value5_7
private theorem sharedDiskP515Value6_0 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 6 (0:Fin 8))=sharedDiskP515Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value6_1 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 6 (1:Fin 8))=sharedDiskP515Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value6_2 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 6 (2:Fin 8))=sharedDiskP515Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value6_3 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 6 (3:Fin 8))=sharedDiskP515Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value6_4 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 6 (4:Fin 8))=sharedDiskP515Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value6_5 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 6 (5:Fin 8))=sharedDiskP515Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value6_6 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 6 (6:Fin 8))=sharedDiskP515Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value6_7 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 6 (7:Fin 8))=sharedDiskP515Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP515Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 6 j)=sharedDiskP515Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP515Value6_0
  · exact sharedDiskP515Value6_1
  · exact sharedDiskP515Value6_2
  · exact sharedDiskP515Value6_3
  · exact sharedDiskP515Value6_4
  · exact sharedDiskP515Value6_5
  · exact sharedDiskP515Value6_6
  · exact sharedDiskP515Value6_7
private theorem sharedDiskP515Value7_0 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 7 (0:Fin 8))=sharedDiskP515Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value7_1 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 7 (1:Fin 8))=sharedDiskP515Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value7_2 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 7 (2:Fin 8))=sharedDiskP515Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value7_3 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 7 (3:Fin 8))=sharedDiskP515Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value7_4 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 7 (4:Fin 8))=sharedDiskP515Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value7_5 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 7 (5:Fin 8))=sharedDiskP515Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value7_6 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 7 (6:Fin 8))=sharedDiskP515Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP515Value7_7 : truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 7 (7:Fin 8))=sharedDiskP515Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP515Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points 7 j)=sharedDiskP515Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP515Value7_0
  · exact sharedDiskP515Value7_1
  · exact sharedDiskP515Value7_2
  · exact sharedDiskP515Value7_3
  · exact sharedDiskP515Value7_4
  · exact sharedDiskP515Value7_5
  · exact sharedDiskP515Value7_6
  · exact sharedDiskP515Value7_7
theorem sharedDiskP515Values_eq : ∀ (i : Fin 8) (j : Fin 8), truncatedChordCell 2 sharedDiskP515Params (sharedChord514Gauss8Points i j)=sharedDiskP515Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP515Values0_eq
  · exact sharedDiskP515Values1_eq
  · exact sharedDiskP515Values2_eq
  · exact sharedDiskP515Values3_eq
  · exact sharedDiskP515Values4_eq
  · exact sharedDiskP515Values5_eq
  · exact sharedDiskP515Values6_eq
  · exact sharedDiskP515Values7_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP515Box : HorizontalRectangle := ⟨(301/400),(151/200),(307370705156169/549755813888000),(309518188804169/549755813888000),(409788564069802636906909629261965/649037107316853453566312041152512),(1185615694518728253100720498780301/649037107316853453566312041152512),(-4651548883660313206707940140093149/1298074214633706907132624082305024),(-3063096482745551604343156123995869/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP515Grid : CGrid := momentChordGrid sharedDiskP515Params chordGaussRule8 2 sharedChord514Bd sharedChord514M (23175049/18014398509481984)
theorem sharedDiskP515Columns : containedInReported sharedDiskP515Grid.re sharedDiskP515Box.reLo sharedDiskP515Box.reHi=true ∧ containedInReported sharedDiskP515Grid.im sharedDiskP515Box.imLo sharedDiskP515Box.imHi=true := by
  rw [sharedDiskP515Grid,momentChordGrid_eq_tabulated sharedDiskP515Params chordGaussRule8 2 sharedChord514Bd sharedChord514M (23175049/18014398509481984) sharedChord514Gauss8Points sharedChord514Gauss8Weights sharedDiskP515Values sharedChord514Gauss8Points_eq sharedChord514Gauss8Weights_eq sharedDiskP515Values_eq]
  decide +kernel
theorem sharedDiskP515Sound : sharedDiskP515Box.Sound := by
  intro t a tl tu al au
  change (((301/400):ℚ):ℝ)≤t at tl
  change t≤(((151/200):ℚ):ℝ) at tu
  change (((307370705156169/549755813888000):ℚ):ℝ)≤a at al
  change a≤(((309518188804169/549755813888000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP515Params_ok] at ps
  have band := sharedChord514ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3/4):ℚ)≤(301/400))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((151/200):ℚ)≤(77/100)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((921051395650439/1649267441664000):ℚ)≤(307370705156169/549755813888000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((309518188804169/549755813888000):ℚ)≤(311497591431881/549755813888000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord514Bd (by decide +kernel) (by decide +kernel) sharedChord514M (by decide +kernel) (sharedChord514Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP515Columns.1 sharedDiskP515Columns.2
def sharedDiskP515Rows : List SignRow := [positive_515.toSignRow]
theorem sharedDiskP515Rows_actual : ∀ r∈sharedDiskP515Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP515Rows.all (sharedDiskP515Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP515Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP516Params : ChordParams := ⟨⟨(-19109210758516906919226),(-18848580756296183300212),true⟩,⟨2187736013355147974035389,2214630174790286805189839,true⟩,⟨115825258499838154753575,118631699339813322324983,true⟩,⟨193560155899887062984373,197914412331186692933204,true⟩,⟨297206324704049808577135,299317615384332969861085,true⟩,⟨1171302107412528277033480,1171807378421371187093332,true⟩,⟨(-2437974471172777833205621),(-2428880591274879035266655),true⟩,⟨⟨1149181248746027595557903,1191083357765937329513159,true⟩,⟨(-928006),928006,true⟩⟩⟩
theorem sharedDiskP516Params_ok : chordParams (Grid.ofRats (151/200) (303/400)) (Grid.ofRats (61545244267357/109951162777600) (61974740996957/109951162777600))=sharedDiskP516Params := by decide +kernel
def sharedDiskP516Values (i : Fin 8) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3265756747557690281565197),(-2627820262073194347230350),true⟩,⟨(-446828450174376649745740),57372232432215351857772,true⟩⟩
  | 0,1 => ⟨⟨(-2824383737943217143690065),(-2248824362337778316989595),true⟩,⟨(-532916411610243078986057),(-60429965599265140519542),true⟩⟩
  | 0,2 => ⟨⟨(-2512960848987818717949949),(-1984448380621527717766996),true⟩,⟨(-601026285925911403676967),(-156565470142989090389041),true⟩⟩
  | 0,3 => ⟨⟨(-2340420949641304603227740),(-1838638127011710321910634),true⟩,⟨(-640903647523169405755466),(-213135430806333585443933),true⟩⟩
  | 0,4 => ⟨⟨(-3802270503566726577564258),(-3097304944300610989143528),true⟩,⟨(-361807278882339472646284),163360216911862934828188,true⟩⟩
  | 0,5 => ⟨⟨(-4362687964578696592751812),(-3598009812980820403373495),true⟩,⟨(-299297565975616476779344),229355147802748929966255,true⟩⟩
  | 0,6 => ⟨⟨(-4845974728023658407281384),(-4038086519534049039805517),true⟩,⟨(-268951929190077384828970),245786933193231205334984,true⟩⟩
  | 0,7 => ⟨⟨(-5152976352081377426261416),(-4321101392091268737169853),true⟩,⟨(-268852382409888855867548),234665792838901427329069,true⟩⟩
  | 1,0 => ⟨⟨(-1333287915966653606104963),(-995662310440318829851340),true⟩,⟨(-880199884410879707233083),(-569959767669555966198763),true⟩⟩
  | 1,1 => ⟨⟨(-1119041707609797397458058),(-816044705876652824891948),true⟩,⟨(-925322356316825741648268),(-641836030708318668003969),true⟩⟩
  | 1,2 => ⟨⟨(-964262458541024125032254),(-685671092440509742076645),true⟩,⟨(-954508804045718622535624),(-690109631990349670408384),true⟩⟩
  | 1,3 => ⟨⟨(-876459321037569843411621),(-611416398670949842477666),true⟩,⟨(-969466535859912684472391),(-715736384895146906848318),true⟩⟩
  | 1,4 => ⟨⟨(-1590993923412291830017187),(-1210973039235081999223566),true⟩,⟨(-821026435032841252796266),(-478693168483679252472691),true⟩⟩
  | 1,5 => ⟨⟨(-1862582549159916900223464),(-1437762392284601511499154),true⟩,⟨(-755729347073658880763835),(-380553496166992905022061),true⟩⟩
  | 1,6 => ⟨⟨(-2103096401589524079460035),(-1639092624838319495677698),true⟩,⟨(-697433495409492354184608),(-294755240645293757528568),true⟩⟩
  | 1,7 => ⟨⟨(-2260460694008851127877911),(-1771286778864208426954253),true⟩,⟨(-659769744839076596346885),(-240196648479211481882360),true⟩⟩
  | 2,0 => ⟨⟨80537952332681324826030,252676925594467219920814,true⟩,⟨(-1038144911989241739649514),(-854510069602122306861202),true⟩⟩
  | 2,1 => ⟨⟨283100993009581001270685,447265124842420024615068,true⟩,⟨(-1020583402514223921058790),(-845654327309544867981307),true⟩⟩
  | 2,2 => ⟨⟨427650872366391577075597,591285446646526392750407,true⟩,⟨(-1002870053210046269536116),(-830967373576422005546622),true⟩⟩
  | 2,3 => ⟨⟨510071666535441915978217,673876778677390957188520,true⟩,⟨(-990597121105958356037214),(-820084479659331831081314),true⟩⟩
  | 2,4 => ⟨⟨(-163013191181887488443639),25582902564773398163639,true⟩,⟨(-1043723214133856176906240),(-846058383522486894138258),true⟩⟩
  | 2,5 => ⟨⟨(-421883308144292611668350),(-210570108687202022718671),true⟩,⟨(-1030957380220996357841505),(-816319428700726873889405),true⟩⟩
  | 2,6 => ⟨⟨(-655702610397060968765260),(-420060638098826247502359),true⟩,⟨(-1004243272825171180509480),(-772463064908422227316336),true⟩⟩
  | 2,7 => ⟨⟨(-814940727944828485832059),(-558598833096789962003917),true⟩,⟨(-979858210817285494820844),(-732714115296487390931282),true⟩⟩
  | 3,0 => ⟨⟨1457535909018008687026606,1635947602215792714975023,true⟩,⟨(-812585598552065919714464),(-645761422307181725721678),true⟩⟩
  | 3,1 => ⟨⟨1671760217832269339222650,1856910308875044254850207,true⟩,⟨(-796868112072912872953372),(-626633937794627012281074),true⟩⟩
  | 3,2 => ⟨⟨1833917583083465302416904,2025490161343681876953981,true⟩,⟨(-803749409220598192750697),(-629206385191318261247991),true⟩⟩
  | 3,3 => ⟨⟨1930105829081966143259443,2126168997737025833531937,true⟩,⟨(-817823542978228667546344),(-639860521744074986421155),true⟩⟩
  | 3,4 => ⟨⟨1208244084330530378283116,1380668854375898810577139,true⟩,⟨(-853177035639089602645966),(-687862844297245461475974),true⟩⟩
  | 3,5 => ⟨⟨949284944247055941799611,1117141557058057714933717,true⟩,⟨(-906386503788389289646584),(-740564999641092268586319),true⟩⟩
  | 3,6 => ⟨⟨719696781889886612177881,884818407481486510299211,true⟩,⟨(-953400575105248342738233),(-785695477864293563748270),true⟩⟩
  | 3,7 => ⟨⟨568094902731596935521175,732141998227155471006810,true⟩,⟨(-981087266399131309856479),(-811455443530061753662241),true⟩⟩
  | 4,0 => ⟨⟨2661510716476049004649537,2959266461770429480131954,true⟩,⟨(-1335351477868556020324272),(-1059678836845263344305599),true⟩⟩
  | 4,1 => ⟨⟨2879784469062408679022083,3230419455738255694399719,true⟩,⟨(-1713182630904594544911272),(-1381919465461456984752853),true⟩⟩
  | 4,2 => ⟨⟨3037935823740186812274674,3444567138524968904990947,true⟩,⟨(-2155730323460007713680018),(-1763146711727554316674614),true⟩⟩
  | 4,3 => ⟨⟨3111843318308179504331499,3560323091953784510910464,true⟩,⟨(-2507864570918454852704120),(-2067992403512820439570635),true⟩⟩
  | 4,4 => ⟨⟨2431736854222851594686966,2687990634887184967995209,true⟩,⟨(-1078583233228880139192088),(-844618823028386663895775),true⟩⟩
  | 4,5 => ⟨⟨2227255297834230390188242,2454448032815883248448253,true⟩,⟨(-930592108623331437845342),(-724524006817582624880956),true⟩⟩
  | 4,6 => ⟨⟨2070107768430089673230575,2278976829164894193286000,true⟩,⟨(-857500845801687843171947),(-668285682510727135982413),true⟩⟩
  | 4,7 => ⟨⟨1976145470649764946243770,2175527204094247447168821,true⟩,⟨(-828159494982167394636828),(-647384176967417866636525),true⟩⟩
  | 5,0 => ⟨⟨2797499533950020028889709,3486710866070674423476073,true⟩,⟨(-4765531344931683731081597),(-4031396833965125048484182),true⟩⟩
  | 5,1 => ⟨⟨2301300697182082726419441,3078155972770344790769055,true⟩,⟨(-5653275028627092908407201),(-4802082491186376102337795),true⟩⟩
  | 5,2 => ⟨⟨1659828382588995913752136,2507917956734757004195334,true⟩,⟨(-6389880407636613634105338),(-5438544753076272216857669),true⟩⟩
  | 5,3 => ⟨⟨1134445130505426691374047,2028369653991360730463518,true⟩,⟨(-6817167868769302876971295),(-5803035037847420737001825),true⟩⟩
  | 5,4 => ⟨⟨3060418950091292662251383,3665195861135470846901584,true⟩,⟨(-3937921875471155345856134),(-3311299195102624927632561),true⟩⟩
  | 5,5 => ⟨⟨3147392248107492846432800,3684399845715767122923879,true⟩,⟨(-3298911764713197717848795),(-2755189363924190468411831),true⟩⟩
  | 5,6 => ⟨⟨3149262925452250098164182,3639885619676207704122719,true⟩,⟨(-2877439645303918845390426),(-2388763034261590878743355),true⟩⟩
  | 5,7 => ⟨⟨3131417742608107636555552,3596925956829280548629194,true⟩,⟨(-2655529283827278669443881),(-2196077260497353037837654),true⟩⟩
  | 6,0 => ⟨⟨(-2018899714820151971965428),(-840898915577510621664754),true⟩,⟨(-7710260932076629744964992),(-6452374675014701700693866),true⟩⟩
  | 6,1 => ⟨⟨(-3086064116678950381166257),(-1836212583295162185005664),true⟩,⟨(-7513613012556762343878991),(-6230675003721935088681796),true⟩⟩
  | 6,2 => ⟨⟨(-3924850203474821281861000),(-2631415105963873340004620),true⟩,⟨(-7160349393846577502336341),(-5882626019248067231448621),true⟩⟩
  | 6,3 => ⟨⟨(-4406811055038071130307346),(-3094995174918402381777006),true⟩,⟨(-6857000321962678123087053),(-5595138880585629083524274),true⟩⟩
  | 6,4 => ⟨⟨(-939411307684209682850049),150252439563696009560165,true⟩,⟨(-7660087931592424130457677),(-6458000860373537312040691),true⟩⟩
  | 6,5 => ⟨⟨(-41878654148523772955560),964065007966153385933005,true⟩,⟨(-7428723252364443048183280),(-6295801583919770321575333),true⟩⟩
  | 6,6 => ⟨⟨577125944682359491020397,1520383483277644526400689,true⟩,⟨(-7156370468216678451925352),(-6084070640819679345691613),true⟩⟩
  | 6,7 => ⟨⟨910523759317039855496744,1825308500025734625327770,true⟩,⟨(-6965408941182491999143723),(-5926460992626154171497896),true⟩⟩
  | 7,0 => ⟨⟨(-6274385545681897749135173),(-5106107707262521375371248),true⟩,⟨(-2885009389012161573075388),(-2062104545084183053470526),true⟩⟩
  | 7,1 => ⟨⟨(-6027459365280764826954261),(-4990910790686734772304217),true⟩,⟨(-1626243511039527106440146),(-987520636892821419291982),true⟩⟩
  | 7,2 => ⟨⟨(-5616205031257875718864571),(-4703922130082275149020473),true⟩,⟨(-744682140382815232270888),(-250021176657344296777844),true⟩⟩
  | 7,3 => ⟨⟨(-5297833237626656023232260),(-4466111186457884410055769),true⟩,⟨(-284592874674218928225747),137755137305209814578279,true⟩⟩
  | 7,4 => ⟨⟨(-6145108234594248505369370),(-4875623337405236358537211),true⟩,⟨(-4280579051437063473412356),(-3273703039041082097293892),true⟩⟩
  | 7,5 => ⟨⟨(-5657661584354281007729594),(-4339823065157441916152844),true⟩,⟨(-5479575311219828708297994),(-4336743499473846297128019),true⟩⟩
  | 7,6 => ⟨⟨(-5059818020916561805751316),(-3734405079410626384276925),true⟩,⟨(-6282052281307576680915925),(-5063124293348406480447504),true⟩⟩
  | 7,7 => ⟨⟨(-4629884055909187913193100),(-3311699890235955123851911),true⟩,⟨(-6685206964506041699140050),(-5434771625174510679687232),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP516Value0_0 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 0 (0:Fin 8))=sharedDiskP516Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value0_1 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 0 (1:Fin 8))=sharedDiskP516Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value0_2 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 0 (2:Fin 8))=sharedDiskP516Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value0_3 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 0 (3:Fin 8))=sharedDiskP516Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value0_4 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 0 (4:Fin 8))=sharedDiskP516Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value0_5 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 0 (5:Fin 8))=sharedDiskP516Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value0_6 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 0 (6:Fin 8))=sharedDiskP516Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value0_7 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 0 (7:Fin 8))=sharedDiskP516Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP516Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 0 j)=sharedDiskP516Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP516Value0_0
  · exact sharedDiskP516Value0_1
  · exact sharedDiskP516Value0_2
  · exact sharedDiskP516Value0_3
  · exact sharedDiskP516Value0_4
  · exact sharedDiskP516Value0_5
  · exact sharedDiskP516Value0_6
  · exact sharedDiskP516Value0_7
private theorem sharedDiskP516Value1_0 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 1 (0:Fin 8))=sharedDiskP516Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value1_1 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 1 (1:Fin 8))=sharedDiskP516Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value1_2 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 1 (2:Fin 8))=sharedDiskP516Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value1_3 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 1 (3:Fin 8))=sharedDiskP516Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value1_4 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 1 (4:Fin 8))=sharedDiskP516Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value1_5 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 1 (5:Fin 8))=sharedDiskP516Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value1_6 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 1 (6:Fin 8))=sharedDiskP516Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value1_7 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 1 (7:Fin 8))=sharedDiskP516Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP516Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 1 j)=sharedDiskP516Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP516Value1_0
  · exact sharedDiskP516Value1_1
  · exact sharedDiskP516Value1_2
  · exact sharedDiskP516Value1_3
  · exact sharedDiskP516Value1_4
  · exact sharedDiskP516Value1_5
  · exact sharedDiskP516Value1_6
  · exact sharedDiskP516Value1_7
private theorem sharedDiskP516Value2_0 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 2 (0:Fin 8))=sharedDiskP516Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value2_1 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 2 (1:Fin 8))=sharedDiskP516Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value2_2 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 2 (2:Fin 8))=sharedDiskP516Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value2_3 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 2 (3:Fin 8))=sharedDiskP516Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value2_4 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 2 (4:Fin 8))=sharedDiskP516Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value2_5 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 2 (5:Fin 8))=sharedDiskP516Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value2_6 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 2 (6:Fin 8))=sharedDiskP516Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value2_7 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 2 (7:Fin 8))=sharedDiskP516Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP516Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 2 j)=sharedDiskP516Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP516Value2_0
  · exact sharedDiskP516Value2_1
  · exact sharedDiskP516Value2_2
  · exact sharedDiskP516Value2_3
  · exact sharedDiskP516Value2_4
  · exact sharedDiskP516Value2_5
  · exact sharedDiskP516Value2_6
  · exact sharedDiskP516Value2_7
private theorem sharedDiskP516Value3_0 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 3 (0:Fin 8))=sharedDiskP516Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value3_1 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 3 (1:Fin 8))=sharedDiskP516Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value3_2 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 3 (2:Fin 8))=sharedDiskP516Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value3_3 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 3 (3:Fin 8))=sharedDiskP516Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value3_4 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 3 (4:Fin 8))=sharedDiskP516Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value3_5 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 3 (5:Fin 8))=sharedDiskP516Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value3_6 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 3 (6:Fin 8))=sharedDiskP516Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value3_7 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 3 (7:Fin 8))=sharedDiskP516Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP516Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 3 j)=sharedDiskP516Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP516Value3_0
  · exact sharedDiskP516Value3_1
  · exact sharedDiskP516Value3_2
  · exact sharedDiskP516Value3_3
  · exact sharedDiskP516Value3_4
  · exact sharedDiskP516Value3_5
  · exact sharedDiskP516Value3_6
  · exact sharedDiskP516Value3_7
private theorem sharedDiskP516Value4_0 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 4 (0:Fin 8))=sharedDiskP516Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value4_1 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 4 (1:Fin 8))=sharedDiskP516Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value4_2 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 4 (2:Fin 8))=sharedDiskP516Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value4_3 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 4 (3:Fin 8))=sharedDiskP516Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value4_4 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 4 (4:Fin 8))=sharedDiskP516Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value4_5 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 4 (5:Fin 8))=sharedDiskP516Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value4_6 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 4 (6:Fin 8))=sharedDiskP516Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value4_7 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 4 (7:Fin 8))=sharedDiskP516Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP516Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 4 j)=sharedDiskP516Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP516Value4_0
  · exact sharedDiskP516Value4_1
  · exact sharedDiskP516Value4_2
  · exact sharedDiskP516Value4_3
  · exact sharedDiskP516Value4_4
  · exact sharedDiskP516Value4_5
  · exact sharedDiskP516Value4_6
  · exact sharedDiskP516Value4_7
private theorem sharedDiskP516Value5_0 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 5 (0:Fin 8))=sharedDiskP516Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value5_1 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 5 (1:Fin 8))=sharedDiskP516Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value5_2 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 5 (2:Fin 8))=sharedDiskP516Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value5_3 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 5 (3:Fin 8))=sharedDiskP516Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value5_4 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 5 (4:Fin 8))=sharedDiskP516Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value5_5 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 5 (5:Fin 8))=sharedDiskP516Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value5_6 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 5 (6:Fin 8))=sharedDiskP516Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value5_7 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 5 (7:Fin 8))=sharedDiskP516Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP516Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 5 j)=sharedDiskP516Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP516Value5_0
  · exact sharedDiskP516Value5_1
  · exact sharedDiskP516Value5_2
  · exact sharedDiskP516Value5_3
  · exact sharedDiskP516Value5_4
  · exact sharedDiskP516Value5_5
  · exact sharedDiskP516Value5_6
  · exact sharedDiskP516Value5_7
private theorem sharedDiskP516Value6_0 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 6 (0:Fin 8))=sharedDiskP516Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value6_1 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 6 (1:Fin 8))=sharedDiskP516Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value6_2 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 6 (2:Fin 8))=sharedDiskP516Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value6_3 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 6 (3:Fin 8))=sharedDiskP516Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value6_4 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 6 (4:Fin 8))=sharedDiskP516Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value6_5 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 6 (5:Fin 8))=sharedDiskP516Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value6_6 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 6 (6:Fin 8))=sharedDiskP516Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value6_7 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 6 (7:Fin 8))=sharedDiskP516Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP516Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 6 j)=sharedDiskP516Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP516Value6_0
  · exact sharedDiskP516Value6_1
  · exact sharedDiskP516Value6_2
  · exact sharedDiskP516Value6_3
  · exact sharedDiskP516Value6_4
  · exact sharedDiskP516Value6_5
  · exact sharedDiskP516Value6_6
  · exact sharedDiskP516Value6_7
private theorem sharedDiskP516Value7_0 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 7 (0:Fin 8))=sharedDiskP516Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value7_1 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 7 (1:Fin 8))=sharedDiskP516Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value7_2 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 7 (2:Fin 8))=sharedDiskP516Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value7_3 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 7 (3:Fin 8))=sharedDiskP516Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value7_4 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 7 (4:Fin 8))=sharedDiskP516Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value7_5 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 7 (5:Fin 8))=sharedDiskP516Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value7_6 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 7 (6:Fin 8))=sharedDiskP516Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP516Value7_7 : truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 7 (7:Fin 8))=sharedDiskP516Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP516Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points 7 j)=sharedDiskP516Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP516Value7_0
  · exact sharedDiskP516Value7_1
  · exact sharedDiskP516Value7_2
  · exact sharedDiskP516Value7_3
  · exact sharedDiskP516Value7_4
  · exact sharedDiskP516Value7_5
  · exact sharedDiskP516Value7_6
  · exact sharedDiskP516Value7_7
theorem sharedDiskP516Values_eq : ∀ (i : Fin 8) (j : Fin 8), truncatedChordCell 2 sharedDiskP516Params (sharedChord514Gauss8Points i j)=sharedDiskP516Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP516Values0_eq
  · exact sharedDiskP516Values1_eq
  · exact sharedDiskP516Values2_eq
  · exact sharedDiskP516Values3_eq
  · exact sharedDiskP516Values4_eq
  · exact sharedDiskP516Values5_eq
  · exact sharedDiskP516Values6_eq
  · exact sharedDiskP516Values7_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP516Box : HorizontalRectangle := ⟨(151/200),(303/400),(61545244267357/109951162777600),(61974740996957/109951162777600),(394515270569647091693952744792671/649037107316853453566312041152512),(1163062013992318586144993954734687/649037107316853453566312041152512),(-4651232772192698900927255338567139/1298074214633706907132624082305024),(-3077816710151513905643498207725027/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP516Grid : CGrid := momentChordGrid sharedDiskP516Params chordGaussRule8 2 sharedChord514Bd sharedChord514M (23175049/18014398509481984)
theorem sharedDiskP516Columns : containedInReported sharedDiskP516Grid.re sharedDiskP516Box.reLo sharedDiskP516Box.reHi=true ∧ containedInReported sharedDiskP516Grid.im sharedDiskP516Box.imLo sharedDiskP516Box.imHi=true := by
  rw [sharedDiskP516Grid,momentChordGrid_eq_tabulated sharedDiskP516Params chordGaussRule8 2 sharedChord514Bd sharedChord514M (23175049/18014398509481984) sharedChord514Gauss8Points sharedChord514Gauss8Weights sharedDiskP516Values sharedChord514Gauss8Points_eq sharedChord514Gauss8Weights_eq sharedDiskP516Values_eq]
  decide +kernel
theorem sharedDiskP516Sound : sharedDiskP516Box.Sound := by
  intro t a tl tu al au
  change (((151/200):ℚ):ℝ)≤t at tl
  change t≤(((303/400):ℚ):ℝ) at tu
  change (((61545244267357/109951162777600):ℚ):ℝ)≤a at al
  change a≤(((61974740996957/109951162777600):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP516Params_ok] at ps
  have band := sharedChord514ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3/4):ℚ)≤(151/200))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((303/400):ℚ)≤(77/100)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((921051395650439/1649267441664000):ℚ)≤(61545244267357/109951162777600))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((61974740996957/109951162777600):ℚ)≤(311497591431881/549755813888000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord514Bd (by decide +kernel) (by decide +kernel) sharedChord514M (by decide +kernel) (sharedChord514Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP516Columns.1 sharedDiskP516Columns.2
def sharedDiskP516Rows : List SignRow := [positive_516.toSignRow]
theorem sharedDiskP516Rows_actual : ∀ r∈sharedDiskP516Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP516Rows.all (sharedDiskP516Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP516Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP517Params : ChordParams := ⟨⟨(-19371694373903972114249),(-19109210758516906918806),true⟩,⟨2177290187152910817482980,2204061114305418044717593,true⟩,⟨116410952317810992493047,119220216841693916342993,true⟩,⟨195259778475249183503357,199631918058498903335192,true⟩,⟨299190140469815722939718,301302353615274522853599,true⟩,⟨1170793459609682377544378,1171302107412528277034296,true⟩,⟨(-2428880591274879035276085),(-2419839560250497678334189),true⟩,⟨⟨1148580593190119405084783,1190578399185493499303789,true⟩,⟨(-1073630),1073630,true⟩⟩⟩
theorem sharedDiskP517Params_ok : chordParams (Grid.ofRats (303/400) (19/25)) (Grid.ofRats (308083681133597/549755813888000) (310231164781597/549755813888000))=sharedDiskP517Params := by decide +kernel
def sharedDiskP517Values (i : Fin 8) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3265056588354594938558288),(-2628167219055010956553815),true⟩,⟨(-442492077036118540117212),60426432617556875034025,true⟩⟩
  | 0,1 => ⟨⟨(-2827063627511704680464194),(-2251948375937078310403868),true⟩,⟨(-527439744510286940004235),(-55685538512947556281417),true⟩⟩
  | 0,2 => ⟨⟨(-2517646897451344286624274),(-1989261733384346467500880),true⟩,⟨(-594824475740195538443907),(-150884435341649144718950),true⟩⟩
  | 0,3 => ⟨⟨(-2346158148029104498594304),(-1844299167842730978985722),true⟩,⟨(-634350536137669508429098),(-206905242294255796165475),true⟩⟩
  | 0,4 => ⟨⟨(-3796851436800093469494814),(-3093647330601400000505483),true⟩,⟨(-358867498792327339634840),164480686447849210578939,true⟩⟩
  | 0,5 => ⟨⟨(-4351709069426237686014437),(-3589468553661347070961850),true⟩,⟨(-297630492030122299085404),228951176849840056477625,true⟩⟩
  | 0,6 => ⟨⟨(-4829767750365006018835249),(-4024829158732392467358168),true⟩,⟨(-268093936787638809390999),244566029643091719438908,true⟩⟩
  | 0,7 => ⟨⟨(-5133290709215855783098708),(-4304643347282175509383315),true⟩,⟨(-268350191150288527640925),233274940358118380114558,true⟩⟩
  | 1,0 => ⟨⟨(-1343886093324203250721536),(-1005315346890489323458260),true⟩,⟨(-872947876644396886510095),(-562189433692943518668406),true⟩⟩
  | 1,1 => ⟨⟨(-1130468614924547475026693),(-826433835787545683388192),true⟩,⟨(-918354531737287971886071),(-634267673876371461619320),true⟩⟩
  | 1,2 => ⟨⟨(-976266211282552229474872),(-696590149536494282575679),true⟩,⟨(-947866725534501350290348),(-682826926476937364556646),true⟩⟩
  | 1,3 => ⟨⟨(-888785325459346058119924),(-622637716098204675532755),true⟩,⟨(-963056073468873074170140),(-708668503442577760858891),true⟩⟩
  | 1,4 => ⟨⟨(-1600523901767840756979702),(-1219715013000365064184327),true⟩,⟨(-813667050692191329877877),(-470961378325220430498039),true⟩⟩
  | 1,5 => ⟨⟨(-1870871140994166050819467),(-1445481359634088819792086),true⟩,⟨(-748495948091976205962682),(-373158073997217363762021),true⟩⟩
  | 1,6 => ⟨⟨(-2110164260059882503080501),(-1645824224002420741864929),true⟩,⟨(-690480412263868119686338),(-287869259255347058721332),true⟩⟩
  | 1,7 => ⟨⟨(-2266660845674630773825993),(-1777320285413704046548324),true⟩,⟨(-653070005125294511648350),(-233731038252500685470185),true⟩⟩
  | 2,0 => ⟨⟨65111300573304166189064,237531996233799500966916,true⟩,⟨(-1036095016182819664679781),(-852365565468417743518270),true⟩⟩
  | 2,1 => ⟨⟨266983377871935770468874,431037818079038135026726,true⟩,⟨(-1019891784025795126402289),(-845054985842016688509773),true⟩⟩
  | 2,2 => ⟨⟨411424493180227340804582,574569486225223549183202,true⟩,⟨(-1002967696305912704329056),(-831361482933772057922845),true⟩⟩
  | 2,3 => ⟨⟨493606622410836197344699,656908935816504894921287,true⟩,⟨(-991274463210191746752437),(-821045923298677536852521),true⟩⟩
  | 2,4 => ⟨⟨(-177623296662203310046855),11371924781959205543832,true⟩,⟨(-1040159010803183716652628),(-842423646785217358157275),true⟩⟩
  | 2,5 => ⟨⟨(-435560113332761152157408),(-223725460796556915122363),true⟩,⟨(-1025996350574431313108842),(-811299432225555776838907),true⟩⟩
  | 2,6 => ⟨⟨(-668549874530142520273935),(-432323286263295738538407),true⟩,⟨(-998259549277747700892112),(-766425370297260783292836),true⟩⟩
  | 2,7 => ⟨⟨(-827491218055989724884534),(-570274361742966938536285),true⟩,⟨(-973372500233121925194719),(-725859272186834213870495),true⟩⟩
  | 3,0 => ⟨⟨1440522383442755557859429,1618614544785886341853334,true⟩,⟨(-819487756981579864557572),(-652592677282719636057060),true⟩⟩
  | 3,1 => ⟨⟨1655368887392384674145160,1840339763379680740556158,true⟩,⟨(-805070684159999899957821),(-634621346325625377326560),true⟩⟩
  | 3,2 => ⟨⟨1818156020376445221722859,2009680847092008319138168,true⟩,⟨(-812974809492899833399660),(-638088858448077753210589),true⟩⟩
  | 3,3 => ⟨⟨1914759275663721163295515,2110862431251558462839983,true⟩,⟨(-827691823108397522189097),(-649302237787162319713705),true⟩⟩
  | 3,4 => ⟨⟨1190874896899360136551861,1362865333782211215336977,true⟩,⟨(-858548256784891147047188),(-693298403598927816847300),true⟩⟩
  | 3,5 => ⟨⟨931963738153571866212543,1099319729020794496076201,true⟩,⟨(-910086659881259682544380),(-744436474339343188642345),true⟩⟩
  | 3,6 => ⟨⟨702722383616241888921122,867326175399629077799457,true⟩,⟨(-955542737570736159494718),(-788078069645370496315900),true⟩⟩
  | 3,7 => ⟨⟨551473661643671090252516,715011050113544253351374,true⟩,⟨(-982172290071301749502351),(-812814262665156339803390),true⟩⟩
  | 4,0 => ⟨⟨2648303081476217124471098,2946715394439910224689828,true⟩,⟨(-1352444881432481369394769),(-1075569197458715395799556),true⟩⟩
  | 4,1 => ⟨⟨2865483214101508521183116,3217031030626999464739084,true⟩,⟨(-1733803258598404063483230),(-1400986379423596661458452),true⟩⟩
  | 4,2 => ⟨⟨3021222675613804079405065,3428974537449274816058017,true⟩,⟨(-2179716179426844659674894),(-1785265483414588681419261),true⟩⟩
  | 4,3 => ⟨⟨3092617446720981947755737,3542323595787342300126568,true⟩,⟨(-2533986115462365068418423),(-2092061764166706699771599),true⟩⟩
  | 4,4 => ⟨⟨2418418290052653097161863,2675094681072235144630381,true⟩,⟨(-1092801470597171756114063),(-857936180352486062315982),true⟩⟩
  | 4,5 => ⟨⟨2213263703985543526717622,2440703309768367199116531,true⟩,⟨(-942779917851679692095508),(-736031786958668125154438),true⟩⟩
  | 4,6 => ⟨⟨2055416708099216153186822,2264419522459008057864378,true⟩,⟨(-868387062309218871030128),(-678633559909745395970791),true⟩⟩
  | 4,7 => ⟨⟨1961009651958250720023973,2160466751779842421161426,true⟩,⟨(-838350018986799168458380),(-657110257639962407192588),true⟩⟩
  | 5,0 => ⟨⟨2755783505365988596229875,3445768551005312749731181,true⟩,⟨(-4793218365894658915529575),(-4057194976432314933431072),true⟩⟩
  | 5,1 => ⟨⟨2249794254611828431850437,3026654165931850533861375,true⟩,⟨(-5674599020229560842682021),(-4822367811281828318650365),true⟩⟩
  | 5,2 => ⟨⟨1600916545014523524239304,2448017250337356032353561,true⟩,⟨(-6401540603814280074366313),(-5450392482567649637851671),true⟩⟩
  | 5,3 => ⟨⟨1070243463213656486285048,1964237225384959380551334,true⟩,⟨(-6821567054767015467724614),(-5807660665251130811162616),true⟩⟩
  | 5,4 => ⟨⟨3027745028898254972408533,3633691099094685236974282,true⟩,⟨(-3967652314158178849526391),(-3338791272028628257216813),true⟩⟩
  | 5,5 => ⟨⟨3121216713165237289920827,3659514098016329076204381,true⟩,⟨(-3328069036615784735596914),(-2782076878430949361346892),true⟩⟩
  | 5,6 => ⟨⟨3126979734916880640393054,3618887793868074967368945,true⟩,⟨(-2905287729317306981740763),(-2414423079124265811309767),true⟩⟩
  | 5,7 => ⟨⟨3111016112070311527434858,3577780531348036469261058,true⟩,⟨(-2682404413083323527241842),(-2220838784758046673433757),true⟩⟩
  | 6,0 => ⟨⟨(-2074950071106051857002959),(-899178150991619320315863),true⟩,⟨(-7668730427504457340370405),(-6416426464235693973394044),true⟩⟩
  | 6,1 => ⟨⟨(-3130412755251635590098338),(-1884698376102880255723625),true⟩,⟨(-7460096627432695649844966),(-6184812919697469162417462),true⟩⟩
  | 6,2 => ⟨⟨(-3957031491315425374513312),(-2669302889528511523625662),true⟩,⟨(-7099843253209663763445991),(-5831228433485318378939546),true⟩⟩
  | 6,3 => ⟨⟨(-4430728696315138647513401),(-3125534556183804319678143),true⟩,⟨(-6793851842212483655661049),(-5541814597645162864908243),true⟩⟩
  | 6,4 => ⟨⟨(-1003023945236550882433909),85956665152790963519672,true⟩,⟨(-7633065576245017521360401),(-6434354813236671958563474),true⟩⟩
  | 6,5 => ⟨⟨(-108287208865377696788014),898304591072530218918944,true⟩,⟨(-7414944556142799545443735),(-6283563030448414899958869),true⟩⟩
  | 6,6 => ⟨⟨511113087843578790149106,1454427109853415022643810,true⟩,⟨(-7152115620445795895356232),(-6080739802638382430859439),true⟩⟩
  | 6,7 => ⟨⟨845386297146472775471149,1759943620260192028997978,true⟩,⟨(-6966333157550064541571903),(-5928043440321585533593179),true⟩⟩
  | 7,0 => ⟨⟨(-6246649135783246349739148),(-5087449795005108240941288),true⟩,⟨(-2848809165566171297009191),(-2034140763450819418835660),true⟩⟩
  | 7,1 => ⟨⟨(-5998237221505712261199330),(-4969351008953874179472414),true⟩,⟨(-1606295210998311154824116),(-973381932547809405931350),true⟩⟩
  | 7,2 => ⟨⟨(-5590384611307212916037842),(-4684180157024305294260204),true⟩,⟨(-736218745756484503043002),(-245442090796844848562004),true⟩⟩
  | 7,3 => ⟨⟨(-5275540095471799901905285),(-4448801730142177567110296),true⟩,⟨(-281807182727084932694756),137767985181363210286355,true⟩⟩
  | 7,4 => ⟨⟨(-6126956780227779222161820),(-4866991335943620982519791),true⟩,⟨(-4228612518017667922729624),(-3231850633560166936082526),true⟩⟩
  | 7,5 => ⟨⟨(-5654514975924808896086089),(-4345581282383581414659727),true⟩,⟨(-5417992960671697893992049),(-4285964182164779231529007),true⟩⟩
  | 7,6 => ⟨⟨(-5070818410864609353131472),(-3753256405239146720181632),true⟩,⟨(-6217668014230981398781559),(-5009301067780314308628254),true⟩⟩
  | 7,7 => ⟨⟨(-4649629550891982015036540),(-3338490300990082887618508),true⟩,⟨(-6621282236173735516651712),(-5380959292669082922875033),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP517Value0_0 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 0 (0:Fin 8))=sharedDiskP517Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value0_1 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 0 (1:Fin 8))=sharedDiskP517Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value0_2 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 0 (2:Fin 8))=sharedDiskP517Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value0_3 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 0 (3:Fin 8))=sharedDiskP517Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value0_4 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 0 (4:Fin 8))=sharedDiskP517Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value0_5 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 0 (5:Fin 8))=sharedDiskP517Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value0_6 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 0 (6:Fin 8))=sharedDiskP517Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value0_7 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 0 (7:Fin 8))=sharedDiskP517Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP517Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 0 j)=sharedDiskP517Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP517Value0_0
  · exact sharedDiskP517Value0_1
  · exact sharedDiskP517Value0_2
  · exact sharedDiskP517Value0_3
  · exact sharedDiskP517Value0_4
  · exact sharedDiskP517Value0_5
  · exact sharedDiskP517Value0_6
  · exact sharedDiskP517Value0_7
private theorem sharedDiskP517Value1_0 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 1 (0:Fin 8))=sharedDiskP517Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value1_1 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 1 (1:Fin 8))=sharedDiskP517Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value1_2 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 1 (2:Fin 8))=sharedDiskP517Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value1_3 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 1 (3:Fin 8))=sharedDiskP517Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value1_4 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 1 (4:Fin 8))=sharedDiskP517Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value1_5 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 1 (5:Fin 8))=sharedDiskP517Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value1_6 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 1 (6:Fin 8))=sharedDiskP517Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value1_7 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 1 (7:Fin 8))=sharedDiskP517Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP517Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 1 j)=sharedDiskP517Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP517Value1_0
  · exact sharedDiskP517Value1_1
  · exact sharedDiskP517Value1_2
  · exact sharedDiskP517Value1_3
  · exact sharedDiskP517Value1_4
  · exact sharedDiskP517Value1_5
  · exact sharedDiskP517Value1_6
  · exact sharedDiskP517Value1_7
private theorem sharedDiskP517Value2_0 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 2 (0:Fin 8))=sharedDiskP517Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value2_1 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 2 (1:Fin 8))=sharedDiskP517Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value2_2 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 2 (2:Fin 8))=sharedDiskP517Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value2_3 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 2 (3:Fin 8))=sharedDiskP517Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value2_4 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 2 (4:Fin 8))=sharedDiskP517Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value2_5 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 2 (5:Fin 8))=sharedDiskP517Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value2_6 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 2 (6:Fin 8))=sharedDiskP517Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value2_7 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 2 (7:Fin 8))=sharedDiskP517Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP517Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 2 j)=sharedDiskP517Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP517Value2_0
  · exact sharedDiskP517Value2_1
  · exact sharedDiskP517Value2_2
  · exact sharedDiskP517Value2_3
  · exact sharedDiskP517Value2_4
  · exact sharedDiskP517Value2_5
  · exact sharedDiskP517Value2_6
  · exact sharedDiskP517Value2_7
private theorem sharedDiskP517Value3_0 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 3 (0:Fin 8))=sharedDiskP517Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value3_1 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 3 (1:Fin 8))=sharedDiskP517Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value3_2 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 3 (2:Fin 8))=sharedDiskP517Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value3_3 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 3 (3:Fin 8))=sharedDiskP517Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value3_4 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 3 (4:Fin 8))=sharedDiskP517Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value3_5 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 3 (5:Fin 8))=sharedDiskP517Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value3_6 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 3 (6:Fin 8))=sharedDiskP517Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value3_7 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 3 (7:Fin 8))=sharedDiskP517Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP517Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 3 j)=sharedDiskP517Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP517Value3_0
  · exact sharedDiskP517Value3_1
  · exact sharedDiskP517Value3_2
  · exact sharedDiskP517Value3_3
  · exact sharedDiskP517Value3_4
  · exact sharedDiskP517Value3_5
  · exact sharedDiskP517Value3_6
  · exact sharedDiskP517Value3_7
private theorem sharedDiskP517Value4_0 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 4 (0:Fin 8))=sharedDiskP517Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value4_1 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 4 (1:Fin 8))=sharedDiskP517Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value4_2 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 4 (2:Fin 8))=sharedDiskP517Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value4_3 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 4 (3:Fin 8))=sharedDiskP517Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value4_4 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 4 (4:Fin 8))=sharedDiskP517Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value4_5 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 4 (5:Fin 8))=sharedDiskP517Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value4_6 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 4 (6:Fin 8))=sharedDiskP517Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value4_7 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 4 (7:Fin 8))=sharedDiskP517Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP517Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 4 j)=sharedDiskP517Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP517Value4_0
  · exact sharedDiskP517Value4_1
  · exact sharedDiskP517Value4_2
  · exact sharedDiskP517Value4_3
  · exact sharedDiskP517Value4_4
  · exact sharedDiskP517Value4_5
  · exact sharedDiskP517Value4_6
  · exact sharedDiskP517Value4_7
private theorem sharedDiskP517Value5_0 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 5 (0:Fin 8))=sharedDiskP517Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value5_1 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 5 (1:Fin 8))=sharedDiskP517Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value5_2 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 5 (2:Fin 8))=sharedDiskP517Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value5_3 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 5 (3:Fin 8))=sharedDiskP517Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value5_4 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 5 (4:Fin 8))=sharedDiskP517Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value5_5 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 5 (5:Fin 8))=sharedDiskP517Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value5_6 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 5 (6:Fin 8))=sharedDiskP517Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value5_7 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 5 (7:Fin 8))=sharedDiskP517Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP517Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 5 j)=sharedDiskP517Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP517Value5_0
  · exact sharedDiskP517Value5_1
  · exact sharedDiskP517Value5_2
  · exact sharedDiskP517Value5_3
  · exact sharedDiskP517Value5_4
  · exact sharedDiskP517Value5_5
  · exact sharedDiskP517Value5_6
  · exact sharedDiskP517Value5_7
private theorem sharedDiskP517Value6_0 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 6 (0:Fin 8))=sharedDiskP517Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value6_1 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 6 (1:Fin 8))=sharedDiskP517Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value6_2 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 6 (2:Fin 8))=sharedDiskP517Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value6_3 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 6 (3:Fin 8))=sharedDiskP517Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value6_4 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 6 (4:Fin 8))=sharedDiskP517Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value6_5 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 6 (5:Fin 8))=sharedDiskP517Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value6_6 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 6 (6:Fin 8))=sharedDiskP517Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value6_7 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 6 (7:Fin 8))=sharedDiskP517Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP517Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 6 j)=sharedDiskP517Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP517Value6_0
  · exact sharedDiskP517Value6_1
  · exact sharedDiskP517Value6_2
  · exact sharedDiskP517Value6_3
  · exact sharedDiskP517Value6_4
  · exact sharedDiskP517Value6_5
  · exact sharedDiskP517Value6_6
  · exact sharedDiskP517Value6_7
private theorem sharedDiskP517Value7_0 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 7 (0:Fin 8))=sharedDiskP517Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value7_1 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 7 (1:Fin 8))=sharedDiskP517Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value7_2 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 7 (2:Fin 8))=sharedDiskP517Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value7_3 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 7 (3:Fin 8))=sharedDiskP517Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value7_4 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 7 (4:Fin 8))=sharedDiskP517Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value7_5 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 7 (5:Fin 8))=sharedDiskP517Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value7_6 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 7 (6:Fin 8))=sharedDiskP517Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP517Value7_7 : truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 7 (7:Fin 8))=sharedDiskP517Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP517Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points 7 j)=sharedDiskP517Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP517Value7_0
  · exact sharedDiskP517Value7_1
  · exact sharedDiskP517Value7_2
  · exact sharedDiskP517Value7_3
  · exact sharedDiskP517Value7_4
  · exact sharedDiskP517Value7_5
  · exact sharedDiskP517Value7_6
  · exact sharedDiskP517Value7_7
theorem sharedDiskP517Values_eq : ∀ (i : Fin 8) (j : Fin 8), truncatedChordCell 2 sharedDiskP517Params (sharedChord514Gauss8Points i j)=sharedDiskP517Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP517Values0_eq
  · exact sharedDiskP517Values1_eq
  · exact sharedDiskP517Values2_eq
  · exact sharedDiskP517Values3_eq
  · exact sharedDiskP517Values4_eq
  · exact sharedDiskP517Values5_eq
  · exact sharedDiskP517Values6_eq
  · exact sharedDiskP517Values7_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP517Box : HorizontalRectangle := ⟨(303/400),(19/25),(308083681133597/549755813888000),(310231164781597/549755813888000),(94792700302115729145951550372537/162259276829213363391578010288128),(285164769424933826885105053792953/162259276829213363391578010288128),(-4650863942950288201022334049519327/1298074214633706907132624082305024),(-3091997063780852984159589155014367/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP517Grid : CGrid := momentChordGrid sharedDiskP517Params chordGaussRule8 2 sharedChord514Bd sharedChord514M (23175049/18014398509481984)
theorem sharedDiskP517Columns : containedInReported sharedDiskP517Grid.re sharedDiskP517Box.reLo sharedDiskP517Box.reHi=true ∧ containedInReported sharedDiskP517Grid.im sharedDiskP517Box.imLo sharedDiskP517Box.imHi=true := by
  rw [sharedDiskP517Grid,momentChordGrid_eq_tabulated sharedDiskP517Params chordGaussRule8 2 sharedChord514Bd sharedChord514M (23175049/18014398509481984) sharedChord514Gauss8Points sharedChord514Gauss8Weights sharedDiskP517Values sharedChord514Gauss8Points_eq sharedChord514Gauss8Weights_eq sharedDiskP517Values_eq]
  decide +kernel
theorem sharedDiskP517Sound : sharedDiskP517Box.Sound := by
  intro t a tl tu al au
  change (((303/400):ℚ):ℝ)≤t at tl
  change t≤(((19/25):ℚ):ℝ) at tu
  change (((308083681133597/549755813888000):ℚ):ℝ)≤a at al
  change a≤(((310231164781597/549755813888000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP517Params_ok] at ps
  have band := sharedChord514ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((3/4):ℚ)≤(303/400))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((19/25):ℚ)≤(77/100)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((921051395650439/1649267441664000):ℚ)≤(308083681133597/549755813888000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((310231164781597/549755813888000):ℚ)≤(311497591431881/549755813888000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord514Bd (by decide +kernel) (by decide +kernel) sharedChord514M (by decide +kernel) (sharedChord514Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP517Columns.1 sharedDiskP517Columns.2
def sharedDiskP517Rows : List SignRow := [positive_517.toSignRow]
theorem sharedDiskP517Rows_actual : ∀ r∈sharedDiskP517Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP517Rows.all (sharedDiskP517Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP517Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP514Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP515Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP516Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP517Rows_actual
