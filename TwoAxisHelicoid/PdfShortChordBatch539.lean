import TwoAxisHelicoid.PdfSharedChord521Gauss8
import TwoAxisHelicoid.PdfSharedChord521Disks

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP539Params : ChordParams := ⟨⟨(-26829348903437476796406),(-26520604406269676955709),true⟩,⟨1926672596991799415505176,1941547438836845582477151,true⟩,⟨131167124081270399262264,133038704642706513000399,true⟩,⟨242615307488304425163626,245618930761880913995587,true⟩,⟨350339211758611800284169,352460639874034088008356,true⟩,⟨1156432100083257760891386,1157023215349237634370508,true⟩,⟨(-2209662999011553951644556),(-2201841569695138850478064),true⟩,⟨⟨1139138396855630938180594,1167886785369628436507081,true⟩,⟨(-34613910),34613910,true⟩⟩⟩
theorem sharedDiskP539Params_ok : chordParams (Grid.ofRats (329/400) (33/40)) (Grid.ofRats (318600320928061/549755813888000) (319674062752061/549755813888000))=sharedDiskP539Params := by decide +kernel
def sharedDiskP539Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3163875409232259992667615),(-2651581700714754145153421),true⟩,⟨(-320320409382165211216039),89264271008046940109735,true⟩⟩
  | 0,1 => ⟨⟨(-2810316308442427752424442),(-2339213499444998596195807),true⟩,⟨(-377698902772810743473704),11245050083907726455729,true⟩⟩
  | 0,2 => ⟨⟨(-2554490417530627522164861),(-2116011158941299471874845),true⟩,⟨(-427014983358119926227971),(-57745409718515291488585),true⟩⟩
  | 0,3 => ⟨⟨(-2410138592030409760645766),(-1991005464498701883815666),true⟩,⟨(-457488531233231158028151),(-100959388799412466640395),true⟩⟩
  | 0,4 => ⟨⟨(-3581777606038555829021509),(-3027155521640548178864175),true⟩,⟨(-269970482163696815782382),153032137528817095825740,true⟩⟩
  | 0,5 => ⟨⟨(-4006360877862689287065321),(-3415988658182305004346585),true⟩,⟨(-239479399739081529003354),187481751240607125742653,true⟩⟩
  | 0,6 => ⟨⟨(-4364555548582560744600907),(-3749811775184551475843384),true⟩,⟨(-231228202484502684222092),188971887280092112280647,true⟩⟩
  | 0,7 => ⟨⟨(-4589102692002015258325176),(-3961444673666898840048967),true⟩,⟨(-238508465121672004752639),176379741182323914512053,true⟩⟩
  | 1,0 => ⟨⟨(-1541484446133690506798396),(-1244864356991046438390553),true⟩,⟨(-671383188446488953713953),(-403329151219238273815032),true⟩⟩
  | 1,1 => ⟨⟨(-1351445838467376500111662),(-1082241556673040225723693),true⟩,⟨(-721058151617346814285088),(-474598909194695613062407),true⟩⟩
  | 1,2 => ⟨⟨(-1213438027431620138631841),(-963872849217233790258170),true⟩,⟨(-756441487581684984372582),(-525686751419285895628328),true⟩⟩
  | 1,3 => ⟨⟨(-1134952033770035911155345),(-896392517440905798772741),true⟩,⟨(-776068498725387431039380),(-554184306029557614529755),true⟩⟩
  | 1,4 => ⟨⟨(-1768040346928990706495297),(-1438614682790714531705575),true⟩,⟨(-612253826041752485613206),(-319014032056260474561428),true⟩⟩
  | 1,5 => ⟨⟨(-2003824381136595470590390),(-1640650001989841687482686),true⟩,⟨(-552478918813622668863621),(-234315675854022779277688),true⟩⟩
  | 1,6 => ⟨⟨(-2209721085170334972782634),(-1817785911439397189522724),true⟩,⟨(-502826816967950256772064),(-164451988885564063629117),true⟩⟩
  | 1,7 => ⟨⟨(-2342859212066034769827546),(-1932812543898954138011799),true⟩,⟨(-472332477549256336975159),(-121831111497823778179510),true⟩⟩
  | 2,0 => ⟨⟨(-266677826303242524068135),(-123403548125311847344153),true⟩,⟨(-941505941812667319525714),(-794671409467434467632271),true⟩⟩
  | 2,1 => ⟨⟨(-82156318167479847428625),49387040400598538596007,true⟩,⟨(-956576530987790519430916),(-818940003896053133152780),true⟩⟩
  | 2,2 => ⟨⟨52528422777725366935924,177449768734634990080791,true⟩,⟨(-962112309672975574653499),(-830259031997347430909777),true⟩⟩
  | 2,3 => ⟨⟨129596335107025027899797,251413823193387410819931,true⟩,⟨(-963357459749316171612621),(-834469954806550574773890),true⟩⟩
  | 2,4 => ⟨⟨(-487387476528727301341292),(-326767750522908317540334),true⟩,⟨(-911956174026304539336948),(-752149669928460852075158),true⟩⟩
  | 2,5 => ⟨⟨(-722980189919967607641682),(-538881071085072955260805),true⟩,⟨(-868465441755067818127290),(-690912327335537276644344),true⟩⟩
  | 2,6 => ⟨⟨(-936918937879992770260272),(-725398902278320728223068),true⟩,⟨(-823119916183660341019914),(-623202195288755408250734),true⟩⟩
  | 2,7 => ⟨⟨(-1079896896618332352395409),(-848968803998527363266705),true⟩,⟨(-789546575506280996316645),(-573838855204572929805668),true⟩⟩
  | 3,0 => ⟨⟨1044597831590781289693520,1172217564496947138626797,true⟩,⟨(-948162129563046844349058),(-822234055647523431769654),true⟩⟩
  | 3,1 => ⟨⟨1265546112694790343053246,1400129454643519933872466,true⟩,⟨(-968700741649817819815170),(-837982998052755542407887),true⟩⟩
  | 3,2 => ⟨⟨1435802225536684067541261,1577272032481270963274511,true⟩,⟨(-1003933778063425487586467),(-867779696697135829411080),true⟩⟩
  | 3,3 => ⟨⟨1537446413667033658597511,1683765870323442152559843,true⟩,⟨(-1035591341153304917954538),(-895340214906169254767291),true⟩⟩
  | 3,4 => ⟨⟨794798263627098037578259,916838199215736186834063,true⟩,⟨(-946562607113755086122393),(-823486863930700529097275),true⟩⟩
  | 3,5 => ⟨⟨543567552901004680769129,662235821459799353911484,true⟩,⟨(-954926052834987591585824),(-832369476850802800495904),true⟩⟩
  | 3,6 => ⟨⟨326675039420966822016473,444255329006224493002223,true⟩,⟨(-961405252615638229919902),(-837545614337094009724152),true⟩⟩
  | 3,7 => ⟨⟨184016592067410855390332,303865699731262986167865,true⟩,⟨(-963467445171219090882888),(-836522757989836920955597),true⟩⟩
  | 4,0 => ⟨⟨2275595087150858391424450,2509271090844961786932342,true⟩,⟨(-1725782856723602549936657),(-1497627298314419622201081),true⟩⟩
  | 4,1 => ⟨⟨2445521371134331859405978,2724333302853499348142301,true⟩,⟨(-2174963872926599792559489),(-1897690012374872795683076),true⟩⟩
  | 4,2 => ⟨⟨2523507128381185925053368,2849289047849438542460575,true⟩,⟨(-2675312600382233297719500),(-2345006195504461558510652),true⟩⟩
  | 4,3 => ⟨⟨2522290514488637365914727,2882432485651410759592963,true⟩,⟨(-3055828151668507598033684),(-2685609158188181837290312),true⟩⟩
  | 4,4 => ⟨⟨2060554354840103838135115,2258537356847898721104548,true⟩,⟨(-1404590077648598316867551),(-1213752835622865320760776),true⟩⟩
  | 4,5 => ⟨⟨1852271993387231843378693,2025305192299159927351396,true⟩,⟨(-1207835146150759624049365),(-1042073347100345443642823),true⟩⟩
  | 4,6 => ⟨⟨1686513675460661191037554,1843928582992020726550727,true⟩,⟨(-1101935965630669529349496),(-951324719353794087015025),true⟩⟩
  | 4,7 => ⟨⟨1586369269940154102390636,1735761547784432240386765,true⟩,⟨(-1054533819082290755791675),(-911500362838504553122912),true⟩⟩
  | 5,0 => ⟨⟨2300616211927384152623540,2747708025385189611399060,true⟩,⟨(-4052402620455390021783354),(-3577208791151829722434500),true⟩⟩
  | 5,1 => ⟨⟨2170646528938532930326797,2643468605579728906516963,true⟩,⟨(-4352701908816489518572454),(-3845355873354841118275626),true⟩⟩
  | 5,2 => ⟨⟨2038083633249969620028982,2532186335435825253157796,true⟩,⟨(-4601810219790131528713038),(-4067484036464855158700090),true⟩⟩
  | 5,3 => ⟨⟨1943754542083822765589940,2451020771164389867675996,true⟩,⟨(-4755993585901550358333507),(-4204796820667332491370990),true⟩⟩
  | 5,4 => ⟨⟨2400913783338000206031022,2821971355118226849232677,true⟩,⟨(-3750374814892623528061985),(-3307203465941551762342235),true⟩⟩
  | 5,5 => ⟨⟨2464334883556873886192054,2862651193001146282948176,true⟩,⟨(-3488725565394295115736095),(-3073112656272252485787565),true⟩⟩
  | 5,6 => ⟨⟨2497485595510130136441039,2878841271948678767708869,true⟩,⟨(-3295283164507017701382418),(-2899973124883782941074193),true⟩⟩
  | 5,7 => ⟨⟨2511214225401580200828493,2882784336554206353186621,true⟩,⟨(-3184452452626639597051089),(-2800758576495172856846475),true⟩⟩
  | 6,0 => ⟨⟨797596510888027568872141,1413975083131242964968423,true⟩,⟨(-5917493071471755265792370),(-5227313335171535918255427),true⟩⟩
  | 6,1 => ⟨⟨305216375593490317353777,967074719536033507689494,true⟩,⟨(-6200969962462835778834394),(-5463265785208280671665377),true⟩⟩
  | 6,2 => ⟨⟨(-142642818967245072851398),558418242658086029349230,true⟩,⟨(-6388852109394130430857072),(-5613449998618136374605260),true⟩⟩
  | 6,3 => ⟨⟨(-437627167196120244169462),288032050565105831147706,true⟩,⟨(-6480899328222753920210071),(-5683655686112033265254148),true⟩⟩
  | 6,4 => ⟨⟨1237637979172098843440936,1815642907397410252991078,true⟩,⟨(-5578633593724705544822110),(-4934172182500235522821782),true⟩⟩
  | 6,5 => ⟨⟨1566424025743571350086702,2116081673617431402601664,true⟩,⟨(-5251100653599670688450755),(-4644573974830908848294587),true⟩⟩
  | 6,6 => ⟨⟨1781575766849316489316839,2308739838126621566713591,true⟩,⟨(-4988833163514550539917989),(-4411861387304109636193657),true⟩⟩
  | 6,7 => ⟨⟨1893763279927734521025483,2407491801867991555923054,true⟩,⟨(-4831661403481713360573417),(-4272130284937167633472268),true⟩⟩
  | 7,0 => ⟨⟨(-3052121712297227617220101),(-2153976857754786452512616),true⟩,⟨(-6336768977508872914260041),(-5436896306794218118131302),true⟩⟩
  | 7,1 => ⟨⟨(-3799219996548011975840817),(-2870772584879560809917672),true⟩,⟨(-5938809642591000336888847),(-5044707226395211757957020),true⟩⟩
  | 7,2 => ⟨⟨(-4339506699406210176245118),(-3397881969282472657364605),true⟩,⟨(-5496712607606037493762683),(-4622686885407820900982627),true⟩⟩
  | 7,3 => ⟨⟨(-4630864867027010174995529),(-3686884481822443573974236),true⟩,⟨(-5178067034262333759216630),(-4323313361274428117743712),true⟩⟩
  | 7,4 => ⟨⟨(-2223612726042965983258246),(-1370337143808084241839716),true⟩,⟨(-6570638306513038224282024),(-5685147632390183580919070),true⟩⟩
  | 7,5 => ⟨⟨(-1470152024330351777164546),(-665972890601600694329466),true⟩,⟨(-6627899508998442992506809),(-5770612626872772027605639),true⟩⟩
  | 7,6 => ⟨⟨(-907205890925334208691272),(-144576649215599375598425),true⟩,⟨(-6580461630386197212843759),(-5752837061140372355398873),true⟩⟩
  | 7,7 => ⟨⟨(-587077261928867126972759),150531352118882778235580,true⟩,⟨(-6518688003351994812544865),(-5711204311297854280414620),true⟩⟩
  | 8,0 => ⟨⟨(-5471204876623511589230192),(-4670262098283792909732642),true⟩,⟨(-2032365590496414679130379),(-1476451184487652095941228),true⟩⟩
  | 8,1 => ⟨⟨(-5226487709069340232078932),(-4510556510321429769356159),true⟩,⟨(-1149133060121396582818285),(-701568099317693605086288),true⟩⟩
  | 8,2 => ⟨⟨(-4908691585014558836201954),(-4269957896923991809717794),true⟩,⟨(-529238156271727618282160),(-167507049218285048542245),true⟩⟩
  | 8,3 => ⟨⟨(-4676061566062966315956328),(-4086446930777828030697138),true⟩,⟨(-199757528002990930494498),119380120307568368060524,true⟩⟩
  | 8,4 => ⟨⟨(-5504344644965157075784503),(-4630203812141114687375092),true⟩,⟨(-3040779157521306064287655),(-2371988794200358436216611),true⟩⟩
  | 8,5 => ⟨⟨(-5305980107354158786298311),(-4386561200239387930591723),true⟩,⟨(-3964575490670737995570577),(-3205619479553844758823897),true⟩⟩
  | 8,6 => ⟨⟨(-5000652560310586861828525),(-4061949072777538374658797),true⟩,⟨(-4639991017612509468007235),(-3823992665154229711464320),true⟩⟩
  | 8,7 => ⟨⟨(-4760647772114090620314534),(-3817196716392145120048639),true⟩,⟨(-5010301613185412616273046),(-4166884285466916986187803),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP539Value0_0 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP539Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value0_1 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP539Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value0_2 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP539Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value0_3 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP539Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value0_4 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP539Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value0_5 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP539Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value0_6 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP539Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value0_7 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP539Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP539Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 0 j)=sharedDiskP539Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP539Value0_0
  · exact sharedDiskP539Value0_1
  · exact sharedDiskP539Value0_2
  · exact sharedDiskP539Value0_3
  · exact sharedDiskP539Value0_4
  · exact sharedDiskP539Value0_5
  · exact sharedDiskP539Value0_6
  · exact sharedDiskP539Value0_7
private theorem sharedDiskP539Value1_0 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP539Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value1_1 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP539Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value1_2 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP539Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value1_3 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP539Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value1_4 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP539Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value1_5 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP539Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value1_6 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP539Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value1_7 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP539Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP539Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 1 j)=sharedDiskP539Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP539Value1_0
  · exact sharedDiskP539Value1_1
  · exact sharedDiskP539Value1_2
  · exact sharedDiskP539Value1_3
  · exact sharedDiskP539Value1_4
  · exact sharedDiskP539Value1_5
  · exact sharedDiskP539Value1_6
  · exact sharedDiskP539Value1_7
private theorem sharedDiskP539Value2_0 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP539Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value2_1 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP539Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value2_2 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP539Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value2_3 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP539Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value2_4 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP539Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value2_5 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP539Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value2_6 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP539Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value2_7 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP539Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP539Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 2 j)=sharedDiskP539Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP539Value2_0
  · exact sharedDiskP539Value2_1
  · exact sharedDiskP539Value2_2
  · exact sharedDiskP539Value2_3
  · exact sharedDiskP539Value2_4
  · exact sharedDiskP539Value2_5
  · exact sharedDiskP539Value2_6
  · exact sharedDiskP539Value2_7
private theorem sharedDiskP539Value3_0 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP539Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value3_1 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP539Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value3_2 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP539Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value3_3 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP539Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value3_4 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP539Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value3_5 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP539Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value3_6 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP539Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value3_7 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP539Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP539Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 3 j)=sharedDiskP539Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP539Value3_0
  · exact sharedDiskP539Value3_1
  · exact sharedDiskP539Value3_2
  · exact sharedDiskP539Value3_3
  · exact sharedDiskP539Value3_4
  · exact sharedDiskP539Value3_5
  · exact sharedDiskP539Value3_6
  · exact sharedDiskP539Value3_7
private theorem sharedDiskP539Value4_0 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP539Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value4_1 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP539Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value4_2 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP539Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value4_3 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP539Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value4_4 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP539Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value4_5 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP539Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value4_6 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP539Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value4_7 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP539Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP539Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 4 j)=sharedDiskP539Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP539Value4_0
  · exact sharedDiskP539Value4_1
  · exact sharedDiskP539Value4_2
  · exact sharedDiskP539Value4_3
  · exact sharedDiskP539Value4_4
  · exact sharedDiskP539Value4_5
  · exact sharedDiskP539Value4_6
  · exact sharedDiskP539Value4_7
private theorem sharedDiskP539Value5_0 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP539Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value5_1 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP539Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value5_2 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP539Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value5_3 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP539Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value5_4 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP539Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value5_5 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP539Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value5_6 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP539Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value5_7 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP539Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP539Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 5 j)=sharedDiskP539Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP539Value5_0
  · exact sharedDiskP539Value5_1
  · exact sharedDiskP539Value5_2
  · exact sharedDiskP539Value5_3
  · exact sharedDiskP539Value5_4
  · exact sharedDiskP539Value5_5
  · exact sharedDiskP539Value5_6
  · exact sharedDiskP539Value5_7
private theorem sharedDiskP539Value6_0 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP539Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value6_1 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP539Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value6_2 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP539Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value6_3 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP539Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value6_4 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP539Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value6_5 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP539Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value6_6 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP539Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value6_7 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP539Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP539Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 6 j)=sharedDiskP539Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP539Value6_0
  · exact sharedDiskP539Value6_1
  · exact sharedDiskP539Value6_2
  · exact sharedDiskP539Value6_3
  · exact sharedDiskP539Value6_4
  · exact sharedDiskP539Value6_5
  · exact sharedDiskP539Value6_6
  · exact sharedDiskP539Value6_7
private theorem sharedDiskP539Value7_0 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP539Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value7_1 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP539Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value7_2 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP539Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value7_3 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP539Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value7_4 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP539Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value7_5 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP539Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value7_6 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP539Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value7_7 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP539Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP539Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 7 j)=sharedDiskP539Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP539Value7_0
  · exact sharedDiskP539Value7_1
  · exact sharedDiskP539Value7_2
  · exact sharedDiskP539Value7_3
  · exact sharedDiskP539Value7_4
  · exact sharedDiskP539Value7_5
  · exact sharedDiskP539Value7_6
  · exact sharedDiskP539Value7_7
private theorem sharedDiskP539Value8_0 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP539Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value8_1 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP539Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value8_2 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP539Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value8_3 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP539Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value8_4 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP539Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value8_5 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP539Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value8_6 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP539Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP539Value8_7 : truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP539Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP539Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points 8 j)=sharedDiskP539Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP539Value8_0
  · exact sharedDiskP539Value8_1
  · exact sharedDiskP539Value8_2
  · exact sharedDiskP539Value8_3
  · exact sharedDiskP539Value8_4
  · exact sharedDiskP539Value8_5
  · exact sharedDiskP539Value8_6
  · exact sharedDiskP539Value8_7
theorem sharedDiskP539Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP539Params (sharedChord521Gauss8Points i j)=sharedDiskP539Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP539Values0_eq
  · exact sharedDiskP539Values1_eq
  · exact sharedDiskP539Values2_eq
  · exact sharedDiskP539Values3_eq
  · exact sharedDiskP539Values4_eq
  · exact sharedDiskP539Values5_eq
  · exact sharedDiskP539Values6_eq
  · exact sharedDiskP539Values7_eq
  · exact sharedDiskP539Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP539Box : HorizontalRectangle := ⟨(329/400),(33/40),(318600320928061/549755813888000),(319674062752061/549755813888000),(91794104057933621648533939790251/1298074214633706907132624082305024),(1053775823556936442082950496100779/1298074214633706907132624082305024),(-2221614198670081775073226856709901/649037107316853453566312041152512),(-1726937795124938893105293401112333/649037107316853453566312041152512),true,[]⟩
noncomputable def sharedDiskP539Grid : CGrid := momentChordGrid sharedDiskP539Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP539Columns : containedInReported sharedDiskP539Grid.re sharedDiskP539Box.reLo sharedDiskP539Box.reHi=true ∧ containedInReported sharedDiskP539Grid.im sharedDiskP539Box.imLo sharedDiskP539Box.imHi=true := by
  rw [sharedDiskP539Grid,momentChordGrid_eq_tabulated sharedDiskP539Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP539Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP539Values_eq]
  decide +kernel
theorem sharedDiskP539Sound : sharedDiskP539Box.Sound := by
  intro t a tl tu al au
  change (((329/400):ℚ):ℝ)≤t at tl
  change t≤(((33/40):ℚ):ℝ) at tu
  change (((318600320928061/549755813888000):ℚ):ℝ)≤a at al
  change a≤(((319674062752061/549755813888000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP539Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(329/400))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((33/40):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(318600320928061/549755813888000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((319674062752061/549755813888000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP539Columns.1 sharedDiskP539Columns.2
def sharedDiskP539Rows : List SignRow := [positive_539.toSignRow]
theorem sharedDiskP539Rows_actual : ∀ r∈sharedDiskP539Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP539Rows.all (sharedDiskP539Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP539Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP540Params : ChordParams := ⟨⟨(-27139789586379719406188),(-26829348903437476795846),true⟩,⟨1917425511362150935484369,1932227256457273785344233,true⟩,⟨131678038339675723097368,133549623898242753350200,true⟩,⟨244492972539635222008505,247504876020427914145918,true⟩,⟨352284080957454268580184,354405357071755537670551,true⟩,⟨1155838035073659680630454,1156432100083257760892460,true⟩,⟨(-2201841569695138850487124),(-2194061800439317839475705),true⟩,⟨⟨1138447449908382939093481,1167228388474451055759346,true⟩,⟨(-39150347),39150347,true⟩⟩⟩
theorem sharedDiskP540Params_ok : chordParams (Grid.ofRats (33/40) (331/400)) (Grid.ofRats (957032188846669/1649267441664000) (960253414318669/1649267441664000))=sharedDiskP540Params := by decide +kernel
def sharedDiskP540Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3161566173927704360177915),(-2649357029288777465553055),true⟩,⟨(-317990405062445161838673),91471249812103920618289,true⟩⟩
  | 0,1 => ⟨⟨(-2810772569021985989970655),(-2339421164169568681481150),true⟩,⟨(-374411371398761291256841),14675451199843351922819,true⟩⟩
  | 0,2 => ⟨⟨(-2556739101154617391187781),(-2117779651572987632479159),true⟩,⟨(-423041988239869687479226),(-53433989559455449284868),true⟩⟩
  | 0,3 => ⟨⟨(-2413319795855881435515556),(-1993582998790869547103014),true⟩,⟨(-453145715336647553868078),(-96160726239204436564817),true⟩⟩
  | 0,4 => ⟨⟨(-3575793374515216386498486),(-3021645143004847616297876),true⟩,⟨(-268693702946177016117124),153954000431242293690357,true⟩⟩
  | 0,5 => ⟨⟨(-3996239637419614756327174),(-3406707891328373300563689),true⟩,⟨(-239083696657838843338941),187427549407706079193493,true⟩⟩
  | 0,6 => ⟨⟨(-4350679180355643317911492),(-3737040976284963049639699),true⟩,⟨(-231428958651292750509244),188398167934852301436236,true⟩⟩
  | 0,7 => ⟨⟨(-4572758527878123707756575),(-3946365347624496601138286),true⟩,⟨(-238883888135745600420439),175672462905088925734901,true⟩⟩
  | 1,0 => ⟨⟨(-1549043018468046586924263),(-1251394029963999229834251),true⟩,⟨(-665512802471645278447830),(-396661970608984130506503),true⟩⟩
  | 1,1 => ⟨⟨(-1359759096119555136614532),(-1089479449977225409359977),true⟩,⟨(-715127321735463494207463),(-467828578062886488789294),true⟩⟩
  | 1,2 => ⟨⟨(-1222266145773342700808862),(-971606888185343825858891),true⟩,⟨(-750554939538625586201430),(-518945209297183610041538),true⟩⟩
  | 1,3 => ⟨⟨(-1144063215187052375653221),(-904404340201373886042878),true⟩,⟨(-770243368752697640445107),(-547500834233026686335953),true⟩⟩
  | 1,4 => ⟨⟨(-1774611785776055731120290),(-1444244068793236104411834),true⟩,⟨(-606613622260096643653439),(-312660287570043024001334),true⟩⟩
  | 1,5 => ⟨⟨(-2009247697152003263995518),(-1645255498712837633929379),true⟩,⟨(-547225357528408941131250),(-228468521211163618469384),true⟩⟩
  | 1,6 => ⟨⟨(-2214028935267136334867631),(-1821408894291261765773984),true⟩,⟨(-498004347641568039423824),(-159162230184205343606359),true⟩⟩
  | 1,7 => ⟨⟨(-2346386370992041882942926),(-1935750964368511008009953),true⟩,⟨(-467823481516020475846039),(-116943852462519928248571),true⟩⟩
  | 2,0 => ⟨⟨(-278596939759028633696795),(-134724714170142504347063),true⟩,⟨(-938135086355576784561934),(-790948104031777992556414),true⟩⟩
  | 2,1 => ⟨⟨(-94714441908939639512019),37319632704547903550794,true⟩,⟨(-954201492196597608647611),(-816239701937809520165492),true⟩⟩
  | 2,2 => ⟨⟨39553008122815884588617,164876495293576430366066,true⟩,⟨(-960530134595975790136846),(-828364165089314637244680),true⟩⟩
  | 2,3 => ⟨⟨116361265596791613722937,238558366550827639779234,true⟩,⟨(-962248449667127200576069),(-833052560689009011188748),true⟩⟩
  | 2,4 => ⟨⟨(-498552275146047390004910),(-337246615880292342314142),true⟩,⟨(-907570800368109806281233),(-747366893329279227959693),true⟩⟩
  | 2,5 => ⟨⟨(-733513737855873475199568),(-548480743611385643457710),true⟩,⟨(-863281640051054637011658),(-685081183056959260534716),true⟩⟩
  | 2,6 => ⟨⟨(-946722392811649537061241),(-734105145940951697078023),true⟩,⟨(-817575184135200211509506),(-616805928141111012669707),true⟩⟩
  | 2,7 => ⟨⟨(-1089203249868296203957675),(-857174275513350738797371),true⟩,⟨(-783781014424877887564737),(-567214783885903551074476),true⟩⟩
  | 3,0 => ⟨⟨1029357960653027660719942,1156897888002145987656540,true⟩,⟨(-952803987269438389346014),(-826763179515953738282417),true⟩⟩
  | 3,1 => ⟨⟨1250118194076199332823126,1384667099087768735416417,true⟩,⟨(-974735706568035408809786),(-843842162091553500529493),true⟩⟩
  | 3,2 => ⟨⟨1420282249513254010902642,1561768662491842338785583,true⟩,⟨(-1011062361021052042338631),(-874671038639556815370494),true⟩⟩
  | 3,3 => ⟨⟨1521871866060291174116668,1668244817835220340122334,true⟩,⟨(-1043393849311885619193269),(-902863325660852879919276),true⟩⟩
  | 3,4 => ⟨⟨779932040644067099107163,901870209236791762554840,true⟩,⟨(-949616930446934046041240),(-826477702133368125597840),true⟩⟩
  | 3,5 => ⟨⟨529269690729840185761164,647846006603961556439997,true⟩,⟨(-956349992509132525752209),(-833756095862278742752573),true⟩⟩
  | 3,6 => ⟨⟨313001633989424006653020,430524103137492925412461,true⟩,⟨(-961410861656600761887025),(-837517323819261612812064),true⟩⟩
  | 3,7 => ⟨⟨170601487489809897957606,290815706637710288743590,true⟩,⟨(-962698810048591891407675),(-835447514523130238498023),true⟩⟩
  | 4,0 => ⟨⟨2257486709798906747607642,2491491153047296938203876,true⟩,⟨(-1739812437046063318917247),(-1510973870438193792197406),true⟩⟩
  | 4,1 => ⟨⟨2424572774405767365511868,2703798726434277386240304,true⟩,⟨(-2191077058288649087720933),(-1912973376404111531619947),true⟩⟩
  | 4,2 => ⟨⟨2498761646327003930716458,2824986273293759896022625,true⟩,⟨(-2692690736753026553043776),(-2361468826203518595092465),true⟩⟩
  | 4,3 => ⟨⟨2494358469365520145814923,2854918713606378713890554,true⟩,⟨(-3073450985788698968447563),(-2702306937749310136883285),true⟩⟩
  | 4,4 => ⟨⟨2043985996547638874775385,2242197848068895053397690,true⟩,⟨(-1416457542547943636247118),(-1225087323412665901361852),true⟩⟩
  | 4,5 => ⟨⟨1836357289228081382974085,2009538492984576494757423,true⟩,⟨(-1217928233430152277047029),(-1051750694486252721627729),true⟩⟩
  | 4,6 => ⟨⟨1670832804548999040369954,1828343264448313217344415,true⟩,⟨(-1110777301715534797383752),(-959826925968685869488150),true⟩⟩
  | 4,7 => ⟨⟨1570765133981895328549595,1720226404397109479117446,true⟩,⟨(-1062669639984429579978103),(-919336947793019263793918),true⟩⟩
  | 5,0 => ⟨⟨2263740099084136962945144,2710984988387382225772340,true⟩,⟨(-4067552232440020559086402),(-3591663130609950861969902),true⟩⟩
  | 5,1 => ⟨⟨2131054329429716820164557,2603886009250012309551247,true⟩,⟨(-4366123358890767744988618),(-3858235471405402039263710),true⟩⟩
  | 5,2 => ⟨⟨1996285178955116407086718,2490252684776109777085039,true⟩,⟨(-4613400649558217497549100),(-4078695352849679390857100),true⟩⟩
  | 5,3 => ⟨⟨1900625886647298809634802,2407654485763364352854831,true⟩,⟨(-4766253768840333418264633),(-4214796540137778011671835),true⟩⟩
  | 5,4 => ⟨⟨2366789297056928198408168,2788112923050208002917111,true⟩,⟨(-3766778601829757092157443),(-3322799860456846600526715),true⟩⟩
  | 5,5 => ⟨⟨2432579608153357596100949,2831236270370927510604166,true⟩,⟨(-3505851060409789415068141),(-3089364681881612289672807),true⟩⟩
  | 5,6 => ⟨⟨2467458275188938735675391,2849195883720883634767113,true⟩,⟨(-3312735544802131812485635),(-2916520419713076935345583),true⟩⟩
  | 5,7 => ⟨⟨2482163663706308121719227,2854134577749379466780030,true⟩,⟨(-3202015464468985309679668),(-2817404684002844143191751),true⟩⟩
  | 6,0 => ⟨⟨745645683309907085525641,1361619653816839189743870,true⟩,⟨(-5911820636829185022867045),(-5222278394136922211328635),true⟩⟩
  | 6,1 => ⟨⟨252791340600662808301111,914842417055830025759807,true⟩,⟨(-6188409539878803078611310),(-5451376044647504100699687),true⟩⟩
  | 6,2 => ⟨⟨(-194617004545212563645347),506392239296003641796823,true⟩,⟨(-6370220809256154570106409),(-5596101820150595884745596),true⟩⟩
  | 6,3 => ⟨⟨(-488687756681237061623914),236618595800017797447279,true⟩,⟨(-6458407425550421690823384),(-5662856850130902616559893),true⟩⟩
  | 6,4 => ⟨⟨1188339404169058052721556,1765352978231909593710056,true⟩,⟨(-5578633562029359271998954),(-4934843466574244672207192),true⟩⟩
  | 6,5 => ⟨⟨1519329070567258925871273,2068343363125843290366099,true⟩,⟨(-5255914092300025455318393),(-4649617727713748461864649),true⟩⟩
  | 6,6 => ⟨⟨1736512019443322304068897,2263263304873281605719637,true⟩,⟨(-4996770798631364624677680),(-4419746803174724535234129),true⟩⟩
  | 6,7 => ⟨⟨1849994830227932990379308,2363431606369484094179751,true⟩,⟨(-4841209765562503731574856),(-4281481852729247584630641),true⟩⟩
  | 7,0 => ⟨⟨(-3080501808450579229226343),(-2185695945569318995428447),true⟩,⟨(-6287529529782705736202850),(-5392898125578549893108091),true⟩⟩
  | 7,1 => ⟨⟨(-3816532868892094972110337),(-2892422484792055638106613),true⟩,⟨(-5885978238550174417087732),(-4997939056717190452934463),true⟩⟩
  | 7,2 => ⟨⟨(-4347370917193213591935803),(-3410798640764943120284204),true⟩,⟨(-5443359866427965493176734),(-4575844064597366017856161),true⟩⟩
  | 7,3 => ⟨⟨(-4633020384223245247673691),(-3694463361254070107991609),true⟩,⟨(-5125523059508913279607531),(-4277432559720254405539478),true⟩⟩
  | 7,4 => ⟨⟨(-2261861214027077600530811),(-1410848158916006766547805),true⟩,⟨(-6527998452573757694217250),(-5646686408884353792243585),true⟩⟩
  | 7,5 => ⟨⟨(-1515251486365679030759072),(-712406536628737900865238),true⟩,⟨(-6592961624500373302611557),(-5738817660175465273995482),true⟩⟩
  | 7,6 => ⟨⟨(-956068164825887349087751),(-194120595267266086555310),true⟩,⟨(-6552081317894302078216854),(-5726808890942149710732214),true⟩⟩
  | 7,7 => ⟨⟨(-637534803068525005741526),99563776815944194294920,true⟩,⟨(-6494285463781526433859468),(-5688704006612772452987402),true⟩⟩
  | 8,0 => ⟨⟨(-5446572390735316097108319),(-4651132568638792784746265),true⟩,⟨(-2008763255607068834919862),(-1457367097510776894570988),true⟩⟩
  | 8,1 => ⟨⟨(-5202596743955408037001159),(-4491242294659017128251178),true⟩,⟨(-1136236350040537362300136),(-691864427901896264337863),true⟩⟩
  | 8,2 => ⟨⟨(-4887715545172167819567484),(-4252648065241857590402951),true⟩,⟨(-523677998026652110386025),(-164115535613818076543411),true⟩⟩
  | 8,3 => ⟨⟨(-4657583189069590173126981),(-4071036621493179192066712),true⟩,⟨(-197870872750103814650873),119710573237319405297859,true⟩⟩
  | 8,4 => ⟨⟨(-5483265839637537483019207),(-4615190447431227079727266),true⟩,⟨(-3005540249436806533234905),(-2342475438865895376394463),true⟩⟩
  | 8,5 => ⟨⟨(-5292161237605096719045023),(-4378861244044617299169561),true⟩,⟨(-3920105590691405137272303),(-3167607201422949683598996),true⟩⟩
  | 8,6 => ⟨⟨(-4994720542972372860386284),(-4061871082712368363280806),true⟩,⟨(-4590252664644088089433863),(-3780956198036535439623046),true⟩⟩
  | 8,7 => ⟨⟨(-4760089303950804154309018),(-3822219799437999251197187),true⟩,⟨(-4958464663015370803763467),(-4121749013579305943295285),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP540Value0_0 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP540Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value0_1 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP540Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value0_2 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP540Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value0_3 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP540Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value0_4 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP540Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value0_5 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP540Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value0_6 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP540Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value0_7 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP540Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP540Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 0 j)=sharedDiskP540Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP540Value0_0
  · exact sharedDiskP540Value0_1
  · exact sharedDiskP540Value0_2
  · exact sharedDiskP540Value0_3
  · exact sharedDiskP540Value0_4
  · exact sharedDiskP540Value0_5
  · exact sharedDiskP540Value0_6
  · exact sharedDiskP540Value0_7
private theorem sharedDiskP540Value1_0 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP540Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value1_1 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP540Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value1_2 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP540Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value1_3 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP540Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value1_4 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP540Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value1_5 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP540Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value1_6 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP540Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value1_7 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP540Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP540Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 1 j)=sharedDiskP540Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP540Value1_0
  · exact sharedDiskP540Value1_1
  · exact sharedDiskP540Value1_2
  · exact sharedDiskP540Value1_3
  · exact sharedDiskP540Value1_4
  · exact sharedDiskP540Value1_5
  · exact sharedDiskP540Value1_6
  · exact sharedDiskP540Value1_7
private theorem sharedDiskP540Value2_0 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP540Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value2_1 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP540Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value2_2 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP540Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value2_3 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP540Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value2_4 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP540Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value2_5 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP540Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value2_6 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP540Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value2_7 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP540Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP540Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 2 j)=sharedDiskP540Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP540Value2_0
  · exact sharedDiskP540Value2_1
  · exact sharedDiskP540Value2_2
  · exact sharedDiskP540Value2_3
  · exact sharedDiskP540Value2_4
  · exact sharedDiskP540Value2_5
  · exact sharedDiskP540Value2_6
  · exact sharedDiskP540Value2_7
private theorem sharedDiskP540Value3_0 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP540Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value3_1 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP540Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value3_2 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP540Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value3_3 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP540Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value3_4 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP540Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value3_5 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP540Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value3_6 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP540Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value3_7 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP540Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP540Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 3 j)=sharedDiskP540Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP540Value3_0
  · exact sharedDiskP540Value3_1
  · exact sharedDiskP540Value3_2
  · exact sharedDiskP540Value3_3
  · exact sharedDiskP540Value3_4
  · exact sharedDiskP540Value3_5
  · exact sharedDiskP540Value3_6
  · exact sharedDiskP540Value3_7
private theorem sharedDiskP540Value4_0 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP540Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value4_1 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP540Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value4_2 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP540Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value4_3 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP540Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value4_4 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP540Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value4_5 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP540Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value4_6 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP540Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value4_7 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP540Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP540Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 4 j)=sharedDiskP540Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP540Value4_0
  · exact sharedDiskP540Value4_1
  · exact sharedDiskP540Value4_2
  · exact sharedDiskP540Value4_3
  · exact sharedDiskP540Value4_4
  · exact sharedDiskP540Value4_5
  · exact sharedDiskP540Value4_6
  · exact sharedDiskP540Value4_7
private theorem sharedDiskP540Value5_0 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP540Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value5_1 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP540Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value5_2 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP540Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value5_3 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP540Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value5_4 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP540Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value5_5 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP540Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value5_6 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP540Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value5_7 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP540Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP540Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 5 j)=sharedDiskP540Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP540Value5_0
  · exact sharedDiskP540Value5_1
  · exact sharedDiskP540Value5_2
  · exact sharedDiskP540Value5_3
  · exact sharedDiskP540Value5_4
  · exact sharedDiskP540Value5_5
  · exact sharedDiskP540Value5_6
  · exact sharedDiskP540Value5_7
private theorem sharedDiskP540Value6_0 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP540Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value6_1 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP540Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value6_2 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP540Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value6_3 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP540Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value6_4 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP540Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value6_5 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP540Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value6_6 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP540Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value6_7 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP540Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP540Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 6 j)=sharedDiskP540Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP540Value6_0
  · exact sharedDiskP540Value6_1
  · exact sharedDiskP540Value6_2
  · exact sharedDiskP540Value6_3
  · exact sharedDiskP540Value6_4
  · exact sharedDiskP540Value6_5
  · exact sharedDiskP540Value6_6
  · exact sharedDiskP540Value6_7
private theorem sharedDiskP540Value7_0 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP540Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value7_1 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP540Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value7_2 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP540Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value7_3 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP540Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value7_4 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP540Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value7_5 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP540Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value7_6 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP540Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value7_7 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP540Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP540Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 7 j)=sharedDiskP540Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP540Value7_0
  · exact sharedDiskP540Value7_1
  · exact sharedDiskP540Value7_2
  · exact sharedDiskP540Value7_3
  · exact sharedDiskP540Value7_4
  · exact sharedDiskP540Value7_5
  · exact sharedDiskP540Value7_6
  · exact sharedDiskP540Value7_7
private theorem sharedDiskP540Value8_0 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP540Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value8_1 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP540Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value8_2 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP540Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value8_3 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP540Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value8_4 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP540Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value8_5 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP540Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value8_6 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP540Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP540Value8_7 : truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP540Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP540Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points 8 j)=sharedDiskP540Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP540Value8_0
  · exact sharedDiskP540Value8_1
  · exact sharedDiskP540Value8_2
  · exact sharedDiskP540Value8_3
  · exact sharedDiskP540Value8_4
  · exact sharedDiskP540Value8_5
  · exact sharedDiskP540Value8_6
  · exact sharedDiskP540Value8_7
theorem sharedDiskP540Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP540Params (sharedChord521Gauss8Points i j)=sharedDiskP540Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP540Values0_eq
  · exact sharedDiskP540Values1_eq
  · exact sharedDiskP540Values2_eq
  · exact sharedDiskP540Values3_eq
  · exact sharedDiskP540Values4_eq
  · exact sharedDiskP540Values5_eq
  · exact sharedDiskP540Values6_eq
  · exact sharedDiskP540Values7_eq
  · exact sharedDiskP540Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP540Box : HorizontalRectangle := ⟨(33/40),(331/400),(957032188846669/1649267441664000),(960253414318669/1649267441664000),(485871789948407149871789989174913/10384593717069655257060992658440192),(4060327415133378731633763901640513/5192296858534827628530496329220096),(-277411437362049190935552830794509/81129638414606681695789005144064),(-216047107003368314283553015524109/81129638414606681695789005144064),true,[]⟩
noncomputable def sharedDiskP540Grid : CGrid := momentChordGrid sharedDiskP540Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP540Columns : containedInReported sharedDiskP540Grid.re sharedDiskP540Box.reLo sharedDiskP540Box.reHi=true ∧ containedInReported sharedDiskP540Grid.im sharedDiskP540Box.imLo sharedDiskP540Box.imHi=true := by
  rw [sharedDiskP540Grid,momentChordGrid_eq_tabulated sharedDiskP540Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP540Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP540Values_eq]
  decide +kernel
theorem sharedDiskP540Sound : sharedDiskP540Box.Sound := by
  intro t a tl tu al au
  change (((33/40):ℚ):ℝ)≤t at tl
  change t≤(((331/400):ℚ):ℝ) at tu
  change (((957032188846669/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((960253414318669/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP540Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(33/40))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((331/400):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(957032188846669/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((960253414318669/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP540Columns.1 sharedDiskP540Columns.2
def sharedDiskP540Rows : List SignRow := [positive_540.toSignRow]
theorem sharedDiskP540Rows_actual : ∀ r∈sharedDiskP540Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP540Rows.all (sharedDiskP540Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP540Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP541Params : ChordParams := ⟨⟨(-27451919758114985304552),(-27139789586379719405618),true⟩,⟨1908217591029694431497998,1922946799371259639805448,true⟩,⟨132186023576722494508558,134057575607400168632660,true⟩,⟨246377073263458872985759,249397222408342828891453,true⟩,⟨354226898305451325709190,356347989134420242537601,true⟩,⟨1155241037793158921208174,1155838035073659680631546,true⟩,⟨(-2194061800439317839484769),(-2186323347865323345428262),true⟩,⟨⟨1137752272296259579419433,1166565118973723857475366,true⟩,⟨(-44248872),44248872,true⟩⟩⟩
theorem sharedDiskP541Params_ok : chordParams (Grid.ofRats (331/400) (83/100)) (Grid.ofRats (958269376417459/1649267441664000) (961490601889459/1649267441664000))=sharedDiskP541Params := by decide +kernel
def sharedDiskP541Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3159215530153349957097116),(-2647057621493969586620098),true⟩,⟨(-315719137218339508423455),93655453765423255133355,true⟩⟩
  | 0,1 => ⟨⟨(-2811167791675638193831026),(-2339540172288396186331481),true⟩,⟨(-371189930632109146277715),18069283705196230271602,true⟩⟩
  | 0,2 => ⟨⟨(-2558916566383690382140402),(-2119453255779116127593756),true⟩,⟨(-419138214211761277575801),(-49166642283470580805314),true⟩⟩
  | 0,3 => ⟨⟨(-2416425373601872725704939),(-1996063325588038382778025),true⟩,⟨(-448872807794523522334650),(-91409209047814934936969),true⟩⟩
  | 0,4 => ⟨⟨(-3569799791449303561417411),(-3016085499080977492797774),true⟩,⟨(-267464614140449019218892),154870659949361394574780,true⟩⟩
  | 0,5 => ⟨⟨(-3986151203771563314419728),(-3397414120870927971187428),true⟩,⟨(-238724697644301082743144),187383048800444176925435,true⟩⟩
  | 0,6 => ⟨⟨(-4336877878854458245691836),(-3724295423463893571562427),true⟩,⟨(-231659648366647306530434),187842200220209946872082,true⟩⟩
  | 0,7 => ⟨⟨(-4556518601953600773480813),(-3931338338688557206215720),true⟩,⟨(-239287146573692434093246),174984508758643943335898,true⟩⟩
  | 1,0 => ⟨⟨(-1556514134495994175106487),(-1257822688492614937429590),true⟩,⟨(-659694628158505434704624),(-390031399384497738450009),true⟩⟩
  | 1,1 => ⟨⟨(-1367983196152201317527935),(-1096615920144256981431705),true⟩,⟨(-709239240545087293974676),(-461086485086643750658045),true⟩⟩
  | 1,2 => ⟨⟨(-1231003712868299382647540),(-979238941283617366840748),true⟩,⟨(-744703052380194362332013),(-512224515331739348581837),true⟩⟩
  | 1,3 => ⟨⟨(-1153082955294585769452998),(-912313732614277462887839),true⟩,⟨(-764447878736416196347103),(-540833573947417950737580),true⟩⟩
  | 1,4 => ⟨⟨(-1781097836943677875024892),(-1449772665217130884226091),true⟩,⟨(-601034238945516378412224),(-306350108745893445533873),true⟩⟩
  | 1,5 => ⟨⟨(-2014588397336792438613686),(-1649760654105037899140924),true⟩,⟨(-542038479118426952513878),(-222668533037762888151542),true⟩⟩
  | 1,6 => ⟨⟨(-2218257603010505757335753),(-1824932601729484390949740),true⟩,⟨(-493251217328089430241834),(-153919833262998089990544),true⟩⟩
  | 1,7 => ⟨⟨(-2349837269022507976157984),(-1938591346859980745132930),true⟩,⟨(-463384410729254114519457),(-112102727132760374430909),true⟩⟩
  | 2,0 => ⟨⟨(-290412692115290645409933),(-145932266484469739824956),true⟩,⟨(-934728552951550511019945),(-787178812600111676331332),true⟩⟩
  | 2,1 => ⟨⟨(-107167064537849102196316),25367201085598965811081,true⟩,⟨(-951777250235404942043309),(-813481508136002492693888),true⟩⟩
  | 2,2 => ⟨⟨26683085813456788765483,152417793029899811286843,true⟩,⟨(-958889922152504769901344),(-826403703324043926641629),true⟩⟩
  | 2,3 => ⟨⟨103231466398067704638267,225816749231589364188792,true⟩,⟨(-961076816404601418030630),(-831565603636970889361438),true⟩⟩
  | 2,4 => ⟨⟨(-509617482659477287595499),(-347614073862542410639449),true⟩,⟨(-903167350530938931539648),(-742553785887728918087483),true⟩⟩
  | 2,5 => ⟨⟨(-743949743064253250925627),(-557944168227895225661356),true⟩,⟨(-858128967753496970334446),(-679232984540291562893317),true⟩⟩
  | 2,6 => ⟨⟨(-956431773088762236163599),(-742707412425361706927998),true⟩,⟨(-812046241170806101538557),(-610413023930634457531784),true⟩⟩
  | 2,7 => ⟨⟨(-1098417487515772994992666),(-865276947596784627675218),true⟩,⟨(-778041403090909716861527),(-560603504643697298804615),true⟩⟩
  | 3,0 => ⟨⟨1014174787580074911195133,1141641952661157309611526,true⟩,⟨(-957358730245793399311678),(-831201188338615077086693),true⟩⟩
  | 3,1 => ⟨⟨1234721773950381953964112,1369241642152986513094600,true⟩,⟨(-980682541268499951757089),(-849610551732577774689812),true⟩⟩
  | 3,2 => ⟨⟨1404770727345701295196511,1546277812657938366022046,true⟩,⟨(-1018101707314680001406629),(-881471567544402832622877),true⟩⟩
  | 3,3 => ⟨⟨1506290570093487448796687,1652720251140493235003057,true⟩,⟨(-1051105876334337076076206),(-910295041569967758631497),true⟩⟩
  | 3,4 => ⟨⟨765144307851063679245289,886989514356672968092669,true⟩,⟨(-952586625710368428638874),(-829378357498899367293303),true⟩⟩
  | 3,5 => ⟨⟨515065006471050003155717,633559870869824984714926,true⟩,⟨(-957694862198620740577724),(-835056442533792829335180),true⟩⟩
  | 3,6 => ⟨⟨299401301811493382828755,416905179100797495078534,true⟩,⟨(-961364583738805413726978),(-837409276824507261837909),true⟩⟩
  | 3,7 => ⟨⟨157291232701537827062525,277878783292584171977375,true⟩,⟨(-961864541535215742622370),(-834300118131026496932464),true⟩⟩
  | 4,0 => ⟨⟨2239224043209558695901443,2473553243554384547461717,true⟩,⟨(-1753687419967374474610733),(-1524172033343158667645272),true⟩⟩
  | 4,1 => ⟨⟨2403423456435922369635444,2683055608573060579962995,true⟩,⟨(-2206970934966533621149599),(-1928048465175316853444589),true⟩⟩
  | 4,2 => ⟨⟨2473789364802411644742982,2800444139568028586117465,true⟩,⟨(-2709764502333529729544724),(-2377644089949039365576696),true⟩⟩
  | 4,3 => ⟨⟨2466196934104915415419212,2827159264694911932084903,true⟩,⟨(-3090698598081810039239819),(-2718651358082539469208695),true⟩⟩
  | 4,4 => ⟨⟨2027313575119576285158373,2225753524340015606475732,true⟩,⟨(-1428207208632981824058097),(-1236307013581466348532349),true⟩⟩
  | 4,5 => ⟨⟨1820380993949932074610887,1993711345805797090847760,true⟩,⟨(-1227920699734029676161093),(-1061328490175493137151795),true⟩⟩
  | 4,6 => ⟨⟨1655120569617300374501032,1812728878376412261249373,true⟩,⟨(-1119524932574838458163314),(-968235373071079140737200),true⟩⟩
  | 4,7 => ⟨⟨1555146472690115104519917,1704679627694671715164600,true⟩,⟨(-1070714143697974640099559),(-927081594681141829266007),true⟩⟩
  | 5,0 => ⟨⟨2226701105499622298126802,2674074085320669037175325,true⟩,⟨(-4082132594750894721271267),(-3605583184062261012963948),true⟩⟩
  | 5,1 => ⟨⟨2091342066772372719608612,2564156198440574674395447,true⟩,⟨(-4378919544390198275085911),(-3870528480026707016560159),true⟩⟩
  | 5,2 => ⟨⟨1954411031156510363208166,2448214691432456750684867,true⟩,⟨(-4624322176322827675160703),(-4089279279203613445683891),true⟩⟩
  | 5,3 => ⟨⟨1857453264953324999396136,2364214830625029215041325,true⟩,⟨(-4775819858740783975857061),(-4224145280034725748826743),true⟩⟩
  | 5,4 => ⟨⟨2332469926570237673910469,2754037091778698994994428,true⟩,⟨(-3782671659581106494482093),(-3337916567138092764379152),true⟩⟩
  | 5,5 => ⟨⟨2400610218763189232103723,2799587025193137616569308,true⟩,⟨(-3522517196301332829270629),(-3105184923903583079543533),true⟩⟩
  | 5,6 => ⟨⟨2437207490434610759549836,2819308596284628954058761,true⟩,⟨(-3329766440997198171886751),(-2932671240004599259584157),true⟩⟩
  | 5,7 => ⟨⟨2452886095093864917129293,2825240412123043469521985,true⟩,⟨(-3219178518915814637693122),(-2833674381237600020627032),true⟩⟩
  | 6,0 => ⟨⟨694028089830711379770443,1309711346877533415270648,true⟩,⟨(-5905352263380833077736966),(-5216410198032394107921905),true⟩⟩
  | 6,1 => ⟨⟨200837697305739922529383,863029144676468130577135,true⟩,⟨(-6175084418485637010595372),(-5438782331058032306645681),true⟩⟩
  | 6,2 => ⟨⟨(-246005667921565976006394),454897064790913448670219,true⟩,⟨(-6350878890191311935352018),(-5578100535853613917471034),true⟩⟩
  | 6,3 => ⟨⟨(-539097592282189667133648),185802125475707253512016,true⟩,⟨(-6435251701503227915132116),(-5641448365705895594864337),true⟩⟩
  | 6,4 => ⟨⟨1138280120778133799412219,1715221897296110411945874,true⟩,⟨(-5578427366495007840988051),(-4934775751044361024289701),true⟩⟩
  | 6,5 => ⟨⟨1472316246050885767651605,2020656586390325524106896,true⟩,⟨(-5259966653708911062241949),(-4653947621667389468777663),true⟩⟩
  | 6,6 => ⟨⟨1691458796790122697242074,2217767065358463616082896,true⟩,⟨(-5003979799896466506272965),(-4426948811821306763244279),true⟩⟩
  | 6,7 => ⟨⟨1806199233159874311232084,2319314546658182118724463,true⟩,⟨(-4850052301455929791037191),(-4290171438865276268276936),true⟩⟩
  | 7,0 => ⟨⟨(-3108014315466836999148678),(-2216565376204559140679277),true⟩,⟨(-6238292074585567917794528),(-5348890981991429859621420),true⟩⟩
  | 7,1 => ⟨⟨(-3833069253817525010170284),(-2913291541463249502127193),true⟩,⟨(-5833372897540012138225386),(-4951358364344044364041831),true⟩⟩
  | 7,2 => ⟨⟨(-4354583872644999931803138),(-3423040030296770906420612),true⟩,⟨(-5390383914275997442444500),(-4529318318560609937113069),true⟩⟩
  | 7,3 => ⟨⟨(-4634618537274937975324226),(-3701448886144598203071581),true⟩,⟨(-5073427027442110988055798),(-4231928665846778297093389),true⟩⟩
  | 7,4 => ⟨⟨(-2299230733302887381996002),(-1450516764188242917002961),true⟩,⟨(-6485116225271902225885861),(-5607998599568264404811687),true⟩⟩
  | 7,5 => ⟨⟨(-1559530313626151573931954),(-758067823354753018229541),true⟩,⟨(-6557579866157423231659773),(-5706614339760308517904608),true⟩⟩
  | 7,6 => ⟨⟨(-1004190572266712937872528),(-242978563686656981666663),true⟩,⟨(-6523127454261278136196021),(-5700254148590122533853314),true⟩⟩
  | 7,7 => ⟨⟨(-687311205064139951988320),49224310523359206179180,true⟩,⟨(-6469245849268333913209995),(-5665618754500455200536348),true⟩⟩
  | 8,0 => ⟨⟨(-5422059291845618326741765),(-4632042914770060992585700),true⟩,⟨(-1985504000431665101849699),(-1438547179584666727715005),true⟩⟩
  | 8,1 => ⟨⟨(-5178868610541957178800131),(-4472023148188607119830796),true⟩,⟨(-1123526807129595086760449),(-682290293569898513130256),true⟩⟩
  | 8,2 => ⟨⟨(-4866882533834092346630743),(-4235427998027934984441163),true⟩,⟨(-518194166125060307211045),(-160760255191943626829941),true⟩⟩
  | 8,3 => ⟨⟨(-4639218704202814718716873),(-4055697165139791105927446),true⟩,⟨(-196007203866097036058903),120048407659007161036826,true⟩⟩
  | 8,4 => ⟨⟨(-5462165329398212238931325),(-4600075626047955437787993),true⟩,⟨(-2970783123105553945196033),(-2313351155179549972487464),true⟩⟩
  | 8,5 => ⟨⟨(-5278120231218091865028355),(-4370870932828740229961224),true⟩,⟨(-3876174781558977917366301),(-3130040872249571081304036),true⟩⟩
  | 8,6 => ⟨⟨(-4988386843067079815763548),(-4061338658744055119240958),true⟩,⟨(-4541032232847802108392942),(-3738353157393305676857007),true⟩⟩
  | 8,7 => ⟨⟨(-4759022733413975926559405),(-3826693119437584953691344),true⟩,⟨(-4907103527476437123176363),(-4077013620344196546757414),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP541Value0_0 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP541Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value0_1 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP541Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value0_2 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP541Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value0_3 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP541Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value0_4 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP541Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value0_5 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP541Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value0_6 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP541Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value0_7 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP541Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP541Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 0 j)=sharedDiskP541Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP541Value0_0
  · exact sharedDiskP541Value0_1
  · exact sharedDiskP541Value0_2
  · exact sharedDiskP541Value0_3
  · exact sharedDiskP541Value0_4
  · exact sharedDiskP541Value0_5
  · exact sharedDiskP541Value0_6
  · exact sharedDiskP541Value0_7
private theorem sharedDiskP541Value1_0 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP541Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value1_1 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP541Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value1_2 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP541Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value1_3 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP541Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value1_4 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP541Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value1_5 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP541Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value1_6 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP541Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value1_7 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP541Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP541Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 1 j)=sharedDiskP541Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP541Value1_0
  · exact sharedDiskP541Value1_1
  · exact sharedDiskP541Value1_2
  · exact sharedDiskP541Value1_3
  · exact sharedDiskP541Value1_4
  · exact sharedDiskP541Value1_5
  · exact sharedDiskP541Value1_6
  · exact sharedDiskP541Value1_7
private theorem sharedDiskP541Value2_0 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP541Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value2_1 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP541Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value2_2 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP541Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value2_3 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP541Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value2_4 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP541Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value2_5 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP541Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value2_6 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP541Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value2_7 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP541Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP541Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 2 j)=sharedDiskP541Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP541Value2_0
  · exact sharedDiskP541Value2_1
  · exact sharedDiskP541Value2_2
  · exact sharedDiskP541Value2_3
  · exact sharedDiskP541Value2_4
  · exact sharedDiskP541Value2_5
  · exact sharedDiskP541Value2_6
  · exact sharedDiskP541Value2_7
private theorem sharedDiskP541Value3_0 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP541Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value3_1 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP541Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value3_2 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP541Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value3_3 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP541Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value3_4 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP541Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value3_5 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP541Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value3_6 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP541Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value3_7 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP541Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP541Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 3 j)=sharedDiskP541Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP541Value3_0
  · exact sharedDiskP541Value3_1
  · exact sharedDiskP541Value3_2
  · exact sharedDiskP541Value3_3
  · exact sharedDiskP541Value3_4
  · exact sharedDiskP541Value3_5
  · exact sharedDiskP541Value3_6
  · exact sharedDiskP541Value3_7
private theorem sharedDiskP541Value4_0 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP541Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value4_1 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP541Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value4_2 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP541Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value4_3 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP541Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value4_4 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP541Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value4_5 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP541Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value4_6 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP541Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value4_7 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP541Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP541Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 4 j)=sharedDiskP541Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP541Value4_0
  · exact sharedDiskP541Value4_1
  · exact sharedDiskP541Value4_2
  · exact sharedDiskP541Value4_3
  · exact sharedDiskP541Value4_4
  · exact sharedDiskP541Value4_5
  · exact sharedDiskP541Value4_6
  · exact sharedDiskP541Value4_7
private theorem sharedDiskP541Value5_0 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP541Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value5_1 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP541Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value5_2 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP541Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value5_3 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP541Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value5_4 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP541Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value5_5 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP541Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value5_6 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP541Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value5_7 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP541Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP541Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 5 j)=sharedDiskP541Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP541Value5_0
  · exact sharedDiskP541Value5_1
  · exact sharedDiskP541Value5_2
  · exact sharedDiskP541Value5_3
  · exact sharedDiskP541Value5_4
  · exact sharedDiskP541Value5_5
  · exact sharedDiskP541Value5_6
  · exact sharedDiskP541Value5_7
private theorem sharedDiskP541Value6_0 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP541Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value6_1 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP541Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value6_2 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP541Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value6_3 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP541Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value6_4 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP541Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value6_5 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP541Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value6_6 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP541Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value6_7 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP541Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP541Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 6 j)=sharedDiskP541Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP541Value6_0
  · exact sharedDiskP541Value6_1
  · exact sharedDiskP541Value6_2
  · exact sharedDiskP541Value6_3
  · exact sharedDiskP541Value6_4
  · exact sharedDiskP541Value6_5
  · exact sharedDiskP541Value6_6
  · exact sharedDiskP541Value6_7
private theorem sharedDiskP541Value7_0 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP541Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value7_1 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP541Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value7_2 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP541Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value7_3 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP541Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value7_4 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP541Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value7_5 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP541Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value7_6 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP541Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value7_7 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP541Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP541Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 7 j)=sharedDiskP541Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP541Value7_0
  · exact sharedDiskP541Value7_1
  · exact sharedDiskP541Value7_2
  · exact sharedDiskP541Value7_3
  · exact sharedDiskP541Value7_4
  · exact sharedDiskP541Value7_5
  · exact sharedDiskP541Value7_6
  · exact sharedDiskP541Value7_7
private theorem sharedDiskP541Value8_0 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP541Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value8_1 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP541Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value8_2 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP541Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value8_3 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP541Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value8_4 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP541Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value8_5 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP541Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value8_6 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP541Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP541Value8_7 : truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP541Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP541Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points 8 j)=sharedDiskP541Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP541Value8_0
  · exact sharedDiskP541Value8_1
  · exact sharedDiskP541Value8_2
  · exact sharedDiskP541Value8_3
  · exact sharedDiskP541Value8_4
  · exact sharedDiskP541Value8_5
  · exact sharedDiskP541Value8_6
  · exact sharedDiskP541Value8_7
theorem sharedDiskP541Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP541Params (sharedChord521Gauss8Points i j)=sharedDiskP541Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP541Values0_eq
  · exact sharedDiskP541Values1_eq
  · exact sharedDiskP541Values2_eq
  · exact sharedDiskP541Values3_eq
  · exact sharedDiskP541Values4_eq
  · exact sharedDiskP541Values5_eq
  · exact sharedDiskP541Values6_eq
  · exact sharedDiskP541Values7_eq
  · exact sharedDiskP541Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP541Box : HorizontalRectangle := ⟨(331/400),(83/100),(958269376417459/1649267441664000),(961490601889459/1649267441664000),(237783798867819063999575855362305/10384593717069655257060992658440192),(3906429441362403039411824110286977/5192296858534827628530496329220096),(-4433748513339531742023363844224969/1298074214633706907132624082305024),(-3459274649025737858523122947700681/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP541Grid : CGrid := momentChordGrid sharedDiskP541Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP541Columns : containedInReported sharedDiskP541Grid.re sharedDiskP541Box.reLo sharedDiskP541Box.reHi=true ∧ containedInReported sharedDiskP541Grid.im sharedDiskP541Box.imLo sharedDiskP541Box.imHi=true := by
  rw [sharedDiskP541Grid,momentChordGrid_eq_tabulated sharedDiskP541Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP541Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP541Values_eq]
  decide +kernel
theorem sharedDiskP541Sound : sharedDiskP541Box.Sound := by
  intro t a tl tu al au
  change (((331/400):ℚ):ℝ)≤t at tl
  change t≤(((83/100):ℚ):ℝ) at tu
  change (((958269376417459/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((961490601889459/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP541Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(331/400))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((83/100):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(958269376417459/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((961490601889459/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP541Columns.1 sharedDiskP541Columns.2
def sharedDiskP541Rows : List SignRow := [positive_541.toSignRow]
theorem sharedDiskP541Rows_actual : ∀ r∈sharedDiskP541Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP541Rows.all (sharedDiskP541Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP541Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharedDiskP542Params : ChordParams := ⟨⟨(-27608616296371276551435),(-27451919758114985303981),true⟩,⟨1904997644720635094404274,1912335217032004107378204,true⟩,⟨133031558101844175566998,133967309089659590495635,true⟩,⟨248549215365853713069300,250062371625727815362085,true⟩,⟨356212881327871438963203,357273347140397949118117,true⟩,⟨1154941445034835837239578,1155241037793158921209268,true⟩,⟨(-2186323347865323345437299),(-2182469509201696391237128),true⟩,⟨⟨1144367188184350595960559,1158785051992462838311510,true⟩,⟨(-46684746),46684746,true⟩⟩⟩
theorem sharedDiskP542Params_ok : chordParams (Grid.ofRats (83/100) (133/160)) (Grid.ofRats (960006490322437/1649267441664000) (961617103058437/1649267441664000))=sharedDiskP542Params := by decide +kernel
def sharedDiskP542Values (i : Fin 9) (j : Fin 8) : CGrid := match i.val, j.val with
  | 0,0 => ⟨⟨(-3038956968187120777812180),(-2751255618021722615476216),true⟩,⟨(-226433456088300357967285),8458811674163956222490,true⟩⟩
  | 0,1 => ⟨⟨(-2702454799177061634488188),(-2437447590846855586255985),true⟩,⟨(-284411816583074562747690),(-61782743519267598870716),true⟩⟩
  | 0,2 => ⟨⟨(-2459295579736480650106522),(-2212176815675122145768813),true⟩,⟨(-335221818237104620585396),(-123748490962375452242550),true⟩⟩
  | 0,3 => ⟨⟨(-2322261437210272020244681),(-2085642119536447997992427),true⟩,⟨(-366946327517372252995040),(-162397798205013251458498),true⟩⟩
  | 0,4 => ⟨⟨(-3437139619747291589823363),(-3126354114804333080800319),true⟩,⟨(-177412201203077404726513),66188053356252784828336,true⟩⟩
  | 0,5 => ⟨⟨(-3842263109340581328478243),(-3512387316111168869634260),true⟩,⟨(-150288316473941162193572),95662130435564454564470,true⟩⟩
  | 0,6 => ⟨⟨(-4184633150445265079116602),(-3842060199591795594497200),true⟩,⟨(-145784846450225804328817),97485526380105429210217,true⟩⟩
  | 0,7 => ⟨⟨(-4399415384230094057538522),(-4050334604385946472265866),true⟩,⟨(-153278274368463430879737),86985987679691683792436,true⟩⟩
  | 1,0 => ⟨⟨(-1493616797304742477342842),(-1325782869342488366616584),true⟩,⟨(-594775067105111591641697),(-441751357909250159718243),true⟩⟩
  | 1,1 => ⟨⟨(-1311913300377967346057516),(-1159520882319675807337482),true⟩,⟨(-648900113729401140956947),(-508366398768029313474138),true⟩⟩
  | 1,2 => ⟨⟨(-1179821889728617816119667),(-1038486092012154899046110),true⟩,⟨(-687797107689324219986318),(-556324684335979854802293),true⟩⟩
  | 1,3 => ⟨⟨(-1104642725611487688914713),(-969499283223045672888257),true⟩,⟨(-709521299822738672413764),(-583158373427671917268554),true⟩⟩
  | 1,4 => ⟨⟨(-1710000219342374981936093),(-1523692282101639260567841),true⟩,⟨(-530970555133159353086565),(-363334584106019482673849),true⟩⟩
  | 1,5 => ⟨⟨(-1934988103889694063884045),(-1729694419648483497898641),true⟩,⟨(-467098162549974997890030),(-284943935051835376317231),true⟩⟩
  | 1,6 => ⟨⟨(-2131331353802554649486929),(-1909885775894287113653585),true⟩,⟨(-414528057596440733046021),(-220541749561489995329444),true⟩⟩
  | 1,7 => ⟨⟨(-2258248264136296419758386),(-2026649764239667809516887),true⟩,⟨(-382477230591423642498513),(-181356493544857506842904),true⟩⟩
  | 2,0 => ⟨⟨(-266744453918302523992112),(-186081774496925651172878),true⟩,⟨(-897956364252591253854542),(-815814385318251569602460),true⟩⟩
  | 2,1 => ⟨⟨(-86665741342450971606509),(-12921917094849293348742),true⟩,⟨(-917776812653882604910405),(-841130062411117011053232),true⟩⟩
  | 2,2 => ⟨⟨45218437790055216172353,115011308230279307172736,true⟩,⟨(-926755261378040909782887),(-853555478952903013966426),true⟩⟩
  | 2,3 => ⟨⟨120893091262148367302729,188821413428263948712237,true⟩,⟨(-929947188970529929349713),(-858513302535766740923135),true⟩⟩
  | 2,4 => ⟨⟨(-481455577167339523445184),(-390741140665273320557706),true⟩,⟨(-862780492865332149012739),(-772862991040612488571547),true⟩⟩
  | 2,5 => ⟨⟨(-709224834381673182226509),(-604784254589925582811827),true⟩,⟨(-813668043700239458161380),(-712902837118142282544099),true⟩⟩
  | 2,6 => ⟨⟨(-914745679423711792891946),(-794797296575721402683986),true⟩,⟨(-762156468330534863801356),(-648415280053147707938183),true⟩⟩
  | 2,7 => ⟨⟨(-1051880292910420880085507),(-921028473321690304900722),true⟩,⟨(-724511023454089054058298),(-601701768240936506681822),true⟩⟩
  | 3,0 => ⟨⟨1031707610973041832030806,1100186329911745228662884,true⟩,⟨(-931102340596243921217984),(-863205196742867717826501),true⟩⟩
  | 3,1 => ⟨⟨1253903626655155813921812,1325783920840580781027407,true⟩,⟨(-954170952532048462894729),(-883950254067300642345019),true⟩⟩
  | 3,2 => ⟨⟨1425611729849062883480445,1500959231571023200697629,true⟩,⟨(-990984766188885172149427),(-918017374915741938719289),true⟩⟩
  | 3,3 => ⟨⟨1528292271852129079971432,1606116502539431272569273,true⟩,⟨(-1023435755238864528677306),(-948365601441313575181423),true⟩⟩
  | 3,4 => ⟨⟨781456315905250142355308,847383576188944749422513,true⟩,⟨(-925992640239019972547322),(-859299622372606165555374),true⟩⟩
  | 3,5 => ⟨⟨530797714704780617949384,595445448625382785467979,true⟩,⟨(-930180903678146330779589),(-863365462609723003291847),true⟩⟩
  | 3,6 => ⟨⟨315163840053808417801509,379771572240813702731104,true⟩,⟨(-932627157975076779816943),(-864683180389501000077026),true⟩⟩
  | 3,7 => ⟨⟨174389735262376547486228,241128490314170600047804,true⟩,⟨(-931415028978112458745558),(-861137734523406075234454),true⟩⟩
  | 4,0 => ⟨⟨2280107007367360542062342,2403077934631977590833907,true⟩,⟨(-1708563484813822548292925),(-1587895044704266010485909),true⟩⟩
  | 4,1 => ⟨⟨2452771606285084358221228,2599247193304189615732515,true⟩,⟨(-2151122972207693821843420),(-2004840268341793196837927),true⟩⟩
  | 4,2 => ⟨⟨2531261948389962249018614,2702192577125218328343147,true⟩,⟨(-2641629005834977493969290),(-2467722742819956434927757),true⟩⟩
  | 4,3 => ⟨⟨2529278650859964778528122,2718071574112135102157223,true⟩,⟨(-3012807417337511343483126),(-2818156993210065880495971),true⟩⟩
  | 4,4 => ⟨⟨2060923388968123412146776,2165348223973033752661880,true⟩,⟨(-1390819230002334642711176),(-1289590666535062552807318),true⟩⟩
  | 4,5 => ⟨⟨1848552025048998155630626,1940073524401213873681921,true⟩,⟨(-1195510114437604720601869),(-1107297405809702181528163),true⟩⟩
  | 4,6 => ⟨⟨1679732398510800825545569,1763226590338547942169080,true⟩,⟨(-1090003169249300982645273),(-1009612604914186988627888),true⟩⟩
  | 4,7 => ⟨⟨1577887882726459055491309,1657282781999625467108948,true⟩,⟨(-1042585891828766606899376),(-966086560994071892451075),true⟩⟩
  | 5,0 => ⟨⟨2303232352658745134036274,2537043580575011126223121,true⟩,⟨(-3976371084195132231273054),(-3727425522753716844394074),true⟩⟩
  | 5,1 => ⟨⟨2171779853119683917122446,2418846040579784821583719,true⟩,⟨(-4263942264344937682350913),(-3998459693868542467379810),true⟩⟩
  | 5,2 => ⟨⟨2038102262787323189518596,2296102587343317777777437,true⟩,⟨(-4501348618403593291456055),(-4222028254974211924191527),true⟩⟩
  | 5,3 => ⟨⟨1943179194316999987031151,2207928738223230215999960,true⟩,⟨(-4647719183935386958335851),(-4359765571942909659578861),true⟩⟩
  | 5,4 => ⟨⟨2405041193462522107996679,2625406595222102351861658,true⟩,⟨(-3685763680939203208716116),(-3453334646579968082850155),true⟩⟩
  | 5,5 => ⟨⟨2469688494070480902433810,2678283817244979026641194,true⟩,⟨(-3432977699410267306517609),(-3214796657082209842506973),true⟩⟩
  | 5,6 => ⟨⟨2503646340285770557903808,2703449947034993064605823,true⟩,⟨(-3245510890052558128108929),(-3037845182635734343293855),true⟩⟩
  | 5,7 => ⟨⟨2517784927796821282244477,2712511334968172122217551,true⟩,⟨(-3137891981339457325470264),(-2936249188765372951820129),true⟩⟩
  | 6,0 => ⟨⟨803115701530596393300361,1125283916634313175946793,true⟩,⟨(-5728830044378017134899968),(-5369245444823455344706026),true⟩⟩
  | 6,1 => ⟨⟨321137775906676587609949,667430379975791133359166,true⟩,⟨(-5981613585607838413295168),(-5597504902953884081185710),true⟩⟩
  | 6,2 => ⟨⟨(-115114250069038852722264),250973396120000758275051,true⟩,⟨(-6143824848138504633424212),(-5740846862133105616631643),true⟩⟩
  | 6,3 => ⟨⟨(-401243317929644596712509),(-22742225190266891284948),true⟩,⟨(-6220120726075598765497853),(-5806275283282437262978313),true⟩⟩
  | 6,4 => ⟨⟨1236564039234926281418884,1537353457028877355337227,true⟩,⟨(-5419436335713955943180183),(-5084072519082767960401690),true⟩⟩
  | 6,5 => ⟨⟨1564810948608379955440586,1851210099555634075713562,true⟩,⟨(-5114314558923472129272361),(-4798163744482020136619945),true⟩⟩
  | 6,6 => ⟨⟨1780311279701289578738247,2055240066015762803911479,true⟩,⟨(-4867848198593559790504776),(-4566735725839525227287713),true⟩⟩
  | 6,7 => ⟨⟨1892932880781142887741711,2160991491191052259672021,true⟩,⟨(-4719381447865670897705223),(-4427168692875151440353060),true⟩⟩
  | 7,0 => ⟨⟨(-2910682154059075699292909),(-2446766981202130700238254),true⟩,⟨(-5980237903560756933799459),(-5517152078237851422486242),true⟩⟩
  | 7,1 => ⟨⟨(-3620076928908312553909395),(-3142037574047198865047082),true⟩,⟨(-5574825558306536364649623),(-5115606409730680205048239),true⟩⟩
  | 7,2 => ⟨⟨(-4131317060913582048347747),(-3647656996169672120260411),true⟩,⟨(-5136927557656840484197037),(-4688547426275649007706020),true⟩⟩
  | 7,3 => ⟨⟨(-4406501392181427175039708),(-3922290893216233235504774),true⟩,⟨(-4825588850228492781425735),(-4387312512200709322401930),true⟩⟩
  | 7,4 => ⟨⟨(-2120241969125601365058536),(-1677967926496114498281777),true⟩,⟨(-6234702057841770892206819),(-5777895554485553468483364),true⟩⟩
  | 7,5 => ⟨⟨(-1397692004291405822741508),(-979537264809617360088899),true⟩,⟨(-6319167732954000299109458),(-5875820372955491890515819),true⟩⟩
  | 7,6 => ⟨⟨(-855361652471322607658492),(-457847213003633065507450),true⟩,⟨(-6296454676957009612482108),(-5867596400803407210927069),true⟩⟩
  | 7,7 => ⟨⟨(-545950799860140119873372),(-161212122267357532824690),true⟩,⟨(-6250268249004465595387183),(-5831347619717297777369658),true⟩⟩
  | 8,0 => ⟨⟨(-5207925879564816203256220),(-4799537476939932629132314),true⟩,⟨(-1832920112492348046553748),(-1546447560536886887723923),true⟩⟩
  | 8,1 => ⟨⟨(-4984198868116451345749694),(-4619920184837609710930106),true⟩,⟨(-1005981745695417133827820),(-775517510358325125064398),true⟩⟩
  | 8,2 => ⟨⟨(-4692840227765685585771532),(-4367463152139682516354372),true⟩,⟨(-427216347482936887773541),(-239912788603635907917264),true⟩⟩
  | 8,3 => ⟨⟨(-4478886257827777541857727),(-4178227406348645684270102),true⟩,⟨(-119907123833847179706627),43777656745289880331799,true⟩⟩
  | 8,4 => ⟨⟨(-5233297114243861850808829),(-4787234863585088561437092),true⟩,⟨(-2782058865510620726787145),(-2438649728744348106505705),true⟩⟩
  | 8,5 => ⟨⟨(-5043902091390538782731312),(-4573984260499833246545683),true⟩,⟨(-3658414828833420725070403),(-3269304896256258736041818),true⟩⟩
  | 8,6 => ⟨⟨(-4755469779546896487792823),(-4274855729558533982706002),true⟩,⟨(-4305129198987860563507432),(-3886876043269113181510275),true⟩⟩
  | 8,7 => ⟨⟨(-4528996963360481358195543),(-4045362455895539388467242),true⟩,⟨(-4662696277406110079775766),(-4230306695506053245617037),true⟩⟩
  | _,_ => CGrid.ofInt 0
private theorem sharedDiskP542Value0_0 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 0 (0:Fin 8))=sharedDiskP542Values 0 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value0_1 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 0 (1:Fin 8))=sharedDiskP542Values 0 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value0_2 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 0 (2:Fin 8))=sharedDiskP542Values 0 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value0_3 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 0 (3:Fin 8))=sharedDiskP542Values 0 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value0_4 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 0 (4:Fin 8))=sharedDiskP542Values 0 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value0_5 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 0 (5:Fin 8))=sharedDiskP542Values 0 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value0_6 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 0 (6:Fin 8))=sharedDiskP542Values 0 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value0_7 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 0 (7:Fin 8))=sharedDiskP542Values 0 (7:Fin 8) := by decide +kernel
theorem sharedDiskP542Values0_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 0 j)=sharedDiskP542Values 0 j := by
  intro j
  fin_cases j
  · exact sharedDiskP542Value0_0
  · exact sharedDiskP542Value0_1
  · exact sharedDiskP542Value0_2
  · exact sharedDiskP542Value0_3
  · exact sharedDiskP542Value0_4
  · exact sharedDiskP542Value0_5
  · exact sharedDiskP542Value0_6
  · exact sharedDiskP542Value0_7
private theorem sharedDiskP542Value1_0 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 1 (0:Fin 8))=sharedDiskP542Values 1 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value1_1 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 1 (1:Fin 8))=sharedDiskP542Values 1 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value1_2 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 1 (2:Fin 8))=sharedDiskP542Values 1 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value1_3 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 1 (3:Fin 8))=sharedDiskP542Values 1 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value1_4 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 1 (4:Fin 8))=sharedDiskP542Values 1 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value1_5 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 1 (5:Fin 8))=sharedDiskP542Values 1 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value1_6 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 1 (6:Fin 8))=sharedDiskP542Values 1 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value1_7 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 1 (7:Fin 8))=sharedDiskP542Values 1 (7:Fin 8) := by decide +kernel
theorem sharedDiskP542Values1_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 1 j)=sharedDiskP542Values 1 j := by
  intro j
  fin_cases j
  · exact sharedDiskP542Value1_0
  · exact sharedDiskP542Value1_1
  · exact sharedDiskP542Value1_2
  · exact sharedDiskP542Value1_3
  · exact sharedDiskP542Value1_4
  · exact sharedDiskP542Value1_5
  · exact sharedDiskP542Value1_6
  · exact sharedDiskP542Value1_7
private theorem sharedDiskP542Value2_0 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 2 (0:Fin 8))=sharedDiskP542Values 2 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value2_1 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 2 (1:Fin 8))=sharedDiskP542Values 2 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value2_2 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 2 (2:Fin 8))=sharedDiskP542Values 2 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value2_3 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 2 (3:Fin 8))=sharedDiskP542Values 2 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value2_4 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 2 (4:Fin 8))=sharedDiskP542Values 2 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value2_5 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 2 (5:Fin 8))=sharedDiskP542Values 2 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value2_6 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 2 (6:Fin 8))=sharedDiskP542Values 2 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value2_7 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 2 (7:Fin 8))=sharedDiskP542Values 2 (7:Fin 8) := by decide +kernel
theorem sharedDiskP542Values2_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 2 j)=sharedDiskP542Values 2 j := by
  intro j
  fin_cases j
  · exact sharedDiskP542Value2_0
  · exact sharedDiskP542Value2_1
  · exact sharedDiskP542Value2_2
  · exact sharedDiskP542Value2_3
  · exact sharedDiskP542Value2_4
  · exact sharedDiskP542Value2_5
  · exact sharedDiskP542Value2_6
  · exact sharedDiskP542Value2_7
private theorem sharedDiskP542Value3_0 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 3 (0:Fin 8))=sharedDiskP542Values 3 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value3_1 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 3 (1:Fin 8))=sharedDiskP542Values 3 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value3_2 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 3 (2:Fin 8))=sharedDiskP542Values 3 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value3_3 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 3 (3:Fin 8))=sharedDiskP542Values 3 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value3_4 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 3 (4:Fin 8))=sharedDiskP542Values 3 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value3_5 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 3 (5:Fin 8))=sharedDiskP542Values 3 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value3_6 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 3 (6:Fin 8))=sharedDiskP542Values 3 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value3_7 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 3 (7:Fin 8))=sharedDiskP542Values 3 (7:Fin 8) := by decide +kernel
theorem sharedDiskP542Values3_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 3 j)=sharedDiskP542Values 3 j := by
  intro j
  fin_cases j
  · exact sharedDiskP542Value3_0
  · exact sharedDiskP542Value3_1
  · exact sharedDiskP542Value3_2
  · exact sharedDiskP542Value3_3
  · exact sharedDiskP542Value3_4
  · exact sharedDiskP542Value3_5
  · exact sharedDiskP542Value3_6
  · exact sharedDiskP542Value3_7
private theorem sharedDiskP542Value4_0 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 4 (0:Fin 8))=sharedDiskP542Values 4 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value4_1 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 4 (1:Fin 8))=sharedDiskP542Values 4 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value4_2 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 4 (2:Fin 8))=sharedDiskP542Values 4 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value4_3 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 4 (3:Fin 8))=sharedDiskP542Values 4 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value4_4 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 4 (4:Fin 8))=sharedDiskP542Values 4 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value4_5 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 4 (5:Fin 8))=sharedDiskP542Values 4 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value4_6 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 4 (6:Fin 8))=sharedDiskP542Values 4 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value4_7 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 4 (7:Fin 8))=sharedDiskP542Values 4 (7:Fin 8) := by decide +kernel
theorem sharedDiskP542Values4_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 4 j)=sharedDiskP542Values 4 j := by
  intro j
  fin_cases j
  · exact sharedDiskP542Value4_0
  · exact sharedDiskP542Value4_1
  · exact sharedDiskP542Value4_2
  · exact sharedDiskP542Value4_3
  · exact sharedDiskP542Value4_4
  · exact sharedDiskP542Value4_5
  · exact sharedDiskP542Value4_6
  · exact sharedDiskP542Value4_7
private theorem sharedDiskP542Value5_0 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 5 (0:Fin 8))=sharedDiskP542Values 5 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value5_1 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 5 (1:Fin 8))=sharedDiskP542Values 5 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value5_2 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 5 (2:Fin 8))=sharedDiskP542Values 5 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value5_3 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 5 (3:Fin 8))=sharedDiskP542Values 5 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value5_4 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 5 (4:Fin 8))=sharedDiskP542Values 5 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value5_5 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 5 (5:Fin 8))=sharedDiskP542Values 5 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value5_6 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 5 (6:Fin 8))=sharedDiskP542Values 5 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value5_7 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 5 (7:Fin 8))=sharedDiskP542Values 5 (7:Fin 8) := by decide +kernel
theorem sharedDiskP542Values5_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 5 j)=sharedDiskP542Values 5 j := by
  intro j
  fin_cases j
  · exact sharedDiskP542Value5_0
  · exact sharedDiskP542Value5_1
  · exact sharedDiskP542Value5_2
  · exact sharedDiskP542Value5_3
  · exact sharedDiskP542Value5_4
  · exact sharedDiskP542Value5_5
  · exact sharedDiskP542Value5_6
  · exact sharedDiskP542Value5_7
private theorem sharedDiskP542Value6_0 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 6 (0:Fin 8))=sharedDiskP542Values 6 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value6_1 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 6 (1:Fin 8))=sharedDiskP542Values 6 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value6_2 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 6 (2:Fin 8))=sharedDiskP542Values 6 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value6_3 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 6 (3:Fin 8))=sharedDiskP542Values 6 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value6_4 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 6 (4:Fin 8))=sharedDiskP542Values 6 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value6_5 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 6 (5:Fin 8))=sharedDiskP542Values 6 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value6_6 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 6 (6:Fin 8))=sharedDiskP542Values 6 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value6_7 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 6 (7:Fin 8))=sharedDiskP542Values 6 (7:Fin 8) := by decide +kernel
theorem sharedDiskP542Values6_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 6 j)=sharedDiskP542Values 6 j := by
  intro j
  fin_cases j
  · exact sharedDiskP542Value6_0
  · exact sharedDiskP542Value6_1
  · exact sharedDiskP542Value6_2
  · exact sharedDiskP542Value6_3
  · exact sharedDiskP542Value6_4
  · exact sharedDiskP542Value6_5
  · exact sharedDiskP542Value6_6
  · exact sharedDiskP542Value6_7
private theorem sharedDiskP542Value7_0 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 7 (0:Fin 8))=sharedDiskP542Values 7 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value7_1 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 7 (1:Fin 8))=sharedDiskP542Values 7 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value7_2 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 7 (2:Fin 8))=sharedDiskP542Values 7 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value7_3 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 7 (3:Fin 8))=sharedDiskP542Values 7 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value7_4 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 7 (4:Fin 8))=sharedDiskP542Values 7 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value7_5 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 7 (5:Fin 8))=sharedDiskP542Values 7 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value7_6 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 7 (6:Fin 8))=sharedDiskP542Values 7 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value7_7 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 7 (7:Fin 8))=sharedDiskP542Values 7 (7:Fin 8) := by decide +kernel
theorem sharedDiskP542Values7_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 7 j)=sharedDiskP542Values 7 j := by
  intro j
  fin_cases j
  · exact sharedDiskP542Value7_0
  · exact sharedDiskP542Value7_1
  · exact sharedDiskP542Value7_2
  · exact sharedDiskP542Value7_3
  · exact sharedDiskP542Value7_4
  · exact sharedDiskP542Value7_5
  · exact sharedDiskP542Value7_6
  · exact sharedDiskP542Value7_7
private theorem sharedDiskP542Value8_0 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 8 (0:Fin 8))=sharedDiskP542Values 8 (0:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value8_1 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 8 (1:Fin 8))=sharedDiskP542Values 8 (1:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value8_2 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 8 (2:Fin 8))=sharedDiskP542Values 8 (2:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value8_3 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 8 (3:Fin 8))=sharedDiskP542Values 8 (3:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value8_4 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 8 (4:Fin 8))=sharedDiskP542Values 8 (4:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value8_5 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 8 (5:Fin 8))=sharedDiskP542Values 8 (5:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value8_6 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 8 (6:Fin 8))=sharedDiskP542Values 8 (6:Fin 8) := by decide +kernel
private theorem sharedDiskP542Value8_7 : truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 8 (7:Fin 8))=sharedDiskP542Values 8 (7:Fin 8) := by decide +kernel
theorem sharedDiskP542Values8_eq : ∀ j : Fin 8, truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points 8 j)=sharedDiskP542Values 8 j := by
  intro j
  fin_cases j
  · exact sharedDiskP542Value8_0
  · exact sharedDiskP542Value8_1
  · exact sharedDiskP542Value8_2
  · exact sharedDiskP542Value8_3
  · exact sharedDiskP542Value8_4
  · exact sharedDiskP542Value8_5
  · exact sharedDiskP542Value8_6
  · exact sharedDiskP542Value8_7
theorem sharedDiskP542Values_eq : ∀ (i : Fin 9) (j : Fin 8), truncatedChordCell 2 sharedDiskP542Params (sharedChord521Gauss8Points i j)=sharedDiskP542Values i j := by
  intro i
  fin_cases i
  · exact sharedDiskP542Values0_eq
  · exact sharedDiskP542Values1_eq
  · exact sharedDiskP542Values2_eq
  · exact sharedDiskP542Values3_eq
  · exact sharedDiskP542Values4_eq
  · exact sharedDiskP542Values5_eq
  · exact sharedDiskP542Values6_eq
  · exact sharedDiskP542Values7_eq
  · exact sharedDiskP542Values8_eq

end TwoAxisHelicoid.PdfVertical

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def sharedDiskP542Box : HorizontalRectangle := ⟨(83/100),(133/160),(960006490322437/1649267441664000),(961617103058437/1649267441664000),(1957044463182824136816478273697557/10384593717069655257060992658440192),(2840967804687141317846112340949899/5192296858534827628530496329220096),(-4185201902762365743563968835416005/1298074214633706907132624082305024),(-3705747657242829154868989652561861/1298074214633706907132624082305024),true,[]⟩
noncomputable def sharedDiskP542Grid : CGrid := momentChordGrid sharedDiskP542Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984)
theorem sharedDiskP542Columns : containedInReported sharedDiskP542Grid.re sharedDiskP542Box.reLo sharedDiskP542Box.reHi=true ∧ containedInReported sharedDiskP542Grid.im sharedDiskP542Box.imLo sharedDiskP542Box.imHi=true := by
  rw [sharedDiskP542Grid,momentChordGrid_eq_tabulated sharedDiskP542Params chordGaussRule8 2 sharedChord521Bd sharedChord521M (23175049/18014398509481984) sharedChord521Gauss8Points sharedChord521Gauss8Weights sharedDiskP542Values sharedChord521Gauss8Points_eq sharedChord521Gauss8Weights_eq sharedDiskP542Values_eq]
  decide +kernel
theorem sharedDiskP542Sound : sharedDiskP542Box.Sound := by
  intro t a tl tu al au
  change (((83/100):ℚ):ℝ)≤t at tl
  change t≤(((133/160):ℚ):ℝ) at tu
  change (((960006490322437/1649267441664000):ℚ):ℝ)≤a at al
  change a≤(((961617103058437/1649267441664000):ℚ):ℝ) at au
  have ht : 0<t := lt_of_lt_of_le (by norm_num) tl
  have hu : t≤7/5 := tu.trans (by norm_num)
  have ps := chordParams_sound (Grid.contains_rats tl tu) (Grid.contains_rats al au) ht
  rw [sharedDiskP542Params_ok] at ps
  have band := sharedChord521ParamSound (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((77/100):ℚ)≤(83/100))).trans tl) (tu.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((133/160):ℚ)≤(17/20)))) (((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((930253465593763/1649267441664000):ℚ)≤(960006490322437/1649267441664000))).trans al) (au.trans ((Rat.cast_le (K:=ℝ)).mpr (by decide +kernel : ((961617103058437/1649267441664000):ℚ)≤(971120623722397/1649267441664000)))) ht
  have result := momentChordGrid_sound ps ht hu chordGaussRule8 chordGaussRule8_nodes chordGaussRule8_half_disk 2 sharedChord521Bd (by decide +kernel) (by decide +kernel) sharedChord521M (by decide +kernel) (sharedChord521Disks band ht)
  exact refined_dual_output_encloses ht hu (lt_of_lt_of_le (by norm_num) al) (au.trans_lt (by norm_num)) result sharedDiskP542Columns.1 sharedDiskP542Columns.2
def sharedDiskP542Rows : List SignRow := [positive_542.toSignRow]
theorem sharedDiskP542Rows_actual : ∀ r∈sharedDiskP542Rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (sourceHorizontalIntegral true t a).re ∧ RealMem r.hImag (sourceHorizontalIntegral true t a).im := by
  have coverage : sharedDiskP542Rows.all (sharedDiskP542Box.coversRow true)=true := by decide +kernel
  intro r hr t a ht ha
  exact HorizontalRectangle.row_sound sharedDiskP542Sound (List.all_eq_true.mp coverage r hr) ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP539Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP540Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP541Rows_actual
#print axioms TwoAxisHelicoid.PdfVertical.sharedDiskP542Rows_actual
