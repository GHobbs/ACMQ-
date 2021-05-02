..Iô ió á WordStaò 4.° filå
.ls±
CAPÚ prograí ­ Documentatioî foò versioî 1.´b
-------------------------------------------­-

Thå  CAPÚ prograí analyzeó switcheä-capacitoò filteró iî thå  ú-
transforí domain¬ computinç ú-transforí transfeò funãtionó  froí 
á  grouğ  oæ inpuô voltagå sourceó tï anù nodå  voltagå  iî  thå 
network® Usinç thå computeä transfeò functions¬ thå prograí  caî 
ploô  gaiî anä phaså versuó frequencù curves¬ poleó  anä  zeros¬ 
anä  timå transienô responseó tï somå excétations®  Thå  prograí 
useó  aî  algïrithí deriveä froí nodaì  analùsis¬  anä  computeó 
transfeò funãtionó usinç interpolátioî bù FFT® Timå anä frequeî
cù responseó arå computeä froí thå transfeò functions¬  allowinç 
thå análysió tï bå swiftlù completed® 

Thå circuiô tï bå analyzeä caî bå composeä bù capacitors¬  ideaì 
switches¬  ideaì  operationaì amplifiers¬ anä  groundeä  voltagå 
sources® Alì thå voltagå sourceó arå considereä unitary.

Thå  switchinç  perioä ió considereä subdivideä iî á  numbeò  oæ 
equaì  duratioî phases® Eacè switcè caî bå oî oò ofæ iî  anù  oæ 
theså phases® Thå signaì sourcå ió considereä sampled¬ remaininç 
constanô durinç alì thå intervaì oæ eacè phase® Thå outpuô  siç
naì caî bå considereä sampleä bù á samplå-anä-holä circuiô oò bù 
aî impulså sampler® 

Thå maiî inpuô tï thå prograí ió á descriptioî oæ thå circuiô tï 
bå analyzed¬ iî thå forí oæ á neô-list:

Firsô lineº Numbeò oæ nodes.
Followinç linesº Onå elemenô peò line:

Capacitorº    C<name¾ <nodå 1¾ <nodå 2¾ <value>
Switchº       S<name¾ <nodå 1¾ <nodå 2¾ <phase¾ [<phase¾ ...]
Doublå Switcè P<name¾ <nodå 1¾ <nodå 2¾ <polå node¾ [<phase>...]
Op® Amp.º     O<name¾ <nodå -¾ <nodå +¾ <outpuô node>
Sourceº       V<name¾ <nodå +¾ ° 

Thå  nodeó  musô bå enumerateä froí ± tï thå  numbeò  oæ  nodes¬ 
withouô missinç numbers® ° ió thå grounä node.
 
Thå  phaseó arå enumerateä froí ± tï thå numbeò oæ  phases®  Thå 
prograí askó foò thå numbeò oæ phaseó tï uså aô thå starô oæ thå 
execution.

Thå phaså lisô iî thå descriptioî oæ thå simplå switcè indicateó 
iî whicè phaseó iô ió closed® Foò thå doublå switch¬ iô  indicá
teó iî whicè phaseó thå switcè ió closeä tï nodå 1¬ beinç closeä 
tï  nodå ² iî thå remaininç phases® Iæ thå lisô ió omitted¬  thå 
doublå  switcè ió closeä tï nodå ± iî phaså ± anä tï nodå  ²  iî 
phaså 2® Thió simplifieó thå descriptioî foò twï phaså circuits.

Capacitoò  valueó shalì bå giveî iî numbeò oæ  uniô  capacitors¬ 
noô Farads¬ tï avoiä erroró duå tï numericaì underflow.

Thå  circuiô  descriptioî caî bå convenientlù generateä  bù  thå Šeditoò prograí EdFil.

Parameteró askeä bù thå prograí aô thå starô oæ thå execution:

-    Inpuô fileº Namå oæ thå filå witè thå neô-list® Thå defaulô 
     suffiø ió ".net".
-    Numbeò  oæ  phasesº  Thå  numbeò  oæ  subdivisionó  oæ  thå 
     switchinç  perioä tï bå used® Iî thió versioî  thå  maximuí 
     numbeò ió 1² phases.
-    Radiuó oæ thå interpolatioî circleº Ideallù thå geometricaì 
     meaî  oæ thå absolutå valuå oæ thå filteò naturaì  frequeî
     cieó  iî thå z plane® Valueó arounä ± arå  satisfactorù  iî 
     mosô cases® Exactlù ± ió inconvenienô becauså severaì usuaì 
     circuitó  havå naturaì frequencieó iî z=± oò z½-1¬ anä  thå 
     filteò  wilì bå analyzeä iî theså frequencies® Thå  defaulô 
     valuå ió 1.1.
-    Dispersioî amonç polynomiaì coefficientsº Maximuí  acceptá
     blå  ratiï betweeî thå absolutå valuå oæ thå greateò  coeæ
     ficienô oæ á polynomiaì anä thå noî-zerï others® Lo÷ valueó 
     maù  leaä tï thå losó oæ coefficientó iî somå  polynomials¬ 
     anä  toï higè valueó maù leaä tï thå consideratioî oæ  verù 
     lo÷ valuå coefficients¬ possiblù consequencå oæ erroò accõ
     mulation¬  aó valid¬ oò noî-zero® Thå defaulô valuå ió  sá
     tisfactorù foò usuaì circuits®
-    Generatå á reportº Á reporô containinç á descriptioî oæ thå 
     circuit¬  thå calculateä transfeò functionó anä  tableó  oæ 
     thå  plotteä graphó caî bå created® Thå reporô caî bå  alsï 
     starteä  later¬ afteò thå plottinç oæ á frequencù  oò  timå 
     responså  graph® Thå inclusioî iî thå reporô oæ pole¬  zerï 
     anä responså tableó ió noô automatic¬ anä musô bå specifieä 
     afteò  á grapè plotting® Thå twï followinç itemó arå  askeä 
     onlù iæ á reporô generatioî ió requested.
-    Inclusioî  oæ partiaì transfeò functionó numeratoró iî  thå 
     reportº  Aî æ-phaseó filteò presentó fxæ  partiaì  transfeò 
     functions¬  froí eacè phaså aô thå inpuô tï eacè  phaså  aô 
     thå  output¬ thaô musô bå calcõlateä anä composeä iî thå  æ 
     transfeò functionó foò eacè phaså aô thå outpuô anä iî  thå 
     globaì transfeò function® Thå listinç oæ theså functionó ió 
     morå  usefuì foò verificationó iî thå workinç oæ  thå  prï
     gram¬ oò foò morå detaileä analysió oæ á filter.
-    Inclusioî  oæ  phaså transfeò functionó numeratoró  iî  thå 
     reportº  Therå arå æ transfeò functionó froí thå  inpuô  tï 
     thå  outpuô  aô eacè phase® Fråquentlù  thå  ideaì  digitaì 
     transfeò  functioî oæ thå filteò ió onå oæ them¬  witè  thå 
     otheró beinç delayeä copies.
-    Denominatoò degreeº Controló thå ordeò oæ thå interpolatinç 
     polynomials® Tï changå thå defaulô valuå ió usefuì onlù foò 
     testó  iî thå program¬ tï tesô thå precisioî oæ  thå  algï
     rithí bù increasinç it¬ foò example.

Thå prograí beginó bù computinç thå denominator¬ oò characterió
tiã polynomiaì oæ thå system¬ iî thå forí oæ á moniã  polynomiaì 
iî z® Afteò this¬ askó foò thå outpuô nodå anä computeó alì  thå 
numeratoró  oæ thå partiaì transfeò functionó froí thå inpuô  tï 
thå  node¬  thå numeratoró oæ thå transfeò  functionó  froí  thå Šinpuô  tï eacè phaså aô thå outpuô anä thå globaì numerator¬  iî 
thå forí oæ moniã polynomialó iî z^(1/phases)¬ witè  multiplyinç 
constants.

Afteò  thå  computatioî oæ thå denominatoò anä  thå  numerators¬ 
theiò coefficientó caî bå viewed¬ anä theiò roots¬ thå poleó  oò 
zeroó  oæ thå tranófeò function¬ caî bå coíputeä anä plotteä  iî 
thå  compleø plane® Alì thå poleó anä zeroó arå computeä iî  thå 
z^(1/phases© domain¬ iî sucè á waù thaô á completå turî oveò thå 
uniô  circlå  correópondó  tï á frequencù rangå froí  °  tï  thå 
switchinç  frequencù multiplieä bù thå numbeò oæ phases® Iæ  thå 
poleó werå computed¬ theù arå presenteä alonç witè thå  computeä 
zeroó  iî thå graphs® Thå scaleó oæ thå polå anä zerï grapè  caî 
bå changeä bù thå cursor¬ +¬ anä ­ keys® Thå Enteò anä Taâ  keyó 
movå  thå cursor® Spacå centeró thå poinô wherå thå  cursoò  is® 
Witè thå Esã keù otheò optionó arå acceósed® Thå poleó anä zeroó 
compõteä arå oæ thå digitaì transfeò function¬ noô beinç  affeã
teä bù thå preseîcå oæ á samplå-anä-holä aô thå output® 

Frequencù oò timå responså graphó caî bå plotteä foò anù  trans
feò  function¬  partial¬ tï aî outpuô phase¬ oò global®  Iî  thå 
graphs¬  thå verticaì scalå caî bå changeä bù thå verticaì  cur
sor¬ +¬ anä ­ keys® Thå horizontaì cursoò keyó turnó oî á cursoò 
aô anù instant® Thå Enteò keù resumeó thå plotting® Thå Esã  keù 
giveó  accesó tï otheò options¬ aó tï savå á grapè tablå iî  thå 
report¬ oò changå scales¬ switchinç fråquency¬ samplinç modå  aô 
thå output¬ excitatioî foò timå respoîså anä grapè resolution.

Thå  plottinç oæ á griä iî thå graphó caî bå selecteä  witè  thå 
"G¢  key¬ anä iî thå frequencù responså graph¬ thå  plottinç  oæ 
thå  phaså curvå caî bå selecteä witè thå "F¢ oò "P¢  keys®  Thå 
phaså limitó arå alwayó oæ ñ18° degrees.

Observations:

Iî  thå useä notation¬ "z¢ correspondó tï á timå advancå oæ  onå 
switchinç  period¬ anä "z^(1/phases)¢ tï á timå advancå  oæ  onå 
phaså oæ thå switchinç period® Alì thå polynomialó arå  computeä 
iî  positivå poweró oæ z® Thå denominatoò aìwayó  presentó  onlù 
integeò poweró oæ z¬ anä thå numeratoró iîvolvinç transfeò func
tionó amonç differenô phaseó alwayó presenô fractionaì poweró oæ 
z® 

Eacè transfeò functioî receiveó á name¬ iî thå formsº
T(outpuô node,inpuô phase,outpuô phase© foò partiaì t® f® 
T(outpuô node,outpuô phase© foò t® f® foò onå outpuô phase®
T(outpuô node© foò thå globaì transfeò function®

Forbiddeî arå circuitó containinç closeä loopó oæ switcheó  clï
seä  iî thå samå phase¬ anä anù circuitó thaô shorô-circuiô  aí
plifieò  inputó  oò outputs¬ oò thå signaì source®  Thå  prograí 
indicateó thå erroò iî theså cases® Forbiddeî arå alsï  circuitó 
iî  whicè á subcircuiô ió lefô floatinç withouô  connectionó  iî 
somå  phase®  Thå prograí detectó thå condition¬  buô  doeó  noô 
localizeó  thå cause® Thió probleí caî alwayó bå solveä  bù  thå Šintroductioî  oæ á switcè thaô connectó thå floatinç  subcircuiô 
tï á noî-floatinç poinô iî thå problematiã phases® Usuallù iô ió 
enougè  tï adä somå phaseó iî thå lisô oæ á switcè coînecteä  tï 
thå subcircuit.

Thå  graphó foò timå responså oæ noî-globaì  transfeò  functionó 
arå  plotteä returninç tï zerï iî alì phaseó differenô froí  thå 
outpuô  phase¬ clearlù showinç thå partialitù oæ  thå  function® 
Theù  arå  obtaineä directlù froí thå  correspondinç  differencå 
equations®  Thå frequencù responså plotteä foò theså caseó  coò
respondó alsï tï thió typå oæ waveform.

Iô  ió possiblå tï varù thå holä timå oæ thå outpuô  samplå-anä-
hold¬ iî numbeò oæ phases¬ iî thå menõ afteò thå frequencù  reó
ponså  graph® Thå normaì value¬ correspondinç tï  thå  waveformó 
showî iî thå timå responså graphs¬ ió alwayó oæ onå phase® Greá
teò valueó caî bå specified¬ buô thå resultó havå  significatioî 
onlù foò noî-globaì transfeò functions¬ wherå thå outpuô  signaì 
witè aî impulså sampleò presentó onlù onå impulså peò  switchinç 
period®  Thå frequencù responså plotteä correspondó theî tï  thå 
holdinç oæ thå outpuô signaì foò thå numbeò oæ pháseó specified® 
Thå  effecô ió noô showî iî thå timå responså graphs®  Thå  maiî 
utilitù oæ thió featurå ió foò testó iî thå prograí algorithm.

Thå  computatioî oæ poleó anä zeroó oæ higè-ordeò  circuitó  caî 
resulô iî numericaì problems® Iî theså cases¬ thå prograí  stopó 
afteò  5° iterationó anä askó foò ne÷ valueó foò thå  toleranceó 
tï use¬ anä foò á ne÷ approximatioî tï thå rooô beinç  computed® 
Therå  arå twï tolerancesº thå tolerancå foò erroò iî rootó  anä 
thå  tolerancå foò polynomiaì magnitudes® Thå  firsô  determineó 
thå precisioî iî á rooô value¬ anä thå seconä ió useä tï  detecô 
á  multiplå root¬ bù thå valuå oæ thå polynomiaì  derivativå  iî 
thå  vicinitieó oæ á root® Bù thå decreasinç oæ onå  oò  anotheò 
anä  anotheò cyclå oæ iterations¬ thå prograí caî bå induceä  tï 
accepô  á rooô aó simplå oò multiple® Thå approximatioî foò  thå 
rooô rarelù needó tï bå changed¬ anä musô noô bå changeä iî  thå 
caså  oæ á multiplå root® Thå toleranceó musô bå kepô aó lo÷  aó 
possible¬ anä oncå modifieä arå useä untiì thå enä oæ thå execõ
tion® Thå calculatioî oæ zeroó ió iî generaì morå criticaì  thaî 
oæ poles¬ anä eventuallù aî overflo÷ erroò maù occur® Thió  prï
bleí caî usuallù bå solveä bù thå specificatioî oæ á ne÷ initiaì 
approximatioî foò rootó tï bå used¬ iî thå menõ acceósiblå afteò 
thå roots calculation.

Iô  ió  possiblå tï simulatå amplifieró witè finitå  gaiî  usinç 
ideaì  amplifieró  witè feedbacë circuitó madå oæ  positivå  anä 
negativå capacitors® Thió usuallù introduceó polå-zerï pairó  aô 
z=± (Iî truth¬ î pairó equallù spaceä oî thå uniô circle¬ inclõ
dinç z=1¬ foò aî î-phaseó circuit® Thå samå occuró iî thå  otheò 
caseó discusseä below)® Thå unitù-gaiî buffeò doeó noô  introdõ
ceó poleó oò zåros® Thå presencå oæ multiplå polå-zerï pairó  aô 
z=± caî causå impråciså plottinç oæ thå frequencù responså grapè 
aô lo÷ fråquency.

Resistoró  caî bå simulateä bù switcheä capacitoró  (usuallù  iî Šthå bilineaò form© operatinç iî á frequencù higheò thaî thå maiî 
switchinç frequency® Witè thå limiteä numbeò oæ phaseó  allowed¬ 
thå limiô ió á simulateä resistoò switcheä ¶ timeó iî eacè phaså 
foò  á ² phaså circuit® Thå resultó maù bå noô simplå tï  inter
pret¬ becauså erroró noô causeä bù thå resistoò arå  introduced® 
Thå uså oæ simulateä resistoró caî easilù resulô iî aî  equátioî 
systeí witè excessivå sizå foò thå existinç memory¬ becauså  thå 
prograí musô computå thå noî-triviaì signaló iî alì thå  circuiô 
nodeó iî alì thå phases.

Operationaì amplifieró witè noî-ideaì frequencù responså maù  bå 
simulateä approximatelù bù circuitó composeä bù simulateä resió
toró anä otheò components® Thå problemó iî usinç thió  techniquå 
arå thå samå oneó oæ thå simulateä resistors.

Thå  prograí produceó resultó iî frequencù responså  thaô  agreå 
witè  thoså oæ SWITCAP¬ foò equaì-duratioî phases¬ largå  ampli
fieò gains¬ inpuô samplå-anä-holä anä outpuô samplå-anä-holä  oò 
impulså  sampleò used® Thå samplinç instanô musô bå seô  aô  thå 
beginninç  oæ  eacè phaså (0+)® Iî thå timå response¬  thå  samå 
resulô ió obtaineä witè thå samå sampling¬ buô (why?© thå outpuô 
musô bå sampleä beforå thå initiaì instanô oæ eacè phaså (°­  iî 
thå TIMÅ instruction)® Thå prograí SwitNeô allowó thå conversioî 
oæ  neô-listó  iî thå CAPÚ formaô tï thå onå  oæ  SWITCAP¬  witè 
parameteró adequatelù specifieä foò similaò råsults.

Alì  thå graphó uså bù defaulô thå highesô possiblå  resolution¬ 
witè colors¬ oæ thå installeä graphicó board® Thió caî bå  over
riddeî bù thå specificatioî iî thå DOÓ commanä linå oæ thå codeó 
oæ  thå desireä driveò anä modå (seå thå Turbï  Pascaì  manual)® 
Somå valiä combinationó areº ± <° tï 4¾ (CGA)¬ ³ <° or1¾  (EGA)¬ 
¹  <°  tï 2¾ (VGA)® Foò exaípleº "CAPÚ xxxø ± 4¢  specifieó  thå 
analysió  oæ  thå circuiô deócribeä iî thå  filå  xxxx.net¬  anä 
causeó  thå  graphó tï bå madå iî thå 640x20° modå  oæ  thå  CGÁ 
graphicó board.

                       === IMPORTANÔ ===

Thå  Turbï Pascaì graphiã driveò (fileó .BGI© foò thå  installeä 
graphicó boarä musô bå presenô oî thå defaulô directory¬ oò iî á 
directorù  pointeä  bù thå patè containeä iî  thå  DOÓ  variablå 
TPBGÉ.

Ne÷ featureó iî versioî 1.4

-    Severaì groundeä inpuô sourceó arå allowed¬ iî anù ordeò iî 
     thå neô-list¬ buô alì arå considereä identical® Connectionó 
     oæ thå outpuô witè thå inpuô arå no÷ properlù treated.
-    Frequencù  responså  graphó foò noî-globaì  transfeò  funã
     tions¬  witè outpuô samplå-anä-holä used¬ arå no÷  computeä 
     witè  thå correcô attenuation® Iî versionó beforå 1.4¬  thå 
     attenuatioî oæ thå samplinç functioî waó normalizeä tï ± aô 
     DC.
-    Alì thå numeratoró arå computeä immediatelù afteò thå  ouô
     puô  nodå  ió given® Afteò this¬ thå  denominatoò  anä  anù Š     numerátoò caî bå vieweä anù numbeò oæ timeó withouô  recal
     culation® 
-    Thå  memorù  managemenô waó improved¬ anä thå  prograí  caî 
     analyzå largeò circuits.

Versioî  1.4á  correctó somå typoó anä otheò  minoò  bugs®  Noî-
integeò holä periodó arå no÷ accepted.

Versioî  1.4â correctó bugó iî thå numbeò oæ rootó aô ° iî  paò
tiaì numerators¬ DÃ gaiî witè noî-unitù holä period¬ anä  memorù 
management® 

Thå EdFiì editoò program
------------------------

Thå EdFiì editoò caî bå useä tï generatå thå inpuô neô-lisô filå 
foò  thå CAPÚ program¬ anä alsï foò otheò programs¬  eveî  SPICÅ 
(witè  somå  editing© oò SWITCAĞ (witè conversioî  donå  bù  thå 
SwitNeô  program)® Thå circuiô ió drawî oî thå screeî usinç  thå 
cursoò keyó anä thå seleãteä keyboarä keyó listeä aô thå  bottoí 
oæ  thå editoò screen® Á helğ screeî ió assesseä bù thå  ¿  key® 
Nameó  anä parameteró foò thå elementó arå giveî bù  movinç  thå 
cursoò tï thå componenô anä touchinç thå Returî key¬ oò bù Ctrì-
X¬ thaô causeó thå prograí tï asë paramåteró foò alì thå visiblå 
elements® Thå besô methoä ió usuallù tï dra÷ alì thå circuiô  aô 
firsô anä lateò givå thå parameters® Therå arå defaulô nameó anä 
parameteró foò alì elements® Thå parameteró arå á text¬ anä  arå 
reproduceä  iî thå neô-lisô aó given¬ unlesó foò formulae¬  thaô 
musô bå encloseä iî parenthåsis.

Oncå  drawî thå circuit¬ thå neô-lisô ió generateä witè  Ctrì-Q® 
Thå  prograí theî askó thå nameó oæ thå fileó wherå tï savå  thå 
circuiô  descriğtioî (.ciò file© anä thå neô-lisô  (.neô  file)® 
Afteò this¬ anù prograí caî bå executeä whilå thå editoò remainó 
residenô  iî memory¬ witè executioî returninç lateò tï thå  edi
tor® 

Aî impoòtanô featurå oæ thå prograí ió thå optionaì uså oæ  foò
mulaå iî thå parameters® Anù mathematicaì expressioî usinç conó
tantó  anä valueó giveî iî á valuå lisô caî bå useä foò á  numå
ricaì  parameter® Thå expressionó arå evaluateä iî thå  neô-lisô 
generátion® Thió allowó easù uså oæ componenô valuå listó  genå
rateä bù synthesió programs¬ oò eveî thå uså oæ EdFiì aó á  syî
thesió  program¬  witè componentó parameteró  giveî  bù  projecô 
formulae.

Thå prograí EdFiì-² ió á versioî oæ EdFiì thaô useó screenó witè 
higheò  resolutioî thaî thå CGA® Iô ió sligtlù sloweò  anä  useó 
morå memory® Thå defaulô screeî modå selectioî caî bå  overrideî 
aó  iî thå CAPÚ program® Thå .BGÉ fileó musô bå presenô  oî  thå 
defaulô  drivå  oò  iî thå patè indicateä bù  thå  DOÓ  variablå 
TPGBI.

Thå  CAPZ¬ EdFil¬ anä SwitNeô programó werå developeä aô  COPPE¬ 
Fedåraì Universitù oæ Riï då Janeiro¬ Bù Antoniï Carloó Moreiraï Šdå  Queiroz® Suggeótionó anä doubtó abouô thå programó shalì  bå 
senô  tï thå authoò aô COPPE/UFRJ¬ CĞ 68504¬ CEĞ 21945¬  Riï  då 
Janeéro¬ Brazil¬ oò viá electroniã maiì tï COE10009@UFRJ.BITNET® 

Antoniï Carloó M® då Queiroú ­ March 3¬ 1992
