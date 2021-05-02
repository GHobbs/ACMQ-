..Imprimir com Wordstar 4.0
.pl66
.ls1
.rm64
.pc32
                        Ï Programa IFFÔ‚ 

± ­ Introdu‡„o

   Ï programá IFFÔ calculá numericamentå transformadaó då Laplá
cå  daó  tens”eó nodaió då circuitoó lineareó å  invárianteó  nï 
tempo¬  ná  formá då raz”eó då polin“mioó då "s"¬  utilizandï  ï 
m‚todï då an liså nodaì coí interpola‡„ï då polin“mioó poò "Fasô 
Fourieò  Transform"® Coí excita‡”eó convenientes¬ estaó  tens”eó 
podeí seò inteòpretadaó comï fun‡”eó då transferˆnciá oõ imitƒî
cias¬ cáracterizandï ï comportamentï CÁ dï circuitï analisado® Á 
partiò daó fuî‡”eó calculadaó podeí seò obtidoó p¢loó å zeros¬ å 
diágramaó då reópostá eí freqˆnciá podeí seò plotadoó å  compá
radoó coí oõtroó previamentå calculados.

   Ï programá ›‚ £tiì principalmentå pará á r pidá veriféca‡„ï då 
projetï då filtros¬ permitindï inclusivå á clará visualiza‡„ï dá 
posi‡„ï då p¢loó å zeroó secund rios® Podå seò usadï tamb‚í comï 
ferramentá  pará ï estudï nï dom¡niï dá freqˆnciá då  problemaó 
ligadoó  á  sistemaó lineares¬ comï compensa‡„ï då  respostá  eí 
freqˆnciá å sistemaó då controle.

² ­ Parƒmetroó då entradá pará ï programa

   Á  descri‡„ï dï circuitï á analisaò devå estaò eí uí  arquivï 
då texto¬ ná formá abaixoº 

- 1a® linhaº numerï då n¢s.

- Linhaó seguintesº Descri‡„ï dï circuito¬ uí elementï poò lénhá 
  (Semelhantå aï formatï SPICE¬ pará quaså todoó oó elementos).

- Resistoò coí resistˆnciá Ò:
  R<nome> <n¢±> <n¢²> <Ò>
- Indutoò coí indutƒnciá Ì:
  L<nome> <n¢±> <n¢²> <L>
- Capacitoò coí capacitƒnciá Ã:
  C<nome> <n¢±> <n¢²> <C>
- Transformadoò  coí indutƒnciaó L11¬ L22¬ M1² å M2² (M2± ›‚  op
  cional¬ så foò diferentå då M12):
  N<nome¾ <n¢1+¾ <n¢±-¾ <n¢2+¾ <n¢²-¾ <L11¾ <L22¾ <M12¾ <M21¾ 
- Girador¬ coí resistˆnciá då gira‡„ï Rç:
  Y<nome¾  <n¢1+¾  <n¢±-¾ <n¢2+¾ <n¢²-¾ <Rç>
- Fontå  då  correntå  controladá á tens„ï  (VCCÓ  oõ  OTÁ 
  ideal© coí tranócondutƒnciá Gm:
  G<nome¾ <n¢I+¾ <n¢É-¾ <n¢V+¾ <n¢Ö-¾ <Gm>
- Amplificadoò  operacional¬ coí ganhï GB/ó (GÂ eí rad/s© å  re
  sistˆnciá då sa¡dá Ro:
  A<nome¾  <n›¢-¾ <n¢+¾ <n›¢ sa¡da¾ <GÂ¾ <Ro>
- Amplificadoò operacionaì idealº modelï  nullatoò-noratoò 
  O<nome¾ <n›¢ entr® 1¾ <n›¢ entr® 2¾ <n›¢ sa¡da>
­ Transistoò bipolarº modelï h¡bridï è completo
  Q<nome¾ <n¢c¾ <n¢b¾ <n¢e¾ <hfe¾ <hie¾ <hre¾ <hoe>
­ Transistoò MOS:
  M<nome¾ <n¢d¾ <n¢g¾ <n¢s¾ <Gm¾ <Gds>Š­ Fontå då corrente:
­ I<nome¾ <n¢+¾ <n¢-¾ <correntå>
- Fontå då tens„o coí resistoò em s‚riå Rs:
  Z<nome¾ <n›¢-¾ <n¢+¾ <Rs¾ [<tens„o>]

  Todaó aó unidadeó eí Ohms¬ Mhos¬ Farads¬ Henrys¬ Voltó å Ampå
res® Ï nomå dever›  possuiò då ± á µ caracteres¬ iîcluindï á iné
cial® Ï n›¢ då terrá ›‚ ï 0¬ å á numera‡„ï doó n¢ó devå seò cont›¡
nua¬ då ± aï n£merï då n¢s® Á ordeí doó elåmentoó å dá numera‡„ï 
podå seò qualquer® Ï arquivï coí á descré‡„ï dever›  teò ï sufixï 
(default©  .net å podå seò geradï autïmaticámentå pelï  programá 
editoò EDFIL.

   Aó  fonteó då tens„ï s„ï consideradaó comï då 1Ö så á  tens„ï 
(opcional©  n„ï  foò dada¬ å aó då correîtå coí  ï  valoò  dado¬ 
impulsionaió pará aó tranóformadaó å coósenoédaió pará á respos
tá  eí freqˆncia® Usualmentå desejá-så ï c lculï då fun‡”eó  då 
transferˆnciá  oõ  impedƒncias¬ å existå apenaó  umá  fonte¬  då 
valoò unit› rio.

   Anteó  dá  an lise¬ ï programá pedå  algunó  parƒmetros¬  quå 
controlaí á precis„ï dï resultadoº 

   Dispers„ï  entrå coeficienteó då polin“mioº å á m ximá  raz„ï 
aceit veì  entrå  m¢duloó dï maioò å dï  menoò  coeficéentå  doó 
polin“mioó  dï numeradoò å denominadoò dá fun‡„ï då  transferˆî
cia¬ normalizadoó pelï fatoò då normaliza‡„ï eí freqˆnciá  usá
do® › usadï pelï programá dá seguintå formaº á interpola‡„ï  poò 
FFÔ  semprå  gerá polin“mioó (nõmeradoreó  å  denominadoreó  daó 
transformadaó interpoladas© coí graõ iguaì ›… potˆnciá då ²  imå
diatamentå  supårioò  aï graõ då complexidadå  estimadï  pará  á 
rede¬  menoó  1® Så ï graõ reaì då uí polin“miï  foò  menoò  quå 
este¬  oó coefécienteó då maioò graõ calculadoó ser„ï apenaó  uí 
pequenï res¡duo¬ idealmeîtå nulo® Pará distinguiò at›‚ ondå vaé ï 
polin“miï  real¬ ï prïgramá prïcurá quaì ï coeficientå då  maioò 
m¢dõlï  dï polin“mio¬ dividå seõ m¢dulï pelá dispeòs„ï  dada¬  å 
compará ï m¢dulï doó demaió coåficienteó coí estå valor¬ zerandï 
todoó  oó  quå foreí menores® Eí circuétoó då ordeí  elevada¬  á 
acumula‡„ï  då errï num‚ricï podå tornaò á dåtermina‡„ï dá  dió
pers„ï  corretá  n„ï trivial¬ raz„ï pelá quaì  suá  escolhá  foé 
deixadá aï usu rio® Á dispers„ï podå seò alteradá ap¢ó ï c lculï 
då  cadá polin›“mio¬ så neceós rio¬ ï quå permitå quå  ï  usu riï 
corrijá uí graõ calcõladï erradamentå pará ï valoò correto® Casï 
ï  graõ  corretï n„ï sejá conhecido¬ umá inspe‡„ï  dï  polin“miï 
obtidï coí umá dispeòs„ï då valoò elevado¬ då modï quå todoó  oó 
coåficienteó sejaí listados¬ podå seò £tiì pará determin› -lo® Eí 
casoó  assim¬ especiaì cuidadï devå seò dadï aï corretï usï  doó 
fatoreó då normaliza‡„o.

   Fatoò  då normaliza‡„ï eí freqˆnciaº ›‚ uí fatoò  usadï  pará 
noòmalizaò á redå eí freqˆncia¬ melhorandï á precés„ï  num‚ricá 
dï algor¡tmo® Devå seò colocadï eí tornï dá m‚diá geom‚tricá daó 
freqˆnciaó  natõraió  dá rede¬ eí rad/s® Ï  programá  indicá  ï 
fatoò ideaì pará cadá polin“miï calculadï (ï valoò quå fariá coí 
quå  oó coeficienteó då maioò å menoò grauó dï polin“miï  fosseí Šéguais)® Pará melhoreó resultados¬ ï fatoò usadï devå seò pr¢xé
mï dï valoò ideal¬ oõ aï menoó dá mesmá ordeí då grandeza®  Pará 
mudaò  ï fatoò durantå ï processamento¬ å necess riï  refázeò  á 
interpïla‡„o® 

   Fatoò  då normaliza‡„ï eí impedƒnciaº ›‚ uí fatoò  usadï  pará 
noòmalizaò á redå eí impedƒncia¬ evitandï "overflows¢ å  "undeò
flows¢ quå podeí ocorreò så ï n¡veì då impedƒnciá dá redå analé
sadá  foò  baixï demaió oõ altï demaió (consåqˆnciá dï  usï  då 
an liså  nodaì pelï programa)® Seõ valoò devå ficaò eí tornï  dï 
n¡veì då impådƒnciá dá redå ná freqˆnciá dï fatoò då normálizá
‡„ï eí fråqˆnciá (eí rad/s)® Ï valoò ideaì quå ï programá  cal
cõla¬ pará cadá polin›“mio¬ ›‚ ï quå fariá coí quå ï polin“miï iî
terpoladï  fosså m“nico® Valoreó muitï maioreó quå ï  neceós riï 
podeí  causaò  "overflow"® Valoreó muitï  menoreó  podeí  causaò 
"underflow"¬ gerandï polin“mioó nuloó (ï programá emitå uí avisï 
nestå  caso)® Ï valoò usadï afetá apenaó á precis„ï num‚ricá  dï 
resultado¬ seí outraó conseqˆncias¬ poió aó fonteó då sinaì s„ï 
tamb‚í  normálizadas® Pará alteraò ï fator¬ ›‚ tamb‚í  necess riï 
refázeò á interpola‡„o.

   Normaliza‡„ï doó resultadoó eí freqˆnciaº ›‚ recomendádï  quå 
sejá usadá semprå quå á redå á analisaò n„ï estiveò  normalizadá 
eí freqˆîciá (p¢loó å zeroó distandï aproxémadamentå ± rad/ó dá 
origem)®  Nestå  caso¬ todoó oó resuìtadoó  (polin›“mios¬  p¢los¬ 
zeroó  å gr ficos© estár„ï normálizadoó pelï fatoò  då  normalé
za‡„ï eí fråqˆnciá usado® Så n„ï foò usada¬ problemaó då "over
flow¢ å "underflow¢ podeí ocorrer.

   Ordeí då complexidadå estimadá dá redeº Ï programá  determiná 
á  ordeí då complexidadå dá redå atrav‚ó då umá   rvorå  normal¬ 
listadá  ap¢ó ï netlist® Está ›‚ á ordeí corretá  pará  circuitoó 
normais®  Så  á ordeí reaì diferente¬ estå  parƒmetrï  podå  seò 
alterado® Så coí istï á ordeí dá FFÔ (menoò potˆnciá då ²  acimá 
dá ordeí estimada© usadá foò reduzida¬ á precis„ï doó resultadoó 
ser›  maior® Observå-så quå freqˆnciaó naturaió eí ° deveí  sem
prå seò contadas¬ assií comï p¢loó canceladoó poò zeros.

³ ­ Opera‡„ï dï programa

   Ï programá analisá ï circuitï pelï m‚todï doó n¢ó nï  dom¡niï 
dá freqˆnciá eí uí n£merï då pontoó (potˆnciá då 2©  igualmentå 
espa‡adoó  á partiò dï eixï reaì sobrå uí c¡rculï nï planï  com
plexï då raiï iguaì aï fatoò då normáliza‡„ï eí freqˆnciá  usa
do¬  calcõlandï pará cadá pontï ï determinantå dá matriú då  ad
mitƒîciá doó n¢s¬ denominadoò då todaó daó fun‡”eó á interpolar¬ 
å  oó numåradoreó då todaó aó tens”eó nodais® Comï ï circuitï  ›‚ 
real¬ pontoó noó quadranteó inferioreó geraí resultadoó  comple
xoó coîjugadoó doó resultadoó noó quadranteó superiores¬ å  istï 
›‚ usadï pará reduziò á computa‡„o® Denominadoò å numerádoreó s„ï 
multiplicadoó  poò "s¢ elevadï aï n£merï då elåmentoó  indõtivoó 
(Ì å GB)¬ pará quå oó valoreó caìculádoó correópondaí á  avalia
‡”eó då polin“mioó coí potˆîciaó positivaó då "s"® Umá FFÔ dire
tá podå ent„ï seò usadá pará recuperaò oó polin“mios¬ seguidá dá 
verifica‡„ï dá dispers„ï å då desnormaliza‡„ï eí freqˆncia¬  så Šfoò ï caso® Á noòmalizá‡„ï eí impedƒnciá ›‚ feitá duraîtå á  mon
tageí dï sistemá nodal¬ å n„ï precisá seò desfeita® 
 
   Ï  programá calculá imediatamentå ï polin“miï  caractåristicï 
dï  circuito¬  quå ›‚ ï denominadoò då todaó aó fuî‡”eó  å  cujaó 
ra¡zeó  s„ï  aó freqˆnciaó naturaió (oõ p›¢los)®  Á  seguir¬  oó 
numeradoreó desejadoó podeí seò rapédamentå calculádoó á  partiò 
doó  valoreó  obtidoó naó an léseó iniciais® Oó  polin“mioó  s„ï 
apresentadoó ná formá m“nica® Ap¢ó ï c lculï dï denominadoò å då 
cadá numerador¬ suaó raizeó (p¢loó oõ zeros© podeí seò  calculá
daó å plotádaó nï planï complexo® Så oó p¢loó foreí  caìculados¬ 
ser„ï plotadoó juntï coí todoó oó zeroó quå foreí pedédos®  Ap¢ó 
ï c lculï då cadá numerador¬ diagramaó då respostá eí freqˆnciá 
dá tens„ï nï n›¢ podeí seò plotados.

Comandoó aceitoó no gr fico de p¢los e zeros:

Escº Terminar.
"+","-"º Ampliar/reduzir.
Cursoresº Mover.
Tab, Backspaceº Moveò ï cursor.

   Todoó  oó resultadoó calculadoó podeí seò armazenadoó eí  aò
quévos¬  å usadoó poò outroó programas¬ pará ï c lculï  då  reó
postaó nï dom¡niï dï tempï (ANATRAN)¬ sensibilidadeó då p¢loó  å 
zeroó (SENSI)¬ Gr ficoó diferentes¬ etc.

   Ï programá plotá gr ficoó då ganhï eí decib‚is¬ faså eí grauó 
å atrasï då grupï eí segundoó eí fun‡„ï dá freqˆîciá (eí Hú  oõ 
rad/s)¬ eí escalá lineaò oõ logar¡tmica.

Comandoó  aceitoó durantå á plotageí då gr ficoó då respoótá  eí 
freqˆncia:

Escº Terminaò oõ mudaò escalas.
"G"º Ligar/desligaò desenhï dá grade.
"F"º Ligar/desligaò plotageí dá fase.
"T"º Ligar/desligaò plotageí dï atrasï då grupo.
"L"º Ligar/desligaò á escalá logar¡tmica.
"A","R"º Ampliaò/reduzir horizontalmente.
"<",">"º Moveò horizontalmente.
"+","-"º Ampliar/reduziò verticalmentå (ganhï apenas).
Cursoò verticalº Moveò verticalmentå (ganhï apenas).
Cursoò horizontalº Cursor® Move-så maió r pidï coí Ctrl.
Tab¬ Backspaceº Mudaò ï cursoò då curva.
"C"º Mudaò ï crit‚riï då colora‡„ï daó curvas.
Returnº Continuaò uí tra‡adï interrompidï pelï acionamentï 
dï cursor.

   Aó  escalaó då freqˆnciaó å då ganhï s„ï graduadas®  Á  grá
dua‡„ï ›‚ inteligenteº aó linhaó mostradaó marcaí apenaó  valoreó 
coí  termina‡„ï inteira® Poò exemploº Coí limiteó då  freqˆnciá 
entrå 0.341² å 0.344· Hz¬ linhaó s„ï trá‡adaó pará 0.342¬  0.34³ 
å  0.34´  Hz® Eí escalá lineaò at›‚ ¹ linhaó s„ï tra‡adas¬  å  eí 
escalá  logar¡ômicá todaó aó potˆîciaó inteiraó då 1° s„ï  indéŠcadaó poò coò difåreîte¬ coí ¹ linhaó entrå elas.

   Oó  limiteó  då ganhï listadoó semprå  correspondeí  ›…  curvá 
apontadá  pelï cursor® Aó linhaó dá gradå tamb‚m¬ maó ï  gr› ficï 
devå  seò  redesånhadï pará suá altåra‡„o® Oó  gr› ficoó  usaí  á 
m ximá  resolu‡„ï poss¡veì á coreó coí á placá gr› ficá usada®  › 
poss¡veì  for‡aò  á utilizá‡„ï då outroó modoó  gr› ficos¬  så  ï 
programá  foò chamadï ¬ á paòtiò dï DOS¬ porº IFFÔ  <arquivï  då 
entrada¾ <pláca¾ <modo>¬ ondå oó doió £ltimoó par›ƒmetroó especi
ficaí  oó n›£meroó dï "dréver¢ á usaò å dï modï gr› ficï (veò  ma
nuaì tï Turbï Pascaì 5.5)® Poò exemploº IFFÔ <arquévo¾ ± ´ espe
céficá ï modï då 640x20° dá CGA® 

   Rotinaó  då impress„ï dá telá eí impressoraó tipï  EPSOÎ  s„ï 
acess¡veió tocandï-så "I¢ oõ "P¢ naó telaó gr ficas¬ maó  apenaó 
quandï á placá CGÁ ›‚ usada® Á impress„ï podå seò imediatá oõ  eí 
arquivo¬  eí doió formatos¬ å podå seò  interrompidá  tocandï-så 
qualqueò tecla® Á tabålá då valïreó geradá nï gr fécï då respos
tá eí freqˆnciá å aó liótaó då p¢loó å zeros¬ siípleó  arquivoó 
då texto¬ podeí seò usadaó pará plotagenó coí outroó programas® 

   Aó curvaó dá respostá eí freqˆnciá dï circuitï sendï  analé
sadï  poder„ï seò plotadaó eí conjuntï coí outras¬  usandï-så  á 
op‡„ï då inclu¡ò outrá curvá nï gr fico® (tåclá "I¢ nï menu)®  Ï 
denominadoò å ï numåradoò dá fun‡„ï á inclu¡ò podeí seò lidoó då 
arquivoó  oõ copiádoó dá £ltimá fun‡„ï calculada® At›‚ trˆó  fun
‡”eó podeí seò plïtadaó eí conjuntï coí á fun‡„ï atual® Cadá umá 
recebå  uí  n£merï då ² á 4¬ sendï á fun‡„ï n£merï  ±  semprå  á 
fun‡„ï atual® Á £ltémá fun‡„ï incluidá podå seò eliminadá  usan
dï-så  á op‡„ï då eléminaò umá curvá (teclá "E¢ nï  menu)®  Cadá 
fun‡„ï  podå seò plotadá coí escalá då ganhï difårentå  daó  de
mais® 

   Á  qualqueò momento¬ oó valoreó associadoó á cadá  compïnentå 
podeí seò modificadoó (teclá "M¢ nï menu)¬ å ï ciòcuitï analisa
dï novámente® Ï efeétï dá modifica‡„ï ná respostá eí  freqˆnciá 
podå  seò observadï så á fun‡„ï då transferˆnciá originaì  tiveò 
sidï inclu¡dá nï gr fico® 

´ ­ Observa‡”es

   Algunó problemaó comunó quå podeí causaò dificuldadeó s„o:

   Resistˆnciaó  å  indutƒnciaó n„ï podeí seò nulas¬  devidï  aï 
sistemá då an liså nodaì usado® Tamb‚í poò isto¬ eí uí transfoò
mador¬  L11*L2² devå seò diferentå då M12*M21® Så istï  n„ï  foò 
obedecido¬ ï programá pará poò divis„ï poò zero.

   Gr ficoó då respostá eí freqˆnciá eí escalá logar¡tmécá  n„ï 
podeí  iò at›‚ freqˆnciá zerï oõ negativa® Eí escalá lineaò  n„ï 
h›   restré‡„o®  Seí á grade¬ ï programá aceitá  quå  oó  limiteó 
horizontaió å verticaió sejaí invertidos® 

   Så  á redå analisadá n„ï estiveò normalizadá eí freqˆîciá  å 
impedƒncia¬  å oó fatoreó då normaliza‡„ï n„ï foreí  usados¬  oó Šresultadoó calculadoó poder„ï seò seí sentidï devidï á  acumulá
‡„ï då errï num‚rico® Ï processï maió segurï då obteò resultadoó 
consistenteó  ›‚ preveò quantoó p¢loó å quantoó zeroó ï  circuitï 
possui¬  å quaì á ordeí då grandezá deles¬ anteó dá  an lése¬  å 
procuraò obteò esteó n£meroó ajustandï oó fatoreó då  normalizá
‡„ï  å á dispeòs„o® Oó fatoreó corretoó podeí seò buscadoó  exá
minandï-så  oó valoreó recïmendadoó pelï programá  comï  ideais® 
Quandï eleó n„ï mudareí maió pará v rioó fatoreó då normaliza‡„ï 
(eí freqˆncia¬ princépalmente© dentrï dá mesmá ordeí då grandå
za¬  á  an liså devå estaò correta® Á dispeòs„ï ideaì  podå  seò 
achadá examinaîdï-så oó polin“mioó calculadoó coí umá  dispers„ï 
iniciaì grandå å polin“mioó normalizadoó eí freqˆncia¬ å  veré
ficandï-så  quaì  á dispers„ï quå eliminá termoó acimá  dï  graõ 
correto.

   Ï circuitï n„ï podå possuiò freqˆnciaó naturaió naó freqˆî
ciaó quå ï programá analisá pará á interpola‡„o® Ï problemá maió 
comuí ocorrå coí p¢loó reaió då m¢dulï iguaì aï fatoò då  normá
liza‡„ï eí freqˆncia.

   Poder›   ocorreò "overflow¢ så ï graficï då m¢dulï å faså  foò 
pedidï eí freqˆnciaó muitï elevadas® Ï problemá ›‚ comuí  quandï 
ï circuitï n„ï est›  normalizadï eí freqˆnciá å á op‡„ï då aprå
sentaò resultadoó normalizadoó n„ï ›‚ utilizada® 

   Så ná fun‡„ï då transferˆnciá calculadá ocorrereí caîcelameî
toó p¢lï-zero¬ eleó n„ï ser„ï considerados¬ sendï oó  polin“mioó 
apråsentadoó  coí raizeó comunó nï numåradoò å denominador®  Noó 
gr ficoó  då  p¢loó å zåros¬ oó cancelámentoó  ser„ï  clarámentå 
vis¡veis®  Istï ›‚ då graîdå utilédadå ná an liså då sistemaó  eí 
quå p¢loó n„ï observ veió podeí ocorrer® Todoó oó p¢loó dï  sis
temá s„ï semprå apråsentádoó noó gr ficos.

   Så  uí polin“miï calculadï possuiò raizeó m£ltiplas¬ ï  algï
ritmï usadï pará c lculï då ra¡zeó n„ï conseguir›  definé-laó coí 
graîdå precis„o® Ï mesmï podå ocorreò coí polin“mioó coí  ra¡zeó 
diferindï poò muitaó ordenó då graîdeza¬ oõ excessivamentå  pr›¢
ximas®  Eventualmentå podå ocoòreò "overflow¢ durantå ï  c lculï 
då ra¡zeó devidï á diveògˆnciá crescentå nï algor¡tmï då  c lcõ
lo®  Umá  mudan‡á nï fatoò då normaliza‡„ï  eí  freqˆnciá  podå 
resolveò ï prïblema® Så ï problemá persistir¬ á solu‡„ï ›‚ salvaò 
ï  polén“mio¬ å calculaò suaó ra¡zeó coí outrï programa® Ï  prï
gramá  HË utilizá uí algor¡tmï maió sofisticadï pará c lcõlï  då 
ra¡zes¬ å podå seò usadï coí está finalidade.

   Circuitoó coí muitoó amplificadoreó operacionaió reaió  ("A"© 
å  outroó circuitoó realimentados¬ podeí geraò s›‚rioó  problemaó 
num‚ricos¬  devidï á presencá då grupoó då fråqˆnciaó  naturaió 
distandï då v riaó ordenó då magnitõdeº Aó freqˆnciaó  naturaió 
dï circuitï ideaì å aó oõtraó secund riaó geradaó peloó aíplifi
cadores® Atrav‚ó då cuédádosï ajustå doó fatoreó då normaliza‡„ï 
å dá dispers„o¬ ›‚ poss›¡veì obteò an liseó precisaó pará á  maioò 
partå doó circuitoó usuais¬ maó så á distƒnciá entrå freqˆnciaó 
naturaió  principaió  å såcund› riaó foò muitï  grande¬  á  formá 
recomendadá pará á oâten‡„ï coí algumá precis„ï destaó  freqˆnŠciaó  ›‚ usaò uí fatoò då normáliza‡„ï eí freqˆnciá  baixï  pará 
obteò  aó freqˆnciaó natõraió priîcipais¬ å uí fatoò maió  altï 
pará obteò aó secund rias® Ï fatoò då normaliza‡„ï eí impedƒnciá 
devå seò ajustadï tamb‚m¬ poió ï n¡veì då impedƒnciá då uí  cir
cuitï  assií  podå seò subótanciaìmentå diferentå  eí  baixaó  å 
altaó  freqˆncias®  Eí quaìqueò caso¬ á  precisaï  doó  valoreó 
calculadoó podå seò aváliadá obseòvandï så mudaí apreciávalventå 
quandï oó fatoreó då normáliza‡„ï s„ï variados® Á dispeòs„ï devå 
seò ajustadá pará quå ï graõ doó polin“mioó estejá semprå corre
to¬ pará menoò erro® Pará evitaò prïblåmaó (å tamb‚í aceleraò  ï 
c lculo¬  poió cadá amplificádoò ideaì eliminá uí n›¢ dï  circui
to)¬ semprå quå poós¡veì amplifécadoreó ideaió deveí seò  utilé
zados® 

   Fun‡”eó á sereí comparadaó nï mesmï gr ficï deveí seò  calcõ
ladaó coí ï mesmï fatoò då normaliza‡„ï eí freqˆîcia¬ oõ  ent„ï 
coí  á apresenta‡„ï då resultadoó normalizádoó  desligada¬  pará 
quå aó escalaó då freqˆnciá sejaí corretas.

   Algunó recursoó £teió s„o:

   Fonteó  ideaió då tens„oº Så suspensas¬ usá-så umá fontå  "Z¢ 
eí  s‚riå  coí uí resistoò dï mesmï valoò quå ï  dá  foîte¬  maó 
negativo® Så aterrada¬ å melhoò colocaò uí "buæfer¢ coí amplifé
cadoò operacionaì ideaì eí s‚riå coí umá fontå "Z".

   Outraó fonteó controladaó al‚í dá VCCSº 

  VCVSº Usá-så umá VCCÓ coí á sa¡dá eí paralelï coí uí  resiótoò 
  då ± Ohí å coí uí resistoò då -± Ohí eí s‚rie.
  CCCSº Usá-så umá VCCÓ coí á entradá eí paralelï coí uí  resis
  toò då ± Ohí å coí uí resistoò då -± Ohí eí s‚rie.
  CCVSº Usá-så oó doió recursoó acima.

   Semprå  quå  á sa¡dá foò eí tens„ï å estiveò aterradá  då  uí 
lado¬ uí buffeò coí amp® op® ideaì å melhoò quå ï råsistoò negá
tivo.

   Amp®  op® coí resistˆnciá då sa¡dá nulaº Colocá-så uí  buffeò 
coí amp® op® ideaì eí s‚riå coí á sa¡da® › melhoò istï quå colï
caò uí resistoò negativï eí s‚rie.

   Correntå eí uí ramoº Colocá-så eí s‚riå coí ï ramï uí  resió
toò då ± Ohí å uí då -± Ohm® Á correntå ›‚ á tens„ï sobrå ï då  ± 
Ohm®  Så elå n„ï estiveò aterrado¬ podå-så copiaò á tens„ï  pará 
outrï n›¢ usandï umá VCCÓ å uí resiótoò aterrado.

   Correntå  då sa¡dá då uí OTAº Colcá-så uí outrï OTÁ  idˆnticï 
aï  OTÁ á mediò coí á entradá eí paralelï coí á deste¬ ligadï  á 
uí  resistoò då ± Ohí aterrado® Á correntå då sa¡dá dï OTÁ  gerá 
umá tens„ï numericamentå iguaì á elá nestå n¢.

   Impedƒnciá  då n¢º Excitá-så ï n›¢ desejadï coí  umá  coòrentå 
unit ria® Á tens„ï nodaì ›‚ á impedƒnciá desejada.
Š   Admitƒnciá  då n¢º Excitá-så ï n›¢ desejadï coí umá  fontå  då 
tens„ï coí uí resistoò s‚riå då ± Ohm® Entrå ï terminaì dá fontå 
quå  iriá ›… terrá å á terrá colocá-så uí resistoò då -±  Ohm®  Á 
tens„ï sobrå elå ›‚ á admitƒnciá desejada.

   Documenta‡„ï v lidá pará á vers„ï 5.6.

(Ï  programá IFFÔ foé substituidï pelï X_IFFT¬ maió  poderosï  å 
coí melhoò interface® Á Vers„ï 5.¶ foé criadá apenaó pará manter
compatibilidade.)

Ant“niï Carloó M® då Queiroú (COE10009@UFRJ.BITNET)

22/10/1992
