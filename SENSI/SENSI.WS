..Imprimir com WordStar 4.0
.LS1
.RM64
.PL66
                     Ï Programá SENSI‚

Documenta‡„ï v lidá pará á vers„ï 4.9a.

± ­ Introdu‡„o

   Ï programá SENSÉ analisá circuitoó lineareó å invariaîteó  nï 
tempo¬ utilizandï umá formá compactá dá an liså nodaì  modifica
da¬ å ï m‚todï dá redå adjuntá pará á an liså då sensibilidades® 
Dá an liså podeí seò obtidos:

­ M¢dulï faså å atrasï då grupï då umá fun‡„ï då transfårˆncia.
- Sensibilidadeó.
­ Desvioó estat¡sticoó då m¢dulï å fase.
- Sensibilidadå de p¢loó å zeroó.
­ Desvioó estat¡sticoó då p¢loó å zeros.
­ An liså då faixá dinƒmicá.

² ­ Parƒmetroó då entradá pará ï programa

   Ï programá l›ˆ á descri‡„ï dï circuitï á analisaò eí uí arqui
vï då texto¬ organizadï ná formaº 

­ Primeirá linhaº n£merï då n¢s.

- Linhaó seguintesº descri‡„ï (neô-list)¬ uí elementï  poò 
  linha:
­ Resistoò coí resistˆnciá R:
  R<nome¾ <n¢1¾ <n¢2¾ <Ò>
­ Indutoò coí indutƒnciá L:
  L<nome¾ <n¢1¾ <n¢2¾ <L>
­ Capacitoò coí capacitƒnciá C:
  C<nome¾ <n¢1¾ <n¢2¾ <Ã>
­ Fontå då tens„o controladá á tens„o (VCVS)¬ coí ganhï Av:
  E<nome¾ <n¢Vo+¾ <n¢Vo-¾ <n¢Vi+¾ <n¢Öi-¾ <Av>
­ Fontå då correntå controladá á correntå (CCCS)¬ coí ganhï Ai:
  F<nome¾ <n¢Io+¾ <n¢Éo-¾ <n¢Ii+¾ <n¢Ii-¾ <Ai>
- Fontå då correntå controladá á tens„ï (VCCS)¬ coí  tranócondõ
  tƒnciá Gm:
  G<nome¾ <n¢Io+¾ <n¢Éo-¾ <n¢Vi+¾ <n¢Öi-¾ <Gí>
­ Fontå   då  tens„ï  controladá  á   correntå   (CCVS)¬   coí 
transresistˆîcia Rm:
  H<nome¾ <n¢Vo+¾ <n¢Vo-¾ <n¢Ii+¾ <n¢Ii-¾ <Rí>
­ Girador¬ coí resistˆnciá då gira‡„ï Rg:
  Y<nome¾ <n¢1+¾ <n¢±-¾ <n¢2+¾ <n¢²-¾ <Rç>
- Amplificadoò operacionaì ideal, modelï nullatoò-norator:
  O<nome¾ <n¢ entr® 1¾ <n¢ entr® 2¾ <n¢ sa¡da>
- Amplificadoò operacional¬ coí ganhï GB/ó (GÂ eí rad/s© å 
  resistˆnciá då sa¡dá Ro:
  A<nome¾ <n›¢-¾ <n¢+¾ <n¢sa¡da¾ <GÂ¾ <Rï>
­ Transistoò bipolar¬ modelï h¡bridï è simplificado:
  Q<nome>¬ <n›¢ c¾ <n›¢ b¾ <n›¢ e¾ <hfe¾ <hie>
­ Transistoò MOS:
  M<nome>¬ <n›¢ d¾ <n›¢ g¾ <n›¢ s¾ <Gm¾ <Gds>
­ Fontå då tens„o coí resistoò eí s‚riå Rs:Š  Z<nome¾ <n¢-¾ <n¢+¾ <Rs¾ <V>
­ Fontå då tens„o:
  V<nome¾ <n¢+¾ <n¢-¾ <V>
­ Fontå då corrente:
  I<nome¾ <n¢+¾ <n¢-¾ <I>

   Todaó  aó  unidadeó eí Ohms¬ Mhos¬ Faradó å Henrys® Ï  n›¢  då 
terrá ›‚ ï n›¢ 0® Oó nomeó deveí possuiò at›‚ µ caractåres¬  inclõ
indï á inicial® Oó componenteó podeí estaò eí qualqueò ordeí å á 
numera‡„ï  doó  n¢ó tambem¬ maó devå seò cont¡nua¬  seí  n£meroó 
faltando.

   Á  descri‡„ï  podå seò geradá pelï programá editoò  EdFil¬  á 
partiò dï diagrámá esquem ticï dï circuito.

3 ­ Respostá eí freqˆncia

   Ï programá considerá aó entradaó dï circuitï (aó fonteó  "Z"© 
comï fonteó då tens„ï unit rias® Todoó oó c lculoó refereí-så …ó 
tens”eó noó n¢ó dï circuito¬ quå equivaleí á fun‡”eó då transfe
rˆnciá daó entradaó at›‚ a¡.

   Ï gr ficï då respostá eí freqˆnciá podå seò pedidï imediatá
mentå  ap¢ó á leiturá dï arquivï då dados¬ usandï-så aó  escalaó 
"default"¬ adequadaó pará circuitoó normalézadoó eí  freqˆncia® 
Outraó  escalaó  podeí seò determinadaó anteó  dá  plotageí  doó 
gr ficos¬ oõ ajustadaó iterativameîtå durantå á plotagem®  Podeí 
seò  plotadas¬ eí uí £nicï gr fico¬ curvaó då m¢dulï å  faså  dá 
fun‡„ï då transferˆîcia¬ atrasï då grupï å desvioó  estat¡sticoó 
dï  m¢dulï å dá faså dá fun‡„ï då  transferˆncia®  Inicialmente¬ 
s„ï plotádaó apenaó curvaó då m¢dulo¬ faså å desviï  estat¡sticï 
dï m¢dulo® Uí cursoò podå seò acionadï á qualqueò instantå  pará 
leiturá då valoreó nï gr fico.

   V riaó  teclaó possueí fun‡„o¬ aï finaì å durantå á  plotageí 
dï gr fico:

­ Setaó horizontaisº Ligaí å movimentaí ï cursor.
­ Ctrl-Setaó horizontaisº Idem, coí passï maior.
­ Tabº Mudá á curvá selecionadá pelï cursor.
- Delº  Removå dï gr ficï á curvá selecionadá (å selecioná á  då 
  m¢dulo).
­ Insº Recolocá nï gr ficï á curvá selecionada.
- Setaó  verticaisº  Deslocaí verticalmentå (1/² tela©  á  curvá 
  selecionada.
- «  å  -º Ampliá (x2© å reduú (/2© ï limitå superioò  dá  curvá   
  selecionada.
- Aº Ampliá ï limitå superioò då freqˆncia¬ colocandï nï gr fé
  cï  ï  quå apareceriá så á largurá dá  reá då  plotágeí  fosså 
  dobrada® 
- Rº Reduú ï limitå superioò då freqˆncia¬ colocandï nï gr ficï 
  ï  quå  apareceriá så á largurá dá  reá då  plotágeí  fosså  á 
  metadå dï quå ‚.
- ¼ å >º Moveí aó curvaó eí freqˆnciá då 1/² tela.
­ Returnº Redesenhá ï gr fico¬ seí ï cursor.Š­ Espa‡oº Mostrá ï cursor.
- Eº Liga/desligá ï tra‡adï daó curvaó då m¢dulï å faså coí seuó 
  desvioó estat¡sticoó somadoó å subtra¡dos.
- Gº Liga/desligá ï tra‡adï dá gradå (aó escalaó dá gradå semprå 
  s„ï aó dá curvá selecionada¬ mesmï quå elá estejá invis¡vel).
­ Fº Liga/desligá ï tra‡adï då curvaó då fase.
­ Tº Liga/desligá ï tra‡adï då curvaó då atrasï då grupo.
- Qº Mudá á posi‡„ï dï quadrï då medidá dï cursor.
­ Escº Encerrá á plotagem¬ retornandï aï menõ principal.

   Oó  valoreó calculadoó s„ï semprå quå  poss¡veì  aproveétadoó 
quandï aó escalaó s„ï mudadas® Ï cursoò tamb‚í n„ï mudá då  frå
qˆncia¬  så poss¡vel® Oó gr ficoó somentå ser„ï totaìmentå  rå
calculadoó  så ï n›¢ då sa¡dá dï circuitï foò mudado¬ oõ  se¬  nï 
menõ  då escalas¬ ï n£merï då segmentoó oõ á escalá då  freqˆî
ciaó  foò  mudada® Ï n£merï iniciaì då segmentoó  (pontoó-1©  nï 
gr ficï  dependå dá mem¢riá dispïn¡vel¬ å ›‚ normalmentå  då  78® 
Havendï  mem¢ria¬  podå seò aumentadï at›‚ uí m ximï  då  256®  Ï 
programá  semprå  usá ï m ximï valoò entrå ï  especificadï  å  ï 
poss¡vel® 

   Aó  respostaó eí freqˆnciá pará v rioó circuitoó  difårenteó 
podeí seò comparadaó pelï programá CPSENSI¬ á paòtiò daó tabelaó 
geradaó pelï SENSI.

4 ­ Listagenó då sensibilidades

   Aó sensibilidadeó S(T,x)=(x/T)*(dT/dx© dá fuî‡„ï då  transfå
rˆnciá T(s© eí rela‡„ï á todoó oó parƒmetroó ø podeí seò  obser
vadaó  ap¢ó á plotageí då uí gr fico® Á partå reaì podå seò  in
teòpretadá  comï  sendï á sensibilidádå dï m¢dulï dá  fun‡„ï  då 
tranóferˆnciá  eí  Neperó å á partå imagin riá comï sendï  á  dá 
faså eí radianos® › liótadï tamb‚í ï valoò då S(T,s)¬ á sensibi
lidadå  dá fun‡„ï då transfårˆnciá eí rela‡„ï á "s"® Á  listageí 
så  iniciá pelá freqˆnciá dï cursor¬ å podå seò mudadá  coí  aó 
setaó horizontais® Á mudan‡á så refletå nï cursoò dï gr fico®  Ï 
cursoò verticaì permitå quå aó sensébilidadeó eí rela‡„ï á todoó 
oó componenteó sejaí listádas¬ casï n„ï caibaí todaó ná tela®  

   Oó parƒmetroó quå comp”eí oó elementoó coí maió då uí parƒmå
trï (Á å Q© s„ï identificadoó nestá listageí å naó demaió por:

­ A<nome¾ ­ GÂ då uí amp® op.
­ a<nome¾ ­ Rï då uí amp® op.
­ Q<nome¾ ­ hfå då uí transistoò bipolar
­ q<nome¾ ­ hiå då uí transistoò bipolar
­ M<nome¾ ­ Gí då uí transistoò MOS
­ m<nome¾ ­ Rdó då umtransistoò MOS

5 ­ Án liså da faixá dinƒmica

   Durantå  oó c lculoó pará ï tra‡adï doó gr ficoó då  respostá 
eí freqˆncia¬ oó m ximoó å m¡nimoó valoreó dï m¢dulï dá  fun‡„ï 
då transferˆnciá pará cadá n›¢ dá redå s„ï computados® Oó valoreó 
s„ï acumuladoó enquantï oó gr ficoó n„ï foreí totalmentå  recaìŠculados®  Aó setaó verticaió permiteí á listageí då n¢ó quå  n„ï 
caibaí ná tela.

6 ­ Desvioó estat¡sticos
   
   Oó desvioó estat¡sticoó representaí ï errï quå så devå  espå
raò construindï ï circuitï coí componenteó coí aó variabilidadeó 
oõ  tolerƒîciaó dadas¬ supondï n„ï correlácionadoó oó  erroó  nï 
valoò  doó  parƒmetros® Poò exemplo¬ så X¥  doó  parƒmetroó  doó 
componenteó usadoó possuéreí menoó quå á variábilidadå dadá (coí 
distribui‡„ï  noòmal)¬  X¥ doó circuitoó quå  foreí  construidoó 
estar„ï dentrï doó liméteó dadoó peloó desvios® 

   Aó variabilidadeó pará todoó oó parƒmetroó dï circuitï  podeí 
seò especificadas¬ pará todoó oó elementoó oõ individualmente® Ï 
valoò  "default¢  ›‚ då 0.0µ (oõ 5¥ då  tolerƒncia)®  Alteraò  aó 
variabilidadeó  faú  coí quå oó desvioó  sejaí  recalculadoó  (ï 
c lculï ›‚ r pido)® Está facilidadå permitå quå ï efeitï då  cadá 
parƒmetrï  nï comportamentï dï ciòcuitï sejá estudado¬ å  quå  á 
tolerƒnciá necess riá pará cadá parƒmetrï sejá fácilmentå deter
minada® Observå-så quå ï errï eí dÂ causadï poò umá variabilida
då isoladá ›‚ fun‡„ï lineaò dá variabélidade® Poò exemplo¬ så coí 
5¥  då  tolerƒnciá pará todoó oó componenteó ï  errï  m ximï  då 
ganhï  eí  umá dadá freqˆnciá foò då µ dB¬  så  aó  tolerƒnciaó 
foreí  reduzidaó pará 1%¬ ï errï cair›  pará ± dB®  Inicialmente¬ 
aó  variabilidadeó  daó fonteó independenteó s„ï nulas¬  j›   quå 
usualmentå n„ï s„ï consideradaó eí an liseó då sensibilidade® Så 
necess rio¬ podeí seò alteradaó individualmente® Á mudan‡á  glo
baì då variabilidadeó n„ï aó afeta.

7 ­ Sensibilidadeó coí desconto

   Á op‡„ï då descontaò aó sensibilidadeó dï valoò eí certá frå
qˆnciá  podå seò usadá pará eliminaò á partå invariantå  coí  á 
freqˆnciá daó sensibilidades¬ apreseîtendï apenaó oó erroó  quå 
distorceí  á formá daó curvaó dá respostá eí freqˆncia®  Eí  uí 
filtrï derivadï då umá reáliza‡„ï passivá LÃ duplamentå termina
dá coí m ximá tranóferˆnciá då potˆncia¬ está freqˆnciá ›‚  ondå 
ï ganhï ›‚ m ximï (så ï m ximï ocorreò eí CC¬ usá-så umá freqˆn
ciá baixa¬ n„ï nula)® Pará filtroó då outroó tipoó podå n„ï  seò 
rigorosamentå  corretï usaò está op‡„o¬ poió  aó  sensébilidadeó 
podeí  n„ï possuiò umá partå invariantå coí á freqˆncia¬  oõ  ï 
valoò  constantå podå n„ï aconteceò pará todoó oó parƒmetroó  ná 
mesmá freqˆncia® Coí ï usï dá op‡„o¬ á partå reaì daó  sensibi
lidadeó  listadaó  ›‚ apreseîtadá coí ï descontï feéto®  Umá  veú 
feitï  uí  descoîto¬ elå permanecå ativï at›‚ quå  á  op‡„ï  sejá 
desligadá oõ quå ï n›¢ då sa¡dá sejá mudado® Notå-så quå oó erroó 
calcõladoó  destá  formá s›¢ s„ï v lidoó eí circuitoó  eí  quå  ï 
valoò absolutï dï ganhï n„ï sejá importante.

8 ­ Sensibilidadeó normalizadaó pelá inclina‡„o
     
   Á  op‡„ï  då normalizaò aó sensibilidadeó pelá  inclina‡„ï  å 
£tiì  pará eliminaò aó falsaó altaó sensibilidadeó  quå  pareceí 
ocorreò  semprå quå m¢dulï oõ faså variaí rapidámente¬ comï  naó Švizinhaîcaó då zeroó då transmiss„o® Oó novoó desvioó podeí  seò 
inteòpretadoó  comï  á distƒnciá perpendiculaò entrå  aó  curvaó 
ideaió å aó reaió då m¢dulï å fase¬ så oó diagramaó foreí plotá
doó  eí m¢dulï eí dÂ ø 20log(w© ("freqˆnciá eí dB")¬ å faså  eí 
grauó ø (180/ã)ln(w© ("freqˆnciá eí graus").

9 ­ Sensibilidadeó doó p¢loó å zeros

   Pará an liseó då sensibilidadå då p¢loó å zeros¬ å necess riï 
uí  arquivï då textï contendï oó p¢loó oõ oó zeros¬  nï  formatï 
geradï  pelï  programá IFFÔ (1a® linhaº n£merï  då  freqˆncias® 
Linhaó seguiîtesº <real¾ <imag.¾ då cadá p¢lï oõ zero)® Aó  seî
sibilidadeó calcõladaó pará p¢loó å zeroó s„ï n„ï  normalizadasº 
S'(s,x)=ds/(dx/x)®  Oó  desvioó estat¡sticoó daó parteó  reaì  å 
imagin riá  calculádoó defineí uí retƒngulï ondå ï p¢lï oõ  zerï 
dever›  estar¬ centradï ná posi‡„ï ideal.

   Comï  uí  refinamentï destá medida¬ s„ï  aindá  calculadoó  á 
dire‡„ï  angulaò  ondå á varia‡„ï maioò ›‚ esperadá  å  oó  raioó 
maioò å menoò då umá elipså dentrï dá quaì ï p¢lï oõ zerï dever›  
estar® Oó retƒnguloó å elipseó podeí seò plïtadoó juntamentå coí 
oó p¢loó oõ zeroó eí uí gr fico® 

   Nestå gr fico¬ aó setaó dï cursoò movimentaí oó limétes¬ «  å 
­ mudaí á amplia‡„ï å Taâ mudá á freqˆnciá sålecionada® Esã eî
cerrá á plotagem.

   Ï c lculï då sensibilidadå doó p¢loó s›¢ funcioná corråtamentå 
så  á impedƒîciá då entradá dá rede¬ comï vistá poò uí cortå  nï 
ramï  ondå estiveò ï elementï usadï comï obseòvador¬  quå  deveò 
seò doó tipoó R¬ L¬ Ã oõ Z¬ possuiò comï zeroó oó p¢loó  desejá
dos¬  sendï nulá nestaó freqˆncias® Oõ seja¬ aó  seîsibilidadeó 
doó  p¢loó dá redå uí rela‡„ï aï parƒmetrï obseòvadoò usadï  n„ï 
podeí seò nulas® Ï programá verificá istï å n„ï calculá aó  seî
sibilidádeó då p¢loó n„ï claramentå observ› veis® Notå-så quå  eí 
algunó  circuitoó  n„ï existå uí elementï quå observå  todoó  oó 
p¢los®  Nestå  caso¬ podeí ocorreò problemaó num‚ricos¬  poió  á 
impedƒnciá  vistá poò uí cortå nï ramï observadoò  poss£é  zeroó 
sobrå  oó p¢loó n„ï observ veis¬ å ï sistemá då  equa‡”eó  usadï 
pelï prïgramá torná-så singular® Umá redu‡„ï ná tolerƒnciá  pará 
admitƒnciaó podå fazeò coí quå ï programá fa‡á ï c lculo¬  aprï
ximadamente¬  assií mesmo¬ n„ï parandï poò  "determinantå  muitï 
pequeno".

   Nï c lculï då sensibilidadå doó zeroó ›‚ tamb‚í feitá á  veré
fica‡„ï dá corre‡„ï doó zeros® 

   Aó  listagenó då sensibilidadeó då p¢loó å zeroó teí ï  mesmï 
formatï  daó listagenó då sensibilidades¬ å obedeceí aoó  mesmoó 
comandosº  cursoò  horizontaì pará mudaò  freqˆnciaó  å  cursoò 
verticaì pará mudaò parƒmetros.

   Ï parƒmetrï då tolerƒîciá pará impedƒnciaó å tens”eó podå seò 
aumentadï pará permitiò c lcõloó aproxémadoó quandï oó p¢loó s„ï 
poucï  observ veió oõ n„ï muitï precésoó oõ oó zeroó  n„ï  muitï Šprecisos®  Ï outrï parƒmetrï då tolerƒncia¬ pará  admitƒnciaó  å 
freqˆncias¬  ›‚ usadï pará detec‡„ï då sistemaó då equa‡”eó  nï
daió  singulareó  (deteòminantå muitï pequeno©  å  pará  impediò 
c lculï då sensibélidadå då zeroó ná origem.

   Ï  programá IFFÔ devå seò usadï pará á obten‡„ï  precisá  doó 
p¢loó å zeros® Oó c lculoó deveí seò feitoó coí á op‡„ï då apre
sentaò resultadoó desnormalizadoó åm freqˆîcia.

   Oó desvioó estat¡sticoó doó p¢loó å zeroó pará diversoó  cir
cuitoó  diferenteó podeí seò comparadoó pelï programá  CPSPZ¬  á 
partiò daó tabelaó geradaó pelï SENSI.

1° ­ Arquivï då sa¡da

   Ï  programá  podå criaò uí arquivï contendï tudï  ï  quå  foò 
calcõladï  usandï-så  á op‡„ï "abriò arquivï då sa¡da¢  dï  menõ 
princépal®  Ï programá perguntá eí ocasi”eó  aprïpriadaó  (op‡„ï 
"Salvar"¬ teclá "s"¬ noó menus© så ï resuìtadï doó ultimoó  c l
culoó  oõ altera‡”eó devå seò aòquivádo® V rioó  arquivoó  podeí 
seò criados® Ï arquivï atuaì ›‚ autom ticamentå fechadï quandï  ›‚ 
pedidá á an liså då outrá redå oõ quandï ï programá ›‚ encerrado.

11 ­ Observa‡”es

   Amplificadoreó  operacionaió ideaió deveí seò  usadoó  semprå 
quå possivel¬ poió istï acelerá ï processï då solõ‡„ï dï circué
tï å reduú ï errï num‚rico.

   Podeí ocorreò problemaó num‚ricoó så oó niveió då  iípedƒnciá 
dï circuitï foreí muitï elevadoó oõ muitï baixos® ›  recomendadï 
quå todaó aó an› liseó sejaí feitaó eí ciòcuitoó normalizadoó  eí 
freqˆnciá å impedƒncia® Principaìmentå eí impedƒncia.

   Nenhumá  admitƒnciá  oõ transadmitƒnciá  podå  seò  infinéta¬ 
implécandï quå resistˆnciaó å indutƒnciaó n„ï podeí seò nulas¬ å 
quå circuitoó contendï indutoreó oõ amplifécadoreó  operacionaió 
reaió n„ï podeí seò analisadaó eí CC® 

   Eí escalá logar¡tmicá n„ï ›‚ permitidá á an liså eí freqˆîciá 
menoò  oõ iguaì á zero® Aó escalaó verticaió å  horizontaió  n„ï 
podeí seò invertidaó så á gradå estiveò sendï usada.

   Quandï á resolu‡„ï usadá noó gr ficoó n„ï ›‚ grande¬  detalheó 
importanteó  podeí seò perdidos® Uí casï cr¡ticï ›‚ ï då  m ximoó 
doó  desvioó då m¢dulï normalizadoó pelá iîclina‡„o¬ quå eí  aì
gunó filtroó formá picoó agudos® Ï valoò corretï doó picoó  podå 
seò obtidï aumentandï-så ï n£merï då segmentos¬ expandiîdï-så  á 
escalá horizontal¬ oõ tïmandï-så ï valoò dï desviï n„ï  normali
zadï  ná freqˆnciá dï pico¬ quå coincidå coí ï normalézado¬  j›  
quå a›¡ á curvá då m›¢dulï ›‚ horizontal.

   Naó telaó gr ficas¬ tocandï-så aó teclaó "H¢ å "V¢ s„ï  aciï
nadaó  rotinaó  då impress„ï dá tela¬ eí formatï  horézontaì  oõ 
vertical¬ eí impressorá tipï EPSON® Aó rotinaó n„ï emiteí  avisï Šalgum¬ å somentå funcionaí coí á placá CGA® Á impress„ï podå seò 
interrompidá tocandï-så qualqueò tecla.

   Á  partiò dá vers„ï 4.4¬ s„ï calculadaó aó sensibilidádeó  eí 
rela‡„ï ›… impedƒnciá då sa¡dá doó amplificadores¬ anteó  ignora
da® Foé introduzidï tamb‚í ï modelï pará transistor.

   Ná vers„ï 4.5¬ ï formatï daó tabelaó å daó listagenó ná  telá 
foé  mudado® Umá nová vers„ï doó programaó CPSENSÉ å CPSPÚ  tevå 
quå seò escrita® Foé introduzidï ï transistoò MOS® 

   Ná vers„ï 4.6¬ pequenaó mudan‡aó foraí feitaó nï formatï  daó 
tabelaó å noó comandoó doó gr ficos.

   Ná  vers„ï 4.7¬ á fontå "F¢ foé mudadá pará "Z"¬ å aó  letraó 
iniciaió  doó segundoó parƒmetroó doó elementoó coí maió  då  uí 
foraí mudadaó pará vers”eó min£sculas¬ comï prepara‡„ï pará  umá 
futurá vers„ï usandï an liså nodaì modificada.

   Ná vers„ï 4.8¬ á an liså nodaì modificadá compactá foé imple
mentada¬  coí todaó aó quatrï fonteó controladaó å aó fonteó  då 
tens„ï å corrente.

   Á  vers„ï 4.¹ inclué umá vers„ï då modï protegidï  (sensé-p)¬ 
quå admitå gr ficoó då maioò resolu‡„o® Ï arquivï då sa¡dá passá 
á incluiò aó curvaó då ganhï +¯­ errï å faså +¯­ erro® Á  vers„ï 
4.9á ›‚ uí poucï maió r pidá devidï á umá otimiza‡„ï nï algor¡tmï 
då fatora‡„ï LU.

   Ï  programá  SENSÉ  podå  seò  distribu¡dï  livrementå   pará 
prop¢sitoó  educacionaió  å  acadˆmicos¬  desdå  quå  n„ï   sejá 
alterado¬  å  quå referˆnciá á seõ usï sejá feitá  eí  trabalhoó 
realizadoó coí suá ajuda.

   Coment rioó  oõ d£vidaó sobrå á utiliza‡„ï dï programá  podem 
seò remetidoó para:

Dr® Ant“niï Carloó Moreir„ï då Queiroú
Programá då Engenhariá El‚trica¬ COPPE 
Universidadå Federaì dï Riï då Janeiro
CĞ 68504
21945-97° Riï då Janeiro¬ RJ¬ Brasil

Ou¬ viá e-mail¬ para: acmq@coe.ufrj.br

ACMQ¬ 13/01/95