.ls1
.rm 73
Progra� ASI� � Analysi� o� switche�-curren� filters
��������������������������������������������������-

Documentatio� �fo� �versio� 1.5�

Introduction
�����������-

     Th� ASI� progra� analyze� switche�-curren� (SI)� �switche�-capac�to� �
(SC� filters� o� an� periodicall� switche� G�-� circui� wher� th� circui� �
stabilize� betwee� th� switchin� instants� Th� progra� ca� comp�te:

Z-transfor� transfe� functions.
Pole� an� zeros.
Frequenc� response� Gain� phase� an� grou� dela� (approximated).
Tim� responses.
Fr�quenc� respons� sensitivities.
Effect� o� nonidea� transistor� i� switche�-curren� circuits.
Error� du� t� componen��tol�rance� (sensitivit� analysis).
Outpu� frequenc� spectrum�

     Th� output� o� th� analyse� ca� b� plotte� o� th� scree� an� sen� t� �
� repor� file� Th� descriptio� o� th� circui� t� b� analyze� i� rea� fro� �
� tex� file� bu� al� th� command� ar� give� interactivel� i� � �gr�phica� �
use� interface.

Input
����-

     Th� circui� t� b� analyze� mus� b� describe� b� it� smal�-signa� �A� �
mode� (th� norma� structur� fo� � S� circuit� an� th� circui� withou� th� �
bia� �source� �fo� � S� circuit)� Th� circui� descriptio� i� give� �b� �� �
tex� file� i� th� format:

Firs� lin�: numbe� o� node� i� th� circuit. �
Followin� line� On� elemen� descriptio� pe� line: �

�	MO� transistor:
	M<name� <drai� node� <gat� node� <sourc� node� <Gm� <Gds>
�	Resistor:
	R<name� <nod� 1� <nod� 2� <resistance>
�	Capacitor:
	C<name� <nod� 1� <nod� 2� <numbe� o� uni� capacitances>
�	Curren� source:
	I<name� <nod� +� <nod� -� <current>
�	Voltag� source:
	V<name� <nod� +� <nod� -� <voltage>
�	Switch:
	S<name� <nod� 1� <nod� 2� <phase� [<phase>...]
�	Transconductor:
	G<name� <nod� I+� <nod� �-� <nod� V+� <nod� �-� <Gm>
�	Idea� operationa� amplifier:
�����	O<name� <inpu� node� <inpu� node� <outpu� node>
�	Voltag� amplifiers:
�	E<name� <nod� Vo+� <nod� V�-� <nod� Vi+� <nod� V�-� <Av>��	A<name� <nod� V�-� <nod� Vi+� <nod� Vo� <Av>

     Th� �node� �ar� enumerate� fro� � t� th� numbe� �o� �nodes� �withou� �
missin� �numbers� � i� th� groun� node� Th� phase� ar� enumerate� fro� �� �
t� th� numbe� o� phases.

     Th�descriptio� ca� b� generate� b� th� EdFi� edito� program. �

Model� fo� th� elements
����������������������-

     Th� �MO� transistor� ca� b� �-channe� o� �-channel� Th� A� mode� �i� �
th� �sam� fo� both� � transisto� i� modele� b� � transconductanc� �Gm� �� �
Gd� �condu�tanc� � � Cg� capacitance� an� � Cg� capacita�ce� G� �an� �Gd� �
ar� �give� �i� th� netlis� file� an� th� othe� parameter� ca� b� �se� �i� �
severa� way� i� th� mosfe� parameter� window.

     Resistor� ca� b� use� t� conver� current� int� voltage� an� t� mode� �
losse� �i� �switche� an� D� curren� sources� Isolate� capacitor� �ca� �b� �
use� i� th� analysi� o� switche�-capacito� filters� an� th� simulatio� o� �
parasiti� capacitanc� effects� Th� curren� source� fee� th� inpu� �signa� �
t� S� filters� an� voltag� source� ar� th� input� fo� S� filters� �Tran��
conductor� ca� b� use� t� mode� OTAs� an� othe� functions� Voltag� ampl��
fier� �ca� �mode� finit�-gai� operationa� amplifier� i� S� �filters� �an� �
othe� �fun�tions� Fo� convenienc� i� usin� th� EdFi� editor� tw� �fo�mat� �
ar� �acce�te� �("E� an� "A")� Idea� operationa� amplifier� �ar� �use� �i� �
switche�-capacito� filter� an� i� precisio� switche�-curren� filters.

     Th� �switchin� perio� i� considere� subdivide� i� � nu�be� o� �equa� �
duratio� �phases� � switc� ca� b� ope� o� close� i� an� o� thes� �phases� �
Th� phas� lis� i� th� descriptio� o� th� switc� indicate� i� whic� phase� �
i� i� closed.

     Onl� on� inpu� ca� b� applie� t� th� circuit� Severa� signa� source� �
ca� �exis� i� th� netlist� bu� th� value� o� al� the� ar� �considere� �a� �
jus� scalin� factor� fo� th� sam� inpu� signal.

Output
�����-

     Th� �progra� �compute� noda� voltage� (i� �-transform)� �I� �th� �A� �
smal�-signa� �mode� th� relatio� betwee� gat�-sourc� vo�tage� �an� �drai� �
current� o� MO� transisto� i� linea� (an� th� Cg� an� othe� �capacitance� �
ar� �als� linear)� an� th� outpu� signa� ca� b� take� i� � �switche�-cu��
ren� filte� a� th� gat� voltag� o� th� transisto� tha� produce� th� �ou��
pu� current� Alternatively� mor� realistically� � resisto� ca� b� use� t� �
sampl� �th� outpu� current� I� thi� case� th� result� ar� als� vali� �fo� �
larg� signals� 

     Th� �voltage� i� th� adjoin� networ� ar� als� available� I� mus� �b� �
observe� tha� som� "voltages� i� th� adjoin� networ� (a� "hig� imp�dance� �
nodes� hav� n� physica� meaning� becaus� the� belon� t� capacitiv� �node� �
fe� �b� curren� sources� Thos� "voltages� ar� use� onl� �fo� �sensit�vit� �
calculations� �wher� �thei� "infinite� value� ar� �multiplie� �b� �"zero� �
conductances� producin� finit� (an� correct� curren� values� Whe� voltag� ��source� �ar� used� additiona� variable� ar� compute� i� th� adjoin� �ne��
work� indexe� wit� number� abov� th� number� o� n�des� The� represen� th� �
negativ� �o� th� current� i� th� voltag� source� i� th� adjoin� �network� �
an� �ar� use� i� sensitivit� calculations� Not� tha� th� adjoin� �networ� �
i� �no� �physicall� realizable� becaus� i� i� th� capacitor� �retai� �th� �
voltag� o� th� nex� phase� no� o� th� last.

     Th� voltage� compute� ca� b� interprete� a� th� respo�se� o� � per��
odicall� �switche� G�-� circuit� wher� th� current� (and� i� �th� �no�ma� �
circuit� �voltages� �ar� allowe� t� reac� th� stead� �stat� �betwee� �th� �
switchin� instants.

     Ther� �ar� restriction� o� th� topolog� o� th� circuit� tha� ca� �b� �
analyzed� Al� th� resistiv� portion� mus� hav� � connectio� t� th� signa� �
groun� a� al� th� phase� an� curren� source� canno� b� connecte� t� pur��
l� �capacitiv� node� (o� th� progra� wil� produc� singula� equatio� �sy��
tems)� Thi� normall� happen� i� an� practica� circui� topology� 

Progra� operation
����������������-

Netlist:

     Th� progra� begin� b� presentin� � director� lis� an� tex� field� t� �
b� fille� wit� th� nam� o� th� inpu� netlis� fil� an� th� numbe� o� �ph��
ses� �Th� fil� nam� ca� b� selecte� wit� th� mous� i� th� director� �wi��
dow� �o� b� give� i� th� DO� comman� line� Th� butto� "Read� �start� �th� �
readin� o� th� file.

Analysis:

     Afte� �th� �reading� � windo� wit� severa� �analysi� �par�meter� �i� �
presented� �Usuall� onl� th� outpu� nod� an� th� samplin� parameter� �ar� �
used� Th� other� rarel� mus� b� changed� Th� butto� "Analyze� start� �th� �
analysis.

     A� �th� en� o� th� analysis� th� compute� denominator� o� �chara�t��
risti� �polynomia� o� th� circuit� i� listed� an� ar� presente� � �windo� �
wit� �numerato� parameter� an� � men� wit� th� displa� options� Onc� �th� �
numerato� parameter� ar� se� t� th� desire� values� th� differen� �anal��
se� �i� �th� men� ca� b� mad� i� an� order� Th� men� ca� b� �reopene� �b� �
pressin� th� righ� mous� butto� o� th� fram� o� an� window.

Frequenc� response:

     Th� frequenc� respons� ca� b� plotte� fo� an� transfe� function� �I� �
i� plotte� i� th� progra� mai� window� wit� severa� option� selectabl� i� �
th� frequenc� respons� parameter� window� Th� sam� plo� i� als� use� �fo� �
th� �displa� o� erro� limit� (sensitivity� an� spectra� �component� �(se� �
below)� 

Transien� response:

     Tim� response� fo� severa� tes� input� ca� b� plotted� als� fo� �an� �
transfe� function� The� ar� plotte� i� � secondar� window� Th� �transien� ��respons� parameter� windo� hold� th� control� fo� th� severa� options.

Pole� an� zeros:

     Pole� an� zero� o� an� transfe� functio� ca� b� compute� an� plotte� �
i� �� �windo� o� listed� Alon� wit� th� frequencies� th� uni� �circl� �i� �
als� �plotte� fo� reference� Th� pole� an� zero� parameter� �windo� �con�
trol� ho� th� pole� an� zero� ar� compute� an� displayed.

Outpu� spectrum:

     Th� �outpu� �spectru� component� fo� � sinusoida� inpu� a� �� �give� �
frequenc� �ca� �b� plotted� superimpose� o� th� mai� �frequenc� �respons� �
plot� �Th� spectru� computatio� ca� b� starte� fro� th� �outpu� �spectru� �
parameter� �window� o� directl� fro� th� frequenc� respons� �window� �Al� �
th� spectru� component� tha� ar� i� th� frequenc� rang� selecte� fo� �th� �
mai� �transfe� �functio� ar� computed� Th� outpu� spectru� �i� �availabl� �
onl� fo� norma� transfe� functions.

Sensitivity:

     Sensitivitie� fro� � transfe� functio� i� relatio� t� th� �vari�tio� �
o� �� selecte� grou� o� circui� parameter� ca� b� computed� �an� �plo�te� �
alon� �wit� �th� gai� an� phas� curve� i� th� frequenc� �respons� �(main� �
window� �a� �error� i� decibel� an� degree� superimpose� �o� �th� �curve� �
shown� Th� error� ca� b� compute� a� deterministi� deviation� (su� o� th� �
error� �du� �t� al� th� selecte� parameters� �o� �statistica� �deviation� �
(squar� �roo� o� th� su� o� th� square� o� th� error� du� t� al� th� �s��
lecte� �parameters)� Al� th� selecte� parameter� ar� assume� t� hav� �th� �
sam� variability� Not� tha� th� sensitivitie� o� jus� on� noda� �voltage� �
th� �on� specifie� i� th� analysi� parameter� windo� a� th� star� o� �th� �
program� �ar� �availabl� afte� th� initia� analysis� �althoug� �frequenc� �
response� �o� an� noda� voltag� ar� alway� availabl� �withou� �recalcul��
tion� Th� comput�tio� o� error� du� t� � larg� grou� o� parameter� ma� b� �
slow� �Th� sensitivitie� o� th� transfe� functio� i� relatio� t� th� �v��
lue� o� al� th� selecte� element� ca� b� listed� b� pressin� "s� whe� th� �
curso� �i� a� th� desire� frequenc� i� th� frequenc� respons� �graph� �I� �
th� presen� version� sensitivitie� fo� unsample� inpu� ar� no� �availabl� �
(se� "sampling� below).

Sensitivitie� wit� gai� sensitivit� discounted:

     I� �i� possibl� t� discoun� th� gai� sensitivitie� a� � �give� �fre�
quenc� �fro� th� sensitivit� calculations� b� pressin� th� �correspondin� �
settin� �butto� i� th� sensitivit� analysi� parameter� window� Afte� �th� �
initia� �plot� �mov� th� curso� t� th� desire� frequenc� an� �pres� �"s"� �
Thi� i� usefu� t� separat� gai� error� fro� error� tha� distor� th� �gai� �
frequenc� �response� Th� techniqu� i� mor� clearl� meaningfu� i� �filter� �
derive� �fro� L� doubl� terminate� networks� wher� a� th� frequencie� �o� �
maximu� gai� onl� th� fla� gai� sensitivitie� affec� th� gain� 

Correlate� elements:

     Fo� �th� �statistica� deviatio� computation� �group� �o� �correlate� �
element� ca� b� specified� Thes� element� hav� thei� sensitivitie� �adde� ��an� ar� treate� a� � singl� elemen� i� th� computation� T� selec� �corr��
lations� �pres� on� o� th� key� "a".."z� befor� selectin� �element� �wit� �
th� �mous� lef� button� Al� th� element� marke� wit� � sam� �lette� �wil� �
belon� �t� � grou� o� correlate� elements� T� mak� element� �uncorrelate� �
wit� th� others� pres� th� "*� ke� befor� selectin� th� element� wit� th� �
mouse� Th� curren� selectio� o� element� an� correlation� ca� b� save� t� �
� fil� o� rea� back.

References:

     Frequenc� �response� an� transien� response� ca� b� save� �a� �ref��
rence� (th� command� ar� i� th� graphi� window� menus)� an� plotte� alon� �
wit� �other� �o� th� sam� circui� o� o� anothe� circui� �fo� �comparison� �
Sensitivit� curve� canno� b� save� a� references� I� i� als� possibl� �t� �
comman� th� progra� t� d� no� clea� th� frequenc� respons� windo� �befor� �
plottin� �� ne� curv� (pres� "x")� I� thi� wa� an� numbe� o� �references� �
wit� erro� curves� ca� b� accumulated.

Repor� file:

     Th� sam� menu� allo� th� savin� o� th� analyse� result� i� � �repor� �
file� �Th� message� windo� ca� als� b� save� i� th� repor� file� Fo� �th� �
frequenc� �response� �� tabl� i� generate� containing� �frequency� �gain� �
phase� �grou� �delay� gai� error� phas� error� minimu� �gai� �limit� �an� �
maximu� �gai� limit� a� column� o� values� Th� error� ar� liste� onl� �i� �
th� sensitivit� analysi� i� selected.

MO� transisto� parameters:

     I� �i� �possibl� t� includ� parasiti� effect� i� th� �circui� �i� �� �
simpl� �wa� usin� th� command� i� th� mosfe� parameter� window� �Onc� �a� �
ite� �i� changed� th� circui� mus� b� rea� agai� an� reanalized� Th� �n��
cessar� window� ope� automatically.
     
Direc� comman� i� th� windows
����������������������������-

Pole/zer� graph:

� Cursor� +� -� Mov� th� grap� an� change� th� scale.
� Mous� middl� button� Mov� th� cursor.
� G� Toggle� th� drawin� o� � grid.
� Esc� Exit� th� graph.
� Mous� lef� button� Draggin� th� mous� define� zoo� area.

Frequenc� respons� graph:

� Horizonta� curso� o� mous� middl� button� Cursor.
� A� R� +� -� Chang� th� horizonta� an� vertica� scales.
� Vertica� cursor� <(,)� >(.)� Panning.
� L� Change� th� horizonta� scal� betwee� log� an� linear.
� F� Toggle� th� drawin� o� phas� curves.
� T� Toggle� th� drawin� o� grou� dela� curves.
� V� List� th� linea� gai� a� th� curso� frequency.
� Mous� lef� button� Draggin� th� mouse define� zoo� area.�� G� Toggle� th� drawin� o� the grid.
� C� Change� betwee� colo� an� b&� picture.
� I� Invert� th� colors.
-�S� Lis� al� th� selecte� sensitivitie� a� th� curso� freque�cy� and,
     if the discount of gain sensitivities is enabled, plots a new graph.
� E� Plot� th� spectru� component� fo� a� inpu� a� th� curso� frequency.
� W� List� th� sam� spectrum.
� X� Toggle� th� clearin� o� th� windo� befor� th� plotting.
     (Usefu� fo� sensitivit� comparisons.)

(G� C� an� � affec� th� othe� plot� also� whe� the� ar� redrawn).

Transien� respons� graph:

� Horizonta� curso� o� mous� middle� Mov� th� cursor.
� A� R� +� -� Chang� th� horizonta� an� vertica� scales.
� G� Toggle� th� drawin� o� � grid.

     Th� �direc� command� i� grap� window� onl� wor� whe� th� graph� �ar� �
valid� �I� �som� paramete� i� change� i� som� windo� tha� �invalidate� �� �
graph� i� remain� unchangeabl� unti� redrawn.

     Eac� grap� ha� � men� o� options� presente� befor� th� plottin� �an� �
als� accessibl� throug� th� grap� menu� wher� sc�le� an� othe� par�meter� �
ca� b� directl� specified.

Observations
�����������-

Graphic� mode�

     Th� graphic� mod� ca� b� specifie� i� th� comman� line� i� th� form:
ASI� <netlis� file� <driver� <mode>
Wher� th� drive� an� mod� number� specif� th� BG� drive� (Turb� Pasca� 7� �
an� th� mod� t� b� use� i� th� plots� Ex� � � produce� � b&� 640x48� mod� �
o� VG� boards� tha� use� littl� memory� Th� defaul� i� 640x480� 1� color� �
mod� (unde� Windows� ther� i� n� reaso� t� chang� it).

Use� interface�

     Th� progra� use� a� interfac� wit� graphi� windows� wher� th� �mous� �
command� al� th� actions:
Th� �lef� �butto� i� use� t� pres� buttons� selec� men� �item� �(eve� �i� �
presse� �wit� �th� mous� ou� o� th� men� area)� selec� �tex� �field� �fo� �
edition� an� mov� an� resiz� windows.
Th� middl� butto� close� � windo� i� presse� o� it� frame� I� als� close� �
menu� withou� selectin� a� item.
Th� righ� butto� open� menus� Ther� ar� menu� i� mos� o� th� window� �(i� �
thei� frames)� an� i� th� graphi� areas.
Th� �interfac� �work� wit� al� th� graphic� board� supporte� b� �th� �BG� �
drivers� 
Windo� movemen� an� openin� ca� b� impossibl� du� t� memor� �limitations� �
Th� progra� beep� whe� thi� happens.
Th� �progra� �ca� b� operate� withou� � mouse� I� � mous� drive� �i� �no� �
found� a� emulate� mous� appears� tha� i� operate� wit� th� curso� �keys� ��Th� �thre� �button� ar� replace� b� th� retur� (left)� es� �(middle� �an� �
spac� �(right� keys� I� Cap� Loc� i� active� th� key� operat� �i� �toggl� �
mod� �(fo� �dragging� fo� exa�ple)� I� Scrol� Loc� i� active� �th� �mous� �
emulatio� i� disabled� s� th� keyboar� ca� b� use� normally.
� tw�-button� mous� ca� als� b� used� Window� an� menu� ca� b� close� �b� �
pressin� th� tw� button� simultaneously.

Pole� an� zeros:

     Th� �defaul� tolerance� an� initia� approxim�tion� i� th� pole� �an� �
zero� parameter� windo� ar� sufficien� fo� mos� usua� cases� bu� the� ca� �
hav� t� b� change� i� som� cases� Th� mos� usua� problem� ar� wit� group� �
o� closel� space� root� tha� th� progra� interpret� a� � multipl� roo� o� �
o� �� �multipl� roo� tha� th� progra� interpret� a� � �grou� �o� �closel� �
space� �roots� Th� paramete� o� "magnitud� tolerance� ca� b� adjuste� �t� �
guid� �th� routin� t� th� correc� result� Smalle� value� �forc� �multipl� �
root� �an� highe� value� forc� distinc� roots� Th� routin� ca� als� �hav� �
problem� o� convergence� I� wil� lowe� th� toleranc� fo� th� root� �unti� �
the� �ca� b� found� Pole� an� zero� ar� compute� i� th� �z^(1/f� �domain� �
wher� �� i� th� numbe� o� phases� � complet� tur� aroun� th� uni� �circl� �
correspond� t� � time� th� switchin� frequency.

Globa� an� Partia� numerators:

     Th� globa� transfe� functio� o� � switche� circui� wit� � phase� �i� �
th� compositio� o� fx� partia� transfe� fun�tions� fro� eac� phas� a� th� �
inpu� �t� eac� phas� a� th� output� Th� denominato� o� al� th� �function� �
i� �th� same� bu� th� numerator� ar� different� Th� progra� compute� �al� �
th� partia� numerator� an� add� the� t� obtai� th� globa� numerato� �(Th� �
samplin� �operatio� divide� th� su� b� � i� th� frequenc� �response� �an� �
th� tim� separatio� o� th� phase� doe� th� sam� i� th� transien� �respo��
se� �Du� �t� this� th� globa� numerato� coe�ficients� a� �listed� �appea� �
multiplie� �b� f)� Zeros� frequenc� respo�ses� sensitivities� �an� �tran�
sien� re�ponse� ca� b� compute� fo� al� th� partia� transfe� functions.
     Usuall� th� desi�ne� digita� transfe� functio� o� � filte� i� on� o� �
th� partia� transfe� functions� Not� tha� i� thes� case� th� gai� appear� �
divide� b� th� numbe� o� phases� a� � partia� transfe� functio� outpu� i� �
zer� a� th� othe� outpu� phases.

Switche�-curren� filters:

     Al� th� biasin� D� curren� source� mus� b� omitte� fro� th� de�cri��
tio� (remember� AL� th� source� ar� AC)� The� ca� als� b� subst�tute� �b� �
resistor� r�presentin� thei� outpu� resistances� bu� i� i� mor� practica� �
t� �se� � convenien� valu� fo� Gd� i� th� mosfe� parameter� �window� �Al� �
th� �capacitance� �an� transconductance� shal� b� �normalize� �t� �value� �
aroun� �� fo� goo� accurac� i� th� analysis� Independen� scalin� �factor� �
ca� b� use� fo� capacitance� an� transconductances� 

Switche�-capacito� filters:

     Finit�-gai� �voltag� amplifier� an� voltag� source� ca� b� use� �d��
rectly� Alternatively� � cu�ren� sourc� o� � tran�conducto� wit� � resi��
to� �i� paralle� wit� it� outpu� i� equivalen� t� � voltag� sourc� �o� �� �
voltag� amplifier� fo� capacitiv� loads� Not� tha� th� idea� �operati�na� ��amplifie� �i� reall� ideal� an� reduce� th� siz� o� th� system� o� �equ��
tion� tha� th� progra� solve� whe� used� Impedanc� normalizatio� shal� b� �
used� wit� capacitor� havin� value� aroun� 1.

Sensitivities:

     I� �prope� �switche�-curren� filters� th� sensitivitie� t� �al� �th� �
capacitance� ar� alway� nul� (o� low� i� parasiti� capacitances� a� �Cgd� �
ar� included)� A� default� th� progra� mark� th� transconductor� t� �hav� �
thei� sensitivitie� computed� becaus� onl� the� ar� significan� i� �idea� �
S� filters.

Sampling:

Thre� samplin� method� ar� available:

-����Sample/hold� �Th� �inpu� an� outpu� ar� considere� �sample� �a� �th� �
�����beginnin� o� eac� phas� an� hel� fo� th� phas� interval� Thi� i� th� �
�����usua� samplin� method� Filter� wil� exhibi� th� usua� sin(x)/� �gai� �
�����distortio� cause� b� th� outpu� sampling.

- ���Impulse� �Th� inpu� i� considere� sample� a� th� beginnin� �o� �eac� �
�����phas� �an� �hel� fo� th� phas� interval� Th� �outpu� �i� �considere� �
�����sample� �b� �a� unitar� impuls� functio� a� th� �beginnin� �o� �eac� �
�����phase� �Filter� �wil� presen� th� idea� digita� �transfe� �function� �
�����Not� tha� th� progra� assume� tha� th� outpu� i� sample� a� al� �th� �
�����phases� �Thi� ca� caus� som� confusio� i� i�puls� samplin� i� �used� �
�����becaus� �eve� i� th� ou�pu� varie� onl� onc� pe� period� th� �outpu� �
�����exhibit� � impulse� pe� p�riod� Thi� cause� th� app�aranc� o� �extr� �
�����zero� �i� �th� �transfe� �functio� (a� �multiple� �o� �th� �sa�plin� �
�����frequency� �i� �al� �th� impulse� ar� equal)� Th� �artifac� �ca� �b� �
�����eliminate� b� zeroin� th� outpu� (wit� switches� a� al� th� �phases� �
�����excep� th� on� wher� th� outpu� changes.

- ���N� �sampling� Th� effect� o� direc� signa� feedthroug� �throug� �th� �
�����circui� ar� considered� I� i� assume� tha� th� tim� constant� i� th� �
�����pat� �ar� �negligible� �s� effect� �o� �inpu� �variation� �propagat� �
�����instantaneously� Frequenc� responses� transien� responses� an� spec�
�����tr� wil� b� compute� considerin� th� signa� feedthrough� Sensitivit� �
�����analysi� i� no� availabl� (yet� i� thi� case�

     Not� tha� othe� samplin� method� ca� b� analyzed� b� usin� �explici� �
samplin� circuit� adde� t� th� inpu� o� output� � sample/hol� circui� ca� �
b� mad� wit� � switch� � capacitor� an� � buffe� circuit.

Outpu� spectrum:

     Fo� usua� filters� th� outpu� spectru� component� appea� a� al� �th� �
frequencie� �i� th� for� n<samplin� frequency>+�-<inpu� �frequency>� �an� �
th� amplitude� agre� wit� th� mai� transfe� functio� amplitude� a� �thos� �
frequencies� �Thi� �i� no� alway� true� becaus� �modulatio� �effect� �ca� �
affec� �th� spectru� components� causin� som� o� the� t� disappea� o� �t� �
assum� differen� values� Th� progra� take� al� thes� effect� int� �cons��
deration.
�Grou� delay:

    Th� �grou� dela� i� compute� b� th� numerica� differentiatio� o� �th� �
phas� curves� an� s� i� mor� precis� i� mor� point� ar� used� (Th� �exac� �
computatio� i� possible� an� wil� b� include� i� � futur� version.� �Spi�
ke� �ma� appea� a� 36� degree� phas� transition� i� no� �enoug� �segment� �
ar� used.

Circuit� wit� cancelle� unstabl� poles:

    I� � transfe� functio� ha� cancelle� pole� ou� o� th� uni� circle� a� �
happen� �wit� balance� structure� withou� commo�-mod� feedback� th� �pr��
gra� �ca� �hav� problem� whe� plottin� th� transien� �response� �Usually� �
numerica� �residue� o� th� analysi� wil� excit� th� unstabl� �poles� �an� �
th� �transien� respons� wil� diverg� afte� som� time� Th� effec� i� �ver� �
dependen� �o� numerica� details� a� th� interpolatio� radiu� �used� �Not� �
tha� thes� circuit� hav� onl� theoretica� interest� Thi� not� i� jus� �t� �
explai� th� apparen� error.

Vali�results�

     I� mus� b� note� tha� th� progra� assume� tha� al� th� element� �ar� �
linea� (smal�-signa� model)� Th� result� ar� vali� fo� larg� signal� onl� �
i� certai� topologi� restri�tion� (switche�-curren� o� switche�-capacito� �
techniques� ar� followed� Also� th� progra� assume� tha� switchin� �tra��
sient� �ar� muc� faste� tha� th� switchin� period� and� o� �course� �tha� �
th� continuou�-tim� circuit� forme� i� an� phas� ar� stable.

Analysi� method�

     Th� analysi� metho� use� b� th� progra� wa� describe� i� th� �paper� �
"Systemati� �noda� analysi� o� switche�-curren� filters,� b� A� C� M� �d� �
Queiroz� �P� �R� M� Pinheiro� an� L� P� Caloba� proceeding� o� �th� �199� �
IEE� ISCAS� Singapore� pp� 180�-1804� Jun� 1991� � mor� detaile� de�crip�
tio� appeare� i� th� pape� "Noda� analysi� o� switche�-curren� �fi�ters,� �
IEE� �Transaction� o� Circuit� an� System�-II� vol� 40� no� �1� � J�nuar� �
1993� �pp� �1�-18� an� � stil� mor� detaile� descriptio� i� i� �th� �boo� �
"Switche�-Currents� A� Analogu� Techniqu� fo� Dig�ta� Technology"� edite� �
b� �C� Toumazou� N� C� Battersby� an� J� B� Hughes� an� publishe� b� �th� �
IE� i� 1993� 

Protecte� mode�

     Th� �ASI� progra� work� i� protecte� mod� o� � P� wit� � �286� �386� �
486� o� Pentiu� processor� wit� extende� memory� I� ca� b� execute� unde� �
Window� �9� �o� �unde� DOS/Window� 3*� bu� i� th� late� �cas� �th� �file� �
RTM.EX� �an� DMPI16BI.OV� mus� b� presen� o� th� DO� path� o� som� �othe� �
DPM� drive� mus� b� installed� � rea� mod� versio� o� th� program� �name� �
ASI�-R� �i� als� include� i� th� distribution� I� doesn'� �requir� �DPMI� �
bu� �canno� us� al� th� availabl� memory� an� s� canno� analyz� bi� �cir�
cuits.

Mai� revisions:
Versio� 1.5� Discoun� o� gai� sensitivitie� implemented.
Versio� �1.4d� �Bug� �i� th� treatmen� o� voltag� �sources� �nois� �inpu� �������withou� �sampling� �an� � possibl� caus� o� cras� i� �th� �transien� �
�����plottin� removed� Single-precisio� versio� o� th� progra� removed.
Versio� 1.4c� Nois� inpu� i� th� transien� respons� added.
Versio� 1.4b� Tim� limi� i� th� transien� respons� eliminated.
Versio� �1.4a� Approximat� grou� dela� computatio� included� an� �listin� �
����o� �th� �gai� �values� �fo� eas� dynami� �rang� �equalizatio� �o� �S� �
����filters.
Versio� �1.4� �Direc� �signa� feedthroug� �considered� �wit� �th� �"None� �
����samplin� �option� �Genera� �rewrittin� o� �interna� �procedures� �Th� �
����transien� response� save� i� th� repor� no� contai� th� value� a� th� �
����tw� extreme� o� eac� phas� interval� an� wil� plo� correctl� i� � �X� �
����plotte� program.
Versio� 1.3a� A� optimizatio� i� numerica� procedure� increase� �signif��
����cantl� th� analysi� speed� �-3� fo� tw�-phase� circuits� an� mor� fo� �
����mor� phases.
Versio� 1.3� Outpu� spectru� calculatio� included� Retainin� o� th� �fre�
����quenc� �respons� grap� (comman� "X"� added� Correcte� potentia� �pro�
����ble� i� th� savin� o� th� sensitivit� selection.
Versio� 1.2d� Correcte� � bu� i� th� numbe� o� phase� i� references.
Versio� 1.2c� Frequenc� response� an� sensitivitie� ar� no� availabl� fo� �
����th� partia� transfe� functions� Th� sensitivit� calculatio� wa� opti�
����m�zed� an� i� no� � o� � time� faster.
Versio� 1.2b� Th� impuls� inpu� no� last� fo� on� entir� period� an� �th� �
����plottin� o� th� inpu� i� th� transien� respons� i� optional.
Versio� 1.2a� Mor� correlate� groups� Mos� recen� version� co�pile� �wit� �
����slightl� change� interface.
Versio� 1.2� Group� o� correlate� element� i� th� statistica� deviation.
Versio� 1.1b� Sensitivitie� ca� b� listed.
Versio� 1.1a� Voltag� source� included.
Versio� �1.1� Memor� allocatio� improve� t� allo� th� analysi� o� �large� �
����circuits� Th� progra� no� accept� circuit� o� u� t� 20� node� an� �1� �
����phases� resultin� i� system� o� u� t� 40� equ�tions.

File� o� th� compresse� distributio� file
�����������������������������������------

ASIZ.EX� � Th� basi� S� analysi� program� protecte� mode.
ASI�-R.EX� � Real-mod� version� Fo� simple� machines.
ASIZ.TX� � Documentatio� fo� th� ASI� program.
EXAMPLES.TX� � Descriptio� o� th� examples.
EDFIL.EX� � Circui� schemati� editor.
RTM.EX� � Use� b� protecte� mod� programs� Mus� b� i� th� path.
DMI16BI.OV� � Necessar� whe� no� unde� Window� 9*� Mus� b� i� th� path.
*.BG� � Turb� Pasca� � graphic� drivers� Mus� b� o� � pat� pointe� b� th� �
DO� environmen� variabl� "TPBGI".
LITT.CH� � Smal� fon� file� Idem.
*.CI� � Schemati� circui� file� fo� EdFil.
*.NE� � Netlis� files.
*.VA� � Valu� lis� file� fo� Edfil.

Specia� versions
----------------

     Version� o� th� ASI� an� EdFi� program� compile� wit� GN� � �(djgpp� �
ar� als� availabl� fro� th� sam� site� Thes� program� accep� large� �ci���cuits� Th� X_EdFi� progra� use� a� interfac� a� th� on� o� th� ASI� �pr��
gram� �an� �th� X_ASI� progra� i� somewha� faste� tha� �th� �norma� �ASI� �
program� I� operate� exactl� i� th� sam� way.
     Version� �o� th� ASI� an� EdFi� program� fo� UNIX� i� �Su� �workst��
tion� �an� �unde� Linu� i� PCs� ar� als� available� The� �operat� �almos� �
exactl� �a� �th� P� versions� usin� th� XVie� Ope�-Loo� �interface� �Thi� �
manua� �i� als� vali� fo� th� UNI� ASI� version� wit� sligh� �change� �i� �
th� interfac� operation� Th� progra� ha� � o�-lin� hel� syste� tha� �co��
tain� mos� o� th� information� i� thi� text.

Distributio� an� use
�������������������-

     Th� ASI� progra� ca� b� distribute� freel� fo� educati�na� purp�ses� �
a� lon� a� n� charg� i� made� i� i� no� change� i� an� way� an� referenc� �
t� it� us� i� mad� i� an� wor� don� wit� it� help.
     Fo� commercia� utilization� � registratio� fe� i� required� �Co�tac� �
th� author� 
     Th� �autho� �believe� tha� th� progra� work� correctly� �bu� �canno� �
assum� �responsibilit� �fo� losse� cause� b� flaw� i� �th� �progra� �tha� �
escape� hi� attention.
     Th� �mos� curren� versio� o� th� progra� an� auxiliar� file� ca� �b� �
obtaine� b� "anonymou� ftp� i� th� Internet� a� th� director� �"pub/acmq� �
a� th� sit� "coe.ufrj.br"� o� throug� th� Worl� Wid� Web� at:
http://www.coe.ufrj.br/~acmq/ASIZ.html.
     User� �ar� encourage� t� sen� � lette� o� �-mai� t� th� autho� �tel�
lin� ho� th� progra� i� bein� used.
     Comments� �suggestion� an� question� abou� th� �progra� �utilizatio� �
shal� b� sen� to:

Dr� Antoni� Carlo� M� d� Queiroz
Program� d� Engenhari� Eletrica
COPP� � Universidad� Federa� d� Ri� d� Janeiro
C� 68504
2194�-970� Ri� d� Janeiro� RJ� Brazil

or� vi� �-mail� t� acmq@coe.ufrj.br

26/07/1998
