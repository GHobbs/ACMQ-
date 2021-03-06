..Imprimir com WordStar 4.0
.LS1
.RM64
.PL66
                     � Program� SENSI�

Documenta��� v�lid� par� � vers�� 4.9a.

� � Introdu��o

   � program� SENS� analis� circuito� lineare� � invaria�te� �n� �
tempo� utilizand� um� form� compact� d� an�lis� noda� �modifica�
da� � � m�tod� d� red� adjunt� par� � an�lis� d� sensibilidades� �
D� an�lis� pode� se� obtidos:

� M�dul� fas� � atras� d� grup� d� um� fun��� d� transf�r�ncia.
- Sensibilidade�.
� Desvio� estat�stico� d� m�dul� � fase.�
- Sensibilidad� de p�lo� � zero�.
� Desvio� estat�stico� d� p�lo� � zeros.�
� An�lis� d� faix� din�mic�.

� � Par�metro� d� entrad� par� � programa

   � program� l�� � descri��� d� circuit� � analisa� e� u� arqui�
v� d� texto� organizad� n� forma� 

� Primeir� linha� n�mer� d� n�s.

- Linha� seguintes� descri��� (ne�-list)� u� element� �po� �
��linha:
� Resisto� co� resist�nci� R:
  R<nome� <n�1� <n�2� <�>
� Induto� co� indut�nci� L:
  L<nome� <n�1� <n�2� <L>
� Capacito� co� capacit�nci� C:
  C<nome� <n�1� <n�2� <�>
� Font� d� tens�o controlad� � tens�o (VCVS)� co� ganh� Av:
  E<nome� <n�Vo+� <n�Vo-� <n�Vi+� <n��i-� <Av>
� Font� d� corrent� controlad� � corrent� (CCCS)� co� ganh� Ai:
  F<nome� <n�Io+� <n��o-� <n�Ii+� <n�Ii-� <Ai>
- Font� d� corrent� controlad� � tens�� (VCCS)� co� �tran�cond��
��t�nci� Gm:
  G<nome� <n�Io+� <n��o-� <n�Vi+� <n��i-� <G�>
� Font� ��d� �tens�� �controlad� �� ��corrent� ��(CCVS)� ��co� �
transresist��cia Rm:
  H<nome� <n�Vo+� <n�Vo-� <n�Ii+� <n�Ii-� <R�>
� Girador� co� resist�nci� d� gira��� Rg:
  Y<nome� <n�1+� <n��-� <n�2+� <n��-� <R�>
- Amplificado� operaciona� ideal, model� nullato�-norator:
  O<nome� <n� entr� 1� <n� entr� 2� <n� sa�da>
- Amplificado� operacional� co� ganh� GB/� (G� e� rad/s� � �
��resist�nci� d� sa�d� Ro:
  A<nome� <n��-� <n�+� <n�sa�da� <G¾ <R�>
� Transisto� bipolar� model� h�brid� � simplificado:
  Q<nome>� <n�� c� <n�� b� <n�� e� <hfe� <hie>
� Transisto� MOS:
  M<nome>� <n�� d� <n�� g� <n�� s� <Gm� <Gds>
� Font� d� tens�o co� resisto� e� s�ri� Rs:�  Z<nome� <n�-� <n�+� <Rs� <V>
� Font� d� tens�o:
  V<nome� <n�+� <n�-� <V>
� Font� d� corrente:
  I<nome� <n�+� <n�-� <I>

   Toda� �a� �unidade� e� Ohms� Mhos� Farad� � Henrys� � �n�� �d� �
terr� �� � n�� 0� O� nome� deve� possui� at�� � caract�res� �incl��
ind� � inicial� O� componente� pode� esta� e� qualque� orde� � � �
numera��� �do� �n�� tambem� ma� dev� se� cont�nua� �se� �n�mero� �
faltando.

   � �descri��� �pod� se� gerad� pel� program� edito� �EdFil� �� �
parti� d� diagr�m� esquem�tic� d� circuito.

3 � Respost� e� freq��ncia

   � program� consider� a� entrada� d� circuit� (a� fonte� �"Z"� �
com� fonte� d� tens�� unit�rias� Todo� o� c�lculo� refere�-s� �� �
tens�e� no� n�� d� circuito� qu� equivale� � fun��e� d� transfe�
r�nci� da� entrada� at�� a�.

   � gr�fic� d� respost� e� freq��nci� pod� se� pedid� imediat��
ment� �ap�� � leitur� d� arquiv� d� dados� usand�-s� a� �escala� �
"default"� adequada� par� circuito� normal�zado� e� �freq��ncia� �
Outra� �escala� �pode� se� determinada� ante� �d� �plotage� �do� �
gr�ficos� o� ajustada� iterativame�t� durant� � plotagem� �Pode� �
se� �plotadas� e� u� �nic� gr�fico� curva� d� m�dul� � �fas� �d� �
fun��� d� transfer��cia� atras� d� grup� � desvio� �estat�stico� �
d� �m�dul� � d� fas� d� fun��� d� �transfer�ncia� �Inicialmente� �
s�� plot�da� apena� curva� d� m�dulo� fas� � desvi� �estat�stic� �
d� m�dulo� U� curso� pod� se� acionad� � qualque� instant� �par� �
leitur� d� valore� n� gr�fico.

   V�ria� �tecla� possue� fun��o� a� fina� � durant� � �plotage� �
d� gr�fico:

� Seta� horizontais� Liga� � movimenta� � cursor.
� Ctrl-Seta� horizontais� Idem, co� pass� maior.
� Tab� Mud� � curv� selecionad� pel� cursor.
- Del� �Remov� d� gr�fic� � curv� selecionad� (� selecion� � �d� �
��m�dulo).
� Ins� Recoloc� n� gr�fic� � curv� selecionada.
- Seta� �verticais� �Desloca� verticalment� (1/� tela� �� �curv� �
��selecionada.
- � �� �-� Ampli� (x2� � redu� (/2� � limit� superio� �d� �curv�   �
��selecionada.
- A� Ampli� � limit� superio� d� freq��ncia� colocand� n� gr�f��
��c� �� �qu� apareceri� s� � largur� d� �re� d� �plot�ge� �foss� �
��dobrada� 
- R� Redu� � limit� superio� d� freq��ncia� colocand� n� gr�fic� �
��� �qu� �apareceri� s� � largur� d� �re� d� �plot�ge� �foss� �� �
��metad� d� qu� �.
- � � >� Move� a� curva� e� freq��nci� d� 1/� tela.
� Return� Redesenh� � gr�fico� se� � cursor.�� Espa�o� Mostr� � cursor.
- E� Liga/deslig� � tra�ad� da� curva� d� m�dul� � fas� co� seu� �
��desvio� estat�stico� somado� � subtra�dos.
- G� Liga/deslig� � tra�ad� d� grad� (a� escala� d� grad� sempr� �
��s�� a� d� curv� selecionada� mesm� qu� el� estej� invis�vel).
� F� Liga/deslig� � tra�ad� d� curva� d� fase.
� T� Liga/deslig� � tra�ad� d� curva� d� atras� d� grupo.
- Q� Mud� � posi��� d� quadr� d� medid� d� cursor.
� Esc� Encerr� � plotagem� retornand� a� men� principal.

   O� �valore� calculado� s�� sempr� qu� �poss�ve� �aprove�tado� �
quand� a� escala� s�� mudadas� � curso� tamb�� n�� mud� d� �fr��
q��ncia� �s� poss�vel� O� gr�fico� soment� ser�� tota�ment� �r��
calculado� �s� � n�� d� sa�d� d� circuit� fo� mudado� o� �se� �n� �
men� �d� escalas� � n�mer� d� segmento� o� � escal� d� �freq����
cia� �fo� �mudada� � n�mer� inicia� d� segmento� �(ponto�-1� �n� �
gr�fic� �depend� d� mem�ri� disp�n�vel� � �� normalment� �d� �78� �
Havend� �mem�ria� �pod� se� aumentad� at�� u� m�xim� �d� �256� �� �
program� �sempr� �us� � m�xim� valo� entr� � �especificad� �� �� �
poss�vel� 

   A� �resposta� e� freq��nci� par� v�rio� circuito� �dif�rente� �
pode� se� comparada� pel� program� CPSENSI� � pa�ti� da� tabela� �
gerada� pel� SENSI.

4 � Listagen� d� sensibilidades

   A� sensibilidade� S(T,x)=(x/T)*(dT/dx� d� fu���� d� �transf��
r�nci� T(s� e� rela��� � todo� o� par�metro� � pode� se� �obser�
vada� �ap�� � plotage� d� u� gr�fico� � part� rea� pod� se� �in�
te�pretad� �com� �send� � sensibilid�d� d� m�dul� d� �fun��� �d� �
tran�fer�nci� �e� �Neper� � � part� imagin�ri� com� send� �� �d� �
fas� e� radianos� �� li�tad� tamb�� � valo� d� S(T,s)� � sensibi�
lidad� �d� fun��� d� transf�r�nci� e� rela��� � "s"� � �listage� �
s� �inici� pel� freq��nci� d� cursor� � pod� se� mudad� �co� �a� �
seta� horizontais� � mudan�� s� reflet� n� curso� d� gr�fico� �� �
curso� vertica� permit� qu� a� sens�bilidade� e� rela��� � todo� �
o� componente� seja� list�das� cas� n�� caiba� toda� n� tela�  

   O� par�metro� qu� comp�e� o� elemento� co� mai� d� u� par�m��
tr� (� � Q� s�� identificado� nest� listage� � na� demai� por:

� A<nome� � G� d� u� amp� op.
� a<nome� � R� d� u� amp� op.
� Q<nome� � hf� d� u� transisto� bipolar
� q<nome� � hi� d� u� transisto� bipolar
� M<nome� � G� d� u� transisto� MOS
� m<nome� � Rd� d� umtransisto� MOS

5 � �n�lis� da faix� din�mica

   Durant� �o� c�lculo� par� � tra�ad� do� gr�fico� d� �respost� �
e� freq��ncia� o� m�ximo� � m�nimo� valore� d� m�dul� d� �fun��� �
d� transfer�nci� par� cad� n�� d� red� s�� computados� O� valore� �
s�� acumulado� enquant� o� gr�fico� n�� fore� totalment� �reca���culados� �A� seta� verticai� permite� � listage� d� n�� qu� �n�� �
caiba� n� tela.

6 � Desvio� estat�sticos
   
   O� desvio� estat�stico� representa� � err� qu� s� dev� �esp��
ra� construind� � circuit� co� componente� co� a� variabilidade� �
o� �toler��cia� dadas� supond� n�� correl�cionado� o� �erro� �n� �
valo� �do� �par�metros� Po� exemplo� s� X� �do� �par�metro� �do� �
componente� usado� possu�re� meno� qu� � vari�bilidad� dad� (co� �
distribui��� �no�mal)� �X� do� circuito� qu� �fore� �construido� �
estar�� dentr� do� lim�te� dado� pelo� desvios� 

   A� variabilidade� par� todo� o� par�metro� d� circuit� �pode� �
se� especificadas� par� todo� o� elemento� o� individualmente� � �
valo� �"default� ��� d� 0.0� (o� 5� d� �toler�ncia)� �Altera� �a� �
variabilidade� �fa� �co� qu� o� desvio� �seja� �recalculado� �(� �
c�lcul� �� r�pido)� Est� facilidad� permit� qu� � efeit� d� �cad� �
par�metr� �n� comportament� d� ci�cuit� sej� estudado� � �qu� �� �
toler�nci� necess�ri� par� cad� par�metr� sej� f�cilment� deter�
minada� Observ�-s� qu� � err� e� d� causad� po� um� variabilida�
d� isolad� �� fun��� linea� d� variab�lidade� Po� exemplo� s� co� �
5� �d� �toler�nci� par� todo� o� componente� � �err� �m�xim� �d� �
ganh� �e� �um� dad� freq��nci� fo� d� � dB� �s� �a� �toler�ncia� �
fore� �reduzida� par� 1%� � err� cair�� par� � dB� �Inicialmente� �
a� �variabilidade� �da� fonte� independente� s�� nulas� �j�� �qu� �
usualment� n�� s�� considerada� e� an�lise� d� sensibilidade� S� �
necess�rio� pode� se� alterada� individualmente� � mudan�� �glo�
ba� d� variabilidade� n�� a� afeta.

7 � Sensibilidade� co� desconto

   � op��� d� desconta� a� sensibilidade� d� valo� e� cert� fr��
q��nci� �pod� se� usad� par� elimina� � part� invariant� �co� �� �
freq��nci� da� sensibilidades� aprese�tend� apena� o� erro� �qu� �
distorce� �� form� da� curva� d� respost� e� freq��ncia� �E� �u� �
filtr� derivad� d� um� re�liza��� passiv� L� duplament� termina�
d� co� m�xim� tran�fer�nci� d� pot�ncia� est� freq��nci� �� �ond� �
� ganh� �� m�xim� (s� � m�xim� ocorre� e� CC� us�-s� um� freq��n�
ci� baixa� n�� nula)� Par� filtro� d� outro� tipo� pod� n�� �se� �
rigorosament� �corret� usa� est� op��o� poi� �a� �sens�bilidade� �
pode� �n�� possui� um� part� invariant� co� � freq��ncia� �o� �� �
valo� �constant� pod� n�� acontece� par� todo� o� par�metro� �n� �
mesm� freq��ncia� Co� � us� d� op��o� � part� rea� da� �sensibi�
lidade� �listada� ��� aprese�tad� co� � descont� fe�to� �Um� �ve� �
feit� �u� �desco�to� el� permanec� ativ� at�� qu� �� �op��� �sej� �
desligad� o� qu� � n�� d� sa�d� sej� mudado� Not�-s� qu� o� erro� �
calc�lado� �dest� �form� s�� s�� v�lido� e� circuito� �e� �qu� �� �
valo� absolut� d� ganh� n�� sej� importante.

8 � Sensibilidade� normalizada� pel� inclina��o
     
   � �op��� �d� normaliza� a� sensibilidade� pel� �inclina��� �� �
�ti� �par� elimina� a� falsa� alta� sensibilidade� �qu� �parece� �
ocorre� �sempr� qu� m�dul� o� fas� varia� rapid�mente� com� �na� ��vizinha�ca� d� zero� d� transmiss�o� O� novo� desvio� pode� �se� �
inte�pretado� �com� �� dist�nci� perpendicula� entr� �a� �curva� �
ideai� � a� reai� d� m�dul� � fase� s� o� diagrama� fore� plot��
do� �e� m�dul� e� d� � 20log(w� ("freq��nci� e� dB")� � fas� �e� �
grau� � (180/�)ln(w� ("freq��nci� e� graus").

9 � Sensibilidade� do� p�lo� � zeros

   Par� an�lise� d� sensibilidad� d� p�lo� � zeros� � necess�ri� �
u� �arquiv� d� text� contend� o� p�lo� o� o� zeros� �n� �format� �
gerad� �pel� �program� IFF� (1a� linha� n�mer� �d� �freq��ncias� �
Linha� segui�tes� <real� <imag.� d� cad� p�l� o� zero)� A� �se��
sibilidade� calc�lada� par� p�lo� � zero� s�� n�� �normalizadas� �
S'(s,x)=ds/(dx/x)� �O� �desvio� estat�stico� da� parte� �rea� �� �
imagin�ri� �calcul�do� define� u� ret�ngul� ond� � p�l� o� �zer� �
dever�� estar� centrad� n� posi��� ideal.

   Com� �u� �refinament� dest� medida� s�� �aind� �calculado� �� �
dire��� �angula� �ond� � varia��� maio� �� esperad� �� �o� �raio� �
maio� � meno� d� um� elips� dentr� d� qua� � p�l� o� zer� dever�� �
estar� O� ret�ngulo� � elipse� pode� se� pl�tado� juntament� co� �
o� p�lo� o� zero� e� u� gr�fico� 

   Nest� gr�fico� a� seta� d� curso� movimenta� o� lim�tes� � �� �
� muda� � amplia��� � Ta� mud� � freq��nci� s�lecionada� Es� e��
cerr� � plotagem.

   � c�lcul� d� sensibilidad� do� p�lo� s�� funcion� corr�tament� �
s� �� imped��ci� d� entrad� d� rede� com� vist� po� u� cort� �n� �
ram� �ond� estive� � element� usad� com� obse�vador� �qu� �deve� �
se� do� tipo� R� L� � o� Z� possui� com� zero� o� p�lo� �desej��
dos� �send� nul� nesta� freq��ncias� O� seja� a� �se�sibilidade� �
do� �p�lo� d� red� u� rela��� a� par�metr� obse�vado� usad� �n�� �
pode� se� nulas� � program� verific� ist� � n�� calcul� a� �se��
sibilid�de� d� p�lo� n�� clarament� observ��veis� Not�-s� qu� �e� �
algun� �circuito� �n�� exist� u� element� qu� observ� �todo� �o� �
p�los� �Nest� �caso� pode� ocorre� problema� num�ricos� �poi� �� �
imped�nci� �vist� po� u� cort� n� ram� observado� �poss�� �zero� �
sobr� �o� p�lo� n�� observ�veis� � � sistem� d� �equa��e� �usad� �
pel� pr�gram� torn�-s� singular� Um� redu��� n� toler�nci� �par� �
admit�ncia� pod� faze� co� qu� � program� fa�� � c�lculo� �apr��
ximadamente� �assi� mesmo� n�� parand� po� �"determinant� �muit� �
pequeno".

   N� c�lcul� d� sensibilidad� do� zero� �� tamb�� feit� � �ver��
fica��� d� corre��� do� zeros� 

   A� �listagen� d� sensibilidade� d� p�lo� � zero� te� � �mesm� �
format� �da� listagen� d� sensibilidades� � obedece� ao� �mesmo� �
comandos� �curso� �horizonta� par� muda� �freq��ncia� �� �curso� �
vertica� par� muda� par�metros.

   � par�metr� d� toler��ci� par� imped�ncia� � tens�e� pod� se� �
aumentad� par� permiti� c�lc�lo� aprox�mado� quand� o� p�lo� s�� �
pouc� �observ�vei� o� n�� muit� prec�so� o� o� zero� �n�� �muit� ��precisos� �� outr� par�metr� d� toler�ncia� par� �admit�ncia� �� �
freq��ncias� ��� usad� par� detec��� d� sistema� d� equa��e� �n��
dai� �singulare� �(dete�minant� muit� pequeno� �� �par� �impedi� �
c�lcul� d� sensib�lidad� d� zero� n� origem.

   � �program� IFF� dev� se� usad� par� � obten��� �precis� �do� �
p�lo� � zeros� O� c�lculo� deve� se� feito� co� � op��� d� apre�
senta� resultado� desnormalizado� �m freq���cia.

   O� desvio� estat�stico� do� p�lo� � zero� par� diverso� �cir�
cuito� �diferente� pode� se� comparado� pel� program� �CPSPZ� �� �
parti� da� tabela� gerada� pel� SENSI.

1� � Arquiv� d� sa�da

   � �program� �pod� cria� u� arquiv� contend� tud� �� �qu� �fo� �
calc�lad� �usand�-s� �� op��� "abri� arquiv� d� sa�da� �d� �men� �
princ�pal� �� program� pergunt� e� ocasi�e� �apr�priada� �(op��� �
"Salvar"� tecl� "s"� no� menus� s� � resu�tad� do� ultimo� �c�l�
culo� �o� altera��e� dev� se� a�quiv�do� V�rio� �arquivo� �pode� �
se� criados� � arquiv� atua� �� autom�ticament� fechad� quand� ��� �
pedid� � an�lis� d� outr� red� o� quand� � program� �� encerrado.

11 � Observa��es

   Amplificadore� �operacionai� ideai� deve� se� �usado� �sempr� �
qu� possivel� poi� ist� aceler� � process� d� sol���� d� circu��
t� � redu� � err� num�rico.

   Pode� ocorre� problema� num�rico� s� o� nivei� d� �i�ped�nci� �
d� circuit� fore� muit� elevado� o� muit� baixos� �� �recomendad� �
qu� toda� a� an��lise� seja� feita� e� ci�cuito� normalizado� �e� �
freq��nci� � imped�ncia� Principa�ment� e� imped�ncia.

   Nenhum� �admit�nci� �o� transadmit�nci� �pod� �se� �infin�ta� �
impl�cand� qu� resist�ncia� � indut�ncia� n�� pode� se� nulas� � �
qu� circuito� contend� indutore� o� amplif�cadore� �operacionai� �
reai� n�� pode� se� analisada� e� CC� 

   E� escal� logar�tmic� n�� �� permitid� � an�lis� e� freq���ci� �
meno� �o� igua� � zero� A� escala� verticai� � �horizontai� �n�� �
pode� se� invertida� s� � grad� estive� send� usada.

   Quand� � resolu��� usad� no� gr�fico� n�� �� grande� �detalhe� �
importante� �pode� se� perdidos� U� cas� cr�tic� �� � d� �m�ximo� �
do� �desvio� d� m�dul� normalizado� pel� i�clina��o� qu� e� �a��
gun� filtro� form� pico� agudos� � valo� corret� do� pico� �pod� �
se� obtid� aumentand�-s� � n�mer� d� segmentos� expandi�d�-s� �� �
escal� horizontal� o� t�mand�-s� � valo� d� desvi� n�� �normali�
zad� �n� freq��nci� d� pico� qu� coincid� co� � normal�zado� �j�� �
qu� a�� � curv� d� m��dul� �� horizontal.

   Na� tela� gr�ficas� tocand�-s� a� tecla� "H� � "V� s�� �aci��
nada� �rotina� �d� impress�� d� tela� e� format� �hor�zonta� �o� �
vertical� e� impressor� tip� EPSON� A� rotina� n�� emite� �avis� ��algum� � soment� funciona� co� � plac� CGA� � impress�� pod� se� �
interrompid� tocand�-s� qualque� tecla.

   � �parti� d� vers�� 4.4� s�� calculada� a� sensibilid�de� �e� �
rela��� �� imped�nci� d� sa�d� do� amplificadores� ante� �ignora�
da� Fo� introduzid� tamb�� � model� par� transistor.

   N� vers�� 4.5� � format� da� tabela� � da� listagen� n� �tel� �
fo� �mudado� Um� nov� vers�� do� programa� CPSENS� � CPSP� �tev� �
qu� se� escrita� Fo� introduzid� � transisto� MOS� 

   N� vers�� 4.6� pequena� mudan�a� fora� feita� n� format� �da� �
tabela� � no� comando� do� gr�ficos.

   N� �vers�� 4.7� � font� "F� fo� mudad� par� "Z"� � a� �letra� �
iniciai� �do� segundo� par�metro� do� elemento� co� mai� �d� �u� �
fora� mudada� par� vers�e� min�sculas� com� prepara��� par� �um� �
futur� vers�� usand� an�lis� noda� modificada.

   N� vers�� 4.8� � an�lis� noda� modificad� compact� fo� imple�
mentada� �co� toda� a� quatr� fonte� controlada� � a� fonte� �d� �
tens�� � corrente.

   � �vers�� 4.� inclu� um� vers�� d� mod� protegid� �(sens�-p)� �
qu� admit� gr�fico� d� maio� resolu��o� � arquiv� d� sa�d� pass� �
� inclui� a� curva� d� ganh� +�� err� � fas� +�� erro� � �vers�� �
4.9� �� u� pouc� mai� r�pid� devid� � um� otimiza��� n� algor�tm� �
d� fatora��� LU.

   � �program� �SENS� �pod� �se� �distribu�d� �livrement� ��par� �
prop�sito� �educacionai� �� �acad�micos� �desd� �qu� �n�� ��sej� �
alterado� �� �qu� refer�nci� � se� us� sej� feit� �e� �trabalho� �
realizado� co� su� ajuda.

   Coment�rio� �o� d�vida� sobr� � utiliza��� d� program� �podem �
se� remetido� para:

Dr� Ant�ni� Carlo� Moreir�� d� Queiro�
Program� d� Engenhari� El�trica� COPPE 
Universidad� Federa� d� Ri� d� Janeiro
C� 68504
21945-97� Ri� d� Janeiro� RJ� Brasil

Ou� vi� e-mail� para: acmq@coe.ufrj.br

ACMQ� 13/01/95