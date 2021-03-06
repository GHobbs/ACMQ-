Example� file� fo� th� ASI� program:

   Th� �file� ar� distribute� a� th� EdFi� description� �(.CIR)� �
th� ASI� inpu� file� (.NET� an� valu� list� (.VAL).

LP5SC� � 5t� orde� bilinea� ellipti� S� filte� wit� �� �phases� �
Outpu� �node:21� �� circui� use� a� exampl� �i� �variou� �paper� �
abou� �S� circui� analysis� From� J� A� Nosse� an� G� C� �Temes� �
"Switche�-Capacito� �filte� desig� usin� bilinea� elemen� �mode�
ling"� IEE� Trans� Circ� Syst.� pp� 48�-491� Jun� 1980.

LP6BS� �� 6t� orde� bilinea� Chebysche� S� filte� i� cascad� �o� �
biquads� From� J� B� Hughes� I� C� Macbeth� an� D� M� �Pattullo� �
"Switche� �curren� filters"� IE� Proceedings� Vol� 137� �Pt� �G� �
No� 2� pp� 15�-162� Apri� 1990.

LP5BS� �� 5t� orde� bilinea� Chebyshe� S� filte� usin� �bilinea� �
integrators� �Valu� list� CH5.VAL� From� I� Son� an� G� �W� �R��
berts� "� 5t� orde� bilinea� switche�-curren� Chebyshe� filter"� �
Proc� �199� �IEE� ISCAS� Chicago� IL� USA� �pp� �109�-1100� �Ma� �
1993.

LP5E1S� �� 5t� orde� bilinea� lo�-pas� filte� usin� �firs�-gen��
ratio� Eule� integrators� From� G� Robert� an� A� Sedra� Chapte� �
� �o� �th� boo� "Switche�-currents� a� �analogu� �techniqu� �fo� �
digita� technology"� Edite� b� C� Toumazou� J� B� Hughe� an� �N� �
C� �Battersby� IEE� London� 1993� Th� formula� fo� th� �element� �
wer� �take� fro� th� followin� example� Valu� list� �CH5.VA� �o� �
EL5.VAL.

LP5E2S� � 5t� orde� bilinea� lo�-pas� filte� usin� �secon�-gen��
ratio� Eule� integrators� From� A� C� M� d� Queiro� an� P� R� M� �
Pinheiro� "Bilinea� switche�-curren� ladde� filter� usin� �Eule� �
integrators"� IEE� Transaction� o� Circuit� an� System�-I� �Vol� �
43� �No� �1� �Januar� 1996� pp� 6�-70� Valu� �list� �CH5.VA� �o� �
EL5.VAL.

BP6BS� �� �6t� orde� bilinea� ellipti� �ban�-pas� �filte� �usin� �
bilinea� �integrators� �Th� valu� lis� i� �th� �fil� �BP610.VAL� �
From� A� C� M� d� Queiro� an� P� M� Pinheiro� �"Switche�-curren� �
ladde� �ban�-pas� filters"� Proc� 199� IEE� ISCAS� �London� �UK� �
pp� 30�-312� Ma� 1994.

BP6ES� �� �6t� orde� bilinea� ellipti� �ban�-pas� �filte� �usin� �
Eule� �integrators� �Valu� list� BP610.VAL� From� A� �C� �M� �d� �
Queiro� �an� P� M� Pinheiro� "Switche�-curren� ladde� �ban�-pas� �
filters"� �Proc� 199� IEE� ISCAS� London� UK� pp� �30�-312� �Ma� �
1994.

   Eigh� �differen� �basi� structure� fo� S� �lo�-pas� �bilinea� �
filters� al� o� 5t� order� an� usin� th� valu� list� CH5.VA� �o� �
EL5.VAL� fo� Chebyshe� o� Caue� (elliptic� filters:

BILIN1� �-Bilinea� filte� usin� firs�-generatio� bilinea� �inte�
grators.�
BILIN2� -Bilinea� filte� usin� secon�-generatio� bilinea� �inte�
grators.

EULER1� �-Bilinea� filte� usin� firs�-generatio� Eule� �integra�
tors.

EULER2� -Bilinea� filte� usin� secon�-generatio� Eule� �integra�
tors.

CSBILIN�-Bilinea� �filte� �usin� �componen�-simulatio� �bilinea� �
integrator� i� direc� form.

CSBILIN�-Bilinea� �filte� �usin� �componen�-simulatio� �bilinea� �
integrator� i� modulate� form.

CSEULER�-Bilinea� filte� usin� componen�-simulatio� Eule� �inte�
grator� i� direc� form.

CSEULER�-Bilinea� filte� usin� componen�-simulatio� Eule� �inte�
grator� i� modulate� form.

   Fo� �componen�-simulatio� filters� see� J� Schechtman� A� �C� �
M� �d� Queiroz� an� L� P� Caloba� "Switche�-curren� �filter� �b� �
componen� �simulation"� �Analo� Integrate� Circuit� �an� �Signa� �
Processing� jul� 1997� pp� 30�-309.

   Mos� o� th� example� includ� formula� fo� th� elemen� �value� �
i� th� .CI� file� Th� EdFi� progra� evaluate� thes� formula� �t� �
obtai� th� fina� elemen� value� fo� th� netlis� file� T� �desig� �
� differen� filter� i� i� enoug� t� chang� th� rat� th� �netlis� �
file� Th� valu� list� include� ar� elemen� value� fo� passiv� L� �
doubl� �terminate� �ladde� filters� wit� �appropriat� �frequenc� �
predistortio� �fo� �� bilinea� filter� no�-malize� �fo� �unitar� �
terminations.
   Th� example� o� bilinea� Chebyshe� filter� illustrat� �poss��
bl� problem� i� findin� multipl� transmissio� zeros� Chang� �th� �
magnitud� toleranc� i� th� pole� an� zero� parameter� windo� �t� �
� �highe� valu� t� comput� correctl� th� multipl� zero� �a� �th� �
Nyquis� frequenc� i� thes� filters.
   Th� outpu� nod� fo� al� th� S� filter� i� 1� I� al� th� exa��
ple� �th� �correc� transfe� functio� i� �obtaine� �wit� �impuls� �
sampling.

ACM� -27/7/199� 