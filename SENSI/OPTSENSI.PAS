PROGRAM OptSensi;
{******************************************************************************
 * OTIMIZACAO POR ANALISE DE SENSIBILIDADES                                   *
 * Antìnio Carlos MoreirÑo de Queiroz - COPPE/UFRJ 1993                       *
 * V. 1.0  de 05/07/93: AcrÇscimos sobre o SENSI                              *
 ******************************************************************************}
{$M 60000 0 655360}
{
Funcionando para todos os elementos exceto Z, A e Q.
Otimizacao:
Em redes duplamente terminadas, as sensibilidades nulas na MTP exigem
que analises nos maximos sejam feitas em frequencias deslocadas, ou que
as equacoes sejam ignoradas.
Em qualquer rede, se todos os elementos reativos forem variaveis, e apenas
eles, e o numero de restricoes for igual ao de variaveis, o sistema tambem
fica singular nos extremos pois as linhas da matriz A somam zero.
Mesmo assim, o sistema fica singular se mais equacoes do que a ordem de
complexidade do circuito forem usadas, em redes duplamente terminadas.
}

{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}

USES Dos,Crt,Printer,Graph,Tela;

{$I seta.p}

CONST
  versao='1.0 de 05/07/93';
  MaxEq=40;
  MaxVar=60;
  MaxEl=150;
  Ln10=2.30258509299405;
  maxsegm=256;
  espera=120;
  tn=5;
  tolz:REAL=1e-5;
  toly:REAL=1e-7;
  condensar:BOOLEAN=TRUE;
  uf:ARRAY[BOOLEAN] of STRING[5]=('rad/s','Hz');
  cm:INTEGER=14;
  dc:INTEGER=9;
  {Otimizacao}
  otimizar:BOOLEAN=FALSE;
  restricoes:INTEGER=0;
  incognitas:INTEGER=0;
  MaxEsp=40;
  fixo=0;
  movel=-1;
  maxdelta:REAL=0.2;
  fator:REAL=0.75;
  usar_fator:BOOLEAN=FALSE;
  tolf:REAL=1e-5;
  told:REAL=1e-10;
  tols:REAL=1e-4;
  refinar:BOOLEAN=TRUE;
  apenas_localizar:BOOLEAN=FALSE;
  flat_loss:REAL=0;
  evitar_extremos:BOOLEAN=FALSE;

TYPE
  sensibilidades=ARRAY[1..MaxEl] of REAL;
  medida=(frq,mdl,fas,tg,dm,df);
  nulo=STRING[2];
  apontadores=Array[0..MaxVar] of BYTE;
  umponto=
    RECORD
      analisado: BOOLEAN;
      S1,S2:sensibilidades;
      CASE BOOLEAN of
        TRUE: (V: ARRAY[medida] of REAL);
        FALSE: (re,im,vre,vim,ang,rma,rme:REAL; calculavel:BOOLEAN);
    END;
CONST
  prm: ARRAY[frq..df] OF STRING[4]=
    ('Freq','Modl','Fase','AtGr','VeMo','VeFa');
  min: ARRAY[frq..df] OF REAL=(0.2,-60,-180,0,0,0);
  max: ARRAY[frq..df] OF REAL=(5,10,180,15,7,15);
  unid:ARRAY[frq..df] OF STRING[5]=('rad/s','dB','gr','s','dB','gr');
  cor: ARRAY[1..6] OF BYTE=(3,2,3,1,1,2);
  forte=1; media=4; fraca=6;
  plotar: ARRAY[mdl..df] OF BOOLEAN=(TRUE,FALSE,FALSE,FALSE,FALSE);
  linear:   BOOLEAN=FALSE;
  normincl: BOOLEAN=FALSE;
  descontar:BOOLEAN=FALSE;
  hertz:    BOOLEAN=FALSE;
  superpor: BOOLEAN=FALSE;
  grade:    BOOLEAN=TRUE;
  retangulos:BOOLEAN=FALSE;
  elipses:BOOLEAN=TRUE;

VAR
  Espec:ARRAY[1..MaxEsp] OF
    RECORD
      tipo,erro:CHAR;
      pular:INTEGER;
      wk,ganho,ek:REAL
    END;
  Elemento: ARRAY[1..MaxEl] OF             {DescriáÑo do circuito}
    RECORD
      nome: STRING[tn];
      omodo:INTEGER;
      valor: REAL;
      n1,n2,n3,n4,nx: BYTE;
    END;
  M1,M2: ARRAY[0..MaxEq,0..MaxEq] OF REAL; {Matriz de admitÉncia dos n¢s}
  E1,E2,A1,A2: ARRAY[0..MaxEq] OF REAL;    {ExcitaáÑo normal e adjunta}
  DP,Y1,Y2: ARRAY[1..MaxEl] OF REAL;       {Variabilidade, admitÉncia}
  C,L,L0: apontadores;                     {Apontadores}
  Maximo,Minimo: ARRAY[1..MaxVar] OF REAL; {Faixa dinÉmica}
  Desconto: sensibilidades;                {Sensibilidades a descontar}
  ponto: ARRAY[0..maxsegm+1] of ^umponto;  {Valores dos gr†ficos}
  ay,by:ARRAY[mdl..df] OF REAL;
  ii,sel: medida;
  salvar,pzvalido,mfvalido,ok,polos,dividir,novosdesvios: BOOLEAN;
  np,Csaida,csr,x,xatual,nsaida,i,j,k,m,e,i1,elementos,obs,x1,x2,x3,
  placa,modo,xmin,xmax,ymin,ymax,altura,xq,yq,segm,r_atual: INTEGER;
  nos:INTEGER;        {Numero de nos}
  equacoes:INTEGER;   {Numero de equacoes, menor que nos pelo no. de amp. ops.}
  variaveis:INTEGER;  {Numero de variaveis, maior que nos pelo no. de fontes de tensao}
  dx,d,dh,f,z1,z2,Ires,t,t1,t2,d1,d2,sr,si,default: REAL;
  sufixo,pz: STRING[4];
  txt,rede: STRING;
  arquivo,relat: TEXT;
  r: CHAR;
  p: POINTER;
  zsubindo,zsubia:BOOLEAN;
  asubindo,asubia:BOOLEAN;
  bsubindo,bsubia:BOOLEAN;
  pulos:INTEGER;

LABEL
  Inicio;

PROCEDURE Beep;
BEGIN
 Sound(2000);
 Delay(20);
 NoSound;
 Sound(1500);
 Delay(20);
 NoSound
END;

FUNCTION Sri(x:INTEGER):STRING;
VAR
  tmp:STRING;
BEGIN
  Str(x,tmp);
  Sri:=tmp
END;

FUNCTION Sre(x:REAL; c,d:INTEGER):STRING;
VAR
  tmp:STRING;
BEGIN
  Str(x:c:d,tmp);
  Sre:=tmp
END;

PROCEDURE ErroFatal(texto:STRING);
BEGIN
  TextMode(80);
  WriteLn(tl,#10'[Erro]: '+texto);
  WriteLn(#10'Toque uma tecla...');
  r:=ReadKey;
  Halt
END;

FUNCTION Ex(x,y: REAL): REAL;
BEGIN Ex:=Exp(y*Ln(x)) END;

FUNCTION Angle(r,i:REAL):REAL;
VAR
  t:REAL;
BEGIN
  IF i=0 THEN i:=1.0e-10;
  IF r=0 THEN r:=Abs(i*1.0e-10);
  t:=Arctan(i/r);
  IF r<0 THEN
    IF i>0 THEN t:=pi+t ELSE t:=t-pi;
  Angle:=t
END;

PROCEDURE FecharSaida;
BEGIN
  IF salvar THEN BEGIN
    Write(relat,^L);
    Close(relat)
  END;
  salvar:=FALSE
END; {FecharSaida}

FUNCTION Rmult(x1,x2,y1,y2: REAL): REAL;
BEGIN
  Rmult:=x1*y1-x2*y2;
  Ires:=x1*y2+x2*y1
END; {Rmult}

FUNCTION Rdiv(x1,x2,y1,y2: REAL): REAL;
BEGIN
  t:=y1*y1+y2*y2;
  Rdiv:=Rmult(x1,x2,y1,-y2)/t;
  Ires:=Ires/t
END; {Rdiv}

PROCEDURE AbrirSaida;
BEGIN
  IF salvar THEN Write(tl,'[H†] um') ELSE Write(tl,'[NÑo h†]');
  WriteLn(' relat¢rio aberto.');
  WriteLn(tl,#10'[A]brir relat¢rio');
  WriteLn(tl,'[F]echar relat¢rio');
  WriteLn(tl,'[Esc]');
  r:=UpKey;
  IF r='A' THEN BEGIN
    FecharSaida;
    salvar:=TRUE;
    sufixo:='.tab';
    txt:=rede+sufixo;
    Write(tl,#10'Arquivo de relat¢rio: '); EditarLinha(txt,WhereX,WhereY,1);
    WriteLn;
    IF Pos('.',txt)=0 THEN txt:=txt+sufixo;
    Assign(relat,txt);
    ReWrite(relat);
    WriteLn(relat,'SENSI - Versao ',versao,' - Rede: ',rede,#13#10);
    Beep
  END
  ELSE IF r='F' THEN BEGIN FecharSaida; Beep END
END; {AbrirSaida}

PROCEDURE CalcularTudo; {Calcula tensîes e sensibilidades na freqÅància sr+jsi}

  PROCEDURE Admitancia(a,b:REAL; n1,n2:BYTE);
  BEGIN
    Y1[e]:=a; Y2[e]:=b;
    IF a<>0 THEN BEGIN
      M1[L[n1],C[n1]]:=M1[L[n1],C[n1]]+a;
      M1[L[n2],C[n2]]:=M1[L[n2],C[n2]]+a;
      M1[L[n1],C[n2]]:=M1[L[n1],C[n2]]-a;
      M1[L[n2],C[n1]]:=M1[L[n2],C[n1]]-a
    END;
    IF b<>0 THEN BEGIN
      M2[L[n1],C[n1]]:=M2[L[n1],C[n1]]+b;
      M2[L[n2],C[n2]]:=M2[L[n2],C[n2]]+b;
      M2[L[n1],C[n2]]:=M2[L[n1],C[n2]]-b;
      M2[L[n2],C[n1]]:=M2[L[n2],C[n1]]-b
    END;
  END; {Admitancia}

  PROCEDURE TransAdmitancia(a,b:REAL; n1,n2,n3,n4:BYTE);
  BEGIN
    Y1[e]:=a; Y2[e]:=b;
    IF a<>0 THEN BEGIN
      M1[L[n1],C[n3]]:=M1[L[n1],C[n3]]+a;
      M1[L[n2],C[n4]]:=M1[L[n2],C[n4]]+a;
      M1[L[n1],C[n4]]:=M1[L[n1],C[n4]]-a;
      M1[L[n2],C[n3]]:=M1[L[n2],C[n3]]-a
    END;
    IF b<>0 THEN BEGIN
      M2[L[n1],C[n3]]:=M2[L[n1],C[n3]]+b;
      M2[L[n2],C[n4]]:=M2[L[n2],C[n4]]+b;
      M2[L[n1],C[n4]]:=M2[L[n1],C[n4]]-b;
      M2[L[n2],C[n3]]:=M2[L[n2],C[n3]]-b
    END
  END; {TransAdmitancia}

  PROCEDURE SGm(n1,n2,n3,n4:BYTE);
  BEGIN
    {S#(Eo,Gm)=Y*A12*E34}
    t1:=Rmult(A1[L[n1]]-A1[L[n2]],A2[L[n1]]-A2[L[n2]],E1[C[n3]]-E1[C[n4]],E2[C[n3]]-E2[C[n4]]);
    t2:=Ires;
    t1:=Rmult(Y1[e],Y2[e],t1,t2);
    t2:=Ires
  END;

  PROCEDURE SIs(n1,n2:BYTE);
  BEGIN
    IF polos THEN BEGIN
      {Fontes nao afetam polos}
      t1:=0; t2:=0
    END
    ELSE BEGIN
      {S#(Eo,I)=A12*Is}
      t1:=Elemento[e].valor*(A1[L[n1]]-A1[L[n2]]);
      t2:=Elemento[e].valor*(A2[L[n1]]-A2[L[n2]])
    END
  END;

BEGIN
  L:=L0; {A condensaáÑo muda L. Isto repîe como estava}
  {Montar sistema e armazenar condutÉncias}
  FOR i:=0 TO equacoes DO BEGIN
    E1[i]:=0; E2[i]:=0; A1[i]:=0; A2[i]:=0;
    FOR j:=0 TO equacoes DO
      BEGIN M1[i,j]:=0; M2[i,j]:=0 END
  END;
  FOR e:=1 to elementos DO WITH elemento[e] DO
    CASE nome[1] OF
      'R','a','q':Admitancia(1/valor,0,n1,n2); {R, Ro e hie}
      'L':BEGIN
            t:=valor*(sr*sr+si*si);
            Admitancia(sr/t,-si/t,n1,n2)
          END;
      'C':Admitancia(sr*valor,si*valor,n1,n2);
      'G','Q','M','m':TransAdmitancia(valor,0,n1,n2,n3,n4); {Gm, hfe/hie, Gm e Gds}
      'A':BEGIN {GB/(sRo)}
            t:=valor/(sr*sr+si*si);
            TransAdmitancia(t*sr,-t*si,n1,n2,n3,n4);
          END;
      'Z':BEGIN {Rs da fonte Z}
            t:=1/valor;
            Admitancia(t,0,n1,n2)
          END;
      'I','v':IF not polos THEN BEGIN {Fonte I, excitaáÑo normal}
                E1[L[n1]]:=E1[L[n1]]-valor;
                E1[L[n2]]:=E1[L[n2]]+valor
              END;
      'V':BEGIN {Fonte V}
             k:=L[nx];
             IF not polos THEN E1[k]:=E1[k]-valor; {ExcitaáÑo normal}
             M1[k,C[n1]]:=M1[k,C[n1]]-1;
             M1[k,C[n2]]:=M2[k,C[n2]]+1;
          END;
      'E':BEGIN {VCVS}
            k:=L[nx];
            M1[k,C[n1]]:=M1[k,C[n1]]-1;
            M1[k,C[n2]]:=M2[k,C[n2]]+1;
            M1[k,C[n3]]:=M1[k,C[n3]]+valor;
            M1[k,C[n4]]:=M2[k,C[n4]]-valor;
            Y1[e]:=valor; Y2[e]:=0;
          END;
      'F':BEGIN {CCCS}
            j:=C[nx];
            M1[L[n1],j]:=M1[L[n1],j]+valor;
            M1[L[n2],j]:=M1[L[n2],j]-valor;
            M1[L[n3],j]:=M1[L[n3],j]+1;
            M1[L[n4],j]:=M1[L[n4],j]-1;
            Y1[e]:=valor; Y2[e]:=0;
          END;
      'H':TransAdmitancia(1/valor,0,n3,n4,n1,n2); {CCVS}
      'Y':BEGIN {Girador: Y12=1/Rg e Y21=-1/Rg}
            t:=1/valor;
            TransAdmitancia(t,0,n1,n2,n3,n4);
            TransAdmitancia(t,0,n4,n3,n1,n2);
          END;
  END;
  {ExcitaáÑo p/s.polos e adjunta}
  IF polos THEN
    WITH Elemento[obs] DO BEGIN
      e:=obs;
      Admitancia(-Y1[e],-Y2[e],n1,n2); {retirar elemento do circuito}
      Y1[e]:=-Y1[e]; Y2[e]:=-Y2[e];    {repor admitÉncia como estava}
      E1[L[n2]]:=E1[L[n2]]+1; E1[L[n1]]:=E1[L[n1]]-1;
      A1[C[n1]]:=A1[C[n1]]+1; A1[C[n2]]:=A1[C[n2]]-1
    END
  ELSE A1[Csaida]:=-1;
  {Recoloca a tensÑo de terra como zero}
  E1[0]:=0; A1[0]:=0;
  {Fatoracao LU}
  FOR i:=1 to m DO BEGIN
    i1:=i+1;
    t1:=M1[i,i]; t2:=M2[i,i];
    {CondensaáÑo pivotal}
    IF condensar THEN BEGIN
      k:=i;
      FOR j:=i1 TO equacoes DO
        IF Abs(M1[j,i])+Abs(M2[j,i])>Abs(t1)+Abs(t2) THEN BEGIN
          t1:=M1[j,i];
          t2:=M2[j,i];
          k:=j
        END;
      IF k<>i THEN BEGIN
        FOR j:=1 TO equacoes DO BEGIN
          t:=M1[i,j]; M1[i,j]:=M1[k,j]; M1[k,j]:=t;
          t:=M2[i,j]; M2[i,j]:=M2[k,j]; M2[k,j]:=t
        END;
      t:=E1[i]; E1[i]:=E1[k]; E1[k]:=t;
     {Isto nÑo Ç necess†rio com fontes reais}
     {t:=E2[i]; E2[i]:=E2[k]; E2[k]:=t;}
      FOR j:=1 TO variaveis DO
        IF L[j]=i THEN L[j]:=k
        ELSE IF L[j]=k THEN L[j]:=i
    END
  END;
  {Pivot muito pequeno}
  IF (Abs(t1)+Abs(t2)<toly) THEN BEGIN
    IF dividir THEN TextMode(80);
    ErroFatal('Determinante muito pequeno.');
  END;
  FOR j:=i1 TO equacoes DO
    BEGIN M1[i,j]:=Rdiv(M1[i,j],M2[i,j],t1,t2); M2[i,j]:=ires; END;
    FOR j:=i1 TO equacoes DO BEGIN
      t1:=M1[j,i]; t2:=M2[j,i];
      FOR k:=i1 TO equacoes DO BEGIN
        M1[j,k]:=M1[j,k]-Rmult(t1,t2,M1[i,k],m2[i,k]);
        M2[j,k]:=M2[j,k]-Ires
      END
    END
  END;
  {SubstituiáÑo direta}
  E1[1]:=Rdiv(E1[1],E2[1],M1[1,1],M2[1,1]); E2[1]:=Ires;
  FOR k:=2 TO equacoes DO BEGIN
    t1:=0; t2:=0; d1:=0; d2:=0;
    FOR j:=1 TO k-1 DO BEGIN
      t1:=t1+Rmult(M1[k,j],M2[k,j],E1[j],E2[j]);
      t2:=t2+Ires;
      d1:=d1+Rmult(M1[j,k],M2[j,k],A1[j],A2[j]);
      d2:=d2+Ires
    END;
    E1[k]:=Rdiv(E1[k]-t1,E2[k]-t2,M1[k,k],M2[k,k]);
    E2[k]:=Ires;
    A1[k]:=A1[k]-d1;
    A2[k]:=A2[k]-d2
  END;
  {SubstituiáÑo reversa}
  A1[equacoes]:=Rdiv(A1[equacoes],A2[equacoes],M1[equacoes,equacoes],M2[equacoes,equacoes]); A2[equacoes]:=Ires;
  FOR k:=m DOWNTO 1 DO BEGIN
    t1:=0; t2:=0; d1:=0; d2:=0;
    FOR j:=k+1 TO equacoes DO BEGIN
      t1:=t1+Rmult(M1[k,j],M2[k,j],E1[j],E2[j]);
      t2:=t2+Ires;
      d1:=d1+Rmult(M1[j,k],M2[j,k],A1[j],A2[j]);
      d2:=d2+Ires
    END;
    A1[k]:=Rdiv(A1[k]-d1,A2[k]-d2,M1[k,k],M2[k,k]);
    A2[k]:=Ires;
    E1[k]:=E1[k]-t1;
    E2[k]:=E2[k]-t2
  END;
  {C†lculo de Sensibilidades}
  FOR e:=1 TO elementos DO
    WITH Elemento[e] DO BEGIN
      CASE nome[1] OF
        'Z':BEGIN
              IF polos THEN t:=0 ELSE t:=Elemento[e+1].valor; {Vs em serie}
              {S#(Eo,Rs)=Y*A21*(E12+v)}
              t1:=Rmult(A1[L[n2]]-A1[L[n1]],A2[L[n2]]-A2[L[n1]],E1[C[n1]]-E1[C[n2]]+t,E2[C[n1]]-E2[C[n2]]);
              t2:=Ires;
              t1:=Rmult(Y1[e],Y2[e],t1,t2);
              t2:=Ires
            END;
        'I','v':SIs(n1,n2); {Fontes I}
        'V':SIs(nx,0);      {Fonte V}
        'C','R','L':BEGIN {ImpedÉncias}
              {S#(Eo,C)=Y*A12*E12}
              {S#(Eo,R,L,m)=-Y*A12*E12}
              SGm(n1,n2,n1,n2);
              IF nome[1]<>'C' THEN BEGIN t1:=-t1; t2:=-t2 END
            END;
        'G','A','Q','M','m':SGm(n1,n2,n3,n4); {TransadmitÉncias}
        'E':SGm(nx,0,n3,n4);
        'F':SGm(n1,n2,nx,0);
        'H':BEGIN SGm(n3,n4,n1,n2); t1:=-t1; t2:=-t2 END;
        'Y':BEGIN {Girador}
              {S#(Eo,Rg)=Y*(A34*E12-A12*E34)}
              t1:=Rmult(A1[L[n3]]-A1[L[n4]],A2[L[n3]]-A2[L[n4]],E1[C[n1]]-E1[C[n2]],E2[C[n1]]-E2[C[n2]]);
              t2:=Ires;
              t1:=t1-Rmult(A1[L[n1]]-A1[L[n2]],A2[L[n1]]-A2[L[n2]],E1[C[n3]]-E1[C[n4]],E2[C[n3]]-E2[C[n4]]);
              t2:=t2-Ires;
              t1:=Rmult(Y1[e],Y2[e],t1,t2);
              t2:=Ires
            END;
        'a','q':BEGIN {Ro e hie}
              {S#(Eo,Ro)=-S#(Eo,GB)-A12*E12/Ro}
              {S#(Eo,hie)=-S#(Eo,hfe)-A12*E12/hie}
              t1:=-t1-Rmult(A1[L[n1]]-A1[L[n2]],A2[L[n1]]-A2[L[n2]],E1[C[n1]]-E1[C[n2]],E2[C[n1]]-E2[C[n2]])/valor;
              t2:=-t2-Ires/valor;
            END
      END;
      {DivisÑo por Eo}
      WITH ponto[x]^ DO
        IF dividir THEN BEGIN
          S1[e]:=Rdiv(t1,t2,E1[Csaida],E2[Csaida]);
          S2[e]:=Ires
        END
        ELSE BEGIN S1[e]:=t1; S2[e]:=t2 END;
    END;
  {Sensibilidade do elemento que "và" os polos}
  IF polos THEN BEGIN
    {S#(Eo,obs)=1/Y (-1/Y para C)}
    t1:=Rdiv(1.0,0.0,Y1[obs],Y2[obs]);
    t2:=Ires;
    IF Elemento[obs].nome[1]='C' THEN BEGIN t1:=-t1; t2:=-t2 END;
    ponto[x]^.S1[obs]:=t1;
    ponto[x]^.S2[obs]:=t2;
  END;
END; {CalcularTudo}

PROCEDURE CalcularSTs; {Calcula S(T,s)}
VAR
  e:INTEGER;
BEGIN
  {S(T,s)=Som[S(T,L,C,-GB)]}
  d1:=0; d2:=0;
  WITH ponto[x]^ DO BEGIN
    FOR e:=1 TO elementos DO
      IF (Elemento[e].nome[1]='C') or (Elemento[e].nome[1]='L') THEN
        BEGIN d1:=d1+S1[e]; d2:=d2+S2[e] END
      ELSE
        IF Elemento[e].nome[1]='A' THEN
          BEGIN d1:=d1-S1[e]; d2:=d2-S2[e] END;
  END
END; {CalcularSTs}

PROCEDURE ImprimirTelaH;
VAR
  i,j,l,p:INTEGER;
  b7,b6,b5,b4,b3,b2,b1,b0,b,k:BYTE;
LABEL Fim;
BEGIN
  IF placa<>CGA THEN Exit;
  Write(lst,#27'@'#27'A'#8#27'l'#13#13);
  l:=0;
  REPEAT
    Write(lst,#27'L'#128#2);
    FOR i:=l TO l+79 DO BEGIN
      b7:=Mem[$b800:i];
      b6:=Mem[$b800:i+8192];
      b5:=Mem[$b800:i+80];
      b4:=Mem[$b800:i+8272];
      b3:=Mem[$b800:i+160];
      b2:=Mem[$b800:i+8352];
      b1:=Mem[$b800:i+240];
      b0:=Mem[$b800:i+8432];
      k:=128; j:=7;
      REPEAT
        b:=(b7 and k) shr j shl 7+(b6 and k) shr j shl 6+(b5 and k) shr j shl 5+
        +(b4 and k) shr j shl 4+(b3 and k) shr j shl 3
        +(b2 and k) shr j shl 2+(b1 and k) shr j shl 1+(b0 and k) shr j;
        IF l=7920 THEN b:=b and 224;
        Write(lst,Chr(b)); k:=k shr 1; j:=j-1
      UNTIL k<1;
    END;
    IF KeyPressed THEN BEGIN r:=ReadKey; GoTo Fim END;
    WriteLn(lst);
    l:=l+320
  UNTIL (l>7920);
 Fim:
  WriteLn(lst,#27'@');
  Beep
END; {ImprimirTelaH}

PROCEDURE ImprimirTelaV;
VAR
  i,j:INTEGER;
LABEL Fim;
BEGIN
  IF placa<>CGA THEN Exit;
  Write(lst,#27'@'#27'A'#8#27'l'#7#13);
  FOR i:=0 TO 79 DO BEGIN
    Write(lst,#27'K'#144#1);
    j:=7920+i;
    REPEAT
      Write(lst,Chr(Mem[$B800:j+8192]),Chr(Mem[$B800:j+8192]),Chr(Mem[$B800:j]),Chr(Mem[$B800:j]));
      j:=j-80
    UNTIL j=i-80;
    IF KeyPressed THEN BEGIN r:=ReadKey; GoTo Fim END;
    WriteLn(lst);
  END;
 Fim:
  WriteLn(lst,#27'@');
  Beep
END; {ImprimirTelaV}

PROCEDURE EntrarArquivo;
BEGIN
  ok:=FALSE;
  REPEAT
    txt:=rede;
    Write(tl,#10'Arquivo com a descriáÑo do circuito (.net) ou ?: ');
    EditarLinha(txt,WhereX,WhereY,1);
    WriteLn;
    IF txt='?' THEN Diretorio
    ELSE BEGIN
      IF Pos('.',txt)=0 THEN txt:=txt+'.net';
      rede:=Copy(txt,1,Pos('.',txt)-1);
      Assign(arquivo,txt);
      {$I-} Reset(arquivo) {$I+};
      ok:=(IOresult=0);
      IF not ok THEN WriteLn(tl,#10'[*] Arquivo [',txt,'] inexistente.')
    END
  UNTIL ok;
END; {EntrarArquivo}

PROCEDURE InicializarVariabilidades;
BEGIN
  FOR e:=1 TO elementos DO
    IF Elemento[e].nome[1] in ['v','I','V'] THEN DP[e]:=0 ELSE DP[e]:=default;
END;

PROCEDURE LerCircuito;
VAR
  maior,menor:INTEGER;

  PROCEDURE Ordenar(a,b:INTEGER);
  BEGIN
    IF a>b THEN BEGIN maior:=a; menor:=b END
    ELSE IF a<b THEN BEGIN maior:=b; menor:=a END
    ELSE ErroFatal('Circuito proibido');
  END;

  PROCEDURE Somar(VAR C:apontadores; a,b:BYTE); {"Soma" linhas ou colunas}
  VAR
    i,j:INTEGER;
  BEGIN
    Ordenar(C[a],C[b]);
    FOR j:=1 TO variaveis DO BEGIN
      IF C[j]=maior THEN C[j]:=menor;
      IF C[j]>maior THEN Dec(C[j])
    END
  END;

  PROCEDURE TestarVariaveis;
  BEGIN
    IF variaveis>MaxVar THEN ErroFatal('N£mero m†ximo de vari†veis (['+Sri(MaxVar)+'] excedido.');
  END;

  PROCEDURE SomarEquacoes(a,b:BYTE; VAR x:BYTE; VAR L,C:apontadores);
  {"Soma" linhas/colunas, alocando a eq./var. "maior" para x}
  VAR
    i,j:INTEGER;
  BEGIN
    Inc(variaveis);
    TestarVariaveis;
    x:=variaveis;
    Ordenar(L[a],L[b]);
    FOR j:=1 TO variaveis DO IF L[j]=maior THEN L[j]:=menor;
    L[variaveis]:=maior;
    C[variaveis]:=0;
  END;

  PROCEDURE MaisUm;
  BEGIN
    Inc(elementos);
    IF elementos>MaxEl THEN ErroFatal('N£mero m†ximo de elementos (['+Sri(MaxEl)+']) excedido.');
  END;

BEGIN
  ReadLn(arquivo,nos); equacoes:=nos; variaveis:=nos;
  WriteLn(tl,#10'N£mero de n¢s: [',nos,']');
  TestarVariaveis;
  FOR i:=0 TO nos DO BEGIN C[i]:=i; L[i]:=i END;
  WriteLn(tl,#10'[DescriáÑo do circuito:'#10']');
  elementos:=0;
  REPEAT
    MaisUm;
    WITH elemento[elementos] DO BEGIN
      nome:='';
      REPEAT
        Read(arquivo,r);
        IF r<>' ' THEN nome:=nome+UpCase(r)
      UNTIL (r=' ') or (Length(nome)=tn);
      Write(tl,'[',nome:tn,']: ');
      CASE nome[1] OF
        'R','L','C','I':BEGIN
              ReadLn(arquivo,n1,n2,valor);
              WriteLn(tl,valor:11,' de [',n1,'] para [',n2,']')
            END;
        'Z':BEGIN
              ReadLn(arquivo,n1,n2,valor,t1);
              WriteLn(tl,'Rs:',valor:11,' Vs:',t1:11,' de [',n1,'] para [',n2,']');
              MaisUm;
              t1:=t1/valor;
              WITH elemento[elementos] DO BEGIN
                nome:='v'+Copy(elemento[elementos-1].nome,2,255);
                valor:=t1;
                n1:=elemento[elementos-1].n1; n2:=elemento[elementos-1].n2
              END
            END;
        'V':BEGIN
              ReadLn(arquivo,n1,n2,valor);
              WriteLn(tl,valor:11,' de [',n1,'] para [',n2,']');
              SomarEquacoes(n1,n2,nx,L,C);
            END;
        'E':BEGIN
              ReadLn(arquivo,n1,n2,n3,n4,valor);
              WriteLn(tl,'Av:',valor:11,' entre [',n3,'](vi+), [',n4,'](vi-) [',n1,'](vo+) e [',n2,'](vo-)');
              SomarEquacoes(n1,n2,nx,L,C);
            END;
        'F':BEGIN
              ReadLn(arquivo,n1,n2,n3,n4,valor);
              WriteLn(tl,'Ai:',valor:11,' entre [',n3,'](ii+), [',n4,'](ii-) [',n1,'](io+) e [',n2,'](io-)');
              SomarEquacoes(n3,n4,nx,C,L);
            END;
        'H':BEGIN
              ReadLn(arquivo,n1,n2,n3,n4,valor);
              WriteLn(tl,'Rm:',valor:11,' entre [',n3,'](ii+), [',n4,'](ii-) [',n1,'](vo+) e [',n2,'](vo-)');
              Somar(C,n3,n4);
              Somar(L,n1,n2);
              Dec(equacoes);
            END;
        'A':BEGIN
              ReadLn(arquivo,n4,n3,n2,t1,t2); n1:=0;
              WriteLn(tl,'GB:',t1:11,' Ro:',t2:11,' entre [',n3,'](+), [',n4,'](-) e [',n2,'](sa°da)');
              valor:=t1/t2;
              MaisUm;
              WITH elemento[elementos] DO BEGIN
                nome:='a'+Copy(elemento[elementos-1].nome,2,255);
                valor:=t2;
                n1:=elemento[elementos-1].n1; n2:=elemento[elementos-1].n2
              END;
            END;
        'M':BEGIN
              ReadLn(arquivo,n1,n3,n2,t1,t2); n4:=n2;
              WriteLn(tl,'Gm:',t1:11,' Gds',t2:11,' entre [',n1,'](d), [',n3,'](g) e [',n2,'](s)');
              valor:=t1;
              IF t2<>0 THEN BEGIN
                MaisUm;
                WITH elemento[elementos] DO BEGIN
                  nome:='m'+Copy(elemento[elementos-1].nome,2,255);
                  valor:=t2;
                  n1:=elemento[elementos-1].n1; n2:=elemento[elementos-1].n2;
                  n3:=n1; n4:=n2;
                END
              END
            END;
        'Q':BEGIN
              ReadLn(arquivo,n1,n3,n2,t1,t2); n4:=n2;
              WriteLn(tl,'hfe:',t1:11,' hie',t2:11,' entre [',n1,'](c), [',n3,'](b) e [',n2,'](e)');
              valor:=t1/t2;
              MaisUm;
              WITH elemento[elementos] DO BEGIN
                nome:='q'+Copy(elemento[elementos-1].nome,2,255);
                valor:=t2;
                n1:=elemento[elementos-1].n3; n2:=elemento[elementos-1].n4
              END
            END;
        'Y':BEGIN
              ReadLn(arquivo,n1,n2,n3,n4,valor);
              WriteLn(tl,'rg:',valor:11,' entre [',n1,'](1+), [',n2,'](1-) [',n3,'](2+) e [',n4,'](2-)')
            END;
        'G':BEGIN
              ReadLn(arquivo,n1,n2,n3,n4,valor);
              WriteLn(tl,'Gm:',valor:11,' entre [',n3,'](v+), [',n4,'](v-) [',n1,'](i+) e [',n2,'](i-)')
            END;
        'O':BEGIN
              ReadLn(arquivo,n1,n2,n3);
              WriteLn(tl,'Sa°da em [',n3,'], entradas em [',n1, '] e [',n2,']');
              Somar(C,n1,n2);
              Somar(L,0,n3);
              Dec(equacoes); Dec(elementos);
            END;
        ELSE ErroFatal('Elemento desconhecido.')
      END;
    END
  UNTIL SeekEof(arquivo);
  Close(arquivo);
  WriteLn(tl,#10,'N£mero de elementos efetivos: [',elementos,']');
  InicializarVariabilidades;
  WriteLn(tl,'N£mero de vari†veis: [',variaveis,']');
  WriteLn(tl,'Ordem do sistema: [',equacoes,'] equaáîes');
  IF equacoes>MaxEq THEN ErroFatal('N£mero m†ximo de equaáîes (['+Sri(MaxEq)+']) excedido.');
  m:=equacoes-1;
  L0:=L; {Para repor L antes de cada soluáÑo}
  {otimizar:=FALSE; refinar:=FALSE}
END; {LerCircuito}

PROCEDURE ZerarDesconto;
BEGIN
  FOR e:=1 TO elementos DO Desconto[e]:=0;
END; {ZerarDesconto}

PROCEDURE ZerarGrafico;
BEGIN
  j:=segm;
  Release(p);
  i:=(MaxAvail-1000) div (SizeOf(umponto)); {Corrigir para expansao da free-list}
  IF segm+2>i THEN segm:=i-2;
  IF segm>maxsegm THEN segm:=maxsegm;
  IF Odd(segm) THEN Dec(segm);
  IF segm<>j THEN
    WriteLn(tl,#10'N£mero de segmentos no gr†fico ajustado para [',segm,']');
  FOR i:=1 TO nos DO BEGIN
    Maximo[i]:=0;
    Minimo[i]:=1e+37
  END;
  mfvalido:=FALSE;
  novosdesvios:=TRUE;
  csr:=0;
  FOR i:=0 TO segm+1 DO BEGIN
    New(ponto[i]);
    ponto[i]^.analisado:=FALSE
  END
END; {ZerarGrafico}

PROCEDURE EscolherSaida;
BEGIN
  REPEAT
    Write(#10'N¢ de sa°da'); LerInt(nsaida);
    ok:=(nsaida>0) and (nsaida<=nos);
    IF ok THEN BEGIN
      Csaida:=C[nsaida];
      ok:=(Csaida>0);
    END;
    IF not ok THEN WriteLn(tl,#10'[*] N¢ inv†lido ou com tensÑo sempre nula.'#10)
  UNTIL ok;
  ZerarDesconto;
  ZerarGrafico;
  descontar:=FALSE;
  pzvalido:=FALSE;
  obs:=elementos;
END; {EscolherSaida}

PROCEDURE MudarEscalas;
VAR
  alinear,ahertz:BOOLEAN;
  asegm:INTEGER;
BEGIN
  t1:=min[frq];
  t2:=max[frq];
  alinear:=linear;
  ahertz:=hertz;
  asegm:=segm;
  Write(#10'Escala linear'); LerBool(linear);
  Write(#10'FreqÅàncias em Hertz'); LerBool(hertz);
  unid[frq]:=uf[hertz];
  Write(#10'Segmentos no gr†fico'); LerInt(segm);
  WriteLn(#10'Novos limites:');
  FOR ii:=frq TO df DO BEGIN
    Write(#10,prm[ii],' m°nimo (',unid[ii],')'); LerReal(min[ii]);
    Write(prm[ii],' m†ximo (',unid[ii],')'); LerReal(max[ii]);
  END;
  IF (segm<>asegm) or (linear<>alinear) or (ahertz<>hertz) or (min[frq]<>t1) or (max[frq]<>t2) THEN ZerarGrafico;
END; {MudarEscalas}

PROCEDURE MudarNormalizacao;
VAR
  anormincl:BOOLEAN;
BEGIN
  anormincl:=normincl;
  Write(#10'Normalizar sensibilidades p/inclinaáÑo'); LerBool(normincl);
  novosdesvios:=anormincl<>normincl
END; {MudarNormalizacao}

PROCEDURE MudarDesconto;
BEGIN
  Write(#10'Descontar a parte real das sensibilidades'); LerBool(descontar);
  IF descontar THEN BEGIN
    Write('Calcular descontos (ou editar)'); ok:=TRUE; LerBool(ok);
    IF ok THEN BEGIN
      IF mfvalido THEN si:=ponto[csr]^.V[frq] ELSE si:=1e-6;
      sr:=0; x:=segm+1;
      Write(#10'FreqÅància do desconto: ');
      Write('(',unid[frq],')'); LerReal(si);
      IF hertz THEN si:=2*Pi*si;
      polos:=FALSE; dividir:=TRUE;
      CalcularTudo;
      Desconto:=ponto[x]^.S1;
    END
    ELSE
      FOR e:=1 TO elementos DO BEGIN
        Write(tl,'Desconto de [',Elemento[e].nome:tn,']'); LerReal(Desconto[e]);
      END;
    novosdesvios:=TRUE;
  END
  ELSE BEGIN
    ZerarDesconto;
    novosdesvios:=TRUE
  END
END; {MudarDesconto}

PROCEDURE MudarVariabilidades;
BEGIN
  WriteLn(tl,'[Variabilidades]');
  Write(tl,#10'Mudar [T]odas ou [U]ma a uma? [');
  REPEAT
    r:=UpKey
  UNTIL r in ['T','U'];
  WriteLn(tl,r,']',#10);
  IF r='T' THEN BEGIN
    Write('Valor das variabilidades'); LerReal(default);
    InicializarVariabilidades;
  END
  ELSE
    FOR e:=1 TO elementos DO BEGIN
      Write(tl,'Variabilidade de [',Elemento[e].nome:tn,']'); LerReal(DP[e]);
    END;
  novosdesvios:=TRUE;
  IF salvar THEN BEGIN
    WriteLn(tl,#10'[S]alvar [Esc]');
    REPEAT r:=UpKey UNTIL r in [#27,'S'];
    IF r='S' THEN BEGIN
      WriteLn(relat,'Variabilidades ds parametros');
      FOR i:=1 TO elementos DO BEGIN
        Write(relat,elemento[i].nome:tn,' ',DP[i]:cm:dc,' ');
        IF (i mod 4=0) or (i=elementos) THEN WriteLn(relat)
      END;
      WriteLn(relat);
      Beep
    END
  END;
END; {MudarVariabilidades}

PROCEDURE ListarSensibilidades;
LABEL
  Ler;

  PROCEDURE EscreverLinha(e:INTEGER);
  BEGIN
    IF (e>0) and (e<=elementos) THEN BEGIN
      t1:=(ponto[csr]^.S1[e]-Desconto[e])/z1;
      t2:=ponto[csr]^.S2[e]/z2;
      Write(tl,'S(T,[',Elemento[e].nome:tn,']):',t1:cm:dc,' ',t2:cm:dc,'j');
      ClrEol
    END;
    IF WhereY<>25 THEN WriteLn
  END;

BEGIN
  ClrScr;
  Write(tl,'[Cursor], [Esc]');
  IF salvar THEN Write(tl,' [S]alvar');
  j:=1; k:=25-6;
  REPEAT
    GoToXY(1,3);
    Write(tl,'N¢ [',nsaida,']; Sensibilidades de T(s) em [',ponto[csr]^.V[frq]:cm:dc,' ',unid[frq],']');
    IF descontar THEN Write(' descontadas');
    IF normincl THEN Write(' normalizadas');
    ClrEol;
    WriteLn(#10);
    Delay(espera);
    IF not KeyPressed THEN BEGIN
      x:=csr; CalcularSTs;
      IF normincl THEN BEGIN
        z1:=Sqrt(1+Sqr(d1));
        z2:=Sqrt(1+Sqr(d2))
      END
      ELSE BEGIN
        z1:=1; z2:=1
      END;
      WriteLn(tl,'S(T,[s]):',d1:cm:dc,' ',d2:cm:dc,'j'#10);
      FOR e:=j TO k DO EscreverLinha(e);
    END;
   Ler:
    CASE UpKey of
      #0:CASE ReadKey of
           'M':IF csr<xatual THEN Inc(csr);
           'K':IF csr>0 THEN Dec(csr);
           'H':BEGIN
                  Dec(j); Dec(k);
                  GoToXY(1,7);
                  InsLine;
                  EscreverLinha(j);
                  GoTo Ler
                END;
           'P':BEGIN
                 Inc(k); Inc(j);
                 GoToXY(1,7);
                 DelLine;
                 GoToXY(1,25);
                 EscreverLinha(k);
                 GoTo Ler
               END
         END;
      #27:BEGIN ClrScr; Exit END;
      'S':IF salvar THEN BEGIN
            Write(relat,'Sensibilidades em ',ponto[csr]^.V[frq]:cm:dc,' ',unid[frq]);
            IF descontar THEN Write(relat,' descontadas');
            IF normincl THEN Write(relat,' normalizadas');
            WriteLn(relat,'; Saida ',nsaida);
             FOR e:=1 TO elementos DO BEGIN
              Write(relat,Elemento[e].nome:tn,' ',(ponto[csr]^.S1[e]-Desconto[e])/z1:cm:dc,' ',ponto[csr]^.S2[e]/z2:cm:dc,' ');
              IF (e mod 3=0) or (e=elementos) THEN WriteLn(relat)
             END;
            WriteLn(relat);
            Beep
          END
    END
  UNTIL FALSE;
END; {ListarSensibilidades}

PROCEDURE SensibilidadePolosZeros;
LABEL
  Continuar;

  PROCEDURE ListarSpz;
  LABEL
    Ler;

    PROCEDURE EscreverLinha(e:INTEGER);
    BEGIN
      IF (e>0) and (e<=elementos) THEN BEGIN
        Write(tl,'S''(s,[',Elemento[e].nome:tn,']):');
        Write(tl,ponto[x]^.S1[e]:cm:dc,' ',ponto[x]^.S2[e]:cm:dc,'j');
        IF polos and (e=obs) THEN Write(tl,' ([observador])');
        ClrEol
      END;
      IF WhereY<>25 THEN WriteLn
    END;

  BEGIN
    ClrScr;
    Write(tl,'[Cursor], [Esc]');
    IF salvar THEN Write(tl,' [S]alvar');
    j:=1; k:=25-8;
    REPEAT
      WITH ponto[x]^ DO BEGIN
        GoToXY(1,3);
        IF not polos THEN Write(tl,'N¢ [',nsaida,']: ');
        WriteLn(tl,'Sensibilidades do [',pz,x:3,'] em [',re:cm:dc,' ',im:cm:dc,'j]',#10);
        Delay(espera);
        IF not KeyPressed THEN
          IF calculavel THEN BEGIN
            WriteLn(tl,'[Desvio Real]:',vre:cm:dc,' [Desvio Imag]:',vim:cm:dc);
            WriteLn(tl,'[Raio maior] :',rma:cm:dc,' [Raio menor]: ',rme:cm:dc);
            WriteLn(tl,'[Angulo do raio maior]:',ang*180/pi:cm:dc,#10);
            FOR e:=j TO k DO EscreverLinha(e)
          END
          ELSE BEGIN
            ClrEol;
            WriteLn('NÑo calcul†veis');
            FOR i:=WhereY TO 25 DO BEGIN GoToXY(1,i); ClrEol END
          END;
       Ler:
        CASE UpKey of
          #0:CASE ReadKey of
               'M':IF x<np THEN x:=x+1;
               'K':IF x>1 THEN x:=x-1;
               'H':IF calculavel THEN BEGIN
                     Dec(j); Dec(k);
                     GoToXY(1,9);
                     InsLine;
                     EscreverLinha(j);
                     GoTo Ler
                   END
                   ELSE GoTo Ler;
               'P':IF calculavel THEN BEGIN
                     Inc(k); Inc(j);
                     GoToXY(1,9);
                     DelLine;
                     GoToXY(1,25);
                     EscreverLinha(k);
                     GoTo Ler
                   END
                   ELSE GoTo Ler;
             END;
         #27:BEGIN ClrScr; Exit END;
         'S':IF salvar and calculavel THEN BEGIN
               Write(relat,'Sensibilidades do ',pz,' em ',re:cm:dc,' ',im:cm:dc,'j:');
               IF polos THEN WriteLn(relat,' Observador: ',Elemento[obs].nome)
               ELSE WriteLn(relat,' Saida ',nsaida);
               FOR e:=1 TO elementos DO BEGIN
                 Write(relat,Elemento[e].nome:tn,' ',ponto[x]^.S1[e]:cm:dc,' ',ponto[x]^.S2[e]:cm:dc,' ');
               IF (e mod 3=0) or (e=elementos) THEN WriteLn(relat)
             END;
             WriteLn(relat);
             Beep
           END
        END
      END;
    UNTIL FALSE;
  END; {ListarSpz}

  PROCEDURE PlotarSpz;
  VAR
    remin,immin,delta,ay,by,ax,bx,w:REAL;
    xmax,ymax,base:INTEGER;
    xa,ya:WORD;

  LABEL atualizar;

    FUNCTION LimX(x:REAL):INTEGER;
    BEGIN
      LimX:=Round(ax*x+bx)
    END;

    FUNCTION LimY(y:REAL):INTEGER;
    BEGIN
      LimY:=Round(ay*y+by)
    END;

    PROCEDURE Elipse(x0,y0,a,b,angulo: REAL; cor:INTEGER);
    CONST
      lados=8;
    BEGIN
      SetColor(cor);
      IF a=0 THEN Exit;
      t:=a/lados;
      d:=b/a;
      d1:=Cos(angulo);
      d2:=Sin(angulo);
      FOR j:=-lados TO lados DO BEGIN
        z1:=j*t;
        z2:=d*Sqrt(Abs(Sqr(a)-Sqr(z1)));
        IF j>-lados THEN BEGIN
          Line(LimX(x0+t1*d1-t2*d2),LimY(y0+t1*d2+t2*d1),LimX(x0+z1*d1-z2*d2),LimY(y0+z1*d2+z2*d1));
          Line(LimX(x0+t1*d1+t2*d2),LimY(y0+t1*d2-t2*d1),LimX(x0+z1*d1+z2*d2),LimY(y0+z1*d2-z2*d1));
        END;
        t1:=z1;
        t2:=z2;
      END;
    END;

  BEGIN
    remin:=0.1;
    FOR i:=1 TO np DO WITH ponto[i]^ DO BEGIN
      IF Abs(re)>remin THEN remin:=Abs(re);
      IF Abs(im)>remin THEN remin:=Abs(im)
    END;
    remin:=-Ex(2,Trunc(Ln(remin)/Ln(2))+1);
    immin:=remin;
    delta:=-2*remin;
    REPEAT
      SetGraphMode(modo);
      SetTextStyle(SmallFont,HorizDir,4);
      RemoveSprite;
      SetFillStyle(EmptyFill,1);
      ymax:=GetMaxY;
      GetAspectRatio(xa,ya);
      xmax:=Trunc(ymax*ya/xa);
      base:=xmax+4;
      ay:=-ymax/delta; by:=ymax-ay*immin;
      ax:=xmax/delta; bx:=-ax*remin;
      SetColor(cor[forte]);
      OutTextXY(base,0,'Re:'+Sre(remin,10,-1));
      OutTextXY(base,8,'   '+Sre(remin+delta,10,-1));
      OutTextXY(base,16,'Im:'+Sre(immin,10,-1));
      OutTextXY(base,24,'   '+Sre(immin+delta,10,-1));
      SetViewPort(0,0,xmax,ymax,ClipOn);
      SetLineStyle(DottedLn,0,NormWidth);
      SetColor(cor[fraca]);
      i:=Limx(0);
      Line(i,0,i,ymax);
      i:=Limy(0);
      Line(0,i,xmax,i);
      SetLineStyle(SolidLn,0,NormWidth);
      SetColor(cor[forte]);
      Rectangle(0,0,xmax,ymax);
      FOR i:=1 TO np DO WITH ponto[i]^ DO BEGIN
        x1:=LimX(re);
        x2:=LimY(im);
        IF (x1>=0) and (x1<=xmax) and (x2>=0) and (x2<=ymax) THEN BEGIN
          SetColor(cor[forte]);
          IF polos THEN BEGIN
            Line(x1-2,x2-2,x1+2,x2+2);
            Line(x1-2,x2+2,x1+2,x2-2)
          END
          ELSE Circle(x1,x2,4);
          IF calculavel THEN BEGIN
            SetColor(cor[media]);
            IF retangulos THEN Rectangle(LimX(re-vre),LimY(im-vim),LimX(re+vre),LimY(im+vim));
            IF elipses THEN Elipse(re,im,rma,rme,ang,cor[forte]);
          END
        END;
        IF KeyPressed THEN GoTo atualizar
      END;
      SetViewPort(0,0,GetMaxX,GetMaxY,ClipOn);
      OutTextXY(base,40,rede);
      IF not polos THEN OutTextXY(base,48,'No '+Sri(nsaida));
      REPEAT
        WITH ponto[x]^ DO BEGIN
          x1:=LimX(re);
          x2:=LimY(im);
          IF (x1>=0) and (x1<=xmax) and (x2>0)  and (x2<=ymax)
            THEN PutsPrite(x1,x2) ELSE PutSprite(-100,-100);
          Bar(base,100,GetMaxX,GetMaxY);
          SetColor(cor[media]);
          OutTextXY(base,100,pz+' '+Sri(x));
          OutTextXY(base,116,'Re:'+Sre(re,10,-1));
          OutTextXY(base,124,'Im:'+Sre(im,10,-1));
          w:=Sqrt(Sqr(re)+Sqr(im));
          OutTextXY(base,132,'w: '+Sre(w,10,-1));
          MoveTo(base,140); OutText('Q: ');
          IF re<>0 THEN OutText(Sre(-0.5*w/re,10,-1)) ELSE OutText(' infinito');
          IF calculavel THEN BEGIN
            SetColor(cor[forte]);
            OutTextXY(base,156,'VRe:'+Sre(vre,10,-1));
            OutTextXY(base,164,'VIm:'+Sre(vim,10,-1));
            OutTextXY(base,172,'Ra:'+Sre(rma,10,-1));
            OutTextXY(base,180,'Rb:'+Sre(rme,10,-1));
            OutTextXY(base,188,'Ang:'+Sre(ang*180/pi,9,3))
          END
        END;
       atualizar:
        r:=UpKey;
        CASE r OF
          ' ':WITH ponto[x]^ DO BEGIN
                remin:=re-delta/2;
                immin:=im-delta/2
              END;
          'R':retangulos:=not retangulos;
          'E':elipses:=not elipses;
          #9:IF x<np THEN x:=x+1 ELSE x:=1;
          #8:IF x>1 THEN x:=x-1 ELSE x:=np;
          #0:BEGIN
               r:=ReadKey;
               CASE r OF
                 'M':remin:=remin+delta/4;
                 'K':remin:=remin-delta/4;
                 'H':immin:=immin+delta/4;
                 'P':immin:=immin-delta/4
               END
             END;
         '-':BEGIN
               remin:=remin-delta/2;
               immin:=immin-delta/2;
               delta:=delta*2
             END;
         '+':BEGIN
               remin:=remin+delta/4;
               immin:=immin+delta/4;
               delta:=delta/2;
             END;
         'H':ImprimirTelaH;
         'V':ImprimirTelaV;
        END
      UNTIL r in [' ','R','E',#27,'M','K','H','P','V','+','-'];
    UNTIL r=#27;
    TextMode(80);
  END; {PlotarSpz}

  PROCEDURE SalvarSpz;
  BEGIN
    Write(relat,'Desvios estat. dos ',pz,'s');
    IF polos THEN Write(relat,'; Obs: ',Elemento[obs].nome)
    ELSE Write(relat,'; Saida ',nsaida);
    WriteLn(relat,' (Re, Im, VRe, VIm, Ra, Rb, Ang)');
    FOR i:=1 TO np DO
      WITH ponto[i]^ DO IF calculavel THEN
        WriteLn(relat,re:cm:dc,' ',im:cm:dc,' ',vre:cm:dc,' ',vim:cm:dc,' ',rma:11:6,' ',rme:cm:dc,' ',ang*180/pi:cm:dc);
    WriteLn(relat);
    Beep
  END; {SalvarSpz}

BEGIN
  IF polos THEN BEGIN
    e:=obs;
    Write(tl,#10'Selecione o elemento observador ([<],[>],[Cr]):[ '); i:=WhereX; j:=WhereY;
    REPEAT
      GoToXY(i,j);
      Write(Elemento[e].nome); ClrEol;
      r:=ReadKey;
      CASE r OF
        '<',',':IF e>1 THEN Dec(e) ELSE e:=elementos;
        '>','.':IF e<elementos THEN Inc(e) ELSE e:=1;
        #13:WriteLn(tl,']');
      END
    UNTIL r=#13;
    IF not (Elemento[e].nome[1] in ['Z','R','L','C']) THEN BEGIN
      WriteLn(tl,'[*] O elemento observador tem que ser [Z], [R], [L] ou [C]');
      Exit
    END;
    IF obs<>e THEN pzvalido:=FALSE;
    obs:=e
  END;
  IF not pzvalido THEN BEGIN {Ler polos/zeros e calcular sensibilidades}
    IF polos THEN sufixo:='.r'
    ELSE BEGIN
      Str(nsaida,sufixo);
      sufixo:='.z'+sufixo;
    END;
    txt:=rede+sufixo;
    Write(tl,#10'Arquivo de freqÅàncias: '); EditarLinha(txt,WhereX,WhereY,1);
    WriteLn;
    IF Pos('.',txt)=0 THEN txt:=txt+sufixo;
    Assign(arquivo,txt);
    {$I-} Reset(arquivo) {$I+};
    ok:=(IOResult=0);
    IF not ok THEN BEGIN
      WriteLn(tl,#10'[*] Arquivo [',txt,'] inexistente.');
      Exit
    END;
    WriteLn;
    IF polos THEN pz:='Polo' ELSE pz:='Zero';
    Read(arquivo,np);
    FOR x:=1 TO np DO WITH ponto[x]^ DO BEGIN
      analisado:=FALSE;
      ReadLn(arquivo,sr,si);
      WriteLn(tl,'[',pz,x:3,'] ',sr:cm:dc,' ',si:cm:dc,'j');
      dividir:=FALSE;
      re:=sr; im:=si;
      IF (Abs(sr)<toly) and (Abs(si)<toly) THEN BEGIN
        WriteLn(tl,'[*] NÑo Ç permitida an†lise em CC.');
        calculavel:=FALSE;
        GoTo Continuar
      END;
      CalcularTudo;
      IF polos THEN WITH Elemento[obs] DO BEGIN
        t1:=E1[C[n1]]-E1[C[n2]]-Rdiv(1.0,0.0,Y1[obs],Y2[obs]);
        t2:=E2[C[n1]]-E2[C[n2]]-Ires;
        IF (Abs(t1)>tolz) or (Abs(t2)>tolz) THEN BEGIN
          WriteLn(tl,'[*] ImpedÉncia vista por [',nome,'] muito alta: [',t1:7,' ',t2:7,'j]');
          WriteLn(tl,'  Polo nÑo observ†vel ou incorreto.');
          calculavel:=FALSE;
          GoTo Continuar
        END
      END
      ELSE
        IF (Abs(E1[Csaida])>tolz) or (Abs(E2[Csaida])>tolz) THEN BEGIN
          WriteLn(tl,'[*]  TensÑo de sa°da muito alta: [',E1[Csaida]:7,' ',E2[Csaida]:7,'j]');
          WriteLn(tl,'   Zero incorreto.');
          calculavel:=FALSE;
          GoTo Continuar
        END;
      {t=-s/S#(T,s)}
      CalcularSTs;
      d1:=Rdiv(-sr,-si,d1,d2); d2:=Ires;
      FOR e:=1 TO elementos DO BEGIN
        {S#(s,x)=t*S#(T,x)}
        S1[e]:=Rmult(d1,d2,S1[e],S2[e]);
        S2[e]:=Ires;
      END;
      calculavel:=TRUE;
     Continuar:
    END;
    Close(arquivo);
  END;
  {Calcular desvios}
  Write(tl,#10,'Calculando desvios...[');
  FOR x:=1 TO np DO WITH ponto[x]^ DO IF calculavel THEN BEGIN
    Write(' ',x);
    {Calcular Éngulo da elipse}
    sr:=0; si:=0;
    FOR e:=1 TO elementos DO BEGIN
      d:=Sqr(DP[e])*(Sqr(S1[e])+Sqr(S2[e]));
      t:=Angle(S1[e],S2[e]);
      t1:=d*Cos(t);
      t2:=d*Sin(t);
      z1:=sr+t1;
      z2:=si+t2;
      d1:=sr-t1;
      d2:=si-t2;
      IF Sqr(z1)+Sqr(z2)>Sqr(d1)+Sqr(d2) THEN BEGIN
        sr:=z1;
        si:=z2;
      END
      ELSE BEGIN
        sr:=d1;
        si:=d2;
      END;
    END;
    ang:=Angle(sr,si);
    {Calcular desvios estat°sticos}
    t1:=Cos(ang);
    t2:=Sin(ang);
    vre:=0; vim:=0;
    rma:=0; rme:=0;
    FOR e:=1 TO elementos DO BEGIN
      vre:=vre+Sqr(S1[e]*DP[e]);
      vim:=vim+Sqr(S2[e]*DP[e]);
      rma:=rma+Sqr((S1[e]*t1+S2[e]*t2)*DP[e]);
      rme:=rme+Sqr((-S1[e]*t2+S2[e]*t1)*DP[e]);
    END;
    vre:=Sqrt(vre);
    vim:=Sqrt(vim);
    rma:=Sqrt(rma);
    rme:=Sqrt(rme)
  END;
  {Mostrar resultados}
  WriteLn;
  x:=1;
  REPEAT
    ok:=FALSE;
    WriteLn(tl,#10'[P]lotar freqÅàncias e desvios');
    WriteLn(tl,'[L]istar sensibilidades e desvios');
    IF salvar THEN WriteLn(tl,'[S]alvar freqÅàncias e desvios');
    WriteLn(tl,'[Esc]');
    CASE UpKey of
      'P':PlotarSpz;
      'L':ListarSpz;
      'S':IF salvar THEN SalvarSpz;
      #27:ok:=TRUE
    END
  UNTIL ok;
  mfvalido:=FALSE;
  pzvalido:=TRUE;
END; {SensibilidadePolosZeros}

PROCEDURE ListarFaixa;

  PROCEDURE EscreverLinha(i:INTEGER);
  BEGIN
    IF (i>0) and (i<=nos) THEN {Nao lista auxiliares, nulas}
      Write(tl,'Min([',i:2,']):',Minimo[i]:cm:dc,' Max([',i:2,']):',Maximo[i]:cm:dc);
    ClrEol;
    IF WhereY<>25 THEN WriteLn
  END;

BEGIN
  ClrScr;
  Write(tl,'[Cursor], [Esc]');
  IF salvar THEN Write(tl,' [S]alvar');
  j:=1; k:=25-4;
  WriteLn(#10);
  WriteLn('Extremos de n°vel de sinal nos n¢s'#10);
  FOR i:=j TO k DO EscreverLinha(i);
  REPEAT
    CASE UpKey of
      #0:CASE ReadKey of
           'H':BEGIN
                  Dec(j); Dec(k);
                  GoToXY(1,5);
                  InsLine;
                  EscreverLinha(j);
                END;
           'P':BEGIN
                 Inc(k); Inc(j);
                 GoToXY(1,5);
                 DelLine;
                 GoToXY(1,25);
                 EscreverLinha(k);
               END
         END;
      #27:BEGIN ClrScr; Exit END;
      'S':IF salvar THEN BEGIN
            WriteLn(relat,'Extremos de sinal (no, min, max):');
            FOR i:=1 TO nos DO
              WriteLn(relat,i:2,' ',Minimo[i]:cm:dc,' ',Maximo[i]:cm:dc);
            WriteLn(relat);
            Beep
          END
    END
  UNTIL FALSE;
END; {ListarFaixa}

PROCEDURE SalvarSmf;
BEGIN
  Write(relat,'# Resp. em freq. (',uf[hertz],'): Saida ',nsaida,'; Dsv. ');
  IF normincl THEN Write(relat,'norm. p/incl.') ELSE Write(relat,'normais');
  IF descontar THEN Write(relat,' desc.') ELSE Write(relat);
  WriteLn(relat,' (Frq, Mod, Fas, Atr, VeM, VeF, Mod-VeM, Mod+Vem)');
  FOR i:=0 TO xatual DO
    WITH ponto[i]^ DO
      WriteLn(relat,V[frq]:cm:dc,' ',V[mdl]:cm:dc,' ',V[fas]:cm:dc,' ',V[tg]:cm:dc,' ',V[dm]:cm:dc,' ',V[df]:cm:dc,
      ' ',V[mdl]-V[dm]:cm:dc,' ',V[mdl]+V[dm]:cm:dc);
  WriteLn(relat);
  Beep
END; {SalvarSmf}

PROCEDURE RespostaEmFrequencia;
VAR
  i,j,k,l,xa,xb,dc,centro,kcor,xx,r_efetivas:INTEGER;
  pivot,tt,det,me,ax,bx,delta,ttt,dg:REAL;
  A,At,An:ARRAY[1..MaxEsp,1..MaxEsp+1] OF REAL;
  b:ARRAY[1..MaxEsp] OF REAL;

LABEL
  Atualizar,DeNovo;

  FUNCTION Lim(y:REAL):INTEGER;
  CONST
    ymin=-2000;
    ymax=2000;
  BEGIN
    IF y<ymin THEN Lim:=ymin
    ELSE IF y>ymax THEN Lim:=ymax
      ELSE Lim:=Round(y)
  END;

  PROCEDURE Cursor;
  VAR
    y:REAL;
  BEGIN
    y:=ponto[csr]^.V[sel]*ay[sel]+by[sel];
    IF y<0 THEN y:=0
    ELSE IF y>altura THEN y:=altura;
    IF plotar[sel] THEN PutSprite(Round(csr*dx),Round(y))
    ELSE PutSprite(-1000,-1000)
  END;

  PROCEDURE Escalas;
  VAR
    z:INTEGER;
  BEGIN
    Str(min[frq]:7:4,txt); OutTextXY(xmin,ymax,txt);
    Str(max[frq]:7:4,txt); OutTextXY(xmax-TextWidth(txt),ymax,txt);
    OutTextXY((xmax+xmin-TextWidth(unid[frq])) div 2,ymax,unid[frq]);
    OutTextXY(0,0,rede);
    OutTextXY(0,8,'No '+Sri(nsaida));
    z:=24;
    FOR ii:=mdl TO df DO IF plotar[ii] THEN BEGIN
      SetColor(cor[Ord(ii)]);
      OutTextXY(0,ymin+z,prm[ii]+':');
      OutTextXY(0,ymin+z+8,Sre(max[ii],7,2));
      OutTextXY(0,ymin+z+16,Sre(min[ii],7,2)+' '+unid[ii]);
      z:=z+24;
    END;
    SetColor(cor[forte]);
    OutTextXY(0,ymax-40,'Escala:'); MoveTo(0,ymax-32);
    IF linear THEN OutText('linear') ELSE OutText('log.');
    OutTextXY(0,ymax-24,'Desvios:');
    MoveTo(0,ymax-16);
    IF normincl THEN BEGIN OutText('normaliz.'); MoveTo(0,ymax-8) END;
    IF descontar THEN OutText('descont.');
    IF not normincl and not descontar THEN OutText('normais');
  END;

  PROCEDURE Medir;
  BEGIN
    SetColor(cor[forte]);
    Rectangle(xq-2,yq-1,xq+120,yq+51);
    SetFillStyle(EmptyFill,0);
    Bar(xq-1,yq,xq+119,yq+50);
    SetFillStyle(SolidFill,cor[forte]);
    Bar(xq-1,yq+8*(ord(sel))+1,xq+119,yq+8*(Ord(sel)+1)+1);
    WITH ponto[csr]^ DO
      FOR ii:=frq TO df DO BEGIN
        IF ii=sel THEN SetColor(0) ELSE SetColor(cor[forte]);
        OutTextXY(xq,yq+8*(ord(ii))-1,prm[ii]+Sre(V[ii],10,4)+' '+unid[ii])
      END
  END;

  PROCEDURE PlotarComErro(val,dval:medida);
  BEGIN
    SetColor(cor[Ord(dval)]);
    Line(xa,Lim(ay[val]*(ponto[x-1]^.V[val]-ponto[x-1]^.V[dval])+by[val]),
         xb,Lim(ay[val]*(ponto[x]^.V[val]-ponto[x]^.V[dval])+by[val]));
    Line(xa,Lim(ay[val]*(ponto[x-1]^.V[val]+ponto[x-1]^.V[dval])+by[val]),
         xb,Lim(ay[val]*(ponto[x]^.V[val]+ponto[x]^.V[dval])+by[val]));
  END;

  PROCEDURE InicializarGrafico(x1,x2,y1,y2:REAL; xlog:BOOLEAN);
  VAR
    {ax,bx,}ay,by,t1,t2:REAL;
  BEGIN
    SetGraphMode(modo);
    SetFillStyle(emptyfill,0);
    SetTextStyle(SmallFont,HorizDir,4);
    RemoveSprite;
    ay:=(altura)/(y1-y2);
    by:=ymax-ay*y1;
    IF not xlog THEN BEGIN
      ax:=(xmax-xmin)/(x2-x1);
      bx:=xmin-ax*x1;
    END
    ELSE BEGIN
      ax:=(xmax-xmin)/(Ln(x2)-Ln(x1)); bx:=xmin-ax*Ln(x1)
    END;
    IF grade THEN BEGIN
      SetLineStyle(DottedLn,0,NormWidth);
      SetColor(cor[fraca]);
      IF xlog and (x2-x1>x1) THEN t1:=x1
      ELSE t1:=x2-x1;
      t1:=Exp(Ln(10)*Round(Ln(t1)/Ln(10)-0.499999));
      t2:=Round(x1/t1+0.5)*t1;
      WHILE t2<x2 DO
        IF xlog THEN BEGIN
          IF Round(t2/t1)=10 THEN BEGIN
            t1:=10*t1;
            SetColor(cor[media]);
          END;
          i:=Round(ax*Ln(t2)+bx);
          Line(i,ymin,i,ymax);
          t2:=t2+t1;
          SetColor(cor[fraca]);
        END
        ELSE BEGIN
          i:=Round(ax*t2+bx);
          Line(i,ymin,i,ymax);
          t2:=t2+t1
        END;
      t1:=y2-y1;
      t1:=Exp(Ln(10)*Round(Ln(t1)/Ln(10)-0.5));
      t2:=Round(y1/t1+0.5)*t1;
      WHILE t2<y2 DO BEGIN
        i:=Round(ay*t2+by);
        Line(xmin,i,xmax,i);
        t2:=t2+t1
      END;
      SetLineStyle(SolidLn,0,NormWidth)
    END;
    SetColor(cor[forte]);
    Rectangle(xmin,ymin,xmax,ymax);
  END;

PROCEDURE Analisar(f:REAL; tudo:BOOLEAN);
VAR
  i:INTEGER;
BEGIN
  WITH ponto[x]^ DO BEGIN
    IF not analisado THEN BEGIN  {Calcular M¢dulo,fase e sensibilidades}
      IF hertz THEN si:=2*PI*f ELSE si:=f;
      CalcularTudo;
      V[frq]:=f;
      V[mdl]:=10*Ln(Sqr(E1[Csaida])+Sqr(E2[Csaida]))/Ln10;
      IF tudo THEN BEGIN
        V[fas]:=Angle(E1[Csaida],E2[Csaida])*180/pi;
        CalcularSTs;
        V[tg]:=-d2/si;
        {Faixa dinÉmica}
        FOR i:=1 TO nos DO BEGIN
          t:=Sqrt(Sqr(E1[C[i]])+Sqr(E2[C[i]]));
          IF t>Maximo[i] THEN Maximo[i]:=t;
          IF t<Minimo[i] THEN Minimo[i]:=t
        END
      END
    END;
    IF tudo and ((not analisado) or novosdesvios) THEN BEGIN  {Calcular desvios}
      t1:=0; t2:=0;
      FOR e:=1 TO elementos DO BEGIN
        t1:=t1+Sqr((S1[e]-Desconto[e])*DP[e]);
        t2:=t2+Sqr(S2[e]*DP[e])
      END;
      IF normincl THEN BEGIN {Normalizar pela inclinaáÑo}
        IF analisado THEN CalcularSTs; {senÑo foi calculado acima}
        t1:=t1/(1+Sqr(d1));
        t2:=t2/(1+Sqr(d2));
      END;
      V[dm]:=20/Ln10*Sqrt(t1);
      V[df]:=180/Pi*Sqrt(t2);
    END;
    analisado:=TRUE
  END
END;

BEGIN
  sr:=0; dividir:=TRUE; polos:=FALSE; ok:=FALSE; kcor:=cor[1];
  REPEAT
    IF linear THEN dh:=(max[frq]-min[frq])/segm ELSE dh:=Ex(max[frq]/min[frq],1/segm);
    dx:=(xmax-xmin)/segm;
    centro:=segm div 2;
    FOR ii:=mdl TO df DO BEGIN
      ay[ii]:=(ymin-ymax)/(max[ii]-min[ii]);
      by[ii]:=altura-ay[ii]*min[ii]
    END;
    InicializarGrafico(min[frq],max[frq],min[sel],max[sel],not linear);
    IF KeyPressed THEN GoTo Atualizar;
    Escalas;
    SetViewPort(xmin,ymin,xmax,ymax,ClipOn);
   DeNovo:
    f:=min[frq]; x:=0; xatual:=0;
    REPEAT
      WITH ponto[x]^ DO BEGIN
        Analisar(f,TRUE);
        xb:=Round(x*dx); {+xmin}
        IF x>0 THEN BEGIN
          FOR ii:=mdl TO df DO
            IF plotar[ii] THEN BEGIN
              IF superpor THEN
                IF ii=mdl THEN PlotarComErro(mdl,dm)
                ELSE IF ii=fas THEN PlotarComErro(fas,df);
              SetColor(cor[Ord(ii)]);
              Line(xa,Lim(ay[ii]*ponto[x-1]^.V[ii]+by[ii]),
                   xb,Lim(ay[ii]*ponto[x]^.V[ii]+by[ii]));
            END
        END;
        xa:=xb
      END;
      xatual:=x;
      IF KeyPressed THEN GoTo Atualizar;
      IF linear THEN f:=f+dh ELSE f:=f*dh;
      x:=x+1;
    UNTIL x>segm;
    xatual:=x-1;
    novosdesvios:=FALSE;

    IF otimizar THEN BEGIN
      {Varrer resposta}
      r_atual:=1; pulos:=0; r_efetivas:=1;
      zsubindo:=TRUE; zsubia:=FALSE;
      asubindo:=TRUE; asubia:=FALSE;
      bsubindo:=TRUE; bsubia:=FALSE;
      FOR xx:=1 TO segm DO BEGIN
        zsubindo:=ponto[xx]^.V[mdl]>ponto[xx-1]^.V[mdl];
        asubindo:=ponto[xx]^.V[mdl]+ponto[xx]^.V[dm]>ponto[xx-1]^.V[mdl]+ponto[xx-1]^.V[dm];
        bsubindo:=ponto[xx]^.V[mdl]-ponto[xx]^.V[dm]>ponto[xx-1]^.V[mdl]-ponto[xx-1]^.V[dm];
        IF r_atual<=restricoes THEN WITH Espec[r_atual] DO BEGIN
          IF ((tipo='P') and (ponto[xx]^.V[frq]-1e-6>wk)) or
             ((erro='Z') and
              (((tipo='M') and zsubindo and not zsubia) or
               ((tipo='X') and not zsubindo and zsubia)
              )
             ) or
             ((erro='A') and {usa os maximos sem erro}
              (((tipo='M') and zsubindo and not zsubia) or
               ((tipo='X') and not zsubindo and zsubia)
              )
             ) or
             ((erro='B') and
              (((tipo='M') and bsubindo and not bsubia) or
               ((tipo='X') and not bsubindo and bsubia)
              )
             )
          THEN BEGIN {Achou restricao}
            IF tipo='P' THEN BEGIN
              IF refinar THEN BEGIN {refinar passagem}
                x:=segm+1;
                ponto[x]^.analisado:=FALSE;
                Analisar(wk,erro<>'Z');
              END
              ELSE x:=xx-1;
              dg:=0
            END
            ELSE BEGIN {Maximo ou minimo}
              IF refinar and (pulos=pular) THEN BEGIN {refinar extremo}
                wk:=ponto[xx]^.V[frq]; {Inicio da busca}
                delta:=ponto[xx-1]^.V[frq]-ponto[xx-2]^.V[frq]; {Assim para garantir que passa pelo ponto aproximado}
                k:=1; {Direcao da busca}
                ttt:=ponto[xx]^.V[mdl]; {Ganho atual}
                {IF erro='A' THEN ttt:=ttt+ponto[xx]^.V[dm]}
                IF erro='B' THEN ttt:=ttt-ponto[xx]^.V[dm];
                x:=segm+1; {Onde guardar os resultados temporarios}
                REPEAT
                  delta:=delta/2; k:=-k; {Reduz o passo e volta}
                  {
                  Bar(1,1,80,18);
                  OutTextXY(2,1,'df='+Sre(delta,6,-1));
                  OutTextXY(2,9,'fr='+Sre(wk,6,-1));
                  }
                  REPEAT {Procura extremo}
                    tt:=ttt;
                    wk:=wk+k*delta;
                    ponto[x]^.analisado:=FALSE;
                    Analisar(wk,erro<>'Z');
                    ttt:=ponto[x]^.V[mdl];
                    {IF erro='A' THEN ttt:=ttt+ponto[x]^.V[dm];}
                    IF erro='B' THEN ttt:=ttt-ponto[x]^.V[dm];
                  UNTIL (ttt>tt) xor (tipo='X');
                UNTIL delta<tolf;
              END
              ELSE BEGIN
                x:=xx-1;
                wk:=ponto[x]^.V[frq]; {So para lembrar onde}
              END;
              IF evitar_extremos THEN BEGIN
                {Busca o mais distante do extremo dos tres ultimos pontos}
                IF ponto[x]^.V[frq]>ponto[xx-1]^.V[frq] THEN k:=xx-2 ELSE k:=xx;
                dg:=ponto[k]^.V[mdl]-ponto[x]^.V[mdl];
                IF erro='B' THEN dg:=dg-ponto[k]^.V[dm]+ponto[x]^.V[dm];
                x:=k;
              END
              ELSE dg:=0;
            END;
            Inc(pulos);
            IF pulos>pular THEN BEGIN
              pulos:=0;
              {Montar equacao}
              WITH ponto[x]^ DO BEGIN
                k:=0;
                FOR e:=1 TO elementos DO WITH Elemento[e] DO BEGIN
                  IF (omodo=movel) THEN BEGIN
                    Inc(k);
                    A[r_efetivas,k]:=S1[e];
                  END
                  ELSE IF (omodo>0) THEN A[r_efetivas,k]:=A[r_efetivas,k]+S1[e];
                END;
                tt:=V[mdl];
                IF erro='A' THEN tt:=tt+V[dm]
                ELSE IF erro='B' THEN tt:=tt-V[dm];
                ek:=-tt-flat_loss;
                ttt:=ganho+dg-tt;
                {Testar validade da equacao}
                ok:=(ganho<>flat_loss) or (Abs(ttt)>tols);
                b[r_efetivas]:=Ln10/20*ttt;
                IF refinar THEN BEGIN
                  IF linear THEN k:=Round(ax*V[frq]+bx-xmin) ELSE k:=Round(ax*Ln(V[frq])+bx-xmin)
                END
                ELSE k:=Round(x*dx);
                IF ok THEN i:=5 ELSE i:=10;
                Circle(k,Lim(ay[mdl]*tt+by[mdl]),i)
              END;
              Inc(r_atual);
              IF ok THEN Inc(r_efetivas);
            END
          END;
        END
        ELSE Break;
        zsubia:=zsubindo;
        asubia:=asubindo;
        bsubia:=bsubindo
      END;
      Dec(r_efetivas);
      IF r_atual<=restricoes THEN BEGIN
        Beep;
        Bar(1,1,80,18);
        OutTextXY(2,1,'Faltam restricoes');
        GoTo Atualizar;
      END;
      IF apenas_localizar THEN BEGIN
        TextMode(80);
        WriteLn(tl,'[Restriáîes encontradas]:'#10);
        FOR i:=1 TO restricoes DO WITH Espec[i] DO BEGIN
          WriteLn(tl,'RestriáÑo [',i,']: [freq.]:',wk:6:4,' [Ganho]:',ek:7:4);
        END;
        WriteLn(tl,#10'[Toque uma tecla]...');
        r:=ReadKey;
        Exit
      END;
      IF cor[1]=cor[2] THEN cor[1]:=cor[3] ELSE cor[1]:=cor[2];
      {Resolver o sistema e atualizar valores:
      Se restricoes=incognitas: [A]x=b
      Se restricoes>incognitas: [At][A]x=[A]tb (minimos quadrados, nao implementado)
      Se restricoes<incognitas: [A][At]z=b, x=[At]z (minima norma 2 em x)}
      IF r_efetivas<incognitas THEN BEGIN
        {Calcula [At]}
        An:=A;
        FOR i:=1 TO r_efetivas DO
          FOR j:=1 TO incognitas DO
            At[j,i]:=An[i,j];
        {Calcula [A][At]}
        FOR i:=1 TO r_efetivas DO
          FOR j:=1 TO r_efetivas DO BEGIN
            A[i,j]:=0;
            FOR k:=1 TO incognitas DO A[i,j]:=A[i,j]+An[i,k]*At[k,j]
          END;
      END;
      {Resolve o sistema [A]x=b}
      det:=1;
      FOR i:=1 TO r_efetivas DO A[i,r_efetivas+1]:=b[i];
      FOR i:=1 TO r_efetivas DO BEGIN
        pivot:=0; k:=i;
        FOR l:=i TO r_efetivas DO
          IF ABS(A[l,i])>ABS(pivot) THEN BEGIN k:=l; pivot:=A[l,i] END;
        IF i<>k THEN BEGIN
          FOR l:=i TO r_efetivas+1 DO
            BEGIN tt:=A[i,l]; A[i,l]:=A[k,l]; A[k,l]:=tt END;
          det:=-det
        END;
        det:=det*pivot;
        IF Abs(pivot)<told THEN BEGIN
          Beep;
          Bar(1,1,80,18);
          OutTextXY(2,1,'Pivot '+Sri(i)+' (de '+Sri(r_efetivas)+') muito baixo');
          GoTo Atualizar
        END;
        FOR j:=r_efetivas+1 DOWNTO i+1 DO BEGIN
          A[i,j]:=A[i,j]/pivot; tt:=A[i,j];
          FOR l:=1 TO r_efetivas DO
            IF i<>l THEN
              A[l,j]:=A[l,j]-A[l,i]*tt;
        END
      END;
      IF Abs(det)<told THEN BEGIN
        Beep;
        Bar(1,1,80,18);
        OutTextXY(2,1,'Determinante muito baixo');
        GoTo Atualizar
      END;
      IF r_efetivas=incognitas THEN
        FOR i:=1 TO incognitas DO b[i]:=A[i,r_efetivas+1]
      ELSE
        {Correcao x=[At]z}
        FOR i:=1 TO incognitas DO BEGIN
          b[i]:=0;
          FOR j:=1 TO r_efetivas DO b[i]:=b[i]+At[i,j]*A[j,r_efetivas+1]
        END;
      {Atualizacao}
      {Normalizar variacoes pela maxima admissivel}
      me:=0;
      FOR k:=1 TO incognitas DO BEGIN
        IF usar_fator THEN b[k]:=b[k]*fator;
        IF Abs(b[k])>me THEN me:=Abs(b[k])
      END;
      Bar(1,1,80,18);
      OutTextXY(2,1,'er='+Sre(me,6,-1));
      OutTextXY(2,9,'dt='+Sre(det,6,-1));
      IF me>maxdelta THEN
        FOR k:=1 TO incognitas DO b[k]:=b[k]*maxdelta/me;
      {Atualizar valores}
      k:=0;
      FOR e:=1 TO elementos DO WITH Elemento[e] DO BEGIN
        IF omodo=movel THEN BEGIN
          Inc(k);
          {Isto assume que mudar o valor muda a estampa dos elementos. Checar fontes}
          valor:=valor*(1+b[k]);
        END
        ELSE IF omodo>0 THEN valor:=Elemento[omodo].valor
      END;
      ZerarGrafico;
      GoTo DeNovo;
    END;

   Atualizar:
    ok:=FALSE;
    cor[1]:=kcor; {Repoe cor normal}
    r:=UpKey;
    CASE r OF
      #0:BEGIN
           r:=ReadKey;
           CASE r of
             'H','P':IF plotar[sel] THEN BEGIN
                       d:=(max[sel]-min[sel])/2;
                       IF r='P' THEN d:=-d;
                       min[sel]:=min[sel]+d;
                       max[sel]:=max[sel]+d
                     END
                     ELSE GoTo Atualizar;
             'I','Q':BEGIN
                       IF r='Q' THEN BEGIN
                       IF sel<df THEN sel:=Succ(sel) ELSE sel:=mdl
                       END
                       ELSE IF sel>mdl THEN sel:=Pred(sel) ELSE sel:=df;
                       Cursor; Medir;
                       GoTo Atualizar
                     END;
             'K',#115:BEGIN
                   IF r='K' THEN dc:=1 ELSE dc:=10;
                   IF csr>=dc THEN csr:=csr-dc;
                   Cursor; Medir;
                   GoTo Atualizar
                 END;
             'M',#116:BEGIN
                   IF r='M' THEN dc:=1 ELSE dc:=10;
                   IF csr+dc<=xatual THEN csr:=csr+dc;
                   Cursor; Medir;
                   GoTo Atualizar
                 END;
             #82:plotar[sel]:=TRUE;
             #83:BEGIN
                   plotar[sel]:=FALSE;
                   sel:=mdl
                 END;
             ELSE GoTo Atualizar
           END
         END;
      {
      'F':plotar[fas]:=not plotar[fas];
      'T':plotar[tg]:=not plotar[tg];
      }
      '-':IF plotar[sel] THEN max[sel]:=2*(max[sel]-min[sel])+min[sel] ELSE GoTo Atualizar;
      '+':IF plotar[sel] THEN max[sel]:=(max[sel]-min[sel])/2+min[sel] ELSE GoTo Atualizar;
      'R':BEGIN
            IF linear THEN max[frq]:=2*(max[frq]-min[frq])+min[frq]
            ELSE max[frq]:=Sqr(max[frq])/min[frq];
            FOR j:=1 TO centro DO ponto[j]^:=ponto[j+j]^;
            FOR j:=centro+1 TO segm DO ponto[j]^.analisado:=FALSE;
            csr:=csr div 2;
          END;
      'A':BEGIN
            IF linear THEN max[frq]:=(max[frq]-min[frq])/2+min[frq]
            ELSE max[frq]:=Sqrt(min[frq]*max[frq]);
            FOR j:=centro DOWNTO 1 DO ponto[j+j]^:=ponto[j]^;
            FOR j:=0 TO centro-1 DO ponto[j+j+1]^.analisado:=FALSE;
            IF csr<=centro THEN csr:=csr*2 ELSE csr:=segm;
          END;
      '>','.':BEGIN
            IF linear THEN BEGIN
              d:=(max[frq]-min[frq])/2; min[frq]:=min[frq]+d; max[frq]:=max[frq]+d
            END
            ELSE BEGIN
              d:=Sqrt(max[frq]/min[frq]); min[frq]:=d*min[frq]; max[frq]:=d*max[frq]
            END;
            FOR j:=0 TO centro DO ponto[j]^:=ponto[j+centro]^;
            FOR j:=centro+1 TO segm DO ponto[j]^.analisado:=FALSE;
            IF csr>=centro THEN csr:=csr-centro ELSE csr:=0;
          END;
      '<',',':BEGIN
            IF linear THEN BEGIN
              d:=(max[frq]-min[frq])/2; min[frq]:=min[frq]-d; max[frq]:=max[frq]-d
            END
            ELSE BEGIN
              d:=Sqrt(max[frq]/min[frq]); min[frq]:=min[frq]/d; max[frq]:=max[frq]/d
            END;
            FOR j:=centro DOWNTO 0 DO ponto[j+centro]^:=ponto[j]^;
            FOR j:=0 TO centro-1 DO ponto[j]^.analisado:=FALSE;
            IF csr<=centro THEN csr:=csr+centro ELSE csr:=segm;
          END;
      'V':ImprimirTelaV;
      'H':ImprimirTelaH;
      'Q':IF yq=altura-56 THEN yq:=6 ELSE yq:=altura-56;
      'E':superpor:=not superpor;
      'G':grade:=not grade;
      ' ':BEGIN Cursor; GoTo Atualizar END;
      #27:ok:=TRUE;
      ^R:refinar:=not refinar;
      #13:;
      ELSE GoTo Atualizar
    END;
  UNTIL ok;
  mfvalido:=TRUE;
  pzvalido:=FALSE;
  TextMode(80)
END; {RespostaEmFrequencia}

PROCEDURE ApresentarMenu;
BEGIN
  WriteLn;
  WriteLn(tl,'[G]r†ficos de resposta em freqÅància');
  WriteLn(tl,'[E]scalas dos gr†ficos');
  WriteLn(tl,'[N]ormalizaáÑo pela inclinaáÑo');
  WriteLn(tl,'[D]esconto de sensibilidades');
  IF mfvalido THEN BEGIN
    WriteLn(tl,'[L]istar Sensibilidades');
    WriteLn(tl,'Fai[X]a dinÉmica');
    IF salvar THEN WriteLn(tl,'[S]alvar tabela do gr†fico');
  END;
  IF salvar THEN WriteLn(tl,'Inclu°r [C]oment†rio no relat¢rio');
  WriteLn(tl,'Sensibilidades dos [P]olos');
  WriteLn(tl,'Sensibilidades dos [Z]eros');
  WriteLn(tl,'[M]udar n¢ de sa°da');
  WriteLn(tl,'[V]ariabilidade dos parÉmetros');
  WriteLn(tl,'Abrir arquivo de [R]elat¢rio');
  WriteLn(tl,'D[I]ret¢rio');
  WriteLn(tl,'[T]olerÉncias e parÉmetros');
  WriteLn(tl,'Outra [A]n†lise; [F]im');
  WriteLn(tl,'[O]timizaáÑo do circuito');
END; {ApresentarMenu}

PROCEDURE SetarParametrosOtimizacao;
BEGIN
  WriteLn(tl,'[OtimizaáÑo por gradiente] (experimental):'#10);
  otimizar:=TRUE;
  WriteLn(tl,'[E]lementos [R]estriáîes [C]onfiguraáÑo [N]Ño otimizar');
  r:=UpKey;
  CASE r OF
    'E':BEGIN
      txt:=rede+'.opt';
      ok:=FALSE;
      Write(#10'Ler valores'); LerBool(ok);
      IF ok THEN BEGIN
        Write(tl,'Arquivo: '); EditarLinha(txt,WhereX,WhereY,1); WriteLn;
        Assign(arquivo,txt);
        {$I-} Reset(arquivo); {$I+}
        IF IOResult=0 THEN BEGIN
          Read(arquivo,r);
          IF r='e' THEN BEGIN
            ReadLn(arquivo,r,i);
            FOR e:=1 TO i DO WITH Elemento[e] DO BEGIN
              REPEAT Read(arquivo,r) UNTIL r=' ';
              ReadLn(arquivo,valor,omodo);
            END;
            WriteLn(tl,'[*] Arquivo lido');
          END
          ELSE WriteLn(tl,'[* Arquivo inv†lido]');
          Close(arquivo);
        END
        ELSE WriteLn(tl,'[* Arquivo inexistente]')
      END;
      REPEAT
        WriteLn(tl,#10'Modo:[',fixo,']=fixo, [',movel,']=vari†vel, <[n]>=c¢pia de valor, [-2]=editar:'#10);
        incognitas:=0;
        FOR e:=1 TO elementos DO WITH Elemento[e] DO
          IF not (nome[1] in ['Z','v','A','a','Q','q']) THEN BEGIN
            REPEAT
              Write(tl,'n: [',e,']; ',nome,':',valor:cm:dc,'; modo'); LerInt(omodo);
              IF omodo=-2 THEN BEGIN
                GoToXY(40,WhereY-1); Write('Valor'); LerReal(valor);
              END
            UNTIL (omodo>=-1) and (omodo<e) and ((omodo<=0) or (Elemento[omodo].omodo=movel));
            IF omodo=movel THEN Inc(incognitas);
          END;
        ok:=TRUE; Write(tl,#10'Confirma'); LerBool(ok);
      UNTIL ok;
      ok:=FALSE;
      Write(#10'Salvar valores'); LerBool(ok);
      IF ok THEN BEGIN
        Write(tl,'Arquivo: '); EditarLinha(txt,WhereX,WhereY,1); WriteLn;
        Assign(arquivo,txt);
        ReWrite(arquivo);
        WriteLn(arquivo,'e ',elementos);
        FOR e:=1 TO elementos DO WITH Elemento[e] DO
          WriteLn(arquivo,nome,' ',valor,' ',omodo);
        Close(arquivo);
        WriteLn(tl,'[*] Arquivo escrito');
      END;
    END;
    'R':BEGIN
      txt:=rede+'.rst';
      ok:=FALSE;
      Write(#10'Ler restriáîes'); LerBool(ok);
      IF ok THEN BEGIN
        Write(tl,'Arquivo: '); EditarLinha(txt,WhereX,WhereY,1); WriteLn;
        Assign(arquivo,txt);
        {$I-} Reset(arquivo); {$I+}
        IF IOResult=0 THEN BEGIN
          Read(arquivo,r);
          IF r='r' THEN BEGIN
            ReadLn(arquivo,r,restricoes);
            FOR i:=1 TO restricoes DO WITH Espec[i] DO BEGIN
              ReadLn(arquivo,tipo,r,erro,r,wk,ganho,pular);
            END;
            WriteLn(tl,'[*] Arquivo lido');
          END
          ELSE WriteLn(tl,'[* Arquivo inv†lido]');
          Close(arquivo);
        END
        ELSE WriteLn(tl,#10'[Arquivo inexistente]')
      END;
      REPEAT
        REPEAT
          Write(tl,#10']N£mero de restriáîes (max=[',incognitas,'])'); LerInt(restricoes);
        UNTIL restricoes<=incognitas;
        WriteLn(tl,#10'Entre com as [',restricoes,'] restriáîes em ordem de freqÅància:');
        WriteLn(tl,'Tipo = [M]°nimo, m†[X]imo ou [P]assagem; Erro = [A]cima, a[B]aixo ou [Z]ero');
        FOR i:=1 TO restricoes DO WITH Espec[i] DO BEGIN
          Write(tl,'RestriáÑo [',i,']; Tipo:[',tipo,']');
          REPEAT r:=UpKey UNTIL r in [#13,'M','X','P'];
          IF r<>#13 THEN BEGIN
            GoToXY(WhereX-1,WhereY); tipo:=r; Write(tl,'[',tipo,']');
          END;
          Write(tl,' Erro:[',erro,']');
          REPEAT r:=UpKey UNTIL r in [#13,'A','B','Z'];
          IF r<>#13 THEN BEGIN
            GoToXY(WhereX-1,WhereY); erro:=r; Write(tl,'[',erro,']');
          END;
          Write(' Ganho'); k:=WhereX; LerReal(ganho);
          GoToXY(60,WhereY-1);
          IF tipo='P' THEN BEGIN Write('FreqÅància'); LerReal(wk); pular:=0 END
          ELSE BEGIN Write('Pular'); LerInt(pular) END
        END;
        ok:=TRUE; Write(tl,#10'Confirma'); LerBool(ok);
      UNTIL ok;
      ok:=FALSE;
      Write(#10'Salvar restriáîes'); LerBool(ok);
      IF ok THEN BEGIN
        Write(tl,'Arquivo: '); EditarLinha(txt,WhereX,WhereY,1); WriteLn;
        Assign(arquivo,txt);
        ReWrite(arquivo);
        WriteLn(arquivo,'r ',restricoes);
        FOR i:=1 TO restricoes DO WITH Espec[i] DO
          WriteLn(arquivo,tipo,'_',erro,' ',wk,' ',ganho,' ',pular);
        Close(arquivo);
        WriteLn(tl,'[*] Arquivo escrito');
      END;
      IF descontar THEN
        WriteLn(tl,'[*] Certifique-se da validade do desconto de sensibilidades.');
    END;
    'C':BEGIN
          Write(#10'Apenas localizar restriáîes'); LerBool(apenas_localizar);
          Write(tl,'Refinar freqÅàncias ([^R] muda)'); LerBool(refinar);
          Write('PrecisÑo para freqÅàncias de extremo de ganho'); LerReal(tolf);
          IF apenas_localizar THEN evitar_extremos:=FALSE
          ELSE BEGIN
            Write('TolerÉncia p/erro de ganho na otimizaáÑo'); LerReal(tols);
            Write('TolerÉncia p/determinante na otimizaáÑo'); LerReal(told);
            Write('M†xima variaáÑo relativa de elemento (dx/x)'); LerReal(maxdelta);
            Write('AtenuaáÑo na M. T. P. ("flat-loss")'); LerReal(flat_loss);
            Write('Evitar gerar equaáîes nos extremos de ganho'); LerBool(evitar_extremos);
            Write(tl,'Usar fator de reduáÑo nos dx/x calculados'); LerBool(usar_fator);
            IF usar_fator THEN BEGIN
              Write('Fator multiplicativo para dx/x'); LerReal(fator);
            END
          END
        END;
     'N':otimizar:=FALSE;
    END;
    IF otimizar THEN ZerarGrafico;
  END;

{Programa Principal}
BEGIN
  DetectGraph(placa,modo);
  IF (placa=CGA) THEN modo:=CGAC1;
  IF paramcount=3 THEN BEGIN
    Val(ParamStr(2),placa,i);
    Val(ParamStr(3),modo,i);
  END;
  InitGraph(placa,modo,GetEnv('TPBGI'));
  IF placa>0 THEN BEGIN
    SetTextStyle(SmallFont,HorizDir,4);
    xmin:=GetMaxX-64*((GetMaxX-TextWidth('-999.99')) div 64);
    xmax:=GetMaxX;
    ymin:=0;
    ymax:=GetMaxY-TextHeight('X')-2;
    altura:=ymax-ymin;
    xq:=8; yq:=altura-56;
    IF placa<>1 THEN BEGIN
      cor[1]:=White;
      cor[2]:=Yellow;
      cor[3]:=LightRed;
      cor[4]:=LightGreen;
      cor[5]:=LightBlue;
      cor[6]:=Lightgray;
    END;
    InitSprite(cor[forte],cor[media]);
  END;
  TextMode(80);
  i:=GraphResult; IF i<>GrOk THEN ErroFatal(GraphErrorMsg(i));
  sel:=mdl; default:=0.05; salvar:=FALSE; segm:=78;
  FOR i:=1 TO MaxEsp DO WITH Espec[i] DO BEGIN tipo:='P'; erro:='Z'; Ganho:=0 END;
  IF ParamCount>0 THEN rede:=ParamStr(1) ELSE rede:='';
  Mark(p);
 Inicio:
  ClrScr;
  WriteLn(tl,'[…ÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕª');
  WriteLn(tl,'∫]  An†lise de Sensibilidades e otimizaáÑo [∫');
  WriteLn(tl,'»ÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕº]');
  WriteLn('Por: Antìnio Carlos MoreirÑo de Queiroz (acmq@coe.ufrj.br)');
  WriteLn('COPPE/DEEL - Universidade Federal do Rio de Janeiro');
  WriteLn('VersÑo ',versao,' - PrecisÑo ',precisao);
  WriteLn(tl,'Este programa Ç igual ao [Sensi], mas inclui um [otimizador] de ganho.');
  EntrarArquivo;
  LerCircuito;
  nsaida:=1; Csaida:=C[nsaida];
  EscolherSaida;
  WHILE TRUE DO BEGIN
    ApresentarMenu;
    r:=UpKey;
    ClrScr;
    CASE r OF
      'R':AbrirSaida;
      'G':RespostaEmFrequencia;
      'E':MudarEscalas;
      'V':MudarVariabilidades;
      'L':IF mfvalido THEN ListarSensibilidades;
      'X':IF mfvalido THEN ListarFaixa;
      'S':IF mfvalido and salvar THEN SalvarSmf;
      'C':IF salvar THEN BEGIN
            txt:='';
            Write('Coment†rio: '); EditarLinha(txt,WhereX,WhereY,1); WriteLn;
            WriteLn(relat,'- ',txt,#13#10)
          END;
      'D':MudarDesconto;
      'P':BEGIN pzvalido:=pzvalido and polos; polos:=TRUE; SensibilidadePolosZeros END;
      'Z':BEGIN pzvalido:=pzvalido and not polos; polos:=FALSE; SensibilidadePolosZeros END;
      'N':MudarNormalizacao;
      'A':BEGIN FecharSaida; GoTo Inicio END;
      'F':BEGIN FecharSaida; WriteLn(tl,#10'---[Fim]---'); Halt END;
      'M':EscolherSaida;
      'I':BEGIN Diretorio; r:=ReadKey END;
      'T':BEGIN
            Write('TolerÉncia p/admitÉncias e freqÅàncias'); LerReal(toly);
            Write('TolerÉncia p/impedÉncias e tensîes'); LerReal(tolz);
            Write('Campo numÇrico'); LerInt(cm);
            Write('Decimais'); LerInt(dc);
            pzvalido:=FALSE;
          END;
      'O':SetarParametrosOtimizacao;
      '#':BEGIN Write(#10'Usar condensaáÑo pivotal'); LerBool(condensar) END;
    END
  END;
END. {Sensi}
