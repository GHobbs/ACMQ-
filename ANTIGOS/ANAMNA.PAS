PROGRAM Anafil;
{******************************************************************************
 * An lise de filtros e circuitos lineares                                    *
 * Ant“nio Carlos Moreir„o de Queiroz - COPPE/UFRJ - 1987                     *
 * V. 1.2  de 01/11/87: Novo formato de entrada                               *
 * V. 1.3  de 08/04/88: Gr fico com fase, etc.                                *
 * V. 1.4  de 30/04/88: Constante complexa X inclu¡da                         *
 * V. 1.4a de 07/08/88: Mudados nomes: G->Y; I->G; M->N                       *
 * V. 1.5  de 15/09/88: Guarda tens„o de todos os n¢s                         *
 * V. 1.5a de 11/10/88: Corre‡„o na descri‡„o da VCCS                         *
 * V. 1.6  de 25/10/88: Escala log, Q,I, an lise em s dado, edi‡„o            *
 * V. 1.6a de 10/11/88: Incluida linha de transmiss„o LC                      *
 * V. 1.7  de 03/03/89: Turbo 5.0, VCCS com parasitas, impress„o              *
 * V. 1.7b de 11/03/89: C lculo em real, imag, faixa dinƒmica                 *
 * V. 1.8  de 18/10/89: Turbo 5.5, novo gr fico, referˆncia, f. din. correta  *
 * V. 1.8a de 26/10/89: Listagens limitadas de tens”es de n¢                  *
 * V. 1.8b de 17/11/89: N£mero maior de n¢s e elementos, precis„o extendida   *
 * V. 1.9  de 21/11/89: VCCS no formato Spice, BJT c/3 terminais              *
 * V. 1.9a de 17/02/90: Cursor com Ctrl                                       *
 * V. 2.0  de 14/03/90: Transformador n„o rec¡proco, edi‡„o de texto          *
 * V. 2.0a de 31/03/90: Wp e Wz mantidos ao fim de an lise                    *
 * V. 2.1  de 07/04/90: Girador invertido                                     *
 * V. 2.2  de 17/04/90: Estrutura de dados reformulada                        *
 * V. 2.2a de 08/06/90: Corrigido OTA (VCCS)                                  *
 * V. 2.2b de 26/06/90: Corrigido £ltimo tipo, at‚ reatƒncia                  *
 * V. 2.3  de 23/07/91: Mudada estrutura dos gr ficos; ViewPort; TPBGI        *
 * V. 2.4  de 16/08/91: Transistor MOS; .net                                  *
 * V. 2.4a de 07/11/91: Tabelas com #, corrigidos underflow e fim             *
 * V. 2.4b de 03/01/92: Cores sem EGA, Turbo 6.0                              *
 * V. 2.5  de 05/11/92: Analise Nodal Modificada, edicao melhor, Fonte Z      *
 * V. 2.5a de 18/11/92: Melhor tratamento dos nomes de arquivo                *
 ******************************************************************************}

{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}

USES Crt,DOS,Graph,Tela;

{$I seta.p}

CONST
  versao='2.5a de 18/11/92';
  MaxNos=45;
  MaxNos1=46;
  MaxEl=150;
  MaxNosAntes=70;
  tamnome=5;
  cor3:INTEGER=3;
  cor2:INTEGER=2;
  cor1:INTEGER=1;
  segmax=640;
  minreal= 1e-19;

TYPE
  resposta=ARRAY[1..MaxNos1] OF
  RECORD
    re,im:REAL
  END;
  componente=(Resistor,Capacitor,Indutor,FonteI,FonteZ,Amplificador,AmpOp,
              Girador,VCCS,Transformador,Transistor,MOS,URC,LinhaLC,Reatancia,
              FonteV,VCVS,CCCS,CCVS);
CONST
  biblioteca:ARRAY[componente] of RECORD
                                    letra:CHAR;
                                    nnos:BYTE;
                                    nmno:ARRAY[1..4] of STRING[2];
                                    nval:BYTE;
                                    nmval:ARRAY[1..4] of STRING[3];
                                  END
  =(
    (letra:'R'; nnos:2; nmno:('a','b','',''); nval:1; nmval:('R','','','')),
    (letra:'C'; nnos:2; nmno:('a','b','',''); nval:1; nmval:('C','','','')),
    (letra:'L'; nnos:2; nmno:('a','b','',''); nval:1; nmval:('L','','','')),
    (letra:'I'; nnos:2; nmno:('I+','I-','',''); nval:1; nmval:('I','','','')),
    (letra:'Z'; nnos:2; nmno:('V-','V+','',''); nval:2; nmval:('Rs','V','','')),
    (letra:'A'; nnos:3; nmno:('-','+','s',''); nval:2; nmval:('GB','Rs','','')),
    (letra:'O'; nnos:3; nmno:('e1','e2','s',''); nval:0; nmval:('','','','')),
    (letra:'Y'; nnos:4; nmno:('11','12','21','22'); nval:1; nmval:('Rg','','','')),
    (letra:'G'; nnos:4; nmno:('I+','I-','V+','V-'); nval:3; nmval:('Gm','Wp','Wz','')),
    (letra:'N'; nnos:4; nmno:('11','12','21','22'); nval:4; nmval:('L11','L22','M12','M21')),
    (letra:'Q'; nnos:3; nmno:('c','b','e',''); nval:4; nmval:('hfe','hie','hre','hoe')),
    (letra:'M'; nnos:3; nmno:('d','g','s',''); nval:2; nmval:('Gm','Gds','','')),
    (letra:'U'; nnos:3; nmno:('a','b','c',''); nval:2; nmval:('R','C','','')),
    (letra:'T'; nnos:3; nmno:('a','b','c',''); nval:2; nmval:('Zo','T','','')),
    (letra:'X'; nnos:2; nmno:('a','b','',''); nval:1; nmval:('X','','','')),
    (letra:'V'; nnos:2; nmno:('a','b','',''); nval:1; nmval:('V','','','')),
    (letra:'E'; nnos:4; nmno:('V+','V-','v+','v-'); nval:1; nmval:('Av','','','')),
    (letra:'F'; nnos:4; nmno:('I+','I-','i+','i-'); nval:1; nmval:('Ai','','','')),
    (letra:'H'; nnos:4; nmno:('V+','V-','i+','i-'); nval:1; nmval:('Rm','','',''))
    );
VAR
  cp:componente;
  ponto:ARRAY[0..segmax] OF ^resposta;
  calculado:ARRAY[0..segmax] OF BOOLEAN;
  Yr,Yi:ARRAY[0..MaxNos,0..MaxNos1] OF REAL;
  C,L:ARRAY[0..MaxNosAntes] OF INTEGER;
  elemento:ARRAY[1..MaxEl] OF
  RECORD
    tipo:componente;
    nome:STRING[tamnome];
    no:ARRAY[1..6] of BYTE;
    val:ARRAY[1..4] of REAL
  END;
  x1,x2,y1,y2,Imag,tr,ti,t,t1,t2,ta,tb,sr,si,Wp,Wz,Go,Gin,Co,Cin,refax,refbx:REAL;
  saida,dx,refdx,refxa,refsaida,i,j,k,nos,nosantes,numero,nosmesmo,a1,b1,c1:INTEGER;
  modo,placa,xq,yq,xmin,xmax,segm,mx1,mx2,mx3,ymin,ymax:INTEGER;
  referencia,plotarfase,grade,lerWzWp,ok,hertz,linear:BOOLEAN;
  txt:STRING;
  rede,refrede:NameStr;
  td:DirStr;
  te:ExtStr;
  arquivo:TEXT;
  r:CHAR;

PROCEDURE Espera(i:INTEGER);
BEGIN
  IF i and 15=0 THEN BEGIN
    WriteLn('Mais...');
    r:=ReadKey
  END
END;

FUNCTION Noj(n:INTEGER):STRING;
BEGIN
  IF n>nosmesmo THEN Noj:='j:  ' ELSE Noj:='No: '
END;

FUNCTION Sri(x:INTEGER):STRING;
VAR
  tmp:STRING;
BEGIN
  Str(x,tmp);
  Sri:=tmp
END;

PROCEDURE ErroFatal(texto:STRING);
BEGIN
  WriteLn(tl,#10'[Erro]: '+texto);
  WriteLn(#10'Toque uma tecla...');
  r:=ReadKey;
  Halt
END;

FUNCTION Cmult(x1,x2,y1,y2:REAL):REAL;
BEGIN
  Cmult:=x1*y1-x2*y2;
  Imag:=x1*y2+x2*y1
END; {Cmult}
  
FUNCTION Cdiv(x1,x2,y1,y2:REAL):REAL;
  VAR
    d:REAL;
BEGIN
  d:=Sqr(y1)+Sqr(y2);
  Cdiv:=(x1*y1+x2*y2)/d;
  Imag:=(x2*y1-x1*y2)/d
END;
  
FUNCTION Csqrt(a,b:REAL):REAL;
  VAR
    mdl,ang:REAL;
BEGIN
  IF a=0 THEN BEGIN
    ang:=pi/4;
    IF b<0 THEN ang:=-ang
  END
  ELSE BEGIN
    ang:=ArcTan(b/a);
    IF a<0 THEN
      IF b>0 THEN ang:=ang-pi
      ELSE ang:=ang+pi;
    ang:=ang/2
  END;
  mdl:=Sqrt(Sqrt(Sqr(a)+Sqr(b)));
  Csqrt:=mdl*Cos(ang);
  Imag:=mdl*Sin(ang)
END; {Csqrt}

FUNCTION Ex(x:REAL;t:REAL):REAL;
BEGIN Ex:=Exp(t*Ln(x)) END;
  
PROCEDURE ResolverSistema;
  VAR
    t,tr,ti,qr,qi:REAL;
    i,j,k,m:INTEGER;
BEGIN
  FOR i:=1 TO nos DO BEGIN
    tr:=0; ti:=0; m:=i;
    FOR k:=i TO nos DO
      IF Abs(Yr[k,i])+Abs(Yi[k,i])>Abs(tr)+Abs(ti) THEN BEGIN
        m:=k;
        tr:=Yr[k,i];
        ti:=Yi[k,i]
      END;
    IF i<>m THEN BEGIN
      FOR k:=i TO nos+1 DO BEGIN
        t:=Yr[i,k];
        Yr[i,k]:=Yr[m,k];
        Yr[m,k]:=t;
        t:=Yi[i,k];
        Yi[i,k]:=Yi[m,k];
        Yi[m,k]:=t
      END
    END;
    FOR j:=nos+1 DOWNTO i+1 DO BEGIN
      t:=tr*tr+ti*ti;
      IF t=0 THEN BEGIN
        TextMode(80);
        ErroFatal('Sistema de eq. nodais singular')
      END;
      qr:=(Yr[i,j]*tr+Yi[i,j]*ti)/t;
      qi:=(Yi[i,j]*tr-Yr[i,j]*ti)/t;
      Yi[i,j]:=qi;
      Yr[i,j]:=qr;
      FOR k:=1 TO nos DO
        IF i<>k THEN BEGIN
          Yr[k,j]:=Yr[k,j]-Cmult(Yr[k,i],Yi[k,i],qr,qi);
          Yi[k,j]:=Yi[k,j]-Imag
        END
    END
  END;
END; {ResolverSistema}

PROCEDURE TransAdmitancia(a,b:REAL; n1,n2,n3,n4:INTEGER);
BEGIN
  IF a<>0 THEN BEGIN
    Yr[L[n1],C[n3]]:=Yr[L[n1],C[n3]]+a;
    Yr[L[n2],C[n4]]:=Yr[L[n2],C[n4]]+a;
    Yr[L[n1],C[n4]]:=Yr[L[n1],C[n4]]-a;
    Yr[L[n2],C[n3]]:=Yr[L[n2],C[n3]]-a
  END;
  IF b<>0 THEN BEGIN
    Yi[L[n1],C[n3]]:=Yi[L[n1],C[n3]]+b;
    Yi[L[n2],C[n4]]:=Yi[L[n2],C[n4]]+b;
    Yi[L[n1],C[n4]]:=Yi[L[n1],C[n4]]-b;
    Yi[L[n2],C[n3]]:=Yi[L[n2],C[n3]]-b
  END
END; {TransAdmitancia}

PROCEDURE Admitancia(a,b:REAL; n1,n2:INTEGER);
BEGIN
  TransAdmitancia(a,b,n1,n2,n1,n2);
END; {Admitancia}

PROCEDURE Corrente(I:REAL; a,b:INTEGER);
BEGIN
  Yr[L[a],nos+1]:=Yr[L[a],nos+1]-I;
  Yr[L[b],nos+1]:=Yr[L[b],nos+1]+I;
END;

PROCEDURE Gyrator(G:REAL; a,b,c,d:INTEGER);
BEGIN
  TransAdmitancia(G,0,a,b,c,d);
  TransAdmitancia(G,0,d,c,a,b)
END;

PROCEDURE MontarSistema;
BEGIN
  FOR i:=0 TO nos DO
    FOR j:=0 TO nos+1 DO BEGIN Yr[i,j]:=0; Yi[i,j]:=0 END;
  FOR i:=1 to numero DO
  WITH elemento[i] DO BEGIN
    CASE tipo OF
      Resistor:Admitancia(1/val[1],0,no[1],no[2]);
      Indutor:BEGIN
          t:=val[1]*(Sqr(sr)+Sqr(si));
          Admitancia(sr/t,-si/t,no[1],no[2])
        END;
      Capacitor:Admitancia(sr*val[1],si*val[1],no[1],no[2]);
      Amplificador:BEGIN
          { Y12=-GB/sRo; Y22=1/Ro }
          Admitancia(1/val[2],0,no[3],0);
          t:=val[1]/val[2]/(Sqr(sr)+Sqr(si));
          TransAdmitancia(t*sr,-t*si,0,no[3],no[2],no[1]);
        END;
      VCCS:BEGIN
             t:=val[1]*val[2]/val[3];
             tr:=t*Cdiv(val[3]+sr,si,val[2]+sr,si);
             TransAdmitancia(tr,t*Imag,no[1],no[2],no[3],no[4]);
             Admitancia(Gin,0,no[3],no[4]);
             Admitancia(Go,0,no[1],no[2]);
             Admitancia(sr*Cin,si*Cin,no[3],no[4]);
             Admitancia(sr*Co,si*Co,no[1],no[2]);
           END;
      FonteZ:BEGIN {Fonte com resistor s‚rie}
          Corrente(val[2]/val[1],no[1],no[2]);
          Admitancia(1/val[1],0,no[1],no[2])
        END;
      FonteI:Corrente(val[1],no[1],no[2]); {Fonte de corrente}
      Girador:
          { Y12=1/R Y21=-1/R }
          Gyrator(1/val[1],no[1],no[2],no[3],no[4]);
      Transformador:BEGIN
          { Y11=L2/sDet(L) }
          { Y22=L1/sDet(L) }
          { Y12=-M12/sDet(L) }
          { Y21=-M21/sDet(L) }
          t:=(val[1]*val[2]-val[3]*val[4])*(Sqr(sr)+Sqr(si));
          t1:=val[2]/t;  {Y11}
          Admitancia(t1*sr,-t1*si,no[1],no[2]);
          t1:=val[1]/t;  {Y22}
          Admitancia(t1*sr,-t1*si,no[3],no[4]);
          t1:=-val[3]/t; {Y12}
          TransAdmitancia(t1*sr,-t1*si,no[1],no[2],no[3],no[4]);
          t1:=-val[4]/t; {Y21}
          TransAdmitancia(t1*sr,-t1*si,no[3],no[4],no[1],no[2]);
        END;
      Transistor:BEGIN
          Admitancia(1/val[2],0,no[2],no[3]); {hie}
          Admitancia(val[4],0,no[1],no[3]);   {hoe}
          TransAdmitancia(val[1]/val[2],0,no[1],no[3],no[2],no[3]); {hfe/hie}
          TransAdmitancia(val[3]/val[2],0,no[3],no[2],no[1],no[3]); {hre/hie}
          TransAdmitancia(val[3]*val[1]/val[2],0,no[1],no[3],no[3],no[1]); {hre*hfe/hie}
        END;
      MOS:BEGIN
            Transadmitancia(val[1],0,no[1],no[3],no[2],no[3]); {Gm}
            Admitancia(val[2],0,no[1],no[3]) {Gds}
          END;
      URC:BEGIN
          { Y11=Y22= (û(sCR)/R)Coth(û(sRC)) }
          { Y12=Y21=-(û(sRC)/R)Csch(û(sRC)) }
          t:=val[1]*val[2];         {RC}
          tr:=Csqrt(t*sr,t*si); {à=Re[û(sRC)]}
          ti:=Imag;             {á=Im[û(sRC)]}
          t:=Exp(tr);           {e^à}
          t1:=Cos(ti);          {Cosá}
          t2:=Sin(ti);          {Sená}
          ta:=Cdiv(tr,ti,t1*(t-1/t),t2*(t+1/t))/val[1];
          tb:=Imag/val[1];        {(x/R)/(e^x-e^-x)}
          tr:=-2*ta; ti:=-2*tb;
          TransAdmitancia(tr,ti,no[3],no[2],no[1],no[2]);
          TransAdmitancia(tr,ti,no[1],no[2],no[3],no[2]);
          tr:=Cmult(ta,tb,t1*(t+1/t),t2*(t-1/t));
          ti:=Imag;
          Admitancia(tr,ti,no[1],no[2]);
          Admitancia(tr,ti,no[2],no[3])
        END;
      LinhaLC:BEGIN
          { Y11=Y22= (1/Zo)Coth(sT) }
          { Y12=Y21= (1/Zo)Csch(sT) }
          tr:=sr*val[2];          {à=Re(s)T}
          ti:=si*val[2];          {á=Im(s)T}
          t:=Exp(tr);             {e^à}
          t1:=Cos(ti);            {Cosá}
          t2:=Sin(ti);            {Sená}
          ta:=Cdiv(1/val[1],0,t1*(t-1/t),t2*(t+1/t));
          tb:=Imag;               {(1/Zo)/(e^x-e^-x)}
          tr:=-2*ta; ti:=-2*tb;
          TransAdmitancia(tr,ti,no[3],no[2],no[1],no[2]);
          TransAdmitancia(tr,ti,no[1],no[2],no[3],no[2]);
          tr:=Cmult(ta,tb,t1*(t+1/t),t2*(t-1/t));
          ti:=Imag;
          Admitancia(tr,ti,no[1],no[2]);
          Admitancia(tr,ti,no[3],no[2])
        END;
     Reatancia:Admitancia(0,-1/val[1],no[1],no[2]);
     FonteV:BEGIN
              Gyrator(1,no[1],no[2],no[5],0);
              Corrente(val[1],no[5],0)
            END;
     VCVS:BEGIN
            Gyrator(1,no[1],no[2],no[5],0);
            TransAdmitancia(val[1],0,no[5],0,no[3],no[4])
          END;
     CCCS:BEGIN
            TransAdmitancia(val[1],0,no[1],no[2],no[5],0);
            Gyrator(1,no[3],no[4],no[5],0)
          END;
     CCVS:BEGIN
            TransAdmitancia(val[1],0,no[6],0,no[5],0);
            Gyrator(1,no[1],no[2],no[6],0);
            Gyrator(1,no[3],no[4],no[5],0)
          END
    END
  END
END; {MontarSistema}

PROCEDURE LerCircuito;
VAR
  leutudo:BOOLEAN;
LABEL Achou;

  PROCEDURE TestarNos;
  BEGIN
    IF nosantes>MaxNosAntes THEN ErroFatal('O m ximo n£mero de n¢s ‚ ['+Sri(MaxNosAntes)+']');
  END;

BEGIN
  ReadLn(arquivo,nosantes); nos:=nosantes; nosmesmo:=nos;
  FOR i:=0 TO MaxNosAntes DO BEGIN C[i]:=i; L[i]:=i END;
  WriteLn(tl,#10'N£mero de n¢s: [',nosmesmo,']');
  TestarNos;
  WriteLn(tl,#10'[Descri‡„o do circuito:]'#10);
  numero:=1;
  REPEAT
    IF numero>MaxEl THEN ErroFatal('O m ximo n£mero de elementos efetivos ‚ ['+Sri(MaxEl)+']');
    WITH elemento[numero] DO BEGIN
      nome:='';
      REPEAT
        Read(arquivo,r);
        IF r<>' ' THEN nome:=nome+UpCase(r)
      UNTIL (r=' ') or (Length(nome)=tamnome);
      nome[1]:=UpCase(nome[1]);
      Write(tl,'[',nome,']: ');
      FOR cp:=Resistor TO CCVS DO
        WITH biblioteca[cp] DO
          IF nome[1]=letra THEN BEGIN
            leutudo:=TRUE;
            tipo:=cp;
            FOR i:=1 TO nnos DO Read(arquivo,no[i]);
            FOR i:=1 TO nval DO
              IF not SeekEoln(arquivo) THEN Read(arquivo,val[i])
              ELSE leutudo:=FALSE;
            ReadLn(arquivo);
            { Casos especiais }
            CASE tipo OF
              FonteZ:IF not leutudo THEN val[2]:=1;
              Transformador: IF not leutudo THEN val[4]:=val[3];
              VCCS:IF not leutudo THEN BEGIN val[2]:=Wp; val[3]:=Wz END;
              FonteV,VCVS,CCCS:BEGIN
                Inc(nosantes); Inc(nos);
                TestarNos;
                no[5]:=nosantes;
                Write(tl,'[',nosantes,'](j) ')
              END;
              CCVS:BEGIN
                Inc(nosantes,2); Inc(nos,2);
                TestarNos;
                no[5]:=nosantes-1;
                no[6]:=nosantes;
                Write(tl,'[',no[5],'](j1) [',no[6],'](j2) ')
              END
            END;
            FOR i:=1 TO nnos DO Write(tl,'[',no[i],'](',nmno[i],') ');
            FOR i:=1 TO nval DO Write(nmval[i],':',Cpct(val[i]),' ');
            WriteLn;
            GoTo Achou
          END;
      ErroFatal('Elemento desconhecido');
     Achou:
      IF tipo<>AmpOp THEN Inc(numero)
      ELSE BEGIN
        IF (C[no[1]]>C[no[2]]) THEN BEGIN a1:=C[no[2]]; b1:=C[no[1]] END
        ELSE BEGIN a1:=C[no[1]]; b1:=C[no[2]] END;
        c1:=L[no[3]];
        IF (a1=b1) OR (c1=0) THEN ErroFatal('Circuito inv lido');
        FOR i:=1 TO MaxNosAntes DO BEGIN
          IF C[i]=b1 THEN C[i]:=a1;
          IF C[i]>b1 THEN Dec(C[i]);
          IF L[i]=c1 THEN L[i]:=0;
          IF L[i]>c1 THEN Dec(L[i])
        END;
        Dec(nos)
      END;
    END;
    Espera(numero)
  UNTIL SeekEof(arquivo);
  Close(arquivo);
  Dec(numero);
  WriteLn(tl,#10'N£mero de elementos efetivos: [',numero,']');
  WriteLn(tl,'N£mero de vari veis independentes: [',nos,']');
  IF nos>MaxNos THEN ErroFatal('O m ximo de (n£mero de n¢s+correntes-n£mero de a. o. ideais) ‚ ['+Sri(MaxNos)+']');
  WriteLn;
END; {LerCircuito}

PROCEDURE FazerGrafico;
  VAR
    ax,bx,aa,ba,aw,bw,ay,by,af,bf,d:REAL;
    xg,xa,xant,xatual,mg,ma,fg,fa,resposta,csaida,dc:INTEGER;
  CONST
    unid:ARRAY[BOOLEAN] OF STRING[5]=('rad/s','Hz');
    LABEL
    Ler,Menu,Horizontal,Vertical,Plotar;

  FUNCTION Modulo(r,i:REAL):REAL;
  BEGIN
    IF Abs(r)<minreal THEN r:=minreal;
    Modulo:=4.34294481903252*Ln(Sqr(r)+Sqr(i));
  END;

  FUNCTION Fase(r,i:REAL):REAL;
  BEGIN
    IF Abs(r)<minreal THEN r:=minreal;
    t:=Arctan(i/r)*180/Pi;
    IF r<0 THEN
      IF i>0 THEN t:=180+t ELSE t:=t-180;
    Fase:=t
  END;

  FUNCTION Frequencia(x:INTEGER):REAL; {¡ndice -> w}
  BEGIN
    IF linear THEN Frequencia:=(x-bf)/af
    ELSE Frequencia:=Exp((x-bf)/af)
  END;

  PROCEDURE Grafico;
    LABEL Atualizar;

    FUNCTION LimX(x:REAL):INTEGER; {w -> pixel}
    BEGIN
      IF NOT linear THEN x:=Ln(x);
      LimX:=Round(aw*x+bw);
    END;

    FUNCTION Limy(y:REAL):INTEGER; {ganho -> pixel}
    BEGIN
      y:=ay*y+by;
      IF y>5000 THEN Limy:=5000
      ELSE IF y<-4000 THEN Limy:=-4000
      ELSE Limy:=Round(y)
    END;

    FUNCTION Limyc(y:REAL):INTEGER; {ganho -> pixel p/cursor}
    BEGIN
      y:=ay*y+by;
      IF y>ymax-ymin THEN Limyc:=ymax-ymin
      ELSE IF y<0 THEN Limyc:=0
      ELSE Limyc:=Round(y)
    END;

    PROCEDURE Medir;
    BEGIN
      xg:=0;
      SetLineStyle(SolidLn,0,NormWidth);
      REPEAT
        WITH ponto[xg]^[Csaida] DO BEGIN
          PutSprite(Round(ax*xg+bx),Limyc(Modulo(re,im)));
          SetColor(cor3);
          Bar(xq-1,yq+1,xq+106,yq+35);
          Rectangle(xq-2,yq,xq+107,yq+36);
          SetColor(cor1);
          OutTextXY(xq,yq,rede+' - no '+Sri(saida));
          Str(Frequencia(xg):12,txt); OutTextXY(xq,yq+8,txt+' '+unid[hertz]);
          Str(Modulo(re,im):13:8,txt); OutTextXY(xq,yq+16,txt+' dB');
          Str(Fase(re,im):13:8,txt); OutTextXY(xq,yq+24,txt+' gr');
          r:=UpKey;
          IF r=#0 THEN CASE ReadKey OF
            #116:BEGIN dc:=16*dx; IF (xg<=xa-dc) THEN IF calculado[xg+dc] THEN xg:=xg+dc END;
            #115:BEGIN dc:=16*dx; IF (xg>=dc) THEN IF calculado[xg-dc] THEN xg:=xg-dc END;
            'M':BEGIN dc:=dx; IF (xg<=xa-dc) THEN IF calculado[xg+dc] THEN xg:=xg+dc END;
            'K':BEGIN dc:=dx; IF (xg>=dc) THEN IF calculado[xg-dc] THEN xg:=xg-dc END;
          END
        END
      UNTIL (r=' ') or (r=#27);
    END;

    PROCEDURE MudaPonto(destino,origem:INTEGER);
      VAR
        i:INTEGER;
    BEGIN
      FOR i:=1 TO nos DO ponto[destino]^[i]:=ponto[origem]^[i];
    END;

  BEGIN
    REPEAT
      IF (x1<=0) or (x2<=0) THEN linear:=TRUE;
      IF (x1>=x2) or (ymin>=ymax) THEN grade:=FALSE;
      SetGraphMode(modo);
      SetFillStyle(emptyfill,0);
      SetTextStyle(smallfont,horizdir,4);
      Str(y2:7:2,txt);
      OutTextXY(xmin-TextWidth(txt),ymin,txt);
      Str(y1:7:2,txt);
      OutTextXY(xmin-TextWidth(txt),ymax-8,txt);
      Str(x1:11,txt);
      OutTextXY(xmin,ymax,txt);
      Str(x2:11,txt);
      OutTextXY(xmax-TextWidth(txt),ymax,txt);
      txt:='dB ';
      OutTextXY(xmin-TextWidth(txt),(ymax+ymin) div 2,txt);
      OutTextXY((xmax+xmin-TextWidth(unid[hertz])) div 2,ymax,unid[hertz]);
      OutTextXY(0,16,rede);
      OutTextXY(0,24,Noj(saida)+Sri(saida));
      OutTextXY(0,ymax-24,'R:'+Sri(dx));
      IF referencia THEN BEGIN
        SetColor(cor1);
        OutTextXY(0,40,refrede);
        OutTextXY(0,48,Noj(refsaida)+Sri(refsaida));
      END;
      SetViewPort(xmin,ymin,xmax,ymax,ClipOn);
      ay:=(ymin-ymax)/(y2-y1); by:=ymax-ymin-ay*y1;
      ax:=(xmax-xmin)/segm; bx:=0;
      IF linear THEN BEGIN
        aw:=(xmax-xmin)/(x2-x1); bw:=-aw*x1;
        af:=segm/(x2-x1); bf:=-af*x1
      END
      ELSE BEGIN
        aw:=(xmax-xmin)/(Ln(x2/x1)); bw:=-aw*Ln(x1);
        af:=segm/Ln(x2/x1); bf:=-af*Ln(x1);
      END;
      IF grade THEN BEGIN
        SetLineStyle(DottedLn,0,NormWidth);
        SetColor(cor2);
        IF not linear and (x2-x1>x1) THEN t1:=x1
        ELSE t1:=x2-x1;
        t1:=Exp(Ln(10)*Round(Ln(t1)/Ln(10)-0.499999));
        t2:=Round(x1/t1+0.5)*t1;
        WHILE t2<x2 DO
          IF not linear THEN BEGIN
            IF Round(t2/t1)=10 THEN BEGIN
              t1:=10*t1;
              SetColor(cor1);
            END;
            i:=LimX(t2);
            Line(i,0,i,ymax-ymin);
            t2:=t2+t1;
            SetColor(cor2);
          END
          ELSE BEGIN
            i:=LimX(t2);
            Line(i,0,i,ymax-ymin);
            t2:=t2+t1
          END;
        t1:=y2-y1;
        t1:=Exp(Ln(10)*Round(Ln(t1)/Ln(10)-0.5));
        t2:=Round(y1/t1+0.5)*t1;
        WHILE t2<y2 DO BEGIN
          i:=LimY(t2);
          Line(0,i,xmax-xmin,i);
          t2:=t2+t1
        END;
        SetLineStyle(SolidLn,0,NormWidth)
      END;
      SetColor(cor3);
      Rectangle(0,0,xmax-xmin,ymax-ymin);
      RemoveSprite;
      IF KeyPressed THEN GoTo Atualizar;
      IF referencia THEN BEGIN
        SetColor(cor1);
        xg:=0;
        WHILE xg<=refxa DO BEGIN
          xatual:=Round(refax*xg+refbx);
          WITH ponto[xg]^[MaxNos1] DO BEGIN
            mg:=Limy(Modulo(re,im));
            fg:=Round(aa*Fase(re,im)+ba);
            IF xg>0 THEN BEGIN
              IF plotarfase THEN BEGIN
                SetLineStyle(DottedLn,0,NormWidth);
                Line(xant,fa,xatual,fg);
                SetLineStyle(SolidLn,0,NormWidth)
              END;
              Line(xant,ma,xatual,mg)
            END;
            ma:=mg;
            fa:=fg
          END;
          xant:=xatual;
          xg:=xg+refdx
        END
      END;
      SetColor(cor3);
      xg:=0;
      WHILE xg<=segm DO BEGIN
        xatual:=Round(ax*xg+bx);
        IF NOT calculado[xg] THEN BEGIN
          si:=Frequencia(xg);
          IF hertz THEN si:=si*2*pi;
          sr:=0;
          MontarSistema;
          ResolverSistema;
          FOR i:=1 TO nos DO BEGIN
            ponto[xg]^[i].re:=Yr[i,resposta];
            ponto[xg]^[i].im:=Yi[i,resposta];
          END;
          calculado[xg]:=TRUE
        END;
        WITH ponto[xg]^[Csaida] DO BEGIN
          mg:=Limy(Modulo(re,im));
          fg:=Round(aa*Fase(re,im)+ba);
          IF xg>0 THEN BEGIN
            IF plotarfase THEN BEGIN
              SetLineStyle(DottedLn,0,NormWidth);
              Line(xant,fa,xatual,fg);
              SetLineStyle(SolidLn,0,NormWidth)
            END;
            Line(xant,ma,xatual,mg)
          END;
          ma:=mg;
          fa:=fg
        END;
        xant:=xatual;
        xa:=xg;
        IF KeyPressed THEN GoTo Atualizar;
        xg:=xg+dx;
      END;
      Atualizar:
      r:=UpKey;
      CASE r OF
      '>','.':REPEAT
          IF saida<nosantes THEN saida:=saida+1 ELSE saida:=1;
          Csaida:=C[saida];
        UNTIL Csaida<>0;
      '<',',':REPEAT
          IF saida>0 THEN saida:=saida-1 ELSE saida:=nosantes;
          Csaida:=C[saida];
        UNTIL Csaida<>0;
      'X':IF dx>1 THEN dx:=dx div 2 ELSE dx:=16;
      '-':y2:=2*(y2-y1)+y1;
      '+':y2:=(y2-y1)/2+y1;
      'R':BEGIN
          IF linear THEN x2:=2*(x2-x1)+x1
          ELSE x2:=Sqr(x2)/x1;
          FOR j:=0 TO mx2 DO BEGIN
            xg:=2*j;
            MudaPonto(j,xg);
            calculado[j]:=calculado[xg]
          END;
          FOR j:=mx2+1 TO segm DO calculado[j]:=FALSE
        END;
      'A':BEGIN
          IF linear THEN x2:=(x2-x1)/2+x1
          ELSE x2:=Sqrt(x2*x1);
          FOR j:=mx2 DOWNTO 0 DO BEGIN
            xg:=2*j;
            MudaPonto(xg,j);
            calculado[xg]:=calculado[j]
          END;
          FOR j:=0 TO mx2-1 DO calculado[2*j+1]:=FALSE
        END;
      #0:CASE ReadKey OF
        'H':BEGIN d:=(y2-y1)*0.25; y1:=y1+d ; y2:=y2+d END;
        'P':BEGIN d:=(y2-y1)*0.25; y1:=y1-d ; y2:=y2-d END;
        'M':BEGIN
            IF linear THEN BEGIN
              d:=(x2-x1)*0.25; x1:=x1+d ; x2:=x2+d;
            END
            ELSE BEGIN
              d:=Sqrt(Sqrt(x2/x1)); x1:=x1*d; x2:=x2*d;
            END;
            FOR j:=0 TO mx3 DO BEGIN
              xg:=j+mx1;
              MudaPonto(j,xg);
              calculado[j]:=calculado[xg]
            END;
            FOR j:=mx3+1 TO segm DO calculado[j]:=FALSE;
          END;
        'K':BEGIN
            IF linear THEN BEGIN
              d:=(x2-x1)*0.25; x1:=x1-d; x2:=x2-d;
            END
            ELSE BEGIN
              d:=Sqrt(Sqrt(x2/x1)); x1:=x1/d; x2:=x2/d;
            END;
            FOR j:=segm DOWNTO mx1 DO BEGIN
              xg:=j-mx1;
              MudaPonto(j,xg);
              calculado[j]:=calculado[xg]
            END;
            FOR j:=0 TO mx1-1 DO calculado[j]:=FALSE;
          END
        END;
      ' ':Medir;
      'F':plotarfase:=not plotarfase;
      'G':grade:=not grade;
      #27:BEGIN TextMode(80); Exit END
      END
    UNTIL FALSE;
  END;

BEGIN
  resposta:=nos+1;
  aa:=(ymin-ymax)/360;
  ba:=-aa*180;
 Horizontal:
  FOR j:=0 TO segm DO calculado[j]:=FALSE;
  Write('Freqˆncias em Hertz'); LerBool(hertz);
  Write('Escala linear'); LerBool(linear);
  Write('Resolu‡„o inicial (1-16)'); LerInt(dx);
  Write('Freqˆncia inicial'); LerReal(x1);
  Write('Freqˆncia final'); LerReal(x2);
 Vertical:
  Write('Ganho m ximo (dB)'); LerReal(y2);
  Write('Ganho m¡nimo (dB)'); LerReal(y1);
  REPEAT
    ok:=TRUE;
    Write('N¢ de sa¡da inicial'); LerInt(saida);
    IF (saida>0) AND (saida<=nosantes) THEN Csaida:=C[saida]
    ELSE BEGIN WriteLn(tl,'[*] Sa¡da inv lida'); ok:=FALSE END;
    IF Csaida=0 THEN BEGIN WriteLn(tl,'[*] A tens„o neste n¢ ‚ nula'); ok:=FALSE END;
  UNTIL ok;
 Plotar:
  Grafico;
 Menu:
  WriteLn(tl,']- mudar escala [H]orizontal');
  WriteLn(tl,'- mudar escala [V]ertical');
  WriteLn(tl,'- [A]n lise em freqˆncia especificada');
  WriteLn(tl,'- [M]udar parƒmetros do circuito');
  WriteLn(tl,'- mudar parƒmetros de [O]tas');
  WriteLn(tl,'- m ximas tens”es [N]odais');
  WriteLn(tl,'- m [X]imas tens”es nas entradas dos otas');
  WriteLn(tl,'- [G]r ficos de resposta em freqˆncia');
  WriteLn(tl,'- [S]alvar £ltimas curvas como referˆncia');
  IF referencia THEN WriteLn(tl,'- [E]liminar referˆncia');
  WriteLn(tl,'- [C]omandos diretos do gr fico');
  WriteLn(tl,'- [I]mprimir tabela');
  WriteLn(tl,'- [R]einiciar');
  WriteLn(tl,'- [T]erminar');
 Ler:
  WriteLn(tl,'[#]');
  CASE UpKey OF
  'S':BEGIN
        FOR i:=0 TO xa DO
          ponto[i]^[MaxNos1]:=ponto[i]^[Csaida];
        refxa:=xa;
        refdx:=dx;
        refax:=ax;
        refbx:=bx;
        refrede:=rede;
        refsaida:=saida;
        referencia:=TRUE;
        WriteLn(tl,'[*] Referˆncia salva');
        GoTo Ler
      END;
  'E':BEGIN
        IF referencia THEN BEGIN
          referencia:=FALSE;
          WriteLn(tl,'[*] Referˆncia eliminada');
        END;
        GoTo Ler
      END;
  'G':GoTo Plotar;
  'H':GoTo Horizontal;
  'V':GoTo Vertical;
  'R':ok:=FALSE;
  'T':BEGIN
        ok:=TRUE;
        Write('Terminar'); LerBool(ok);
        IF not ok THEN GoTo Ler
      END;
  'A':BEGIN
      WriteLn('Freqˆncia complexa em ',unid[hertz],':');
      Write('Real'); LerReal(sr);
      Write('Imag'); LerReal(si);
      WriteLn('Tens”es nodais:');
      IF hertz THEN BEGIN sr:=2*pi*sr; si:=2*pi*si END;
      MontarSistema;
      ResolverSistema;
      FOR i:=1 TO nosantes DO BEGIN
        WriteLn(tl,Noj(i),'[',i:2,']: ',Yr[C[i],resposta]:15:11,Yi[C[i],resposta]:15:11,'j');
        Espera(i)
      END;
      GoTo Ler
    END;
  'O':BEGIN
      WriteLn('Parƒmetros para todos os OTAs do circuito:'#10);
      Write(' Gin'); LerReal(Gin);
      Write(' Go '); LerReal(Go);
      Write(' Cin'); LerReal(Cin);
      Write(' Co '); LerReal(Co);
      Write(#10'Mudar Wp e Wz "default" de todos os OTAs'); LerBool(lerWzWp);
      IF lerWzWp THEN BEGIN
        Write(#10' Wp'); LerReal(Wp);
        Write(' Wz'); LerReal(Wz);
        FOR i:=1 TO numero DO WITH elemento[i] DO
          IF tipo=VCCS THEN
            BEGIN val[2]:=Wp; val[3]:=Wz END
      END;
      FOR j:=0 TO segm DO calculado[j]:=FALSE;
      GoTo Ler
    END;
  'M':BEGIN
        WriteLn(tl,'Parƒmetros do circuito: [E]ditar [A]nterior [Cr] [Esc]');
        i:=1; ok:=FALSE;
        REPEAT WITH elemento[i] DO
          WITH biblioteca[tipo] DO BEGIN
            Write(nome,': ');
            FOR j:=1 TO nnos DO Write(tl,'[',no[j],'] (',nmno[j],') ');
            FOR j:=1 TO nval DO Write(tl,'[',nmval[j],']:',Cpct(val[j]),' ');
            r:=UpKey;
            WriteLn;
            CASE r OF
              'E',#13:BEGIN
                    IF r='E' THEN FOR j:=1 TO nval DO BEGIN
                      Write(' ',nmval[j]); LerReal(val[j]);
                      ok:=TRUE
                    END;
                    IF i<numero THEN Inc(i) ELSE r:=#27
                  END;
              'A':IF i>1 THEN Dec(i) ELSE i:=numero;
            END
          END
        UNTIL r=#27;
      IF ok THEN FOR j:=0 TO segm DO calculado[j]:=FALSE;
      GoTo Ler
    END;
  'I':BEGIN
      txt:=td+rede+'.ana';
      Write(tl,'Nome do arquivo: '); EditarLinha(txt,WhereX,WhereY,1);
      WriteLn;
      Assign(arquivo,txt);
      ReWrite(arquivo);
      WriteLn(tl,#10,'Escrevendo arquivo [',txt,']...');
      WriteLn(arquivo,'AnaFil - Versao ',versao,' - Rede: ',rede);
      WriteLn(arquivo);
      WriteLn(arquivo,'# Resp. em freq. (',unid[hertz],'): Saida ',saida,' (Frq, Mod, Fas)');
      FOR j:=0 TO segm DO IF calculado[j] THEN
        WITH ponto[j]^[Csaida] DO
          WriteLn(arquivo,Frequencia(j):14:9,' ',Modulo(re,im):14:9,' ',Fase(re,im):14:9);
      WriteLn(arquivo);
      Close(arquivo);
      GoTo Ler
    END;
  'N':BEGIN
      WriteLn('M ximos n¡veis de sinal nos n¢s:');
      FOR j:=1 TO nosantes DO BEGIN
        t1:=0; t2:=0;
        IF C[j]<>0 THEN
          FOR i:=0 TO segm DO IF calculado[i] THEN
            WITH ponto[i]^[C[j]] DO BEGIN
              t:=Sqr(re)+Sqr(im);
              IF t>t1 THEN BEGIN
                t1:=t;
                t2:=Frequencia(i)
              END
            END;
        WriteLn(tl,Noj(j),'[',j:2,']: M ximo=[',Sqrt(t1):10:5,'] em ',t2:10:5,' ',unid[hertz]);
        Espera(j)
      END;
      GoTo Ler
    END;
  'X':BEGIN
      WriteLn('M ximos n¡veis de sinal em entrada de OTAs:');
      FOR j:=1 TO numero DO WITH elemento[j] DO
        IF tipo=VCCS THEN BEGIN
          t1:=0; t2:=0;
          FOR i:=0 TO segm DO IF calculado[i] THEN BEGIN
            IF C[no[3]]>0 THEN BEGIN
              tr:=ponto[i]^[C[no[3]]].re; ti:=ponto[i]^[C[no[3]]].im
            END
            ELSE BEGIN tr:=0; ti:=0 END;
            IF C[no[4]]>0 THEN BEGIN
              ta:=ponto[i]^[C[no[4]]].re; tb:=ponto[i]^[C[no[4]]].im
            END
            ELSE BEGIN ta:=0; tb:=0 END;
            t:=Sqr(tr-ta)+Sqr(ti-tb);
            IF t>t1 THEN BEGIN
              t1:=t;
              t2:=Frequencia(i)
            END
          END;
          WriteLn(tl,'[',nome:5,']; N¢s [',no[3]:2,',',no[4]:2,']: M ximo=[',Sqrt(t1):10:5,'] em ',t2:10:5,' ',unid[hertz]);
        END;
      GoTo Ler;
    END;
  'C':BEGIN
        WriteLn(tl,'[Comandos diretos:]');
        WriteLn(tl,'- [A,R] : Ampliar/reduzir horizontalmente');
        WriteLn(tl,'- [Cursor horizontal] : Mover horizontalmente');
        WriteLn(tl,'- [+,-] : Ampliar/reduzir verticalmente (ganho)');
        WriteLn(tl,'- [Cursor vertical] : Mover verticalmente (ganho)');
        WriteLn(tl,'- [X] : Mudar a resolu‡„o');
        WriteLn(tl,'- [<,>] : Mudar n¢ de sa¡da');
        WriteLn(tl,'- [G] : Ligar/desligar grade');
        WriteLn(tl,'- [F] : Ligar/desligar curvas de fase');
        WriteLn(tl,'- [" "] : Ligar/desligar o cursor');
        WriteLn(tl,'- [Cursor horizontal com cursor] : Mover o cursor (mais r pido com Ctrl)');
        WriteLn(tl,'[Obs:]');
        WriteLn('- Mudar a escala horizontal n„o afeta as curvas de referˆncia.');
        WriteLn('- Para usar outros modos gr ficos: chamar Anafil <arquivo> <placa> <modo>.');
        WriteLn('  "Anafil <arquivo> 1 4" seleciona o modo 640x200 da CGA.');
        GoTo Ler
      END;
  ELSE GoTo Menu
  END;
  ClrScr;
END; {FazerGrafico}

PROCEDURE EntrarArquivo;
BEGIN
  ok:=FALSE;
  REPEAT
    txt:=rede;
    Write(tl,#10'Arquivo com a descri‡„o do circuito (.net) ou ?: ');
    EditarLinha(txt,WhereX,WhereY,1);
    WriteLn;
    IF txt='?' THEN Diretorio
    ELSE BEGIN
      FSplit(txt,td,rede,te);
      IF te='' THEN te:='.net';
      txt:=td+rede+te;
      Assign(arquivo,txt);
      {$I-} Reset(arquivo) {$I+};
      ok:=(IOresult=0);
      IF not ok THEN WriteLn(tl,#10'[*] Arquivo [',txt,'] inexistente.')
    END
  UNTIL ok;
END; {EntrarArquivo}

BEGIN {Programa Principal}
  DetectGraph(placa,modo);
  IF (placa=CGA) THEN modo:=CGAC1;
  IF paramcount=3 THEN BEGIN
    Val(ParamStr(2),placa,i);
    Val(ParamStr(3),modo,i);
  END;
  InitGraph(placa,modo,GetEnv('TPBGI'));
  IF placa>0 THEN BEGIN
    SetTextStyle(SmallFont,HorizDir,4);
    xmin:=TextWidth('WWWWWWWW');
    xmax:=GetMaxX;
    ymin:=0;
    ymax:=GetMaxY-10;
    xq:=8; yq:=ymax-ymin-41;
    IF placa<>1 THEN BEGIN
      cor3:=White;
      cor2:=Lightgray;
      cor1:=Yellow;
    END;
    InitSprite(cor3,cor2);
  END;
  TextMode(80);
  i:=GraphResult; IF i<>GrOk THEN ErroFatal(GraphErrorMsg(i));
  segm:=64*((MemAvail div SizeOf(resposta)) div 64); j:=segm;
  IF segm>segmax THEN segm:=segmax;
  mx1:=segm div 4;
  mx2:=segm div 2;
  mx3:=mx1+mx2;
  Wp:=1; Wz:=1; Gin:=0; Go:=0; Cin:=0; Co:=0; lerWzWp:=FALSE; {Para OTAs}
  x1:=0.2; x2:=5.0; y1:=-60; y2:=10; dx:=8; {Para gr ficos}
  saida:=1; hertz:=FALSE; linear:=FALSE; plotarfase:=TRUE; grade:=TRUE;
  referencia:=FALSE;
  FOR i:=0 TO segm DO New(ponto[i]);
  WriteLn(tl,'[ÉÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍ»');
  WriteLn(tl,'ºAn ]lise de [Fil]tros e Circuitos Lineares[º');
  WriteLn(tl,'ÈÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍ¼]');
  WriteLn('Ant“nio Carlos Moreir„o de Queiroz - COPPE/UFRJ');
  WriteLn('Vers„o ',versao,' - Precis„o ',precisao);
  WriteLn(tl,'[ÉÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍ»');
  WriteLn(tl,'º]Este programa plota diagramas de resposta em freqˆncia para circuitos linea-[º');
  WriteLn(tl,'º]res. A descri‡„o do circuito a analisar pode ser gerada pelo programa [EdFil]. [º');
  WriteLn(tl,'º]Os componentes aceitos s„o:                                                  [º');
  WriteLn(tl,'º]Resistor ([R]); Capacitor ([C]); Indutor ([L]); Resistor imagin rio ([X]);           [º');
  WriteLn(tl,'º]Amp. Op. com Av=GB/s e resistˆncia de sa¡da ([A]); Amp. Op. ideal ([O]);         [º');
  WriteLn(tl,'º]VCCS ou OTA com Gm,polo,zero (para cada um),Gin,Go,Cin e Co (globais) ([G]);   [º');
  WriteLn(tl,'º]Transistor MOS, com Gm e Gds ([M]);                                            [º');
  WriteLn(tl,'º]Transistor bipolar com modelo h¡brido h completo ([Q]); Girador ([Y]);           [º');
  WriteLn(tl,'º]Transformador ([N]), com L11, L22, M12 e M21 (opcional) dados;                 [º');
  WriteLn(tl,'º]Linha de transmiss„o RC, ou URC ([U]); Linha de transmiss„o LC, sem perdas ([T]);[º');
  WriteLn(tl,'º]Fonte de tens„o unit ria com resistor serie ([Z]); Fonte de corrente ([I]).      [º');
  WriteLn(tl,'º]Com [j] calculado: Fonte de tens„o ([V]); VCVS ([E]); CCCS ([F]); CCVS ([H]).          [º');
  WriteLn(tl,'ÈÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍ¼]');
  WriteLn(tl,'Alocados [',segm,'] segmentos para o gr fico (m ximo=',j,').');
  IF ParamCount>0 THEN rede:=ParamStr(1) ELSE rede:='';
  REPEAT
    EntrarArquivo;
    LerCircuito;
    FazerGrafico
  UNTIL ok;
  WriteLn(tl,#10'[--//--]');
END. {Anafil}
