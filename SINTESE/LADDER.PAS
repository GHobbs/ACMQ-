PROGRAM Ladder;
{*****************************************************************************
 * ExpansÑo de rede ladder RLC passa-baixas                                  *
 * Antìnio Carlos MoreirÑo de Queiroz                                        *
 * VersÑo 1.4 de 04/04/87                                                    *
 * VersÑo 1.5 de 17/01/88                                                    *
 * VersÑo 1.6 de 02/01/89 Turbo 5.0                                          *
 * VersÑo 1.6a de 14/03/89 Pequenas alteraáîes na apresentaáÑo               *
 * VersÑo 1.7 de 15/08/89 CorreáÑo na normalizaáÑo inicial                   *
 * VersÑo 1.8 de 02/09/89 Cores, pequenas mudanáas                           *
 * VersÑo 1.8a de 27/12/89 PrecisÑo extendida                                *
 * VersÑo 1.9 de 13/04/91 ExtraáÑo parcial falsa permitida, gr†ficos, etc.   *
 * VersÑo 1.9a de 31/03/94 ExtraáÑo de cte. qualquer, salva curvas.          *
 * VersÑo 1.9b de 09/07/03 Adicionando extraáÑo de polos reais                            *
 *****************************************************************************}
{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}
USES Crt,Tela,Graph,Dos;
CONST
  max=40;
  mcomp=200;
  versao='1.9b de 09/07/03';
  terminar:BOOLEAN=FALSE;
TYPE
  polinomio=ARRAY[0..max] of REAL;
  tipo=(Ls,Lp,Lps,Lsp,Cs,Cp,Cps,Csp,Rs,Rp,Rl,Rc);
  imitancia=(Z,Y);
  texto=STRING;
  componente=
    RECORD
      tp:tipo;
      nme:string[4];
      val:REAL
    END;
  ckt=ARRAY[1..mcomp] of componente;
  lista=Array[1..max] of REAL;
VAR
  a,b,ab,bb:polinomio;
  p1,p2,z1,z2:lista;
  np,nz,n,m,nb,mb,i,j,el,elb,num,cm,dc:INTEGER;
  kb,k1,k0,d1,d0,zr,zi,dr,di,nr,ni,xi,xr,disp,k,t:REAL;
  imit,imitb:imitancia;
  r,ch:CHAR;
  nome:texto;
  fim:BOOLEAN;
  circuito,circuitob:ckt;
  arquivo:TEXT;
LABEL
  Inicio;

CONST
  pixmin=43;
  pxmin=75;
  pxmax=719;
  wmin:REAL=0.1;
  wmax:REAL=10;
  zmin:REAL=-10;
  zmax:REAL=10;
  log:BOOLEAN=TRUE;
  grade:BOOLEAN=TRUE;
VAR
  cor1,cor2,cor3,placa,modo:INTEGER;
  x0,xm,mx1,mx2,mx3,y0,ym:INTEGER;
  xmin,xmax,ymin,ymax:INTEGER;

TYPE tipodegrafico=(tau,jw);

{$I seta.p}

PROCEDURE Avaliar;
BEGIN
  dr:=0; di:=0;
  FOR i:=m DOWNTO 0 DO BEGIN
    t:=dr*zr-di*zi+b[i];
    di:=dr*zi+di*zr;
    dr:=t
  END;
  nr:=0; ni:=0;
  FOR i:=n DOWNTO 0 DO BEGIN
    t:=nr*zr-ni*zi+a[i];
    ni:=nr*zi+ni*zr;
    nr:=t
  END;
  t:=dr*dr+di*di;
  IF t=0 THEN t:=1e-12;
  xr:=(nr*dr+ni*di)/t;
  xi:=(ni*dr-nr*di)/t;
END;

PROCEDURE Grafico(tipo:tipodegrafico; VAR x1,x2,y1,y2:REAL);
  VAR
    ax,bx,ay,by,w,t1,t2,d,a1,a2:REAL;
    j,xg,xa,ya:INTEGER;
    ponto:ARRAY[pxmin..pxmax] OF RECORD re,im:REAL END;
    calculado:ARRAY[pxmin..pxmax] OF BOOLEAN;
    ok,salvarcurva:BOOLEAN;
  LABEL atualizar;

  FUNCTION Limx(x:REAL):INTEGER;
  BEGIN
    IF log THEN x:=ax*Ln(x)+bx
    ELSE x:=ax*x+bx;
    IF x>xm THEN Limx:=xm
    ELSE IF x<x0 THEN Limx:=x0
    ELSE Limx:=Round(x)
  END;

  FUNCTION Limy(y:REAL):INTEGER;
  BEGIN
    y:=ay*y+by;
    IF y>ym THEN Limy:=ym
    ELSE IF y<y0 THEN Limy:=y0
    ELSE Limy:=Round(y)
  END;

  PROCEDURE Medir;
  BEGIN
    xg:=x0;
    REPEAT
      SetColor(cor1);
      PutSprite(xg,Limy(ponto[xg].re));
      Bar3D(xm-110,y0+3,xm-4,y0+29,4,TRUE);
      w:=(xg-bx)/ax;
      IF log THEN w:=Exp(w);
      Str(w:11:6,nome); OutTextXY(xm-108,y0+5,'w:'+nome);
      Str(ponto[xg].re:11:6,nome); OutTextXY(xm-108,y0+13,'R:'+nome);
      SetColor(cor2);
      Str(ponto[xg].im:11:6,nome); OutTextXY(xm-108,y0+21,'I:'+nome);
      ch:=ReadKey;
      IF ch=#0 THEN
      CASE ReadKey OF
        'M':IF (xg+1<=xm) THEN IF calculado[xg+1] THEN xg:=xg+1;
        'K':IF (xg-1>=x0) THEN IF calculado[xg-1] THEN xg:=xg-1;
        #116:IF (xg+10<=xm) THEN IF calculado[xg+10] THEN xg:=xg+10;
        #115:IF (xg-10>=x0) THEN IF calculado[xg-10] THEN xg:=xg-10;
      END
    UNTIL ch in [' ',#27,#13];
    PutSprite(-10,-10);
    Bar(xm-110,y0+1,xm-1,y0+29);
  END;

BEGIN
  salvarcurva:=FALSE;
  IF (x1<=0) or (x2<=0) THEN log:=FALSE;
  IF (x2<=x1) or (y2<=y1) THEN grade:=FALSE;
  FOR j:=x0 TO xm DO calculado[j]:=FALSE;
  REPEAT
    ay:=(y0-ym)/(y2-y1); by:=ym-ay*y1;
    IF log THEN BEGIN
      ax:=(xm-x0)/Ln(x2/x1); bx:=x0-ax*Ln(x1)
    END
    ELSE BEGIN
      ax:=(xm-x0)/(x2-x1); bx:=x0-ax*x1
    END;
    SetGraphMode(modo);
    SetfillStyle(emptyfill,0);
    IF grade THEN BEGIN
      SetLineStyle(DottedLn,0,NormWidth);
      SetColor(cor3);
      IF log and (x2-x1>x1) THEN t1:=x1
      ELSE t1:=x2-x1;
      t1:=Exp(Ln(10)*Round(Ln(t1)/Ln(10)-0.499999));
      t2:=Round(x1/t1+0.5)*t1;
      WHILE t2<x2 DO
        IF log THEN BEGIN
          IF Round(t2/t1)=10 THEN BEGIN
            t1:=10*t1;
            SetColor(cor2);
          END;
          i:=Round(ax*Ln(t2)+bx);
          Line(i,y0,i,ym);
          t2:=t2+t1;
          SetColor(cor3);
        END
        ELSE BEGIN
          i:=Round(ax*t2+bx);
          Line(i,y0,i,ym);
          t2:=t2+t1
        END;
      t1:=y2-y1;
      t1:=Exp(Ln(10)*Round(Ln(t1)/Ln(10)-0.5));
      t2:=Round(y1/t1+0.5)*t1;
      WHILE t2<y2 DO BEGIN
        i:=Round(ay*t2+by);
        Line(x0,i,xm,i);
        t2:=t2+t1
      END;
      SetLineStyle(SolidLn,0,NormWidth);
      SetColor(cor1)
    END;
    Rectangle(x0,y0,xm,ym);
    IF KeyPressed THEN GOTO atualizar;
    Str(x1:9:4,nome); WHILE nome[1]=' ' DO nome:=Copy(nome,2,255); OutTextXY(x0,ym+2,nome);
    Str(x2:9:4,nome); OutTextXY(xm-72,ym+2,nome);
    Str(y1:9:4,nome); OutTextXY(x0-72,ym-8,nome);
    Str(y2:9:4,nome); OutTextXY(x0-72,y0,nome);
    IF imit=Z THEN nome:='Z(s)' ELSE nome:='Y(s)';
    OutTextXY(x0-56,(ym+y0-8) div 2,nome);
    IF tipo=jw THEN nome:='Im(s)' ELSE nome:='-Re(s)';
    OutTextXY((x0+xm) div 2-20,ym+2,nome);
    FOR xg:=x0 TO xm DO BEGIN
      w:=(xg-bx)/ax;
      IF log THEN w:=Exp(w);
      IF NOT calculado[xg] THEN BEGIN
        IF tipo=jw THEN BEGIN zr:=0; zi:=w END
        ELSE BEGIN zr:=-w; zi:=0 END;
        Avaliar;
        ponto[xg].re:=k*xr;
        ponto[xg].im:=k*xi;
        calculado[xg]:=TRUE
      END;
      IF salvarcurva THEN WriteLn(arquivo,w,' ',ponto[xg].re,' ',ponto[xg].im);
      IF xg>x0 THEN BEGIN
        SetColor(cor1);
        Line(xa,Limy(ponto[xg-1].re),xg,Limy(ponto[xg].re));
        SetColor(cor2);
        Line(xa,Limy(ponto[xg-1].im),xg,Limy(ponto[xg].im))
      END;
      xa:=xg;
      IF KeyPressed THEN GOTO atualizar;
    END;
    atualizar:
    IF salvarcurva THEN BEGIN
      salvarcurva:=FALSE;
      Close(arquivo);
    END;
    ch:=UpKey;
    CASE ch OF
    '-':y2:=2*(y2-y1)+y1;
    '+':y2:=(y2-y1)/2+y1;
    'R':BEGIN
        IF log THEN x2:=Sqr(x2)/x1
        ELSE x2:=2*x2-x1;
        FOR j:=x0 TO mx2 DO BEGIN
          xg:=2*j-x0;
          ponto[j]:=ponto[xg];
          calculado[j]:=calculado[xg]
        END;
        FOR j:=mx2+1 TO xm DO calculado[j]:=FALSE
      END;
    'A':BEGIN
        IF log THEN x2:=Sqrt(x2*x1)
        ELSE x2:=(x2+x1)/2;
        FOR j:=mx2 DOWNTO x0 DO BEGIN
          xg:=2*j-x0;
          ponto[xg]:=ponto[j];
          calculado[xg]:=calculado[j]
        END;
        FOR j:=x0 TO mx2-1 DO calculado[2*j-x0+1]:=FALSE
      END;
    #0:BEGIN
        CASE ReadKey OF
        'H':BEGIN d:=(y2-y1)*0.25; y1:=y1+d ; y2:=y2+d END;
        'P':BEGIN d:=(y2-y1)*0.25; y1:=y1-d ; y2:=y2-d END;
        'M':BEGIN
            IF log THEN BEGIN d:=Sqrt(Sqrt(x2/x1)); x1:=x1*d; x2:=x2*d END
            ELSE BEGIN d:=(x2-x1)*0.25; x1:=x1+d ; x2:=x2+d END;
            FOR j:=x0 TO mx3 DO BEGIN
              xg:=j-x0+mx1;
              ponto[j]:=ponto[xg];
              calculado[j]:=calculado[xg]
            END;
            FOR j:=mx3+1 TO xm DO calculado[j]:=FALSE;
          END;
        'K':BEGIN
            IF log THEN BEGIN d:=Sqrt(Sqrt(x2/x1)); x1:=x1/d; x2:=x2/d END
            ELSE BEGIN d:=(x2-x1)*0.25; x1:=x1-d; x2:=x2-d END;
            FOR j:=xm DOWNTO mx1 DO BEGIN
              xg:=j-mx1+x0;
              ponto[j]:=ponto[xg];
              calculado[j]:=calculado[xg]
            END;
            FOR j:=x0 TO mx1-1 DO calculado[j]:=FALSE;
          END
        END
      END;
    'G':grade:=not grade;
    ' ':BEGIN Medir; GOTO atualizar END;
    #27:;
    ELSE BEGIN
           TextMode(80);
           a1:=x1; a2:=x2; ok:=log;
           Write('Escala logar°tmica'); LerBool(log);
           Write('w m°nimo'); LerReal(x1);
           Write('w m†ximo'); LerReal(x2);
           Write('y m°nimo'); LerReal(y1);
           Write('y m†ximo'); LerReal(y2);
           IF (a1<>x1) or (a2<>x2) or (log<>ok) THEN
             FOR j:=x0 TO xm DO calculado[j]:=FALSE;
           Write(tl,'Salvar curva? ([Cr] ou nome) [');
           ReadLn(nome); Write(tl,']');
           IF nome<>'' THEN BEGIN
             Assign(arquivo,nome);
             ReWrite(arquivo);
             salvarcurva:=TRUE
           END
         END
    END
  UNTIL ch=#27;
  RestoreCrtMode;
END;

PROCEDURE ListarRaizes(zy:CHAR; x1,x2:lista; n:INTEGER);
BEGIN
  FOR i:=1 TO n DO WriteLn(tl,'[',zy,i,']:',x1[i]:cm:dc,x2[i]:cm:dc,'j');
END;

PROCEDURE ListarPolinomio (a:polinomio; grau:INTEGER);
BEGIN
  FOR i:=0 TO grau DO WriteLn(tl,'a([',i:2,']):',a[i]:cm:dc)
END;

PROCEDURE PedirZero;
VAR
  pz:texto;
  i,e:INTEGER;
BEGIN
  REPEAT
    Write(tl,'FreqÅància: ([Re] [Im] ou [nome]) ['); ReadLn(pz); Write(tl,']');
    ch:=UpCase(pz[1]);
    IF ch in ['P','Z'] THEN BEGIN
      Val(Copy(pz,2,Length(pz)-1),i,e);
      IF e=0 THEN
        IF ch='P' THEN
          IF (i>0) and (i<=np) THEN BEGIN
            zr:=p1[i]; zi:=p2[i]
          END
        ELSE e:=1
      ELSE
        IF (i>0) and (i<=nz) THEN BEGIN
          zr:=z1[i]; zi:=z2[i]
        END
      ELSE e:=1
    END
    ELSE BEGIN
      i:=Pos(' ',pz);
      IF i>0 THEN BEGIN
        Val(Copy(pz,1,i-1),zr,e);
        IF e=0 THEN
          Val(Copy(pz,i+1,Length(pz)-i),zi,e)
      END
      ELSE e:=1
    END;
    IF (e<>0) THEN WriteLn(tl,'[*] Incorreto [*]');
  UNTIL e=0;
END;

PROCEDURE MontarPolinomioReal(VAR grau:INTEGER; VAR a:polinomio; VAR cte:REAL);
VAR
  pz:string[3];
  n,i:INTEGER;
  d0,d1:REAL;
BEGIN
  FOR i:=0 TO grau DO a[i]:=0;
  a[0]:=1;
  n:=0;
  WHILE n<grau DO BEGIN
    PedirZero;
    IF Abs(zi)<disp THEN BEGIN
      n:=n+1;
      FOR i:=n DOWNTO 1 DO a[i]:=a[i-1];
      a[0]:=0;
      FOR i:= 0 TO n-1 DO a[i]:=a[i]-zr*a[i+1];
    END
    ELSE BEGIN
      d1:=-2*zr; d0:=zr*zr+zi*zi;
      n:=n+2;
      FOR i:=n DOWNTO 2 DO a[i]:=a[i-2];
      a[1]:=0; a[0]:=0;
      FOR i:=0 TO n-2 DO a[i]:=a[i]+a[i+1]*d1+a[i+2]*d0;
      a[n-1]:=a[n-1]+a[n]*d1
    END;
    IF n>grau THEN BEGIN
      WriteLn(tl,'[*] Foram dadas ra°zes demais [*]');
      grau:=n
    END;
  END;
  WriteLn(tl,'[Polinìmio obtido]:');
  ListarPolinomio(a,grau);
  IF a[0]<>0 THEN cte:=1/a[0] ELSE cte:=1;
  Write('Cte. multiplicativa'); LerReal(cte);
END;

PROCEDURE LerRaizes(VAR x1,x2:lista; VAR n:INTEGER);
BEGIN
  REPEAT
    Write(tl,'Nome do arquivo: ([cr] p/ignorar) [');
    ReadLn(nome); Write(tl,']');
    IF Length(nome)=0 THEN BEGIN n:=0; Exit END;
    Assign(arquivo,nome);
    {$I-} Reset(arquivo); {$I+}
    IF IOResult=0 THEN BEGIN
      ReadLn(arquivo,n);
      WriteLn(tl,'[',n,' freqÅàncias]:');
      FOR i:=1 TO n DO BEGIN
        ReadLn(arquivo,x1[i],x2[i]);
        WriteLn(tl,'[x',i,']:',x1[i]:cm:dc,x2[i]:cm:dc,'j')
      END;
      Exit
    END
    ELSE WriteLn(tl,'[*] Inexistente [*]')
  UNTIL FALSE
END;

PROCEDURE Salvar;
BEGIN
  ab:=a; bb:=b; nb:=n; mb:=m; kb:=k;
  imitb:=imit
END;

PROCEDURE Repor;
BEGIN
  a:=ab; b:=bb; n:=nb; m:=mb; k:=kb;
  imit:=imitb
END;

PROCEDURE LerPolinomio(VAR grau:INTEGER; VAR a:polinomio; VAR cte:REAL);
VAR
  i,n:INTEGER;
  ok:BOOLEAN;
BEGIN
  REPEAT
    Write(tl,'Nome do arquivo: ([cr] p/teclado) [');
    ReadLn(nome); Write(tl,']');
    IF Length(nome)>0 THEN BEGIN
      Assign(arquivo,nome);
      {$I-} Reset(arquivo); {$I+}
      ok:=(IOResult=0);
      IF not ok THEN WriteLn(tl,'[*] Inexistente [*]')
      ELSE BEGIN
        ReadLn(arquivo,grau);
        FOR i:=0 TO grau DO ReadLn(arquivo,a[i]);
        IF not SeekEof(arquivo) THEN ReadLn(arquivo,cte) ELSE cte:=1;
        ListarPolinomio(a,grau);
        WriteLn(tl,'[Cte]:  ',cte:cm:dc);
        Close(arquivo)
      END
    END
    ELSE BEGIN
      Write(tl,'[C]oeficientes ou [R]a°zes? ');
      REPEAT r:=UpCase(ReadKey) until r in ['C','R'];
      Write(#13); ClrEol;
      IF r='C' THEN BEGIN
        Write('Grau do polinìmio: '); ReadLn(grau);
        FOR i:=0 TO grau DO BEGIN
          Write(tl,'a([',i,']): ');
          ReadLn(a[i]);
        END;
        Write('Cte. multiplicativa: ');
        ReadLn(cte)
      END
      ELSE BEGIN
        Write('N£mero de ra°zes: '); LerInt(grau);
        WriteLn(tl,'Entre as [',grau,' ra°zes]: (conjugados sÑo assumidos)');
        ListarRaizes('z',z1,z2,nz);
        ListarRaizes('p',p1,p2,np);
        MontarPolinomioReal(grau,a,cte);
      END;
      Write(tl,'Arquivo onde salvar: ([cr] p/ignorar) [');
      ReadLn(nome); Write(tl,']');
      IF Length(nome)<>0 THEN BEGIN
        Assign(arquivo,nome);
        ReWrite(arquivo);
        WriteLn(arquivo,grau);
        FOR I:=0 TO grau DO WriteLn(arquivo,a[I]:cm:dc);
        WriteLn(arquivo,cte:cm:dc);
        Close(arquivo)
      END;
      ok:=TRUE
    END
  UNTIL ok;
  WriteLn
END;

PROCEDURE Limpar(VAR a:polinomio; VAR grau:INTEGER);
VAR
  x:REAL;
BEGIN
  x:=0;
  FOR i:=0 TO grau DO IF Abs(a[i])>x THEN x:=Abs(a[i]);
  x:=x*disp;
  FOR i:=0 TO grau DO IF Abs(a[i])<x THEN a[i]:=0;
  WHILE (grau>=0) and (a[grau]=0) DO grau:=grau-1;
  IF grau=-1 THEN fim:=TRUE
END;

PROCEDURE Normalizar;
BEGIN
  Limpar(a,n);
  Limpar(b,m);
  IF fim THEN Exit;
  k:=k*a[n]/b[m];
  FOR i:=0 TO n DO a[i]:=a[i]/a[n];
  FOR i:=0 TO m DO b[i]:=b[i]/b[m];
END;

FUNCTION Comentario(tp:tipo):texto;
BEGIN
  CASE tp OF
    Lps,Cps: nome:='tanque // em sÇrie';
    Lsp,Csp: nome:='tanque sÇrie em //';
    Rl: nome:='sÇrie com isto';
    Rc: nome:='// com isto';
    Ls,Cs,Rs: nome:='sÇrie';
    Lp,Cp,Rp: nome:='//';
  END;
  Comentario:=' em '+nome;
END;

PROCEDURE Armazenar(posicao:tipo; valor:REAL; incremento:INTEGER);
BEGIN
  el:=el+1;
  num:=num+incremento;
  IF num=0 THEN num:=1;
  WITH circuito[el] DO BEGIN
    tp:=posicao;
    CASE posicao of
      Rs,Rp:         nme:='R';
      Rl:            nme:='RL';
      Rc:            nme:='RC';
      Ls,Lp,Lps,Lsp: nme:='L';
      Cp,Cs,Cps,Csp: nme:='C'
      ELSE nme:='?'
    END;
    Str(num,nome);
    nme:=nme+nome;
    val:=valor;
    WriteLn(tl,'[',nme,']:',val:cm:dc,Comentario(tp));
  END
END;

PROCEDURE EscreveTipo;
BEGIN
  ClrEol;
  IF imit=Z THEN Write(tl,'[ImpedÉncia]: ')
  ELSE Write(tl,'[AdmitÉncia]: ')
END;

PROCEDURE ListarImitancia;
BEGIN
  EscreveTipo;
  WriteLn(tl,'[Numerador]:');
  ListarPolinomio(a,n);
  WriteLn(tl,'[Denominador]:');
  ListarPolinomio(b,m);
  WriteLn(tl,'[Cte]:  ',k:cm:dc);
END;

PROCEDURE Inverter;
BEGIN
  IF k=0 THEN Exit;
  IF imit=Z THEN imit:=Y ELSE imit:=Z;
  Write('  ');
  EscreveTipo;
  Write(#13);
  k:=1/k;
  IF m>n THEN j:=m ELSE j:=n;
  FOR i:=0 TO j DO BEGIN
    t:=a[i]; a[i]:=b[i]; b[i]:=t
  END;
  j:=m; m:=n; n:=j;
END;

PROCEDURE ExtrairPoloNoInfinito;
BEGIN
  IF n=m+1 THEN BEGIN
    n:=n-1;
    FOR i:=1 TO n DO a[i]:=a[i]-b[i-1];
    IF imit=Z THEN Armazenar(Ls,k,1)
    ELSE Armazenar(Cp,k,1);
    Normalizar
  END
  ELSE WriteLn(tl,'[*] NÑo h† p¢lo simples no infinito [*]');
END;

PROCEDURE ExtrairCteNoInfinito;
BEGIN
  IF n=m THEN BEGIN
    n:=n-1;
    FOR i:=0 TO n DO a[i]:=a[i]-b[i];
    IF imit=Z THEN Armazenar(Rs,k,0)
    ELSE Armazenar(Rp,1/k,0);
    Normalizar
  END
  ELSE WriteLn(tl,'[*] NÑo h† cte. no infinito [*]');
END;

PROCEDURE ExtrairCteDada;
VAR
  x:REAL;
  ok:BOOLEAN;
BEGIN
  IF n>=m THEN BEGIN
    x:=k;
    Write('Cte. a extra°r'); LerReal(x);
    IF x>k THEN BEGIN
      WriteLn(tl,'[*] A Cte. pedida Ç maior que a cte. no infinito [*]');
      Write('Prosseguir');
      ok:=FALSE;
      LerBool(ok);
      IF not ok THEN Exit
    END;
    FOR i:=0 TO m DO a[i]:=k*a[i]-x*b[i];
    k:=1;
    IF imit=Z THEN Armazenar(Rs,x,0)
    ELSE Armazenar(Rp,1/x,0);
    Normalizar
  END
  ELSE WriteLn(tl,'[*] NÑo h† cte. para extrair [*]');
END;

PROCEDURE EliminarFator2(VAR b:polinomio; VAR n:INTEGER);
VAR
  a:polinomio;
BEGIN
  a[0]:=b[0]/d0;
  a[1]:=(b[1]-a[0]*d1)/d0;
  FOR i:=2 TO n {-2} DO a[i]:=(b[i]-a[i-2]-a[i-1]*d1)/d0;
  IF (Abs(a[n])>disp) or (Abs(a[n-1])>disp) THEN
    WriteLn(tl,'[*] Poss°vel remoáÑo incorreta [*]');
  n:=n-2;
  b:=a;
END;

{Modificar para remover um fator de 1a. ordem}
PROCEDURE EliminarFator1(VAR b:polinomio; VAR n:INTEGER);
VAR
  a:polinomio;
BEGIN
  a[0]:=b[0]/d0;
  a[1]:=(b[1]-a[0]*d1)/d0;
  FOR i:=2 TO n {-2} DO a[i]:=(b[i]-a[i-2]-a[i-1]*d1)/d0;
  IF (Abs(a[n])>disp) or (Abs(a[n-1])>disp) THEN
    WriteLn(tl,'[*] Poss°vel remoáÑo incorreta [*]');
  n:=n-2;
  b:=a;
END;

PROCEDURE RemoverTanque;
VAR
  c1,g1,l2,r2:REAL;
BEGIN
  IF zi<>0 THEN BEGIN
    c1:=1/(k*k1);
    g1:=c1*(d1-k0/k1);
    l2:=1/(c1*(d0-g1/c1*k0/k1));
    r2:=l2*k0/k1;
    IF imit=Z THEN BEGIN
      Armazenar(Lps,l2,1);
      IF Abs(r2)>disp THEN Armazenar(Rl,r2,0);
      Armazenar(Cps,c1,0);
      IF Abs(g1)>disp THEN Armazenar(Rc,1/g1,0);
    END
    ELSE BEGIN
      Armazenar(Lsp,c1,1);
      IF Abs(g1)>disp THEN Armazenar(Rl,g1,0);
      Armazenar(Csp,l2,0);
      IF Abs(r2)>disp THEN Armazenar(Rc,1/r2,0)
    END
  END
  ELSE WriteLn(tl,'[*] NÑo implementada extraáÑo de tanque RC ou RL [*]');
END;

PROCEDURE RemoverPolos;
BEGIN
  IF zi<>0 THEN BEGIN
    d1:=-2*zr; d0:=zr*zr+zi*zi;
    EliminarFator2(b,m);
    Avaliar;
    k1:=xi/zi; k0:=xr-k1*zr;
    RemoverTanque;
    FOR i:=0 TO m DO BEGIN
      a[i]:=a[i]-b[i]*k0;
      a[i+1]:=a[i+1]-b[i]*k1
    END;
    EliminarFator2(a,n);
    Normalizar
  END
  ELSE WriteLn(tl,'[*] NÑo implementada extraáÑo de p¢lo real [*]')
END;

PROCEDURE ExtrairParCteNoInfinito;
VAR
  ok:BOOLEAN;
BEGIN
  IF m=0 THEN BEGIN WriteLn(tl,'[*] Ordem insuficiente [*]'); Exit END;
  IF (n<>m) THEN BEGIN
    ok:=FALSE;
    WriteLn(tl,'[*] NÑo h† constante no infinito [*]');
    Write('Prosseguir'); LerBool(ok);
    IF not ok THEN Exit
  END;
  ListarRaizes('z',z1,z2,nz);
  PedirZero;
  Avaliar;
  IF Abs(xi)>disp THEN BEGIN WriteLn(tl,'[*] O elemento a extrair nÑo seria real [*]'); Exit END;
  IF xr<0 THEN BEGIN WriteLn(tl,'[*] O elemento resistivo a extrair Ç negativo [*]'); ok:=FALSE END
  ELSE IF (xr>1) and (n=m) THEN
    BEGIN WriteLn(tl,'[*] O elemento resistivo a extra°r Ç maior que a constante no infinito [*]'); ok:=FALSE END;
  IF not ok THEN BEGIN
    Write('Prosseguir'); LerBool(ok);
    IF not ok THEN Exit
  END;
  IF imit=Z THEN Armazenar(Rs,k*xr,0)
  ELSE Armazenar(Rp,1/(k*xr),0);
  IF m>n THEN BEGIN
    FOR i:=n+1 TO m DO a[i]:=0;
    n:=m
  END;
  FOR i:=0 TO n DO a[i]:=a[i]-b[i]*xr;
  Normalizar;
  Inverter;
  RemoverPolos;
  Inverter
END;

PROCEDURE ExtrairParPoloNoInfinito;
VAR
  ok:BOOLEAN;
BEGIN
  IF m=0 THEN BEGIN WriteLn(tl,'[*] Ordem insuficiente [*]'); Exit END;
  IF (n<>m+1) THEN BEGIN
    ok:=FALSE;
    WriteLn(tl,'[*] NÑo h† p¢lo no infinito [*]');
    Write('Prosseguir'); LerBool(ok);
    IF not ok THEN Exit
  END;
  ListarRaizes('z',z1,z2,nz);
  PedirZero;
  Avaliar;
  t:=zr*zr+zi*zi;
  dr:=(xr*zr+xi*zi)/t;
  di:=(xi*zr-xr*zi)/t;
  IF Abs(di)>disp THEN BEGIN WriteLn(tl,'[*] O elemento a extrair nÑo seria real [*]'); Exit END;
  IF dr<0 THEN BEGIN WriteLn(tl,'[*] O elemento reativo a extrair Ç negativo [*]'); ok:=FALSE END
  ELSE IF (dr>1) and (n=m+1) THEN
    BEGIN WriteLn(tl,'[*] O elemento reativo a extra°r Ç maior que o res°duo do p¢lo no infinito [*]'); ok:=FALSE END;
  IF not ok THEN BEGIN
    Write('Prosseguir'); LerBool(ok);
    IF not ok THEN Exit
  END;
  IF imit=Z THEN Armazenar(Ls,k*dr,1)
  ELSE Armazenar(Cp,k*dr,1);
  IF m>=n THEN BEGIN
    FOR i:=n+1 TO m+1 DO a[i]:=0;
    n:=m+1
  END;
  FOR i:=1 TO n DO a[i]:=a[i]-b[i-1]*dr;
  Normalizar;
  Inverter;
  RemoverPolos;
  Inverter;
END;

PROCEDURE Recomecar;
BEGIN
  WriteLn(tl,'[Recomeáando]:');
  Repor;
  el:=0;
  fim:=FALSE;
  num:=0;
END;

PROCEDURE Menu;
BEGIN
  IF not fim THEN BEGIN
    WriteLn(tl,'- [P]   Extrair p¢lo no infinito');
    WriteLn(tl,'- [C]   Extrair constante no infinito');
    WriteLn(tl,'- [X]   Extrair constante especificada');
    WriteLn(tl,'- [I]   Inverter imitÉncia');
    WriteLn(tl,'- [Z]   Extrair parcialmente p¢lo no infinito');
    WriteLn(tl,'- [T]   Extrair parcialmente constante no infinito');
    WriteLn(tl,'- [F]   Extrair p¢los privados');
    WriteLn(tl,'- [L]   Listar imitÉncia');
    WriteLn(tl,'- [G]   Gr†ficos das partes real e imagin†ria para s=jw');
    WriteLn(tl,'- [R]   Idem, para s real');
  END;
  WriteLn(tl,'- [E]   Listar a rede obtida');
  WriteLn(tl,'- [^R]  Recomeáar com a mesma imitÉncia');
  WriteLn(tl,'- [^O]  Recomeáar com outra imitÉncia');
  WriteLn(tl,'- [M]   Mudar parÉmetros do programa');
  IF fim THEN BEGIN
    WriteLn(tl,'- [N]   Transformaáîes na rede');
    WriteLn(tl,'- [S]   Salvar a rede obtida');
  END;
  WriteLn(tl,'- [esc] Terminar');
  WriteLn(tl,'- [cr]  Este menu');
END;

PROCEDURE Transformar;
VAR
  temp:componente;
  b,w,menorC,menorL:REAL;

  PROCEDURE MudarTanque(l1,c1,l2,c2:REAL; VAR L11,C11,L21,C21:REAL);
  VAR
    x,y,z:REAL;
  BEGIN
    x:=Sqr(1+c1/c2+l2/l1)-4*c1/c2*l2/l1;
    y:=Sqrt(1-4/x*l2/l1);
    z:=Sqrt(1-4/x*c1/c2);
    L11:=l1*(1-y)/2;
    C11:=c2*x*(1-z)/2;
    L21:=l1*(1+y)/2;
    C21:=c2*x*(1+z)/2;
  END;

  PROCEDURE EscalaEmImpedancia(z:REAL);
    BEGIN
    FOR i:=1 TO el DO WITH circuito[i] DO
      CASE nme[1] OF
        'R','L': val:=val*b;
        'C': val:=val/b
      END
    END;

  PROCEDURE PassaBaixasPassaAltas(w:REAL);
  BEGIN
    FOR i:=1 TO el DO WITH circuito[i] DO
      CASE nme[1] OF
        'L': BEGIN val:=1/val/w; tp:=tipo(Ord(tp)+4); nme[1]:='C' END;
        'C': BEGIN val:=1/val/w; tp:=tipo(Ord(tp)-4); nme[1]:='L' END
      END;
  END;

  PROCEDURE PassaBaixasPassaBanda(w,b:REAL);
  VAR
    circuitoc:ckt;
    elc:INTEGER;
  BEGIN
    w:=Sqr(w);
    elc:=el;
    circuitoc:=circuito;
    el:=0;
    num:=0;
    FOR i:=1 TO elc DO WITH circuitoc[i] DO
      CASE tp OF
        Rs,Rp,Rl,Rc: Armazenar(tp,val,0);
        Lp: BEGIN
              Armazenar(Lsp,val/b,1);
              Armazenar(Csp,b/val/w,0)
            END;
        Ls: BEGIN
              Armazenar(Ls,val/b,1);
              Armazenar(Cs,b/val/w,0)
            END;
        Lsp:BEGIN
              Armazenar(Lsp,val/b,1);
              Armazenar(Csp,b/val/w,0)
            END;
        Lps:BEGIN
              Armazenar(Lps,val/b,1);
              Armazenar(Cps,b/val/w,0)
            END;
        Cs: BEGIN
              Armazenar(Cps,val/b,1);
              Armazenar(Lps,b/val/w,0)
            END;
        Cp: BEGIN
              Armazenar(Cp,val/b,1);
              Armazenar(Lp,b/val/w,0)
            END;
        Cps:BEGIN
              Armazenar(Cps,val/b,1);
              Armazenar(Lps,b/val/w,0)
            END;
        Csp:BEGIN
              Armazenar(Csp,val/b,1);
              Armazenar(Lsp,b/val/w,0)
            END;
      END;
    WriteLn(tl,#10'Transformar tanques LC sÇrie duplos? [s/n] ');
    REPEAT r:=UpCase(ReadKey) UNTIL r in ['S','N'];
    IF r='S'THEN BEGIN
      i:=0;
      WHILE i<=el-3 DO BEGIN
        i:=i+1;
        IF (circuito[i].tp=Lps) and (circuito[i+1].tp=Cps) and (circuito[i+2].tp=Cps) and (circuito[i+3].tp=Lps)
        THEN BEGIN
          temp:=circuito[i+2];
          circuito[i+2]:=circuito[i+3];
          circuito[i+3]:=temp;
          MudarTanque(circuito[i+2].val,circuito[i+3].val,circuito[i  ].val,circuito[i+1].val,
                      circuito[i  ].val,circuito[i+1].val,circuito[i+2].val,circuito[i+3].val);
          WriteLn(tl,'Transformado tanque sÇrie [LCCL ',circuito[i].nme,']-[',circuito[i+3].nme,']');
          i:=i+3;
        END
        ELSE IF (circuito[i].tp=Cps) and (circuito[i+1].tp=Lps) and (circuito[i+2].tp=Lps) and (circuito[i+3].tp=Cps)
        THEN BEGIN
          temp:=circuito[i];
          circuito[i]:=circuito[i+1];
          circuito[i+1]:=temp;
          MudarTanque(circuito[i  ].val,circuito[i+1].val,circuito[i+2].val,circuito[i+3].val,
                      circuito[i  ].val,circuito[i+1].val,circuito[i+2].val,circuito[i+3].val);
          WriteLn(tl,'Transformado tanque sÇrie [CLLC ',circuito[i].nme,']-[',circuito[i+3].nme,']');
          i:=i+3;
        END
      END
    END
  END;

BEGIN
  b:=1; w:=1;
  WriteLn(tl,'[TransformaáÑo a aplicar]:');
  WriteLn;
  WriteLn(tl,'- [A]   Passa-Baixas - Passa-Altas');
  WriteLn(tl,'- [B]   Passa-Baixas - Passa-Banda');
  WriteLn(tl,'- [R]   Passa-Baixas - Rejeita-Banda');
  WriteLn(tl,'- [I]   Escalar em impedÉncia');
  WriteLn(tl,'- [F]   Escalar em freqÅància');
  WriteLn(tl,'- [O]   Otimizar dispersÑo de valores LC');
  WriteLn(tl,'- [U]   Recuperar rede original');
  WriteLn(tl,'- [Esc] NÑo transformar');
  WriteLn;
  REPEAT r:=UpCase(ReadKey) UNTIL r in ['A','B','R','I','F','O','U',#27];
  CASE r OF
    #27:Exit;
    'O':BEGIN
          menorL:=1e30;
          menorC:=1e30;
          FOR i:=1 TO el DO WITH circuito[i] DO BEGIN
             IF (nme[1]='C') and (val<menorC) THEN menorC:=val
             ELSE IF (nme[1]='L') and (val<menorL) THEN menorL:=val
          END;
          b:=Sqrt(menorC/menorL);
          EscalaEmImpedancia(b);
          WriteLn('Resistància unit†ria para terminaáîes:');
          Armazenar(Rp,b,0);
        END;
    'U':BEGIN
          circuito:=circuitob;
          el:=elb
        END;
    'I':BEGIN
          Write('Fator de escalamento em impedÉncia: '); LerReal(b);
          EscalaEmImpedancia(b)
        END;
    'F':BEGIN
          Write('Fator de escalamento em freqÅància: '); LerReal(w);
          FOR i:=1 TO el DO WITH circuito[i] DO
            IF nme[1]<>'R' THEN val:=val/w
        END;
    'A':BEGIN
          Write('FreqÅància de corte: (rad/s) '); LerReal(w);
          PassaBaixasPassaAltas(w)
        END;
    'B':BEGIN
          Write('FreqÅància central: (rad/s) '); LerReal(w);
          Write('Largura da banda passante (rad/s) : '); LerReal(b);
          PassaBaixasPassaBanda(w,b)
        END;
    'R':BEGIN
          Write('FreqÅància central: (rad/s) '); LerReal(w);
          Write('Largura da banda de rejeiáÑo (rad/s) : '); LerReal(b);
          PassaBaixasPassaAltas(1);
          PassaBaixasPassaBanda(w,b)
        END;

  END
END;

BEGIN
  DetectGraph(placa,modo);
  IF placa=CGA THEN modo:=CGAC0;
  IF paramcount=2 THEN BEGIN
    Val(ParamStr(1),placa,i);
    Val(ParamStr(2),modo,i);
  END;
  InitGraph(placa,modo,GetEnv('TPBGI'));
  IF placa<>CGA THEN BEGIN
    cor1:=EgaWhite;
    cor2:=EgaYellow;
    cor3:=EgaLightGray
  END
  ELSE BEGIN
    cor1:=3;
    cor2:=1;
    cor3:=2;
  END;
  xmax:=GetMaxX;
  ymax:=GetMaxY-10;
  xmin:=pixmin;
  ymin:=10;
  InitSprite(cor2,cor3);
  x0:=pxmin;
  xm:=GetMaxX; {xm-x0 deve ser m£ltiplo de 4}
  mx2:=(xm+x0) div 2;
  mx1:=(x0+mx2) div 2;
  mx3:=(mx2+xm) div 2;
  y0:=0;
  ym:=GetMaxY-10;
  RestoreCrtMode;
  disp:=1e-8; cm:=20; dc:=15; n:=0; m:=0;
 Inicio:
  ClrScr;
  WriteLn(tl,'[…ÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕª');
  WriteLn('∫   ExpansÑo de redes Ladder   ∫');
  WriteLn('∫ Antìnio Carlos M. de Queiroz ∫');
  WriteLn('∫         COPPE/UFRJ           ∫');
  WriteLn(tl,'»ÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕº]');
  WriteLn('VersÑo ',versao,' - PrecisÑo ',precisao);
  WriteLn;
  WriteLn('Este programa realiza a expansÑo de uma imitÉncia RLC em "ladder", realizando');
  WriteLn('zeros de transmissÑo especificados.  A imitÉncia a expandir  pode ser  gerada');
  WriteLn('pelo programa HK, no caso de realizaáîes em  "ladder" ou "lattice" LC  dupla-');
  WriteLn('mente terminada. Expansîes RLC por "chop-chop" tambÇm podem ser  feitas,  in-');
  WriteLn('clusive com zeros de transmissÑo complexos realizados por tanques LC com per-');
  WriteLn('das. O programa realiza apenas  extraáîes no infinito,  produzindo redes pas-');
  WriteLn('sa-baixas. Transformaáîes  em  freqÅància  e impedÉncia da  rede obtida podem');
  WriteLn('ser feitas ao final da s°ntese.');
  WriteLn;
  Write(tl,'A imitÉncia a expandir Ç uma [I]mpedÉncia ou [A]dmitÉncia? ');
  REPEAT r:=UpCase(ReadKey) UNTIL r in ['I','A'];
  IF r='A' THEN imit:=Y ELSE imit:=Z;
  Write(#13);
  EscreveTipo; WriteLn; WriteLn;
  WriteLn(tl,'[Zeros] de transmissÑo a realizar (opcional)');
  LerRaizes(z1,z2,nz);
  WriteLn(tl,#10'[P¢los] da f. de t. a realizar (opcional)');
  LerRaizes(p1,p2,np);
  IF imit=Z THEN ch:='Z' ELSE ch:='Y';
  WriteLn(tl,#10'[O que ser† realizado]:'#10);
  WriteLn(tl,'- [P] ',ch,' dada por numerador e denominador polinomiais');
  WriteLn(tl,'- [S] ',ch,' metade para rede simÇtrica');
  WriteLn(tl,'- [A] ',ch,' metade para rede antimÇtrica');
  WriteLn;
  REPEAT ch:=UpCase(ReadKey) UNTIL ch in ['P','S','A'];
  CASE ch of
    'P':BEGIN
          WriteLn(tl,'[Numerador]:');
          LerPolinomio(n,a,d0);
          WriteLn(tl,'[Denominador]:');
          LerPolinomio(m,b,d1);
          k:=d0/d1;
        END;
    'S':BEGIN
          WriteLn('Os p¢los da transferància a realizar, e um poss°vel par de zeros simples de');
          WriteLn('transmissÑo finitos em jw, devem ser separados em duas partes, que serÑo p¢los');
          WriteLn('e zeros da imitÉncia de meia-rede.'#10);
          Write('Grau do numerador da imitÉncia realizar: '); LerInt(n);
          Write('Grau do denominador da imitÉncia a realizar: '); LerInt(m);
          WriteLn(tl,#10'Escolha os [',n,' zeros da imitÉncia] (conjugados sÑo assumidos):');
          ListarRaizes('z',z1,z2,nz);
          ListarRaizes('p',p1,p2,np);
          MontarPolinomioReal(n,a,d0);
          WriteLn(tl,'Escolha os [',m,' p¢los da imitÉncia] (conjugados sÑo assumidos):');
          ListarRaizes('z',z1,z2,nz);
          ListarRaizes('p',p1,p2,np);
          MontarPolinomioReal(m,b,d1);
          k:=d0/d1;
        END;
    'A':BEGIN
          WriteLn(tl,'[*] NÑo implementado. Use o programa ELETSIM [*]');
          Delay(1000);
          GoTo Inicio
        END;
  END;
  fim:=FALSE;
  Normalizar;
  Salvar;
  el:=0;
  num:=0;
  WriteLn('#');
  Menu;
  WriteLn('#');
  REPEAT
    r:=UpCase(ReadKey);
    IF not fim THEN BEGIN
      CASE r of
        'P':ExtrairPoloNoInfinito;
        'C':ExtrairCteNoInfinito;
        'X':ExtrairCteDada;
        'I':Inverter;
        'L':ListarImitancia;
        'R':Grafico(tau,wmin,wmax,zmin,zmax);
        'G':Grafico(jw,wmin,wmax,zmin,zmax);
        'Z':ExtrairParPoloNoInfinito;
        'T':ExtrairParCteNoInfinito;
        'F':BEGIN
              ListarRaizes('z',z1,z2,nz);
              PedirZero;
              RemoverPolos
            END;
      END;
      IF fim THEN BEGIN
        WriteLn(tl,'[*] S°ntese completa [*]');
        circuitob:=circuito;
        elb:=el;
        WriteLn('#');
        Menu
      END;
    END;
    CASE r of
      'M':BEGIN
            Write('Nova dispersÑo/tolerÉncia'); LerReal(disp);
            Write('Tamanho de n£meros reais'); LerInt(cm);
            Write('N£mero de decimais'); LerInt(dc)
          END;
      ^R :Recomecar;
      ^O :GoTo Inicio;
      'E':BEGIN
            FOR i:=1 TO el DO WITH circuito[i] DO
              WriteLn(tl,'[',nme,']: ',val:cm:dc,' ',Comentario(tp));
          END;
      'S':BEGIN
            Write(tl,'Arquivo onde salvar: ['); ReadLn(nome); Write(tl,']');
            Assign(arquivo,nome);
            ReWrite(arquivo);
            FOR i:=1 TO el DO WITH circuito[i] DO
              WriteLn(arquivo,nme,' ',val:cm:dc,Comentario(tp));
            Close(arquivo);
            WriteLn('#');
            WriteLn('Edite o arquivo para colocar numeraáÑo de n¢s, terminaáîes, etc.,');
            WriteLn('ou use-o como lista de valores no programa EdFil.');
          END;
      'N':Transformar;
      #27:BEGIN
            Write('Terminar');
            LerBool(terminar);
          END;
      #13:Menu
    END;
    WriteLn('#');
  UNTIL terminar;
END.
