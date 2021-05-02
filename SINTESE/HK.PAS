PROGRAM HK;
{******************************************************************************
 * Aproxima‡”es por Fun‡„o Caracter¡stica                                     *
 * Ant“nio Carlos M. de Queiroz - COPPE/UFRJ - 1987                           *
 * V. 1.3  de 10/10/87                                                        *
 * V. 1.4  de 22/03/88 KdeH corrigido, ReadKey                                *
 * V. 1.5  de 20/04/88 Bessel inclu¡do                                        *
 * V. 1.6  de 05/07/88 Leitura de polin“mio melhor, aviso na lattice: Ke=0    *
 * V. 1.7  de 31/08/88 S¡ntese de imitƒncias com P(s) par                     *
 * V. 1.8  de 13/02/89 Turbo 5.0                                              *
 * V. 1.9  de 07/07/89 Inclu¡do c lculo de ra¡zes m£ltiplas, etc.             *
 * V. 2.0  de 20/07/89 Corrigida convers„o w - s                              *
 * V. 2.0a de 02/09/89 Corre‡„o no menu                                       *
 * V. 2.0b de 28/11/89 Precis„o extendida                                     *
 * V. 2.0c de 07/01/90 Mudado tratamento da cte na montagem de polin“mios     *
 * V. 2.1  de 18/03/90 Edi‡„o de polin“mios inclu¡da                          *
 * V. 2.2  de 23/06/90 Termina‡”es de rede LCDT e rede LCST inclu¡dos         *
 * V. 2.3  de 25/10/90 Rotina de ra¡zes atualizada                            *
 * V. 2.4  de 27/03/91 Cheb. mod. simplificado, novos gr ficos                *
 * V. 2.4a de 10/04/91 Impedƒncias Z1 e Z2 calculadas, controle de xr e xi    *
 * V. 2.4b de 08/06/92 Escalamento em frequencia                              *
 * V. 2.4c de 31/03/94 Salva curvas, confirma saida                           *
 * V. 2.5  de 13/12/02 Graficos com escala linear, E(s) sempre positivo       *
 * V. 2.5a de 18/07/03 Polin“mios normalizados na leitura, y valido nas Z/Y   *
 ******************************************************************************}
{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}

USES Crt,Dos,Graph,Tela;

{$I seta.p}

CONST
  gmax=200;
  versao='2.5a de 18/07/2003';
TYPE
  coeficientes=ARRAY[0..gmax] OF REAL;
  polinomio=RECORD
    a:coeficientes;
    grau:INTEGER;
    cte:REAL;
    existe:BOOLEAN
  END;
  conjunto=SET OF #27..'Z';
VAR
  x,y,z,t,f,e,p,q:polinomio;
  zr,zi:ARRAY[1..gmax] OF REAL;
  i,j,n,l,cm,dc:INTEGER;
  ch:CHAR;
  arquivo:TEXT;
  txt:STRING;
  xr0,xi0,epsilon,w0,Amin,Amax,tolr,toln,tolm,told:REAL;
  inicigual,ok,raizes_calculadas,erro:BOOLEAN;
CONST
  pixmin=43;
  yr1:REAL=-2.0;
  xr1:REAL=-2.0;
  delta:REAL=4;
  pxmin=75;
  pxmax=719;
  wmin:REAL=0.1;
  wmax:REAL=10;
  mmin:REAL=-10;
  mmax:REAL=70;
  mminl:REAL=0;
  mmaxl:REAL=10;
  tmin:REAL=-70;
  tmax:REAL=10;
  fmin:REAL=-180;
  fmax:REAL=180;
  dmin:REAL=0;
  dmax:REAL=40;
  log:BOOLEAN=TRUE;
  logy:BOOLEAN=TRUE;
  grade:BOOLEAN=TRUE;
  fatorw:REAL=1;
  salvarcurva:BOOLEAN=FALSE;
  terminar:BOOLEAN=FALSE;
VAR
  cor1,cor2,cor3,placa,modo:INTEGER;
  x0,xm,mx1,mx2,mx3,y0,ym:INTEGER;
  xmin,xmax,ymin,ymax:INTEGER;
  fator:REAL;
  xasp,yasp:WORD;

PROCEDURE LerNome;
BEGIN
  Write(tl,' ([Enter] ou nome)[ ');
  ReadLn(txt);
  Write(tl,']');
END;

PROCEDURE LerResposta(valido:conjunto);
BEGIN
  Write(tl,'[?]');
  REPEAT
    ch:=UpKey
  UNTIL ch IN valido;
  WriteLn(tl,' [',ch,']');
END;

PROCEDURE PlotarRaizes;
  VAR
    x2,y2,ay,by,ax,bx,t:REAL;
    indice:INTEGER;

  FUNCTION Limx(x:REAL):INTEGER;
  BEGIN
    t:=ax*x+bx;
    IF t>xmax THEN Limx:=xmax
    ELSE IF t<xmin THEN Limx:=xmin
    ELSE Limx:=Round(t)
  END;

  FUNCTION Limy(y:REAL):INTEGER;
  BEGIN
    t:=ay*y+by;
    IF t>ymax THEN Limy:=ymax
    ELSE IF t<ymin THEN Limy:=ymin
    ELSE Limy:=Round(t)
  END;

  PROCEDURE Plotar;
    VAR
      cx,cy:INTEGER;
  BEGIN
    FOR i:=1 TO x.grau DO BEGIN
      cx:=Limx(zr[i]);
      cy:=Limy(zi[i]);
      Line(cx-2,cy-2,cx+2,cy+2);
      Line(cx-2,cy+2,cx+2,cy-2)
    END
  END;

  PROCEDURE Cursor;
  BEGIN
    indice:=1; RemoveSprite;
    REPEAT
      Bar(0,0,GetMaxX,9);
      MoveTo(0,0);
      Str(zr[indice]:7:4,txt); OutText('Raiz:'+txt);
      Str(zi[indice]:7:4,txt); OutText(txt+'j');
      t:=Sqrt(Sqr(zr[indice])+Sqr(zi[indice]));
      Str(t:7:4,txt); OutText(' w:'+txt);
      IF Abs(zr[indice])<tolm THEN txt:=' oo' ELSE Str(-t/2/zr[indice]:7:4,txt); OutText(' Q:'+txt);
      PutSprite(Limx(zr[indice]),Limy(zi[indice]));
      ch:=ReadKey;
      CASE ch OF
      #13,#9:IF indice<x.grau THEN indice:=indice+1 ELSE indice:=1;
      #8:IF indice>1 THEN indice:=indice-1 ELSE indice:=x.grau;
      #0:BEGIN
          ch:=ReadKey;
          CASE ch OF
          'M': xr1:=xr1+delta/4;
          'K': xr1:=xr1-delta/4;
          'H': yr1:=yr1+delta/4;
          'P': yr1:=yr1-delta/4;
          END
        END;
      '-':BEGIN
          xr1:=xr1-delta/2;
          yr1:=yr1-delta/2;
          delta:=delta*2
        END;
      '+':BEGIN
          delta:=delta/2;
          xr1:=xr1+delta/2;
          yr1:=yr1+delta/2
        END;
      ' ':BEGIN
          xr1:=zr[indice]-delta/2;
          yr1:=zi[indice]-delta/2
        END;
      END
    UNTIL ch IN [#27,'M','K','H','P','+','-',' '];
  END;

BEGIN
  IF raizes_calculadas THEN BEGIN
    REPEAT
      y2:=yr1+delta;
      ay:=(ymax-ymin)/(yr1-y2);
      by:=ymax-ay*yr1;
      ax:=-ay*fator;
      bx:=xmin-ax*xr1;
      x2:=(xmax-bx)/ax;
      SetGraphMode(modo);
      SetFillStyle(emptyfill,cor1);
      Line(0,ymax,xmax,ymax);
      Line(xmin,ymin,xmin,GetMaxY);
      SetColor(cor3);
      Line(Limx(0),ymin,Limx(0),ymax);
      Line(xmin,Limy(0),xmax,Limy(0));
      SetColor(cor2);
      Circle(Round(bx),Round(by),Round(ax));
      SetColor(cor1);
      Str(y2:5:1,txt); OutTextXY(0,ymin,txt);
      Str(yr1:5:1,txt); OutTextXY(0,ymax-8,txt);
      Str(xr1:8:3,txt); OutTextXY(xmin+1,ymax+2,txt);
      Str(x2:8:3,txt); OutTextXY(xmax-64,ymax+2,txt);
      OutTextXY(xmin+2,ymin,'Im');
      OutTextXY(xmax-16,ymax-8,'Re');
      Plotar;
      Cursor
    UNTIL ch=#27;
    PutSprite(-10,-10);
    RestoreCrtMode
  END
  ELSE WriteLn(tl,'[*] N„o h  ra¡zes calculadas [*]');
END;

TYPE tipodegrafico=(deH,deK,deT,deF,deA);

PROCEDURE Grafico(x,y:polinomio; tipo:tipodegrafico; VAR x1,x2,y1,y2:REAL);
  VAR
    ax,bx,ay,by,kk,w,d,a1,a2,b1,b2,t1,t2:REAL;
    j,xg,xa,ya:INTEGER;
    ponto:ARRAY[pxmin..pxmax] OF REAL;
    calculado:ARRAY[pxmin..pxmax] OF BOOLEAN;
    tempx,tempy:BOOLEAN;
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
      PutSprite(xg,Limy(ponto[xg]));
      Bar3D(xm-110,y0+3,xm-4,y0+21,4,TRUE);
      w:=(xg-bx)/ax;
      IF log THEN w:=Exp(w);
      Str(w:11:6,txt); OutTextXY(xm-108,y0+5,'w:'+txt);
      Str(ponto[xg]:11:6,txt); OutTextXY(xm-108,y0+13,'y:'+txt);
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
    Bar(xm-110,y0+1,xm-1,y0+21);
  END;

BEGIN
  IF NOT (x.existe AND y.existe) THEN BEGIN
    WriteLn(tl,'[*] Fun‡„o indefinida [*]');
    Exit
  END;
  IF (x1<=0) or (x2<=0) THEN log:=FALSE;
  IF (x2<=x1) or (y2<=y1) THEN grade:=FALSE;
  FOR j:=x0 TO xm DO calculado[j]:=FALSE;
  kk:=x.cte/y.cte;
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
    Str(x1:9:4,txt); WHILE txt[1]=' ' DO txt:=Copy(txt,2,255); OutTextXY(x0,ym+2,txt);
    Str(x2:9:4,txt); OutTextXY(xm-72,ym+2,txt);
    Str(y1:9:4,txt); OutTextXY(x0-72,ym-8,txt);
    Str(y2:9:4,txt); OutTextXY(x0-72,y0,txt);
    CASE tipo OF
      deT:IF logy THEN txt:='|T|(dB)' ELSE txt:='|T|';
      deH:IF logy THEN txt:='|H|(dB)' ELSE txt:='|H|';
      deK:IF logy THEN txt:='|K|(dB)' ELSE txt:='|K|';
      deF:txt:='<T (gr)';
      deA:txt:='Tg (s)'
    END;
    OutTextXY(x0-56,(ym+y0-8) div 2,txt);
    OutTextXY((x0+xm) div 2-20,ym+2,'rad/s');
    FOR xg:=x0 TO xm DO BEGIN
      w:=(xg-bx)/ax;
      IF log THEN w:=Exp(w);
      IF NOT calculado[xg] THEN BEGIN
        b1:=0; b2:=0;
        FOR j:=y.grau DOWNTO 0 DO
          BEGIN d:=b1*w; b1:=y.a[j]-w*b2; b2:=d END;
        a1:=0; a2:=0;
        FOR j:=x.grau DOWNTO 0 DO
          BEGIN d:=a1*w; a1:=x.a[j]-w*a2; a2:=d END;
        IF (b1=0) or (b2=0) THEN BEGIN
          d:=Sqr(b1)+Sqr(b2);
          IF d=0 THEN d:=1e-20;
          t1:=kk*(a1*b1+a2*b2)/d;
          t2:=kk*(a2*b1-a1*b2)/d
        END
        ELSE BEGIN
          d:=b1/b2+b2/b1;
          t1:=kk*(a1/b2+a2/b1)/d;
          t2:=kk*(a2/b2-a1/b1)/d
        END;
        IF t1=0 THEN t1:=1e-20;
        IF t2=0 THEN t2:=1e-20;
        CASE tipo OF
          deT,deH,deK:BEGIN
                        d:=Sqr(t1)+Sqr(t2);
                        IF d=0 THEN d:=1e-20;
                        IF logy THEN d:=Ln(d)*4.342944818
                        ELSE d:=Sqrt(d)
                      END;
          deA:d:=t1;
          deF:BEGIN
                d:=180/Pi*ArcTan(t2/t1);
                IF t1<0 THEN BEGIN
                  IF t2>0 THEN d:=d+180
                  ELSE d:=d-180
                END
              END;
        END;
        ponto[xg]:=d;
        calculado[xg]:=TRUE
      END;
      IF salvarcurva THEN WriteLn(arquivo,w,' ',ponto[xg]);
      IF xg>x0 THEN
        Line(xa,Limy(ponto[xg-1]),xg,Limy(ponto[xg]));
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
           a1:=x1; a2:=x2; tempx:=log; tempy:=logy;
           Write('Escala horizontal logar¡tmica'); LerBool(log);
           IF tipo in [deH,deK,deT] THEN BEGIN
             Write('Escala vertical logar¡tmica'); LerBool(logy);
           END;
           Write('w m¡nimo'); LerReal(x1);
           Write('w m ximo'); LerReal(x2);
           Write('y m¡nimo'); LerReal(y1);
           Write('y m ximo'); LerReal(y2);
           IF (a1<>x1) or (a2<>x2) or (tempx<>log) or (tempy<>logy) THEN
             FOR j:=x0 TO xm DO calculado[j]:=FALSE;
           Write(tl,'Salvar tabela ap¢s o pr¢ximo gr fico? ([Enter] ou nome) [');
           ReadLn(txt); Write(tl,']');
           IF txt<>'' THEN BEGIN
             Assign(arquivo,txt);
             ReWrite(arquivo);
             salvarcurva:=TRUE;
           END
         END
    END
  UNTIL ch=#27;
  RestoreCrtMode;
END;

FUNCTION Inexistente:BOOLEAN;
BEGIN
  Inexistente:=NOT x.existe;
  IF NOT x.existe THEN
    WriteLn(tl,'[*] Polin“mio ainda indefinido [*]')
END;
  
PROCEDURE Limpar;
  VAR
    max:REAL;
BEGIN
  WITH x DO BEGIN
    max:=0;
    FOR i:=0 TO grau DO IF Abs(a[i])>max THEN max:=Abs(a[i]);
    max:=max/toln;
    FOR i:=0 TO grau DO IF Abs(a[i])<max THEN a[i]:=0;
    WHILE (a[grau]=0) AND (grau>=0) DO grau:=grau-1;
  END
END;

PROCEDURE RaizesBiv; {Ra¡zes do polinomio x por Birge-Vieta}
  CONST
    imax=50;
  VAR
    a1,a2,c1,c2:coeficientes;
    Imag,told1,tolm1,t,tolr1,p1,p2,d,xr,xi,p,d1,d2,e1,e2:REAL;
    feito:BOOLEAN;
    nn,n,ordem:INTEGER;

  FUNCTION Cmult(x1,x2,y1,y2:REAL):REAL;
  BEGIN
    Cmult:=x1*y1-x2*y2;
    Imag:=x1*y2+x2*y1
  END;

BEGIN {Programa principal RaizesBiv}
  IF inexistente THEN Exit;
  told1:=told; tolm1:=tolm; tolr1:=tolr; n:=x.grau; a1:=x.a; ordem:=0;
  xr:=xr0; xi:=xi0; feito:=FALSE; nn:=0;
  IF n<1 THEN
    BEGIN WriteLn(tl,'[*] N„o h  raizes a calcular'); Exit END;
  FOR i:=0 TO n DO a2[i]:=0;
  Write(tl,'Calculando...[');
  {Elimina‡„o de ra¡zes na origem}
  WHILE (n>1) AND (a1[0]=0) DO BEGIN
    zr[n]:=0; zi[n]:=0;
    Write(n,' ');
    n:=n-1;
    FOR i:=0 TO n DO a1[i]:=a1[i+1]
  END;
  WHILE NOT feito DO BEGIN
    IF n>1 THEN BEGIN
      {Calculo dos valores do polin“mio (p) e de sua derivada (d)}
      d1:=a1[n]; p1:=d1;
      d2:=a2[n]; p2:=d2;
      FOR i:=n-1 DOWNTO 0 DO BEGIN
        p1:=Cmult(p1,p2,xr,xi)+a1[i];
        p2:=Imag+a2[i];
        IF i>0 THEN BEGIN
          d1:=Cmult(d1,d2,xr,xi)+p1;
          d2:=Imag+p2;
        END
      END;
      {C lculo do erro. Esta forma dificulta overflow}
      IF (d1=0) OR (d2=0) THEN BEGIN
        d:=Sqr(d1)+Sqr(d2);
        e1:=(p1*d1+p2*d2)/d;
        e2:=(p2*d1-p1*d2)/d
      END
      ELSE BEGIN
        d:=d1/d2+d2/d1;
        e1:=(p1/d2+p2/d1)/d;
        e2:=(p2/d2-p1/d1)/d
      END;
      {Testa poss¡vel ra¡z m£ltipla}
      d:=Abs(d1)+Abs(d2);
      p:=Abs(p1)+Abs(p2);
      IF (d<told1) AND (p<tolm1) THEN BEGIN
        {deriva o polin“mio e continua}
        IF ordem=0 THEN BEGIN c1:=a1; c2:=a2 END;
        FOR i:=1 TO n DO BEGIN
          a1[i-1]:=a1[i]*i/n;
          a2[i-1]:=a2[i]*i/n;
        END;
        n:=n-1; ordem:=ordem+1;
        Write('+')
      END
      ELSE BEGIN
        {Atualiza ra¡zes}
        xr:=xr-e1;
        xi:=xi-e2;
        {Testa convergˆncia}
        t:=Abs(e1)+Abs(e2);
        IF t<tolr1 THEN BEGIN
          {Armazena ra¡zes calculadas}
          FOR i:=n+ordem DOWNTO n DO BEGIN
            Write(i,' ');
            zr[i]:=xr; zi[i]:=xi;
          END;
          {Rep”e polin“mio original, se for o caso}
          IF ordem>0 THEN BEGIN
            a1:=c1; a2:=c2; n:=n+ordem;
          END;
          {Deflaciona polin“mio}
          FOR i:=0 TO ordem DO BEGIN
            FOR j:=n-1 DOWNTO 1 DO BEGIN
              a1[j]:=Cmult(xr,xi,a1[j+1],a2[j+1])+a1[j];
              a2[j]:=Imag+a2[j];
            END;
            n:=n-1;
            FOR j:=0 TO n DO
              BEGIN a1[j]:=a1[j+1]; a2[j]:=a2[j+1] END
          END;
          {Prepara c lculo da pr¢xima ra¡z}
          IF inicigual THEN BEGIN xi:=xi0; xr:=xr0 END
          ELSE BEGIN
            IF (Abs(xi)>0.01) THEN xi:=-xi ELSE xi:=0.1;
            IF ordem>0 THEN xr:=xr-0.01; {evita derivada 0 a seguir}
          END;
          ordem:=0; nn:=0;
        END
        ELSE BEGIN
          nn:=nn+1;
          {Demorando a convergir}
          IF (nn>imax) OR KeyPressed THEN BEGIN
            WriteLn(tl,#10#13'[*] Problemas de convergˆncia.');
            IF ordem>0 THEN WriteLn(tl,'[*] Ra¡z de multiplicidade ',ordem+1);
            WriteLn('  Erro atual: ',t);
            WriteLn('  Magnitude:  ',p);
            WriteLn('  Derivada:   ',d);
            Write('  Tolerƒncia p/ra¡zes'); LerReal(tolr1);
            Write('  Tolerƒncia p/magnitudes'); LerReal(tolm1);
            Write('  Tolerƒncia p/derivadas'); LerReal(told1);
            Write('  Aproxima‡„o real'); LerReal(xr);
            Write('  Aproxima‡„o imag'); LerReal(xi);
            Write(tl,'[');
            nn:=0;
          END
        END
      END
    END
    ELSE BEGIN
      {Ultimas ra¡zes}
      d:=-(Sqr(a1[1])+Sqr(a2[1]));
      xr:=(a1[0]*a1[1]+a2[0]*a2[1])/d;
      xi:=(a2[0]*a1[1]-a1[0]*a2[1])/d;
      feito:=TRUE; nn:=0;
      FOR i:=n+ordem DOWNTO n DO BEGIN
        Write(i,' ');
        zr[i]:=xr; zi[i]:=xi;
      END
    END
  END;
  WriteLn(tl,']');
  raizes_calculadas:=TRUE
END; {RaizesBiv}

FUNCTION Angle(re,im:REAL):REAL;
  CONST pouco=1e-9;
  VAR fase:REAL;
BEGIN
  IF Abs(re)<pouco THEN BEGIN
    IF Abs(im)<pouco THEN Angle:=0
    ELSE
      IF im>0 THEN Angle:=pi/2
      ELSE Angle:=-pi/2
  END
  ELSE BEGIN
    fase:=ArcTan(im/re);
    IF re<0 THEN
      IF im>0 THEN fase:=fase+pi ELSE fase:=fase-pi;
    Angle:=fase
  END
END;

PROCEDURE ConverterParaS(VAR x:polinomio);
BEGIN
  WITH x DO BEGIN
    FOR i:=0 TO grau DO BEGIN
      j:=i MOD 4;
      IF ((j=1) OR (j=2)) THEN a[i]:=-a[i]
    END;
    IF a[grau]<0 THEN FOR i:=0 TO grau DO a[i]:=-a[i];
    cte:=Abs(cte);
  END
END;

FUNCTION Ex(x,y: REAL): REAL;
BEGIN Ex:=Exp(y*Ln(x)) END;

PROCEDURE Selecionar;
BEGIN
  Write(tl,'[Q](w),[F](s),[P](s) ou [E](s) (ou [X](s),[Y](s))');
  LerResposta(['Q','F','P','E','X','Y']);
  CASE ch OF
  'F':x:=f;
  'P':x:=p;
  'E':x:=e;
  'Q':x:=q;
  'Y':x:=y;
  END
END;

PROCEDURE Distribuir;
BEGIN
  CASE ch OF
  'F':f:=x;
  'P':p:=x;
  'E':e:=x;
  'Q':q:=x;
  'Y':y:=x
  END
END;

PROCEDURE MultS;
BEGIN
  WITH x DO BEGIN
    FOR i:=grau DOWNTO 0 DO a[i+1]:=a[i];
    a[0]:=0;
    grau:=grau+1;
  END
END;

PROCEDURE MultC(c:REAL);
BEGIN
  x.cte:=x.cte*c
END;

PROCEDURE Normalizar;
BEGIN
  Limpar;
  WITH x DO BEGIN
    IF a[grau]<>1 THEN BEGIN
      cte:=cte*a[grau];
      FOR i:=0 TO grau DO a[i]:=a[i]/a[grau]
    END
  END
END;

PROCEDURE Somar;
BEGIN
  FOR i:=x.grau+1 TO y.grau DO x.a[i]:=0;
  IF x.grau<y.grau THEN x.grau:=y.grau;
  FOR i:=0 TO y.grau DO x.a[i]:=x.cte*x.a[i]+y.cte*y.a[i];
  x.cte:=1;
  Limpar;
  y:=z; z:=t
END;

PROCEDURE Negar;
BEGIN
  x.cte:=-x.cte
END;

PROCEDURE Subtrair;
BEGIN
  Negar;
  Somar;
END;
  
PROCEDURE Multiplicar;
  VAR m:coeficientes;
BEGIN
  m:=x.a;
  FOR i:=0 TO x.grau+y.grau DO x.a[i]:=0;
  FOR i:=0 TO x.grau DO
    FOR j:=0 TO y.grau DO
      x.a[i+j]:=x.a[i+j]+m[i]*y.a[j];
  x.cte:=x.cte*y.cte;
  x.grau:=x.grau+y.grau;
  y:=z; z:=t;
END;
  
PROCEDURE ListarPolinomio;
BEGIN
  IF Inexistente THEN Exit;
  WITH x DO BEGIN
    FOR i:=0 TO grau DO WriteLn(tl,'- a([',i:2,']): ',a[i]:cm:dc);
    WriteLn(tl,'- [Cte]:   ',cte:cm:dc);
    Write('Salvar?'); LerNome;
    IF txt<>'' THEN BEGIN
      Assign(arquivo,txt);
      ReWrite(arquivo);
      WriteLn(arquivo,grau);
      FOR i:=0 TO grau DO WriteLn(arquivo,a[i]:cm:dc);
      WriteLn(arquivo,cte:cm:dc);
      Close(arquivo)
    END
  END
END;

PROCEDURE Entrar;
BEGIN
  t:=z; z:=y; y:=x
END;

PROCEDURE Chebyshev(n:INTEGER);
  VAR k:INTEGER;
BEGIN
  x.a[0]:=1; x.grau:=0; x.cte:=1;
  IF n>0 THEN BEGIN
    Entrar;
    MultS;
    FOR k:=2 TO n DO BEGIN
      Entrar;
      MultC(2);
      MultS;
      Entrar;
      x:=t;
      Subtrair
    END
  END;
  x.existe:=TRUE
END;
  
PROCEDURE Bessel(n:INTEGER);
  VAR k:INTEGER;
BEGIN
  x.a[0]:=1; x.a[1]:=1; x.cte:=1; x.grau:=1;
  y.a[0]:=1; y.cte:=1; y.grau:=0;
  IF n=0 THEN x.grau:=0;
  FOR k:=2 TO n DO BEGIN
    Entrar;
    x:=z;
    MultS;
    MultS;
    Entrar;
    x:=z;
    MultC(2*k-1);
    Somar
  END;
  x.existe:=TRUE;
END;
  
PROCEDURE ListarRaizes;
  VAR
    w:REAL;
BEGIN
  IF raizes_calculadas THEN BEGIN
    FOR i:=1 TO x.grau DO
      WriteLn(tl,'- x([',i:2,']):',zr[i]:cm:dc,zi[i]:cm:dc,'j');
    FOR i:=1 TO x.grau DO
      IF (zi[i]>tolm) AND (Abs(zr[i])>tolm) THEN BEGIN
        w:=Sqrt(Sqr(zr[i])+Sqr(zi[i]));
        WriteLn(tl,'[w],[Q]([',i:2,']):',w:cm:dc,-w/2/zr[i]:cm:dc)
      END;
    WriteLn(tl,'- [Cte]:  ',x.cte:cm:dc);
    Write('Salvar?'); LerNome;
    IF txt<>'' THEN BEGIN
      Assign(arquivo,txt);
      ReWrite(arquivo);
      WriteLn(arquivo,x.grau);
      FOR i:=1 TO x.grau DO WriteLn(arquivo,zr[i]:cm:dc,' ',zi[i]:cm:dc);
      WriteLn(arquivo,x.cte:cm:dc);
      Close(arquivo)
    END;
  END
  ELSE WriteLn(tl,'[*] N„o h  ra¡zes calculadas [*]');
END;
  
FUNCTION Valor(w:REAL):REAL;
  VAR p:REAL;
BEGIN
  WITH x DO BEGIN
    p:=a[grau];
    FOR i:=grau-1 DOWNTO 0 DO p:=p*w+a[i];
    Valor:=p
  END
END;
  
PROCEDURE OrdenarRaizes;
  VAR ordenado:BOOLEAN;
    t:REAL;
BEGIN
  REPEAT
    ordenado:=TRUE;
    FOR i:=1 TO x.grau-1 DO BEGIN
      IF zr[i+1]<zr[i] THEN BEGIN
        t:=zr[i]; zr[i]:=zr[i+1]; zr[i+1]:=t;
        t:=zi[i]; zi[i]:=zi[i+1]; zi[i+1]:=t;
        ordenado:=FALSE
      END
    END
  UNTIL ordenado;
END;

PROCEDURE Moebius(n:INTEGER);
  VAR k:INTEGER;
    w:REAL;
BEGIN
  IF Odd(n) THEN BEGIN
    WriteLn(tl,'[*] O grau deve ser par [*]');
    erro:=TRUE;
    Exit
  END;
  Chebyshev(n);
  w:=Cos((n-1)*Pi/(2*n));
  y.a[0]:=Sqr(w); y.a[1]:=0; y.a[2]:=(1-Sqr(w)); y.cte:=1; y.grau:=2;
  Entrar;
  x.a[0]:=y.a[n]; x.cte:=1; x.grau:=0;
    FOR k:=n-2 DOWNTO 0 DO IF NOT Odd(k) THEN BEGIN
      Entrar;
      x:=t;
      Multiplicar;
      x.a[0]:=x.a[0]+y.a[k];
    END;
  x.existe:=TRUE
END;

PROCEDURE Produto(VAR t:polinomio);
  VAR sinal:REAL;
BEGIN
  x.grau:=t.grau;
  x.cte:=Sqr(t.cte);
  FOR i:=0 TO x.grau DO x.a[i]:=0;
  FOR i:=0 TO t.grau DO BEGIN
    IF Odd(i) THEN sinal:=-1 ELSE sinal:=1;
    FOR j:=0 TO t.grau DO
      IF NOT Odd(i+j) THEN BEGIN
        l:=(i+j) DIV 2;
        x.a[l]:=x.a[l]+t.a[i]*t.a[j]*sinal
      END
  END
END;

PROCEDURE Montar(ct:REAL);
  VAR t:REAL;
BEGIN
  x.cte:=ct;
  y.cte:=ct;
  y.grau:=x.grau;
  FOR i:=0 TO x.grau DO
    BEGIN x.a[i]:=0; y.a[i]:=0 END;
  x.a[0]:=1;
  FOR i:=1 TO x.grau DO BEGIN
    FOR j:=i DOWNTO 1 DO BEGIN
      t:=x.a[j-1]-zr[i]*x.a[j]+zi[i]*y.a[j];
      y.a[j]:=y.a[j-1]-zr[i]*y.a[j]-zi[i]*x.a[j];
      x.a[j]:=t
    END;
    t:=-zr[i]*x.a[0]+zi[i]*y.a[0];
    y.a[0]:=-zr[i]*y.a[0]-zi[i]*x.a[0];
    x.a[0]:=t
  END;
  t:=0;
  FOR i:=0 TO y.grau DO IF Abs(y.a[i])>t THEN t:=Abs(y.a[i]);
  IF t>tolm THEN
    WriteLn(tl,'[*] Montagem inexata de polin“mio: examine resto imagin rio em Y [*]');
  x.existe:=TRUE;
  y.existe:=TRUE;
END;

PROCEDURE LerPolinomio;
  VAR rr:CHAR;
    w,Q:REAL;
BEGIN
  rr:=ch;
  WITH x DO BEGIN
    REPEAT
      Write(tl,'[C]oeficientes, [R]aizes ou w e [Q]');
      LerResposta(['C','R','Q']);
      CASE ch OF
      'C':BEGIN
          Write(tl,'Arquivo:'); LerNome;
          IF txt<>'' THEN BEGIN
            Assign(arquivo,txt);
            {$I-} Reset(arquivo); {$I+}
            ok:=IOResult=0;
            IF ok THEN BEGIN
              ReadLn(arquivo,grau);
              FOR i:=0 TO grau DO ReadLn(arquivo,a[i]);
              IF not SeekEof(arquivo) THEN ReadLn(arquivo,cte) ELSE cte:=1;
              Close(arquivo)
            END
            ELSE WriteLn(tl,'[*] Arquivo inexistente [*]')
          END
          ELSE BEGIN
            IF not existe THEN BEGIN
              grau:=0; FOR i:=0 TO gmax DO a[i]:=1; cte:=1
            END;
            Write('Grau'); LerInt(grau);
            FOR i:=0 TO grau DO BEGIN
              Write(tl,'a([',i:2,'])'); LerReal(a[i])
            END;
            Write('Cte'); LerReal(cte);
            IF a[grau]<>1 THEN BEGIN
              Normalizar;
              WriteLn('(Polin“mio armazenado normalizado para a(',grau,')=1)')
            END;
            ok:=TRUE
          END
        END;
      'R':BEGIN
          Write('Arquivo:'); LerNome;
          IF txt<>'' THEN BEGIN
            Assign(arquivo,txt);
            {$I-} Reset(arquivo); {$I+}
            ok:=IOResult=0;
            IF ok THEN BEGIN
              ReadLn(arquivo,grau);
              FOR i:=1 TO grau DO ReadLn(arquivo,zr[i],zi[i]);
              IF not SeekEof(arquivo) THEN ReadLn(arquivo,cte) ELSE cte:=1;
              Close(arquivo)
            END
            ELSE WriteLn(tl,'[*] Arquivo inexistente [*]')
          END
          ELSE BEGIN
            WriteLn(tl,'[Obs]: Se Im<>0 o conjugado ‚ assumido.');
            Write('Grau: '); ReadLn(grau);
            i:=1;
            WHILE i<=grau DO BEGIN
              Write(tl,'Re Im ([',i:2,']): '); ReadLn(zr[i],zi[i]);
              IF Abs(zi[i])>tolm THEN
                IF i<grau THEN BEGIN
                  zr[i+1]:=zr[i];
                  zi[i+1]:=-zi[i];
                  i:=i+1
                 END;
              i:=i+1
            END;
            Write('Cte: '); ReadLn(cte);
            ok:=TRUE;
          END
        END;
      'Q':BEGIN
          WriteLn(tl,'[Obs]: Q=0.5 para raiz real.');
          Write('Grau: '); ReadLn(grau);
          i:=1;
          WHILE i<=grau DO BEGIN
            Write(tl,'w Q ([',i:2,']): '); ReadLn(w,Q);
            IF Q=0.5 THEN BEGIN
              zr[i]:=-w; zi[i]:=0
            END
            ELSE BEGIN
              zr[i]:=-w/2/Q;
              zi[i]:=Sqrt(4*Sqr(w)-Sqr(w/Q))/2;
              IF i<grau THEN BEGIN
                zr[i+1]:=zr[i];
                zi[i+1]:=-zi[i];
                i:=i+1
              END
            END;
            i:=i+1
          END;
          Write('Cte: '); ReadLn(cte);
          ok:=TRUE;
        END;
      END;
      IF ok AND (ch IN ['R','Q']) THEN BEGIN
        raizes_calculadas:=TRUE;
        WriteLn(tl,'[Raizes lidas]:');
        ListarRaizes;
        Montar(cte);
        WriteLn(tl,'[Polinomio obtido]:');
        ListarPolinomio;
      END
    UNTIL ok;
    existe:=TRUE
  END;
  ch:=rr
END;

PROCEDURE FeldtKeller(FouE:CHAR);
  VAR modulo,fase:REAL;
BEGIN
  IF FouE='E' THEN Produto(f) ELSE Produto(e);
  y:=x;
  Produto(p);
  IF FouE='E' THEN Somar ELSE Subtrair;
  x.existe:=TRUE;
  RaizesBiv;
  OrdenarRaizes;
  IF FouE='F' THEN WriteLn(tl,'[Confirme o sinal das ra¡zes de F(s)]:');
  FOR i:=1 TO x.grau DO BEGIN
    modulo:=Sqrt(Sqrt(Sqr(zr[i])+Sqr(zi[i])));
    fase:=Angle(zr[i],zi[i])/2;
    zr[i]:=-modulo*Cos(fase);
    zi[i]:=modulo*Sin(fase);
    IF FouE='F' THEN BEGIN
      REPEAT
        Write(tl,zr[i]:cm:dc,zi[i]:cm:dc,'j; ([R]e,[I]m,[Enter]) ');
        ch:=UpKey;
        IF ch='R' THEN zr[i]:=-zr[i];
        IF ch='I' THEN zi[i]:=-zi[i];
        IF ch<>#13 THEN Write(#13)
      UNTIL ch=#13;
      WriteLn
    END
  END;
  WriteLn(tl,'Ra¡zes de ',FouE,'(s) calculadas.');
  Montar(1);
END;

PROCEDURE HdeK;
BEGIN
  WriteLn(tl,'[C lculo de E(s) pela equa‡„o de FeldtKeller]:');
  IF NOT(f.existe AND p.existe) THEN BEGIN
    WriteLn(tl,'[*] Faltando K(s)=F(s)/P(s) [*]');
    Exit
  END;
  FeldtKeller('E');
  IF f.grau=p.grau THEN MultC(Sqrt(Sqr(f.cte)+Sqr(p.cte))) ELSE MultC(Abs(f.cte)); {p/ evitar E(s) negativo}
  e:=x;
  WriteLn('Polin“mio E(s) calculado.');
END;

PROCEDURE KdeH;
BEGIN
  WriteLn(tl,'[C lculo de F(s) pela equa‡„o de FeldtKeller]:');
  IF NOT(e.existe AND p.existe) THEN BEGIN
    WriteLn(tl,'[*] Faltando H(s)=E(s)/P(s) [*]');
    Exit
  END;
  FeldtKeller('F');
  IF e.grau=p.grau THEN MultC(Sqrt(Sqr(e.cte)-Sqr(p.cte))) ELSE MultC(e.cte);
  f:=x;
  WriteLn('Polin“mio F(s) calculado.');
END;

PROCEDURE ReEscalar;
  VAR u,v:REAL;
BEGIN
  y:=f;
  x:=p;
  MultC(epsilon);
  Subtrair;
  WITH x DO BEGIN
    w0:=1;
    REPEAT
      u:=0; v:=0;
      FOR i:=grau DOWNTO 0 DO BEGIN
        u:=u*w0+a[i];
        IF i<>0 THEN v:=v*w0+i*a[i]
      END;
      u:=u/v;
      w0:=w0-u;
      Write('wp=',w0:cm:dc,#13);
    UNTIL (Abs(u)<tolr) OR KeyPressed
  END;
  WriteLn(tl,#10'Escalar para wp=1? [s/n] (s)');
  ok:=UpKey<>'N';
  IF not ok THEN Exit;
  FOR i:=0 TO p.grau-1 DO p.a[i]:=p.a[i]/Ex(w0,p.grau-i);
  FOR i:=0 TO f.grau-1 DO f.a[i]:=f.a[i]/Ex(w0,f.grau-i);
  p.cte:=p.cte/Ex(w0,f.grau-p.grau);
END;

PROCEDURE Polinomial;
BEGIN
  WriteLn(tl,'[Aproxima‡„o polinomial]:');
  IF NOT q.existe THEN BEGIN
    WriteLn(tl,'[*] Faltando Q(w), pol. caracter¡stico [*]');
    Exit
  END;
  Write('At. m x. na b. p. (dB)'); LerReal(Amax);
  epsilon:=Sqrt(Ex(10,0.1*Amax)-1);
  WriteLn('î=',epsilon:cm:dc);
  x:=q;
  Normalizar;
  f:=x;
  ConverterParaS(f);
  p.grau:=0;
  p.a[0]:=1;
  p.cte:=1/(epsilon*f.cte);
  f.cte:=1;
  p.existe:=TRUE;
  e.existe:=FALSE;
  WriteLn('Polin“mio F(s) calculado; P(s)=cte')
END;

PROCEDURE Inversa;
BEGIN
  WriteLn(tl,'[Aproxima‡„o polinomial inversa]:');
  IF NOT q.existe THEN BEGIN
    WriteLn(tl,'[*] Faltando Q(w), pol. caracter¡stico [*]');
    Exit
  END;
  Write('At. m x. na b. p. (dB)'); LerReal(Amax);
  Write('At. min. na b. r. (dB)'); LerReal(Amin);
  epsilon:=Sqrt(Ex(10,0.1*Amax)-1);
  WriteLn('î=',epsilon:cm:dc);
  x.cte:=q.cte; x.grau:=q.grau;
  FOR i:=0 TO x.grau DO x.a[i]:=q.a[x.grau-i];
  Normalizar;
  MultC(1/(Sqrt(Ex(10,0.1*Amin)-1)));
  p:=x;
  f.grau:=q.grau;
  f.cte:=1;
  FOR i:=0 TO f.grau-1 DO f.a[i]:=0;
  f.a[f.grau]:=1;
  ReEscalar;
  ConverterParaS(p);
  IF ok THEN w0:=1/w0 ELSE w0:=1;
  WriteLn('ws=',w0:cm:dc);
  f.existe:=TRUE;
  WriteLn('F(s) e P(s) calculados.')
END;

PROCEDURE Racional;
BEGIN
  WriteLn(tl,'[Aproxima‡„o racional sim‚trica]:');
  IF NOT q.existe THEN BEGIN
    WriteLn(tl,'[*] Faltando Q(w), pol. caracter¡stico [*]');
    Exit
  END;
  Write('At. m x. na b. p. (dB)'); LerReal(Amax);
  epsilon:=Sqrt(Ex(10,0.1*Amax)-1);
  WriteLn('î=',epsilon:cm:dc);
  WriteLn('At. min. na b. r.:',10*Ln(1+Sqr(epsilon*Sqr(q.cte)))/Ln(10):cm:dc,' dB');
  x:=q;
  Normalizar;
  f:=x; {alfa incluido na cte.}
  FOR i:=0 TO q.grau DO x.a[i]:=q.a[q.grau-i];
  x.cte:=1; {n„o h  alfa aqui}
  Normalizar;
  MultC(1/(epsilon*f.cte));
  p:=x;
  f.cte:=1;
  ReEscalar;
  ConverterParaS(p);
  ConverterParaS(f);
  IF ok THEN w0:=1/Sqr(w0) ELSE w0:=1/w0;
  WriteLn('ws=',w0:cm:dc);
  WriteLn('F(s) e P(s) calculados.');
END;

PROCEDURE RacModificada;
BEGIN
  WriteLn(tl,'[Aproxima‡„o Racional Sim‚trica modificada]:');
  IF NOT q.existe THEN BEGIN
    WriteLn(tl,'[*] Faltando Q(w), pol. caracter¡stico [*]');
    Exit
  END;
  Write('At. m x. na b. p. (dB)'); LerReal(Amax);
  epsilon:=Sqrt(Ex(10,0.1*Amax)-1);
  WriteLn('î=',epsilon:cm:dc);
  WriteLn('At. min. na b. r.:',10*Ln(1+Sqr(epsilon*(2*Sqr(q.cte)-1)))/Ln(10):cm:dc,' dB');
  x:=q;
  MultC(2);
  y:=x;
  FOR i:=0 TO q.grau DO x.a[i]:=q.a[q.grau-i];
  x.cte:=1;
  Normalizar;
  z:=x;
  Subtrair;
  Normalizar;
  f:=x;
  x:=y;
  MultC(1/(epsilon*f.cte));
  p:=x;
  f.cte:=1;
  ReEscalar;
  ConverterParaS(p);
  ConverterParaS(f);
  IF ok THEN w0:=1/Sqr(w0) ELSE w0:=1/w0;
  WriteLn('ws=',w0:cm:dc);
  WriteLn('F(s) e P(s) calculados.');
END;

PROCEDURE ObterQ;
BEGIN
  erro:=FALSE;
  WriteLn(tl,'[Polin“mio caracter¡stico Q(w)]:');
  WriteLn(tl,'- [C]hebyshev');
  WriteLn(tl,'- Chebyshev [M]odificado');
  WriteLn(tl,'- [B]utterworth');
  WriteLn(tl,'- [O]utro polinomio a definir');
  WriteLn(tl,'- [Esc] cancela');
  LerResposta(['C','M','B','O',#27]);
  IF NOT (ch IN ['O',#27]) THEN BEGIN
    Write('Ordem da aproxima‡„o'); LerInt(n);
  END;
  CASE ch OF
  #27:Exit;
  'C':BEGIN
      WriteLn('Q(w)=Chebyshev ',n);
      Chebyshev(n)
    END;
  'M':BEGIN
      WriteLn('Q(w)=Chebyshev modificado ',n);
      Moebius(n)
    END;
  'B':WITH x DO BEGIN
      FOR i:=0 TO n-1 DO a[i]:=0;
      a[n]:=1;
      grau:=n;
      cte:=1;
      WriteLn('Q(w)=w^',n,' para aprox. de Butterworth.');
      x.existe:=TRUE
    END;
  'O':BEGIN
      WriteLn(tl,'[Obs]: S¢ faz sentido Q(w) puramente par ou ¡mpar.');
      LerPolinomio;
    END
  END;
  IF NOT erro THEN BEGIN
    q:=x;
    f.existe:=FALSE;
    p.existe:=FALSE;
    e.existe:=FALSE;
    raizes_calculadas:=FALSE
  END
END;

PROCEDURE LCDT;
TYPE
  kmult=(Eo,Ee,Fo,Fe);
  ctes=ARRAY[1..6,kmult] OF INTEGER;
CONST
  kn:ctes=(( 0, 1, 0,-1),
           ( 0, 1, 0, 1),
           ( 0, 1, 0, 1),
           ( 0, 1, 0,-1),
           ( 1, 1,-1,-1),
           ( 1, 1,-1, 1));
  kd:ctes=(( 1, 0, 1, 0),
           ( 1, 0, 1, 0),
           ( 1, 0,-1, 0),
           ( 1, 0,-1, 0),
           ( 1, 1, 1, 1),
           ( 1, 1, 1,-1));
VAR
  EmaisF,EmenosF:REAL;
  ke,kf:INTEGER;

BEGIN
  WriteLn(tl,#10'Imitƒncias de porta para rede [LC duplamente terminada]:');
  IF NOT (f.existe and e.existe) THEN BEGIN
    WriteLn(tl,'[*] Faltando calcular F(s) e/ou E(s) [*]');
    Exit
  END;
  Write(tl,#10'Gerar imitƒncia: ');
  IF Odd(p.grau) THEN BEGIN
    WriteLn(tl,'(P(s) ‚ [impar])'#10);
    WriteLn(tl,'[1] - [z11]/rg = (Eo-Fo)/(Ee+Fe)');
    WriteLn(tl,'[2] - [z22]/rl = (Eo+Fo)/(Ee+Fe)');
    WriteLn(tl,'[3] - [y11]*rg = (Eo+Fo)/(Ee-Fe)');
    WriteLn(tl,'[4] - [y22]*rl = (Eo-Fo)/(Ee-Fe)');
    WriteLn(tl,'[5] - [Z1]/rg  = (E-F)/(E+F)');
    WriteLn(tl,'[6] - [Z2]/rl  = (E-Fe+Fo)/(E+Fe-Fo)');
  END
  ELSE BEGIN
    WriteLn(tl,'(P(s) ‚ [par])'#10);
    WriteLn(tl,'[1] - [z11]/rg = (Ee-Fe)/(Eo+Fo)');
    WriteLn(tl,'[2] - [z22]/rl = (Ee+Fe)/(Eo+Fo)');
    WriteLn(tl,'[3] - [y11]*rg = (Ee+Fe)/(Eo-Fo)');
    WriteLn(tl,'[4] - [y22]*rl = (Ee-Fe)/(Eo-Fo)');
    WriteLn(tl,'[5] - [Z1]/rg  = (E-F)/(E+F)');
    WriteLn(tl,'[6] - [Z2]/rl  = (E+Fe-Fo)/(E-Fe+Fo)');
  END;
  WriteLn(tl,'[Esc] cancela');
  LerResposta(['1','2','3','4','5','6',#27]);
  IF ch=#27 THEN Exit;
  i:=Ord(ch)-Ord('0');
  FOR l:=0 TO e.grau DO BEGIN
    IF Odd(l) xor Odd(p.grau) THEN BEGIN ke:=kn[i,Eo]; kf:=kn[i,Fo] END
    ELSE BEGIN ke:=kn[i,Ee]; kf:=kn[i,Fe] END;
    x.a[l]:=ke*e.cte*e.a[l]+kf*f.cte*f.a[l];
    IF Odd(l) xor Odd(p.grau) THEN BEGIN ke:=kd[i,Eo]; kf:=kd[i,Fo] END
    ELSE BEGIN ke:=kd[i,Ee]; kf:=kd[i,Fe] END;
    y.a[l]:=ke*e.cte*e.a[l]+kf*f.cte*f.a[l];
  END;
  x.cte:=1; y.cte:=1; x.grau:=e.grau; y.grau:=e.grau;
  y.existe:=TRUE;
  WriteLn(tl,'[Numerador da imitƒncia]:');
  Normalizar;
  ListarPolinomio;
  x:=y;
  WriteLn(tl,'[Denominador da imitƒncia]:');
  Normalizar;
  ListarPolinomio;
  IF p.a[0]<>0 THEN BEGIN
    WriteLn(tl,#10'[Termina‡”es] (por: F(0)/E(0)=(rg-rl)/(rg+rl)):'#10);
    EmenosF:=e.cte*e.a[0]-f.cte*f.a[0];
    EmaisF:=e.cte*e.a[0]+f.cte*f.a[0];
    IF ch in ['1','3','5'] THEN
      WriteLn(tl,'[rl]=',EmenosF/EmaisF:cm:dc,' * [rg]')
    ELSE
      WriteLn(tl,'[rg]=',EmaisF/EmenosF:cm:dc,' * [rl]')
  END
  ELSE WriteLn(#10'As termina‡”es devem ser as do prot¢tipo passa-baixas');
  IF p.grau>0 THEN WriteLn(tl,#10'Salve as [ra¡zes de P(s)] (zeros de transmiss„o) para usar no programa [LADDER].')
END;

PROCEDURE LCST;
BEGIN
  WriteLn(tl,#10'Imitƒncias de porta para rede [LC simplesmente terminada] (em rg ou rl):');
  IF NOT e.existe THEN BEGIN
    WriteLn(tl,'[*] Faltando calcular E(s) [*]');
    Exit
  END;
  IF Odd(p.grau) THEN
    WriteLn(tl,'P(s) ‚ [¡mpar]: [z11]/rg = [y22]*rl = Eo/Ee')
  ELSE
    WriteLn(tl,'P(s) ‚ [par]: [z11]/rg = [y22]*rl = Ee/Eo');
  x:=e; y:=e;
  FOR l:=0 TO e.grau DO
    IF Odd(l) XOR Odd(p.grau) THEN
      x.a[l]:=0
    ELSE
      y.a[l]:=0;
  WriteLn(tl,'[Numerador da imitƒncia]:');
  Normalizar;
  ListarPolinomio;
  x:=y;
  WriteLn(tl,'[Denominador da imitƒncia]:');
  Normalizar;
  ListarPolinomio;
  WriteLn(tl,#10'Salve as [ra¡zes de P(s)] (zeros de transmiss„o) para usar no programa [LADDER].')
END;

PROCEDURE Lattice;
  VAR a,h:polinomio;
    neg:INTEGER;
BEGIN
  WriteLn(tl,#10'Impedƒncias para rede [lattice LC duplamente terminada] (rg=rl=r):');
  IF NOT (f.existe AND p.existe) THEN BEGIN
    WriteLn(tl,'[*] Faltando calcular F(s) e/ou P(s) [*]');
    Exit
  END;
  WriteLn(tl,#10'[Obs]: C lculo v lido somente se K(s)=F(s)/P(s) for puramente ¡mpar.');
  WriteLn(#10'Fatorando: F(s)+P(s)=h(s)a(s).');
  x:=f; y:=p;
  Somar;
  Normalizar; { cte de h(s) e a(s) ‚ a de x(s) }
  RaizesBiv;
  OrdenarRaizes; { negativas primeiro }
  neg:=0;
  WHILE zr[neg+1]<0 DO neg:=neg+1;
  a.grau:=x.grau-neg;
  x.grau:=neg;
  Montar(1);
  h:=x;
  WriteLn(tl,'[Polin“mio h(s)]:');
  ListarPolinomio;
  FOR i:=1 TO a.grau DO BEGIN
    zr[i]:=zr[i+neg];
    zi[i]:=zi[i+neg]
  END;
  x.grau:=a.grau;
  Montar(1);
  a:=x;
  WriteLn(tl,'[Polin“mio a(s)]:');
  ListarPolinomio;
  y:=a;
  MultC(-1);
  FOR i:=0 TO a.grau DO
    IF Odd(i) THEN y.a[i]:=0 ELSE x.a[i]:=0;
  WriteLn(tl,#10'[Numerador de Za(s)/r=-ao(s)]:');
  Limpar;
  ListarPolinomio;
  x:=y;
  WriteLn(tl,'[Denominador de Za(s)/r=ae(s)]:');
  Limpar;
  ListarPolinomio;
  x:=h; y:=h;
  FOR i:=0 TO h.grau DO
    IF Odd(i) XOR Odd(p.grau) THEN x.a[i]:=0 ELSE y.a[i]:=0;
  WriteLn(tl,'[Numerador de Zb(s)/r=he(s) (ou ho(s))]:');
  Limpar;
  ListarPolinomio;
  x:=y;
  WriteLn(tl,'[Denominador de Zb(s)/r=ho(s) (ou he(s))]:');
  Limpar;
  ListarPolinomio;
END;

PROCEDURE PassaAltas;
  VAR t:REAL;
BEGIN
  FOR i:=p.grau+1 TO f.grau DO p.a[i]:=0;
  p.grau:=f.grau;
  FOR i:=0 TO f.grau DIV 2 DO BEGIN
    WITH e DO BEGIN t:=a[i]; a[i]:=a[grau-i]; a[grau-i]:=t END;
    WITH f DO BEGIN t:=a[i]; a[i]:=a[grau-i]; a[grau-i]:=t END;
    WITH p DO BEGIN t:=a[i]; a[i]:=a[grau-i]; a[grau-i]:=t END;
  END;
END;

PROCEDURE PassaFaixa;
  VAR B:REAL;
    nf,np,k:INTEGER;

  PROCEDURE Simetrizar(VAR p:polinomio);
    VAR BB:REAL;
      k:INTEGER;
  BEGIN
    BB:=B;
    x.grau:=2; x.cte:=1;
    x.a[0]:=1; x.a[1]:=0; x.a[2]:=1;
    Entrar; Entrar; Entrar;
    x.grau:=0; x.cte:=p.cte; x.a[0]:=p.a[p.grau];
    FOR k:=p.grau-1 DOWNTO 0 DO BEGIN
      Multiplicar;
      x.a[p.grau-k]:=x.a[p.grau-k]+BB*p.a[k];
      BB:=BB*B
    END;
    p:=x
  END;

BEGIN
  nf:=f.grau; np:=p.grau;
  Write('Largura da Banda (Rd/s)? '); ReadLn(B);
  Simetrizar(p);
  Simetrizar(f);
  Simetrizar(e);
  x:=p;
  FOR k:=1 TO nf-np DO BEGIN
    MultC(B);
    MultS
  END;
  p:=x
END;

PROCEDURE RejeitaFaixa;
BEGIN
  PassaAltas;
  PassaFaixa
END;

PROCEDURE Escalar(VAR p:polinomio);
VAR
  k:REAL;
BEGIN
  WITH p DO BEGIN
    k:=fatorw;
    FOR i:=grau-1 DOWNTO 0 DO BEGIN
      a[i]:=a[i]*k;
      k:=k*fatorw
    END
  END
END;

PROCEDURE EscalarEmFrequencia;
BEGIN
  Write('Fator de escalamento: '); LerReal(fatorw);
  Escalar(p);
  Escalar(e);
  Escalar(f);
  p.cte:=p.cte*Ex(fatorw,f.grau-p.grau);
END;

PROCEDURE Menu;
BEGIN
  WriteLn(tl,'- Gerar [Q](w)');
  WriteLn(tl,'- K(s) para K(jw) [P]olinomial');
  WriteLn(tl,'- K(s) para K(jw) polinomial [I]nversa');
  WriteLn(tl,'- K(s) para K(jw) [R]acional sim‚trica');
  WriteLn(tl,'- K(s) para K(jw) racional [S]im‚trica modificada');
  WriteLn(tl,'- H(s) para aproxima‡„o de [B]essel');
  WriteLn(tl,'- Calcular [E](s) tendo K(s)=F(s)/P(s)');
  WriteLn(tl,'- Calcular [F](s) tendo H(s)=E(s)/P(s)');
  WriteLn(tl,'- Gerar i[M]itƒncias para s¡ntese');
  WriteLn(tl,'- Tra[N]sforma‡”es de freqˆncia');
  WriteLn(tl,'- [L]istar/salvar polin“mio');
  WriteLn(tl,'- Listar/salvar Rai[Z]es');
  WriteLn(tl,'- Plotar ra¡zes no plano comple[X]o');
  WriteLn(tl,'- Ler/editar p[O]lin“mio');
  WriteLn(tl,'- Elevar polin“mio ao q[U]adrado');
  WriteLn(tl,'- R[A]¡zes de polin“mio');
  WriteLn(tl,'- [G]r ficos de resposta em freqˆncia');
  WriteLn(tl,'- Mudar [T]olerƒncias');
  WriteLn(tl,'- [D]iret¢rio; [Esc]: Fim; [Enter]: Este menu');
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
GetAspectRatio(xasp,yasp);
fator:=yasp/xasp;
x0:=pxmin;
xm:=GetMaxX; {xm-x0 deve ser m£ltiplo de 4}
mx2:=(xm+x0) div 2;
mx1:=(x0+mx2) div 2;
mx3:=(mx2+xm) div 2;
y0:=0;
ym:=GetMaxY-10;
RestoreCrtMode;
Amax:=10*Ln(2)/Ln(10); Amin:=40; n:=1;
  {$IFDEF DOUBLE}
cm:=26; dc:=18; tolr:=1e-12; toln:=1e15; tolm:=1e-8; told:=1e-10;
  {$ELSE}
cm:=18; dc:=11; tolr:=1e-8; toln:=1e10; tolm:=1e-6; told:=1e-6;
  {$ENDIF}
xr0:=-1.1; xi0:=1.1; inicigual:=FALSE;
raizes_calculadas:=FALSE;
e.existe:=FALSE;
f.existe:=FALSE;
p.existe:=FALSE;
q.existe:=FALSE;
x.existe:=FALSE;
y.existe:=FALSE;
WriteLn(tl,'[Aproxima‡”es por Fun‡„o Caracter¡stica]');
WriteLn(tl,'[--------------------------------------]');
WriteLn('Ant“nio Carlos M. de Queiroz - COPPE/UFRJ');
WriteLn('Vers„o ',versao,' - Precis„o ',precisao);
Menu; WriteLn(tl,'[#]');
REPEAT
  CASE UpKey OF
  'B':BEGIN
      Write('Aprox. de Bessel; ordem'); LerInt(n);
      Bessel(n);
      e:=x;
      p.a[0]:=1; p.cte:=e.a[0]; p.grau:=0;
      WriteLn('E(s) e P(s) calculados.');
      p.existe:=TRUE;
      f.existe:=FALSE
    END;
  'N':IF f.existe AND p.existe AND e.existe THEN BEGIN
      Write(tl,'Transforma‡„o pb-p[A], pb-p[F] ou pb-[R]f [E]scalamento [Esc] cancela)');
      LerResposta(['A','F','R','E',#27]);
      CASE ch OF
      'A':PassaAltas;
      'F':PassaFaixa;
      'R':RejeitaFaixa;
      'E':EscalarEmFrequencia;
      END;
      IF ch<>#27 THEN WriteLn('Transformados F(s), P(s) e E(s).');
    END
    ELSE WriteLn(tl,'[*] Transforma‡”es exigem a aproxima‡„o PB completa [*]');
  'M':BEGIN
      Write(tl,'Imitƒncias para rede LC [d]upl. termin., [s]impl. termin. ou em la[t]tice');
      LerResposta(['D','S','T']);
      CASE ch of
        'D':LCDT;
        'S':LCST;
        'T':Lattice
      END;
    END;
  'O':BEGIN
      Selecionar; LerPolinomio; Distribuir;
    END;
  'G':BEGIN
      Write(tl,'Gr fico de ³[K](jw)³, ³[H](jw)³, ³[T](jw)³, [F]ase(jw) ou [A]traso(jw)');
      LerResposta(['H','K','T','F','A']);
      CASE ch OF
        'H':Grafico(e,p,deH,wmin,wmax,mmin,mmax);
        'K':Grafico(f,p,deK,wmin,wmax,mmin,mmax);
        'T':Grafico(p,e,deT,wmin,wmax,tmin,tmax);
        'F':Grafico(p,e,deF,wmin,wmax,fmin,fmax);
        'A':BEGIN
              WITH p DO BEGIN
                ok:=TRUE; {P ‚ par}
                FOR i:=0 TO grau DO IF Odd(i) THEN IF Abs(a[i])>tolr THEN ok:=FALSE;
                IF not ok THEN BEGIN {P n„o ‚ par}
                  ok:=TRUE; {P ‚ ¡mpar}
                  FOR i:=0 TO grau DO IF not Odd(i) THEN IF Abs(a[i])>tolr THEN ok:=FALSE;
                END
              END;
              IF ok THEN x:=e {P ‚ par ou ¡mpar, n„o afetando o atraso}
              ELSE BEGIN
                x:=p;
                FOR i:=0 TO x.grau DO IF Odd(i) THEN x.a[i]:=-x.a[i];
                y:=e;
                Multiplicar;
                Limpar
              END;
              y:=x;
              WITH x DO BEGIN {Derivar}
                IF grau=0 THEN a[0]:=0
                ELSE BEGIN
                  FOR i:=1 TO grau DO a[i-1]:=a[i]*i;
                  grau:=grau-1
                END
              END;
              Grafico(x,y,deA,wmin,wmax,dmin,dmax)
            END
      END
    END;
  'E':HdeK;
  'F':KdeH;
  'T':BEGIN
      Write('Tolerƒncia para raizes'); LerReal(tolr );
      Write('Aproxima‡„o inicial real'); LerReal(xr0);
      Write('Aproxima‡„o inicial imag'); LerReal(xi0);
      Write('Usar sempre a mesma aproxima‡„o inicial'); LerBool(inicigual);
      Write('Dispers„o m xima entre coeficientes de polin“mio'); LerReal(toln);
      Write('Tolerƒncia para magnitudes'); LerReal(tolm);
      Write('Tolerƒncia para derivadas'); LerReal(told);
      Write('Campo para reais'); LerInt(cm);
      Write('Decimais para reais'); LerInt(dc);
    END;
  'A':BEGIN Write('Ra¡zes de '); Selecionar; Limpar; RaizesBiv; ListarRaizes END;
  'L':BEGIN Write('Listar '); Selecionar; ListarPolinomio END;
  'Z':BEGIN WriteLn('Ra¡zes:'); ListarRaizes END;
  'X':PlotarRaizes;
  'Q':ObterQ;
  'P':Polinomial;
  'I':Inversa;
  'R':Racional;
  'S':RacModificada;
  'U':BEGIN
      Write('Elevar au quadrado ');
      Selecionar;
      IF x.existe THEN BEGIN
        y:=x;
        Multiplicar;
        Distribuir;
      END
      ELSE WriteLn(tl,'[*] polin“mio indefinido [*]')
    END;
  'D':Diretorio;
  #27:BEGIN
        Write('Terminar');
        LerBool(terminar);
      END;
  #13:Menu;
  END;
  WriteLn(tl,'[#]');
UNTIL terminar;
END.

