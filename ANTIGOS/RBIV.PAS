{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}

USES Crt,Graph,Tela;

CONST
  dig=10;
  dec=7;
  max=100;

TYPE
  coeficientes=ARRAY[0..max] of REAL;
  polinomio=RECORD
    cf:coeficientes;
    n:INTEGER;
    inc:REAL;
  END;
  raizes=RECORD
    re,im:ARRAY[1..max] of REAL;
    n:INTEGER;
  END;
  tipodepolinomio=(denominador,numparcial,numfase,numglobal);

VAR
  Den,Num:polinomio;
  Polos,Zeros:raizes;
  i,j,k,fases:INTEGER;
  txt:STRING;
  ch:CHAR;
  relatorio,poloscalculados:BOOLEAN;
  tolr,xr0,xi0,Imag:REAL;
  titulo:STRING;
  saida:TEXT;

CONST
  pixmin=43;
  seta:ARRAY[1..8] OF PointType=((x:0;y:0),(x:8;y:0),(x:6;y:2),(x:8;y:4),
                                 (x:4;y:8),(x:2;y:6),(x:0;y:8),(x:0;y:0));

VAR
  cor1,cor2,cor3,placa,modo:INTEGER;
  apontador:POINTER;
  xmin,xmax,ymin,ymax:INTEGER;
  fator,x1,y1,delta:REAL;
  tamapont:WORD;

FUNCTION Ex(x:REAL;t:REAL):REAL;
BEGIN Ex:=Exp(t*Ln(x)) END;

FUNCTION Cmult(x1,x2,y1,y2:REAL):REAL;
BEGIN
  Cmult:=x1*y1-x2*y2;
  Imag:=x1*y2+x2*y1
END;

PROCEDURE InicializarParametros;
VAR
  xasp,yasp:WORD;
BEGIN
  DetectGraph(placa,modo);
  IF placa=CGA THEN modo:=CGAC0;
  InitGraph(placa,modo,'');
  cor1:=GetMaxColor;
  cor2:=cor1-1;
  IF cor2=0 THEN cor2:=1;
  cor3:=cor2-1;
  IF cor3=0 THEN cor3:=1;
  xmax:=GetMaxX;
  ymax:=GetMaxY-10;
  xmin:=pixmin;
  ymin:=10;
  SetFillStyle(solidfill,cor3);
  FillPoly(SizeOf(seta) div SizeOf(PointType),seta);
  tamapont:=ImageSize(0,0,10,10);
  GetMem(apontador,tamapont);
  GetImage(0,0,10,10,apontador^);
  y1:=-2.0;
  x1:=-2.0;
  delta:=4;
  relatorio:=FALSE;
  tolr:=1e-10; xr0:=0.7; xi0:=0.7; fases:=1;
  GetAspectRatio(xasp,yasp);
  fator:=yasp/xasp;
  RestoreCrtMode;
END;

PROCEDURE Biv(VAR Pol:polinomio; tipo:tipodepolinomio; VAR R:raizes);
CONST
  imax=50;
  pouco=1e-6;
VAR
  a1,a2,b1,b2,c1,c2:coeficientes;
  t,tol,p1,p2,d,xr,xi,p,d1,d2,e1,e2:REAL;
  feito:BOOLEAN;
  nn,n,ordem:INTEGER;

  PROCEDURE PlotarRaizes;
  VAR
    x2,y2,ay,by,ax,bx:REAL;
    indice,xcursor,ycursor:INTEGER;

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

    PROCEDURE Plotar(VAR R:raizes; tipo:tipodepolinomio);
    VAR
      x,y:INTEGER;
    BEGIN
      WITH R DO
        FOR i:=1 TO n DO BEGIN
          x:=Limx(re[i]);
          y:=Limy(im[i]);
          IF tipo=denominador THEN BEGIN
            Line(x-2,y-2,x+2,y+2);
            Line(x-2,y+2,x+2,y-2)
          END
          ELSE Circle(x,y,4);
        END
    END;

    PROCEDURE Cursor(VAR R:raizes; tipo:tipodepolinomio);
    BEGIN
      indice:=1;
      WITH R DO
        REPEAT
          Bar(0,0,GetMaxX,9);
          MoveTo(0,0); OutText(titulo+' - ');
          IF tipo=denominador THEN OutText('Polo') ELSE OutText('Zero');
          Str(indice,txt); OutText(' '+txt+':');
          Str(re[indice]:8:5,txt); OutText(txt);
          Str(im[indice]:8:5,txt); OutText(' '+txt+'j');
          PutImage(xcursor,ycursor,apontador^,XORput);
          xcursor:=Limx(re[indice]);
          ycursor:=Limy(im[indice]);
          PutImage(xcursor,ycursor,apontador^,XORput);
          ch:=ReadKey;
          CASE ch OF
            #13:IF indice<n THEN indice:=indice+1 ELSE indice:=1;
            #8:IF indice>1 THEN indice:=indice-1 ELSE indice:=n;
            #0:BEGIN
                 ch:=ReadKey;
                 CASE ch OF
                   'M': x1:=x1+delta/4;
                   'K': x1:=x1-delta/4;
                   'H': y1:=y1+delta/4;
                   'P': y1:=y1-delta/4;
                 END
               END;
           '-':BEGIN
                 x1:=x1-delta/2;
                 y1:=y1-delta/2;
                 delta:=delta*2
               END;
           '+':BEGIN
                 x1:=x1+delta/4;
                 y1:=y1+delta/4;
                 delta:=delta/2;
               END
          END
        UNTIL ch in [#9,#27,'M','K','H','P','+','-'];
    END;

  BEGIN
    REPEAT
      xcursor:=-2000;
      ycursor:=-2000;
      y2:=y1+delta;
      ay:=(ymax-ymin)/(y1-y2);
      by:=ymax-ay*y1;
      ax:=-ay*fator;
      bx:=xmin-ax*x1;
      x2:=(xmax-bx)/ax;
      SetGraphMode(modo);
      SetFillStyle(emptyfill,cor1);
      Line(0,ymax,xmax,ymax);
      Line(xmin,ymin,xmin,GetMaxY);
      SetColor(cor2);
      Line(Limx(0),ymin,Limx(0),ymax);
      Line(xmin,Limy(0),xmax,Limy(0));
      Circle(Round(bx),Round(by),Round(ax));
      SetColor(cor1);
      Str(y2:5:1,txt); OutTextXY(0,ymin,txt);
      Str(y1:5:1,txt); OutTextXY(0,ymax-8,txt);
      Str(x1:8:3,txt); OutTextXY(xmin+1,ymax+2,txt);
      Str(x2:8:3,txt); OutTextXY(xmax-64,ymax+2,txt);
      Plotar(R,tipo);
      IF poloscalculados THEN Plotar(Polos,denominador);
      REPEAT
        Cursor(R,tipo);
        IF (ch=#9) and poloscalculados THEN Cursor(Polos,denominador);
      UNTIL ch<>#9;
    UNTIL ch=#27;
    RestoreCrtMode;
  END;

  PROCEDURE ListarRaizes;
  BEGIN
    WriteLn(tl,#10'[Ra¡zes em z^(1/',fases,'):]'#10);
    FOR i:=1 TO R.n DO BEGIN
      Write(tl,'z([',i:2,'])=',R.re[i]);
      IF R.im[i]<>0 THEN WriteLn(R.im[i],'j') ELSE WriteLn;
    END;
    WriteLn;
  END;

  PROCEDURE ConverterRaizes;
  VAR
    NR:raizes;
    m,f,f1:REAL;
  BEGIN
    WITH R DO BEGIN
      NR.n:=n*fases;
      k:=0;
      FOR i:=1 TO n DO BEGIN
        IF re[i]=0 THEN BEGIN
          f:=Pi/2;
          IF im[i]<0 THEN f:=-f;
        END
        ELSE BEGIN
          f:=Arctan(im[i]/re[i]);
          IF re[i]<0 THEN
            IF im[i]>0 THEN f:=Pi+f ELSE f:=f-Pi;
        END;
        IF (re[i]=0) and (im[i]=0) THEN m:=0
        ELSE m:=Ex(Sqrt(Sqr(re[i])+Sqr(im[i])),1/fases);
        FOR j:=1 TO fases DO BEGIN
          k:=k+1;
          f1:=(f+(j-1)*2*Pi)/fases;
          NR.re[k]:=m*Cos(f1);
          NR.im[k]:=m*Sin(f1);
        END
      END
    END;
    R:=NR;
  END;

  PROCEDURE ApresentarRaizes;
  VAR
    Sair:BOOLEAN;
  BEGIN
    Sair:=FALSE;
    {IF tipo=denominador THEN ConverterRaizes;}
    PlotarRaizes;
    REPEAT
      WriteLn(tl,'[Op‡”es para o c lculo de ra¡zes:]'#10);
      WriteLn(tl,'- mudar [P]arƒmetros');
      IF relatorio THEN WriteLn(tl,'- incluir ra¡zes no [R]elat¢rio');
      WriteLn(tl,'- [L]istar ra¡zes');
      WriteLn(tl,'- plotar [G]r fico');
      WriteLn(tl,'- [C]ontinuar an lise');
      REPEAT ch:=UpCase(ReadKey) UNTIL (ch IN ['P','L','G','C']) or relatorio and (ch='R');
      CASE ch OF
        'P':BEGIN
              Write(#10'Tolerƒncia inicial'); LerReal(tolr);
              Write('Aproxima‡„o inicial real para ra¡z'); LerReal(xr0);
              Write('Aproxima‡„o inicial imag para ra¡z'); LerReal(xi0);
              Write('M¡nimo imagin rio no gr fico'); LerReal(y1);
              Write('M¡nimo real no gr fico'); LerReal(x1);
              Write('Altura do gr fico'); LerReal(delta);
              WriteLn;
            END;
        'R':BEGIN
              WriteLn(saida,#13#10'Raizes em z^(1/',fases,'):');
              FOR j:=1 TO R.n DO WriteLn(saida,R.re[j]:dig:dec,' ',R.im[j]:dig:dec,'j (',j,')');
              WriteLn(tl,#10'[*] Ra¡zes escritas'#10);
            END;
        'L':ListarRaizes;
        'G':PlotarRaizes;
        'C':Sair:=TRUE;
      END;
    UNTIL Sair;
    IF tipo=denominador THEN poloscalculados:=TRUE;
  END;

BEGIN
  tol:=Sqr(tolr); n:=Pol.n; a1:=Pol.cf; R.n:=n; ordem:=0;
  xr:=xr0; xi:=xi0; feito:=FALSE; nn:=0;
  FOR i:=0 TO n DO a2[i]:=0;
  Write('[');
  IF n<1 THEN
    BEGIN feito:=TRUE; WriteLn(tl,#10'[*] N„o h  raizes a calcular') END
  ELSE
    WHILE (n>1) and (Abs(a1[0])<pouco) DO BEGIN
      R.re[n]:=0; R.im[n]:=0;
      Write(n,' ');
      n:=n-1;
      FOR i:=0 TO n DO a1[i]:=a1[i+1]
    END;
  WHILE NOT feito DO BEGIN
    IF n>1 THEN BEGIN
      b1[n]:=a1[n]; d1:=b1[n]; p1:=d1;
      b2[n]:=a2[n]; d2:=b2[n]; p2:=d2;
      FOR i:=n-1 DOWNTO 0 DO BEGIN
        b1[i]:=p1*xr-p2*xi+a1[i]; p:=b1[i];
        b2[i]:=p2*xr+p1*xi+a2[i]; p2:=b2[i];
        p1:=p;
        IF i>0 THEN BEGIN
          d:=d1*xr-d2*xi+p1;
          d2:=d2*xr+d1*xi+p2;
          d1:=d;
        END
      END;
      d:=Sqr(d1)+Sqr(d2);
      e1:=(p1*d1+p2*d2)/d;
      e2:=(p2*d1-p1*d2)/d;
      IF (d<pouco) THEN BEGIN
        IF ordem=0 THEN BEGIN c1:=a1; c2:=a2 END;
        FOR i:=1 TO n DO BEGIN
          a1[i-1]:=a1[i]*i;
          a2[i-1]:=a2[i]*i;
        END;
        n:=n-1; ordem:=ordem+1;
        Write('.')
      END
      ELSE BEGIN
        xr:=xr-e1;
        xi:=xi-e2;
        IF Sqr(e1)+Sqr(e2)<tol THEN BEGIN
          FOR i:=n TO n+ordem DO BEGIN
            Write(i,' ');
            R.re[i]:=xr; R.im[i]:=xi;
          END;
          IF ordem>0 THEN BEGIN
            a1:=c1; a2:=c2; n:=n+ordem;
            FOR i:=0 TO ordem DO BEGIN
              b1[n]:=a1[n]; b2[n]:=a2[n];
              FOR j:=n-1 DOWNTO 1 DO BEGIN
                b1[j]:=Cmult(xr,xi,b1[j+1],b2[j+1])+a1[j];
                b2[j]:=Imag+a2[j];
              END;
              n:=n-1;
              FOR j:=0 TO n DO
                BEGIN a1[j]:=b1[j+1]; a2[j]:=b2[j+1] END
            END;
            ordem:=0;
          END
          ELSE BEGIN
            n:=n-1;
            FOR i:=0 TO n DO
              BEGIN a1[i]:=b1[i+1]; a2[i]:=b2[i+1] END
          END;
          nn:=0;
          IF (Abs(xi)>pouco) THEN xi:=-xi ELSE BEGIN xi:=0.1; xr:=-xr END
        END
        ELSE BEGIN
          nn:=nn+1;
          IF nn>imax THEN BEGIN
            Write(tl,#10#13'[*] Problemas de convergˆncia.');
            tol:=Sqrt(t);
            Write('  Tolerƒncia'); LerReal(tol);
            tol:=1.01*Sqr(tol);
            Write('  Aproxima‡„o real'); LerReal(xr);
            Write('  Aproxima‡„o imag'); LerReal(xi);
            nn:=0;
          END
        END
      END
    END
    ELSE BEGIN
      Write('1');
      d:=-(Sqr(a1[1])+Sqr(a2[1]));
      xr:=(a1[0]*a1[1]+a2[0]*a2[1])/d;
      xi:=(a2[0]*a1[1]-a1[0]*a2[1])/d;
      feito:=TRUE; nn:=0;
      FOR i:=n TO n+ordem DO BEGIN
        Write(i,' ');
        R.re[i]:=xr; R.im[i]:=xi;
      END
    END
  END;
  WriteLn(']');
  ApresentarRaizes;
END;

BEGIN
  InicializarParametros;
  REPEAT
    poloscalculados:=FALSE;
    titulo:='Denominador';
    Write('Grau do denominador'); LerInt(Den.n);
    FOR i:=0 TO Den.n DO BEGIN
      Write('a(',i,'): '); ReadLn(Den.cf[i]);
    END;
    Biv(Den,denominador,Polos);
    Write(#10'Grau do numerador'); LerInt(Num.n);
    Num.inc:=1/fases;
    FOR i:=0 TO Num.n DO BEGIN
      Write('a(',i*Num.inc:5:2,'): '); ReadLn(Num.cf[i]);
    END;
    titulo:='F. de T.';
    Biv(Num,numglobal,Zeros);
    WriteLn(#10'Toque uma tecla (esc p/ fim):'#10);
    ch:=ReadKey;
  UNTIL ch=#27;
END.
