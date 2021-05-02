USES Crt,Graph,Tela;

CONST
  dig=10;
  dec=7;
  max=80;

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
  t0,v0,u0,faixa,Imag:REAL;
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
  t0:=1e-10; u0:=0.1; v0:=-1; faixa:=10; fases:=1;
  GetAspectRatio(xasp,yasp);
  fator:=yasp/xasp;
  RestoreCrtMode;
END;

PROCEDURE Lib(VAR P:polinomio; tipo:tipodepolinomio; VAR R:raizes);
VAR
  m:INTEGER;
  t,u,v,u1,v1,c1,c2,c3,d,t1:REAL;
  A,B:coeficientes;
  continuar:BOOLEAN;

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
        END;
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
               END;
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
        END;
      END;
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
              Write(#10'Tolerƒncia inicial'); LerReal(t0);
              Write('Produto inicial de par de ra¡zes'); LerReal(v0);
              Write('Sim‚trico da soma inicial de par de ra¡zes'); LerReal(u0);
              Write('Distƒncia m xima de ra¡z   origem'); LerReal(faixa);
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

  PROCEDURE Resolver2;
  BEGIN
    Write(m,' ');
    d:=u*u-4*v;
    IF d>=0 THEN BEGIN
      R.re[m]:=(-u+Sqrt(d))/2;
      R.re[m-1]:=(-u-Sqrt(d))/2;
      R.im[m]:=0; R.im[m-1]:=0
    END
    ELSE BEGIN
      R.re[m]:=-u/2; R.re[m-1]:=-u/2;
      R.im[m]:=Sqrt(-d)/2; R.im[m-1]:=-R.im[m]
    END;
    m:=m-2
  END;

BEGIN
  t:=t0; v:=v0; u:=u0; continuar:=TRUE;
  m:=P.n; R.n:=m;
  IF m=0 THEN BEGIN WriteLn(tl,#10'[N„o h ] ra¡zes finitas'); Exit END;
  A:=P.cf;
  WHILE (A[0]=0) and (m>1) DO BEGIN
    R.re[m]:=0; R.im[m]:=0;
    m:=m-1;
    For j:=0 TO m DO A[j]:=A[j+1]
  END;
  REPEAT
    IF m=1 THEN BEGIN
      R.re[1]:=-A[0]/A[1]; R.im[1]:=0;
      ApresentarRaizes;
      Exit
    END;
    IF m=2 THEN BEGIN
      u:=A[1]/A[2]; v:=A[0]/A[2];
      Resolver2;
      ApresentarRaizes;
      Exit
    END;
    i:=0;
    REPEAT
      IF i>100 THEN BEGIN
        Write(#10#13'Problemas de convergˆncia na ',m,'a. raiz. Continuar'); LerBool(continuar);
        IF not continuar THEN BEGIN
          FOR i:=m DOWNTO 1 DO BEGIN R.re[i]:=-2; R.im[i]:=-2 END;
          ApresentarRaizes;
          Exit
        END;
        t:=1.001*t1;
        Write(#10'Tolerƒncia'); LerReal(t);
        i:=0;
      END;
      i:=i+1;
      B[m]:=A[m]; c2:=B[m];
      B[m-1]:=A[m-1]-u*B[m];
      c1:=B[m-1]-u*c2;
      FOR j:=m-2 DOWNTO 1 DO BEGIN
        c3:=c2; c2:=c1;
        B[j]:=A[j]-u*B[j+1]-v*B[j+2];
        c1:=B[j]-u*c2-v*c3
      END;
      B[0]:=A[0]-u*B[1]-v*B[2];
      u1:=(B[0]/c2-B[1]/c3)/(c2/c3-c1/c2);
      v1:=(B[1]/c2-B[0]/c1)/(c2/c1-c3/c2);
      u:=u-u1; v:=v-v1;
      t1:=Abs(u1)+Abs(v1);
      IF t1>faixa THEN BEGIN
        u:=Random*Sqr(faixa);
        v:=Random*2*faixa-faixa;
        Write('.');
      END;
    UNTIL t1<t;
    Resolver2;
    FOR j:=0 TO m DO A[j]:=B[j+2]
  UNTIL FALSE;
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
    Lib(Den,denominador,Polos);
    {
    Write(#10'Grau do numerador'); LerInt(Num.n);
    Num.inc:=1/fases;
    FOR i:=0 TO Num.n DO BEGIN
      Write('a(',i*Num.inc:5:2,'): '); ReadLn(Num.cf[i]);
    END;
    titulo:='F. de T.';
    Lib(Num,numglobal,Zeros);
    }
    WriteLn(#10'Toque uma tecla (esc p/ fim):'#10);
    ch:=ReadKey;
  UNTIL ch=#27;
END.
