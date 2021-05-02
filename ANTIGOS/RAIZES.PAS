PROGRAM Calcula_Raizes;

{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}

USES Graph,Tela,Crt;

CONST
  GrauMax=100;
  entrada='polin.dat';
  saida='raizes.dat';

TYPE
  coeficientes=ARRAY[0..GrauMax] of REAL;
  polinomio=RECORD
    n:INTEGER;
    cf:coeficientes;
  END;
  raizes=RECORD
    re,im:ARRAY[1..GrauMax] of REAL;
    n:INTEGER;
  END;

CONST
  pixmin=43;
  seta:ARRAY[1..8] OF PointType=((x:0;y:0),(x:8;y:0),(x:6;y:2),(x:8;y:4),
                                 (x:4;y:8),(x:2;y:6),(x:0;y:8),(x:0;y:0));

VAR
  dig,dec,i,j,cor1,cor2,cor3,placa,modo,dpm,dpt,xmin,xmax,ymin,ymax:INTEGER;
  Imag,fator,xr0,xi0,tolz,tolp,delta,x1,y1,x2,y2:REAL;
  tamanho,tamapont:WORD;
  csr,pt:POINTER;
  txt:STRING;
  ch:CHAR;
  grade:BOOLEAN;
  P:polinomio;
  R:raizes;
  arquivo:TEXT;

FUNCTION Cmult(x1,x2,y1,y2:REAL):REAL;
BEGIN
  Cmult:=x1*y1-x2*y2;
  Imag:=x1*y2+x2*y1
END;

FUNCTION Ex(x:REAL;t:REAL):REAL;
BEGIN Ex:=Exp(t*Ln(x)) END;

FUNCTION Si(i:INTEGER):STRING;
VAR x:STRING;
BEGIN
  Str(i,x);
  Si:=x;
END;

FUNCTION Sr(r:REAL):STRING;
VAR x:STRING;
BEGIN
  Str(r:dig:dec,x);
  Sr:=x;
END;

PROCEDURE Interromper(mens:STRING);
BEGIN
  WriteLn(tl,#10#13'[*] '+mens+'.');
  WriteLn(#10'Toque uma tecla...');
  ch:=ReadKey; Halt;
END;

PROCEDURE InicializarParametros;
VAR
  xasp,yasp:WORD;
BEGIN
  {$IFDEF DOUBLE}
  tolz:=1e-11; tolp:=1e-6;
  {$ELSE}
  tolz:=1e-8; tolp:=1e-4;
  {$ENDIF}
  dig:=5; dec:=3;
  y1:=-2.0; x1:=-2.0; delta:=4; xr0:=1.1; xi0:=0.1;
  grade:=TRUE;
  DetectGraph(placa,modo);
  IF placa=CGA THEN modo:=CGAHI;
  InitGraph(placa,modo,'');
  i:=GraphResult; IF i<>GrOk THEN Interromper(GraphErrorMsg(i));
  IF placa=CGA THEN BEGIN
    cor3:=1;
    cor2:=2;
    cor1:=3
  END
  ELSE BEGIN
    cor3:=EGAYellow;
    cor2:=EGALightgray;
    cor1:=EGAWhite;
  END;
  xmax:=GetMaxX;
  ymax:=GetMaxY-10;
  xmin:=pixmin;
  ymin:=10;
  SetColor(cor3);
  Line(0,ymin,0,ymax);
  tamanho:=ImageSize(0,ymin,0,ymax);
  GetMem(csr,tamanho);
  GetImage(0,ymin,0,ymax,csr^);
  SetColor(cor1);
  SetFillStyle(solidfill,cor3);
  FillPoly(SizeOf(seta) div SizeOf(PointType),seta);
  tamapont:=ImageSize(0,0,9,9);
  GetMem(pt,tamapont);
  GetImage(0,0,9,9,pt^);
  GetAspectRatio(xasp,yasp);
  fator:=yasp/xasp;
  RestoreCrtMode;
END;

PROCEDURE IniciarGrafico(x1,x2,y1,y2:REAL; xlog:BOOLEAN);
VAR
  ax,bx,ay,by,t1,t2:REAL;
BEGIN
  SetGraphMode(modo);
  SetFillStyle(emptyfill,cor1);
  ay:=(ymax-ymin)/(y1-y2);
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
    SetColor(cor2);
    IF xlog and (x2-x1>x1) THEN t1:=x1
    ELSE t1:=x2-x1;
    t1:=Exp(Ln(10)*Round(Ln(t1)/Ln(10)-0.499999));
    t2:=Round(x1/t1+0.5)*t1;
    WHILE t2<x2 DO
      IF xlog THEN BEGIN
        IF Round(t2/t1)=10 THEN BEGIN
          t1:=10*t1;
          SetColor(cor3);
        END;
        i:=Round(ax*Ln(t2)+bx);
        Line(i,ymin,i,ymax);
        t2:=t2+t1;
        SetColor(cor2);
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
    SetLineStyle(SolidLn,0,NormWidth);
    SetColor(cor1)
  END;
  Line(0,ymax,xmax,ymax);
  Line(xmin,ymin,xmin,GetMaxY);
  Str(y2:5:1,txt); OutTextXY(0,ymin,txt);
  Str(y1:5:1,txt); OutTextXY(0,ymax-8,txt);
  Str(x1:8:3,txt); OutTextXY(xmin+1,ymax+2,txt);
  Str(x2:8:3,txt); OutTextXY(xmax-64,ymax+2,txt);
END;

PROCEDURE CalcularRaizes(VAR Pol:polinomio; VAR R:raizes);
CONST
  imax=50;
VAR
  a1,a2,c1,c2:coeficientes;
  tolm,t,tol,p1,p2,d,xr,xi,p,d1,d2,e1,e2:REAL;
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

    PROCEDURE Plotar(VAR R:raizes);
    VAR
      x,y,i:INTEGER;
    BEGIN
      WITH R DO
        FOR i:=1 TO n DO BEGIN
          x:=Limx(re[i]);
          y:=Limy(im[i]);
	  Line(x-2,y-2,x+2,y+2);
	  Line(x-2,y+2,x+2,y-2)
        END
    END;

    PROCEDURE Cursor(VAR R:raizes);
    BEGIN
      indice:=1;
      WITH R DO
        REPEAT
	  Bar(0,0,GetMaxX,9);
	  MoveTo(0,0);
          Str(re[indice]:8:5,txt); OutText(txt);
          Str(im[indice]:8:5,txt); OutText(' '+txt+'j');
          PutImage(xcursor,ycursor,pt^,XORput);
          xcursor:=Limx(re[indice]);
          ycursor:=Limy(im[indice]);
          PutImage(xcursor,ycursor,pt^,XORput);
          ch:=UpKey;
          CASE ch OF
            'G':grade:=not grade;
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
                 delta:=delta/2;
                 x1:=x1+delta/2;
                 y1:=y1+delta/2
               END;
           ' ':BEGIN
                 x1:=re[indice]-delta/2;
                 y1:=im[indice]-delta/2
               END;
          END
        UNTIL ch in [#9,#27,'M','K','H','P','+','-',' ','G'];
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
      IniciarGrafico(x1,x2,y1,y2,FALSE);
      OutTextXY(xmin+2,ymin,'Im');
      OutTextXY(xmax-16,ymax-8,'Re');
      SetColor(cor3);
      Circle(Round(bx),Round(by),Round(ax));
      SetColor(cor1);
      Plotar(R);
      REPEAT
	Cursor(R);
      UNTIL ch<>#9;
    UNTIL ch=#27;
    RestoreCrtMode;
  END;

  PROCEDURE ListarRaizes;
  BEGIN
    WriteLn(tl,#10'[Raizes calculadas:]'#10);
    j:=0;
    FOR i:=1 TO R.n DO BEGIN
      Write(tl,'z([',i:2,']):',R.re[i]:dig:dec);
      IF Abs(R.im[i])>tolz THEN WriteLn(' ',R.im[i]:dig:dec,'j') ELSE WriteLn;
      j:=j+1;
      IF (j=15) and (i<>R.n) THEN BEGIN Write('Mais...'#13); j:=0; ch:=ReadKey END
    END;
    WriteLn;
  END;

  PROCEDURE ApresentarRaizes;
  VAR
    Sair:BOOLEAN;
  BEGIN
    Sair:=FALSE;
    PlotarRaizes;
    REPEAT
      WriteLn(tl,'[Op‡”es para o c lculo de ra¡zes:]'#10);
      WriteLn(tl,'- mudar [P]arƒmetros');
      WriteLn(tl,'- [L]istar ra¡zes');
      WriteLn(tl,'- plotar [G]r fico');
      WriteLn(tl,'- [T]erminar');
      REPEAT ch:=UpCase(ReadKey) UNTIL (ch IN ['P','L','G','T']);
      CASE ch OF
        'P':BEGIN
              Write(#10'Tolerƒncia inicial para erro em ra¡z'); LerReal(tolz);
              Write('Tolerƒncia inicial para magnitudes'); LerReal(tolp);
              Write('Aproxima‡„o inicial real para ra¡z'); LerReal(xr0);
              Write('Aproxima‡„o inicial imag para ra¡z'); LerReal(xi0);
              Write('M¡nimo imagin rio no gr fico'); LerReal(y1);
              Write('M¡nimo real no gr fico'); LerReal(x1);
	      Write('Altura do gr fico'); LerReal(delta);
	      Write('Digitos'); LerInt(dig);
	      Write('Decimais (-1 p/not. cientifica)'); LerInt(dec);
              WriteLn;
            END;
        'L':ListarRaizes;
        'G':PlotarRaizes;
	'T':Sair:=TRUE;
      END;
    UNTIL Sair;
  END;

BEGIN {Programa principal CalcularRaizes}
  tol:=tolz; n:=Pol.n; a1:=Pol.cf; R.n:=n; ordem:=0; tolm:=tolp;
  xr:=xr0; xi:=xi0; feito:=FALSE; nn:=0;
  IF n<1 THEN
    BEGIN WriteLn(tl,#10#13'[*] N„o h  raizes a calcular'); Exit END;
  FOR i:=0 TO n DO a2[i]:=0;
  Write(tl,#10'Calculando...[');
  {Elimina‡„o de ra¡zes na origem}
  WHILE (n>1) and (a1[0]=0) DO BEGIN
    R.re[n]:=0; R.im[n]:=0;
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
      IF (d1=0) or (d2=0) THEN BEGIN
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
      IF (d<tolm) and (p<tolm) THEN BEGIN
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
        IF t<tol THEN BEGIN
          {Armazena ra¡zes calculadas}
          FOR i:=n+ordem DOWNTO n DO BEGIN
            Write(i,' ');
            R.re[i]:=xr; R.im[i]:=xi;
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
          ordem:=0; nn:=0;
          IF (Abs(xi)>0.01) THEN xi:=-xi ELSE BEGIN xi:=0.1; xr:=-xr END
        END
        ELSE BEGIN
          nn:=nn+1;
          {Demorando a convergir}
          IF nn>imax THEN BEGIN
            WriteLn(tl,#10#13'[*] Problemas de convergˆncia.');
            IF ordem>0 THEN WriteLn(tl,'[*] Ra¡z de multiplicidade ',ordem+1);
            WriteLn('  Erro atual:        ',t);
            WriteLn('  Mag. do polin“mio: ',p);
            WriteLn('  Mag. da derivada:  ',d);
            Write('  Tolerƒncia p/erro em ra¡z'); LerReal(tol);
            Write('  Tolerƒncia p/magnitudes'); LerReal(tolm);
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
        R.re[i]:=xr; R.im[i]:=xi;
      END
    END
  END;
  ApresentarRaizes;
END; {CalcularRaizes}

{
  Write('Grau: '); ReadLn(P.n);
  FOR i:=0 TO P.n DO BEGIN
    Write('a(',i:2,'): ');
    ReadLn(P.cf[i]);
  END;
END;
}

PROCEDURE LerPolinomio(VAR P:polinomio);
BEGIN
  Assign(arquivo,entrada);
  {$I-} Reset(arquivo); {$I+}
  IF IOResult<>0 THEN Interromper('Arquivo "['+entrada+']" nao encontrado');
  ReadLn(arquivo,P.n);
  FOR i:=0 TO P.n-1 DO ReadLn(arquivo,P.cf[i]);
  P.cf[P.n]:=1;
  WriteLn(tl,'[Polinomio lido:]'#10);
  FOR i:=0 TO P.n DO WriteLn(tl,'a([',i:2,']): ',P.cf[i]);
  Close(arquivo);
  Write(#10'Toque uma tecla...');
  ReadLn;
END;

PROCEDURE SalvarRaizes(VAR R:raizes);
BEGIN
  Assign(arquivo,saida);
  ReWrite(arquivo);
  Write(arquivo,'RR:{');
  FOR i:=1 TO R.n DO BEGIN
    Write(arquivo,R.Re[i]:dig:dec);
    IF i<>R.n THEN WriteLn(arquivo,',');
  END;
  Write(arquivo,'},'#13#10#13#10'RI:{');
  FOR i:=1 TO R.n DO BEGIN
    Write(arquivo,R.Im[i]:dig:dec);
    IF i<>R.n THEN WriteLn(arquivo,',');
  END;
  WriteLn(arquivo,'}');
  Close(arquivo);
  WriteLn(tl,#10'Arquivo "[',saida,']" escrito.');
END;

BEGIN
  InicializarParametros;
  WriteLn(tl,'[Calculo de raizes polinomiais]');
  WriteLn(    '-----------------------------');
  WriteLn('ACMQ - COPPE/UFRJ - 1989; Precisao ',precisao,#10);
  LerPolinomio(P);
  CalcularRaizes(P,R);
  SalvarRaizes(R);
END.
