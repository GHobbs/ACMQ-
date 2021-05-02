PROGRAM CAPZ; {VersÑo em Inglàs}
{*****************************************************************************
 * CAPZ - An†lise de filtros a capacitor chaveado usando interpolaáÑo p/FFT  *
 * Antînio Carlos MoreirÑo de Queiroz - COPPE/UFRJ - 1989                    *
 * Desenvolvido a partir da versÑo original, programa CAPZ, de 1984.         *
 * VersÑo 1.0  de 14/06/89                                                   *
 * VersÑo 1.1  de 22/06/89 Acrescentada resposta no tempo                    *
 * VersÑo 1.2  de 30/06/89 Acrescentado c†lculo de polos e zeros (BIV)       *
 * VersÑo 1.2a de 12/07/89 Mudada forma do expoente, hold vari†vel, etc.     *
 * VersÑo 1.2b de 14/07/89 Gr†ficos cont°nuos, pequenos detalhes             *
 * VersÑo 1.2c de 15/07/89 Somar unificada, fonte 1, correáîes               *
 * VersÑo 1.3  de 31/10/89 Escalas nos gr†ficos                              *
 * VersÑo 1.3a de 19/03/90 EdiáÑo de texto, melhor precisÑo no gr†fico mf.   *
 * VersÑo 1.3b de 29/06/90 ApresentaáÑo opcional dos numeradores das fases   *
 * VersÑo 1.4  de 30/03/91 Ligaáîes com as fontes tratadas, interface mudada *
 * VersÑo 1.4a de 03/06/91 Corrigido hold>1 em w=0; hold real; tempo mdy     *
 * VersÑo 1.4b de 09/07/91 Corrigidos zeros em 0 e alocacao de HZ            *
 *****************************************************************************}

{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}

USES Crt,Dos,Graph,Tela_e;

CONST
  versao='1.4b of 09/07/91';
  {$IFDEF DOUBLE}
  linmax=40; {Ordem m†xima do sistema de equaáîes}
  nosmax=60; {M†ximo n£mero de n¢s (>=linmax)}
  {$ELSE}
  linmax=50;
  nosmax=80;
  {$ENDIF}
  fasmax=12; {N£mero m†ximo de fases}
  gramax=32; {M†ximo grau de FFT}
  dig=15;    {Campo numÇrico}
  dec=9;     {Decimais}

TYPE
  coef_curto=ARRAY[0..gramax] of REAL;
  coef_longo=ARRAY[0..gramax*fasmax-1] of REAL;
  polinomio_curto=RECORD
    n,minpot:INTEGER;
    cf:coef_curto;
  END;
  polinomio_longo=RECORD
    n,minpot:INTEGER;
    cf:coef_longo;
  END;
  raizes=RECORD
    re,im:ARRAY[1..gramax*fasmax] of REAL;
    n:INTEGER;
  END;
  tipodepolinomio=(denominador,numparcial,numfase,numglobal);
  MatrizC=ARRAY [0..nosmax,0..nosmax+fasmax] of REAL;
  MatNum=ARRAY [0..linmax*fasmax-1,0..gramax div 2] of REAL;
  Apontador=ARRAY [-1..nosmax*fasmax] OF INTEGER;
  ptr_longo=^polinomio_longo;
  ptr_curto=^polinomio_curto;

VAR
  entrada,saida:TEXT;               {entrada/sa°da}
  Imag:REAL;                        {para Cmult}
  grau,ordem:INTEGER;               {para FFT}
  raio:REAL;                        {raio do c°rculo de interpolaáÑo}
  dispersao:REAL;                   {dispersÑo entre coeficientes de polinìmio}
  linhas,colunas:INTEGER;           {tamanho do sistema reduzido}
  fasxnos:INTEGER;                  {linhas do sistema nÑo reduzido}
  parciais:BOOLEAN;                 {listar numeradores parciais}
  dasfases:BOOLEAN;                 {listar numeradores das fases}
  relatorio:BOOLEAN;                {gerar relat¢rio}
  amostrar:BOOLEAN;                 {"sample-and-hold" na sa°da}
  poloscalculados:BOOLEAN;          {se foram calculados os polos}
  ok:BOOLEAN;                       {geral}
  grade:BOOLEAN;                    {grade nos gr†ficos}
  plotarfase:BOOLEAN;               {plotar gr†fico de fase}
  txt,rede,titulo:STRING;           {geral, nome da rede, nome de transferància}
  nos,fases,ns:INTEGER;             {no. de n¢s, de fases, n¢ de sa°da}
  hold:REAL;                        {tempo de hold entre fases}
  f,i,j,k,h,u,a1,a2,b1,b2:INTEGER;  {geral}
  cted:REAL;                        {cte do denominador}
  ch:CHAR;                          {geral}
  a,b,p:INTEGER;                    {n¢s,fases}
  t,r1,d,da,db,ta,tb,pa,pb:REAL;    {geral}
  w,z,za,zb:REAL;                   {freqÅàncias}
  HZ:^MatrizC;                      {matriz C}
  C,L:Apontador;                                      {apontadores}
  Z1,Z2:ARRAY [0..linmax,0..linmax+fasmax] of REAL;   {matriz do sistema}
  E1,E2:^MatNum;                                      {numeradores}
  X,Y:ARRAY[0..linmax-1] of REAL;                     {para FFT}
  D1,D2:ARRAY[0..gramax div 2] of REAL;               {denominadores}
  C1,C2,L1,L2:ARRAY [1..fasmax] of INTEGER;           {limites no sistema}
  NumP:ARRAY[1..fasmax,1..fasmax] OF ptr_curto;       {numeradores parciais}
  NumF:ARRAY[1..fasmax] OF ptr_longo;                 {numeradores das fases}
  NumG:polinomio_longo;                               {numerador global}
  Den:polinomio_curto;                                {denominador}
  Polos,Zeros:Raizes;                                 {p¢los e zeros}

{ParÉmetros para gr†ficos}

CONST
  unid:ARRAY[BOOLEAN] of STRING[4]=('Hz','rd/s');
  pixmin=43;
  pixmax=719;
  seta:ARRAY[1..8] OF PointType=((x:0;y:0),(x:8;y:0),(x:6;y:2),(x:8;y:4),
                                 (x:4;y:8),(x:2;y:6),(x:0;y:8),(x:0;y:0));

TYPE
  grafico=ARRAY[pixmin..pixmax] OF REAL;
  tipodefuncao=(impulso,degrau,senoide);

VAR
  cor1,cor2,cor3,placa,modo,dpm,dpt,xmin,xmax,ymin,ymax:INTEGER;
  tamanho,tamapont:WORD;
  csr,pt:POINTER;
  freqchav,gmin,gmax,wmin,wmax,vmin,vmax,fator,x1,y1,
  freq,fase,delta,tolz,tolp,xr0,xi0:REAL;
  rads,log:BOOLEAN;
  funcao:tipodefuncao;

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

PROCEDURE Interromper(mens:STRING; algomais:BOOLEAN);
BEGIN
  IF algomais THEN WriteLn(txt);
  WriteLn(tl,#10#13'[*] '+mens+'.');
  IF relatorio THEN BEGIN
    IF algomais THEN WriteLn(saida,txt);
    WriteLn(saida,#13#10'* '+mens+'.');
    Close(saida);
  END;
  WriteLn(#10'Touch any key...');
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
  gmin:=-60; gmax:=10; wmin:=0.2; wmax:=5; dpm:=4;
  freqchav:=1; fases:=2; hold:=1;
  vmin:=-0.5; vmax:=1.5; freq:=0.2; fase:=0; funcao:=degrau; dpt:=4;
  y1:=-2.0; x1:=-2.0; delta:=4; xr0:=1.1; xi0:=0.1;
  dasfases:=FALSE; parciais:=FALSE; relatorio:=FALSE; amostrar:=TRUE;
  rads:=TRUE; log:=TRUE; grade:=TRUE; plotarfase:=TRUE;
  raio:=1.1; dispersao:=1e6;
  New(E1); New(E2);
  DetectGraph(placa,modo);
  IF placa=CGA THEN modo:=CGAC0;
  IF paramcount=3 THEN BEGIN
    Val(ParamStr(2),placa,i);
    Val(ParamStr(3),modo,i);
  END;
  InitGraph(placa,modo,GetEnv('TPBGI'));
  i:=GraphResult; IF i<>GrOk THEN Interromper(GraphErrorMsg(i),FALSE);
  IF placa=1 THEN BEGIN
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
  IF ParamCount>0 THEN rede:=ParamStr(1) ELSE rede:='';
  RestoreCrtMode;
END;

PROCEDURE AbrirSaida;
VAR
  dia,mes,ano,dsem,hora,minuto,segundo,seg100:WORD;
BEGIN
  txt:=rede+'.cpz';
  Write(tl,#10'Output file: '); EditarLinha(txt,WhereX,WhereY,1);
  WriteLn;
  Assign(saida,txt);
  ReWrite(saida);
  GetDate(ano,mes,dia,dsem);
  GetTime(hora,minuto,segundo,seg100);
  WriteLn(saida,'*====* CAPZ *====* Version ',versao,' *====* ',mes,'/'
          ,dia,'/',ano,' ',hora,':',minuto,':',segundo,' *====*');
  WriteLn(saida,#13#10'Title: ',rede);
  WriteLn(saida,#13#10'Nodes: ',nos,'; Phases: ',fases,'; Radius: ',raio:10,'; Dispersion: ',dispersao:10);
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

PROCEDURE Biv(Pol:ptr_longo; VAR R:raizes; tipo:tipodepolinomio);
CONST
  imax=50;
VAR
  a1,a2,c1,c2:coef_longo;
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
          IF tipo=denominador THEN OutText('Pole') ELSE OutText('Zero');
          Str(indice,txt); OutText(' '+txt+':');
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
    WriteLn(tl,#10'[',titulo,': Roots in z^(1/',fases,'):]'#10);
    j:=0;
    FOR i:=1 TO R.n DO BEGIN
      Write(tl,'z([',i:2,']):',R.re[i]:dig:dec);
      IF Abs(R.im[i])>tolz THEN WriteLn(R.im[i]:dig:dec,'j') ELSE WriteLn;
      j:=j+1;
      IF (j=15) and (i<>R.n) THEN BEGIN Write('More...'#13); j:=0; ch:=ReadKey END
    END;
    WriteLn;
  END;

  PROCEDURE ConverterRaizes;
  VAR
    NR:raizes;
    m,f,f1:REAL;
  BEGIN
    WITH R DO BEGIN
      k:=Pol^.minpot;
      NR.n:=n*fases+k;
      FOR i:=1 TO k DO BEGIN NR.re[i]:=0; NR.im[i]:=0 END;
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
    IF tipo<numfase THEN ConverterRaizes;
    PlotarRaizes;
    REPEAT
      WriteLn(tl,'[Root calculation options:]'#10);
      WriteLn(tl,'- change [P]arameters');
      IF relatorio THEN WriteLn(tl,'- include roots in [R]eport');
      WriteLn(tl,'- [L]ist roots');
      WriteLn(tl,'- plot [G]raph');
      WriteLn(tl,'- [C]ontinue analysis');
      REPEAT ch:=UpCase(ReadKey) UNTIL (ch IN ['P','L','G','C']) or relatorio and (ch='R');
      CASE ch OF
        'P':BEGIN
              Write(#10'Initial tolerance for error in root'); LerReal(tolz);
              Write('Initial tolerance for magnitudes'); LerReal(tolp);
              Write('Initial real part approximation for root'); LerReal(xr0);
              Write('Initial imag part approximation for root'); LerReal(xi0);
              Write('Minimum imag value in the graph'); LerReal(y1);
              Write('Minimum real value in the graph'); LerReal(x1);
              Write('Graph height'); LerReal(delta);
              WriteLn;
            END;
        'R':BEGIN
              WriteLn(saida,#13#10,titulo,': Roots in z^(1/',fases,'):');
              FOR j:=1 TO R.n DO WriteLn(saida,'  z(',j:2,'): ',R.re[j]:dig:dec,' ',R.im[j]:dig:dec,'j');
              WriteLn(tl,#10'[*] Roots written'#10);
            END;
        'L':ListarRaizes;
        'G':PlotarRaizes;
        'C':Sair:=TRUE;
      END;
    UNTIL Sair;
    IF tipo=denominador THEN poloscalculados:=TRUE;
  END;

BEGIN {Programa principal BIV}
  n:=Pol^.n; a1:=Pol^.cf;
  tol:=tolz; R.n:=n; ordem:=0; tolm:=tolp;
  xr:=xr0; xi:=xi0; nn:=0; feito:=FALSE;
  IF (n<1) THEN BEGIN
    IF (Pol^.minpot>0) and (a1[0]<>0) THEN WriteLn(tl,#13#10'[',Pol^.minpot,'] roots at z^(1/',fases,')=0')
    ELSE WriteLn(tl,#10#13'[*] No roots to compute');
    Exit
  END;
  Write(tl,#10'Computing...[');
  {EliminaáÑo de ra°zes na origem}
  WHILE (n>1) and (a1[0]=0) DO BEGIN
    R.re[n]:=0; R.im[n]:=0;
    Write(n,' ');
    n:=n-1;
    FOR i:=0 TO n DO a1[i]:=a1[i+1]
  END;
  {NormalizaáÑo}
  FOR i:=0 TO n DO BEGIN a2[i]:=0; a1[i]:=a1[i]/a1[n] END;
  WHILE NOT feito DO BEGIN
    IF n>1 THEN BEGIN
      {Calculo dos valores do polinìmio (p) e de sua derivada (d)}
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
      {C†lculo do erro. Esta forma dificulta overflow}
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
      {Testa poss°vel ra°z m£ltipla}
      d:=Abs(d1)+Abs(d2);
      p:=Abs(p1)+Abs(p2);
      IF (d<tolm) and (p<tolm) THEN BEGIN
        {deriva o polinìmio e continua}
        IF ordem=0 THEN BEGIN c1:=a1; c2:=a2 END;
        FOR i:=1 TO n DO BEGIN
          a1[i-1]:=a1[i]*i/n;
          a2[i-1]:=a2[i]*i/n;
        END;
        n:=n-1; ordem:=ordem+1;
        Write('+')
      END
      ELSE BEGIN
        {Atualiza ra°zes}
        xr:=xr-e1;
        xi:=xi-e2;
        {Testa convergància}
        t:=Abs(e1)+Abs(e2);
        IF t<tol THEN BEGIN
          {Armazena ra°zes calculadas}
          FOR i:=n+ordem DOWNTO n DO BEGIN
            Write(i,' ');
            R.re[i]:=xr; R.im[i]:=xi;
          END;
          {Repîe polinìmio original, se for o caso}
          IF ordem>0 THEN BEGIN
            a1:=c1; a2:=c2; n:=n+ordem;
          END;
          {Deflaciona polinìmio}
          FOR i:=0 TO ordem DO BEGIN
            FOR j:=n-1 DOWNTO 1 DO BEGIN
              a1[j]:=Cmult(xr,xi,a1[j+1],a2[j+1])+a1[j];
              a2[j]:=Imag+a2[j];
            END;
            n:=n-1;
            FOR j:=0 TO n DO
              BEGIN a1[j]:=a1[j+1]; a2[j]:=a2[j+1] END
          END;
          {Prepara c†lculo da pr¢xima ra°z}
          ordem:=0; nn:=0;
          IF (Abs(xi)>0.01) THEN xi:=-xi ELSE BEGIN xi:=0.1; xr:=-xr END
        END
        ELSE BEGIN
          nn:=nn+1;
          {Demorando a convergir}
          IF nn>imax THEN BEGIN
            WriteLn(tl,#10#13'[*] Convergence problems.');
            IF ordem>0 THEN WriteLn(tl,'[*] Root of multiplicity ',ordem+1);
            WriteLn('  Present error:         ',t);
            WriteLn('  Polynomial magnitude.: ',p);
            WriteLn('  Derivative magnitude.: ',d);
            Write('  Tolerance for error in root'); LerReal(tol);
            Write('  Tolerance for magnitudes'); LerReal(tolm);
            Write('  Real part approximation'); LerReal(xr);
            Write('  Imag part appxoximation'); LerReal(xi);
            Write(tl,'[');
            nn:=0;
          END
        END
      END
    END
    ELSE BEGIN
      {Ultimas ra°zes}
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
END; {Biv}

PROCEDURE PlotarTempo(VAR Numx:polinomio_longo; tipo:tipodepolinomio);
LABEL
  Continuar,Retracar,Cursor,Fim;
VAR
  av,bv,dt:REAL;
  colcsr,dc,ultimo:INTEGER;
  Vo,Vi,Tempo:^grafico;

  FUNCTION Vin(t:REAL):REAL;
  BEGIN
    CASE funcao OF
      degrau:Vin:=1;
      impulso:IF t=0 THEN Vin:=1 ELSE Vin:=0;
      senoide:Vin:=Sin(2*Pi*freq*t+fase*Pi/180);
    END;
  END;

  PROCEDURE CalcularConstantes;
  BEGIN
    av:=(ymax-ymin)/(vmin-vmax);
    bv:=ymax-av*vmin;
    dt:=1/(freqchav*fases);
    colcsr:=-10; {para o cursor}
  END;

  FUNCTION Limite(x:REAL):INTEGER;
  VAR
    t:REAL;
  BEGIN
    t:=av*x+bv;
    IF t>ymax THEN t:=ymax
    ELSE IF t<ymin THEN t:=ymin;
    Limite:=Round(t);
  END;

  PROCEDURE MudarParametros;
  BEGIN
    Write(#10'Minimum voltage (V)'); LerReal(vmin);
    Write('Maximum voltage (V)'); LerReal(vmax);
    Write('Switching frequency (Hz)'); LerReal(freqchav);
    Write('Output sample-and-hold'); LerBool(amostrar);
    Write('Pixels per point'); LerInt(dpt);
    Write(tl,'Excitation function: [I]mpulse, [S]tep, si[N]usoid ');
    REPEAT ch:=UpKey UNTIL ch in ['I','S','N'];
    WriteLn(tl,'[',ch,']');
    CASE ch OF
      'I':funcao:=impulso;
      'S':funcao:=degrau;
      'N':funcao:=senoide;
    END;
   IF funcao=senoide THEN BEGIN
      Write('Frequency (Hz)'); LerReal(freq);
      Write('Phase (degrees)'); LerReal(fase);
    END;
    ultimo:=-1;
  END;

  PROCEDURE EscreverTabela;
  BEGIN
    IF not relatorio THEN BEGIN
      Write(tl,#10'[*] No report open. Open one now'); LerBool(relatorio);
      IF not relatorio THEN Exit;
      AbrirSaida;
    END;
    i:=xmin;
    WriteLn(saida,#13#10'Transient response; ',titulo,'; Sw. freq.=',Cpct(freqchav),' Hz');
    CASE funcao OF
      senoide:txt:='Unit sinusoid: '+Sr(freq)+' Hz, '+Sr(fase)+' degrees';
      impulso:txt:='Unit impulse';
      degrau:txt:='Unit step'
    END;
    WriteLn(saida,'Vi(t) = ',txt);
    WriteLn(saida,#13#10,'Time (s)':dig,'Vi(t)':dig,'Vo(t)':dig,#13#10);
    REPEAT
      WriteLn(saida,Tempo^[i]:dig:dec,Vi^[i]:dig:dec,Vo^[i]:dig:dec);
      i:=i+dpt;
    UNTIL i>ultimo;
    WriteLn(tl,#10'[*] Table written.');
  END;

BEGIN
  New(Vo); New(Vi); New(Tempo);
  ultimo:=xmin-1;
 Retracar:
  CalcularConstantes;
  IniciarGrafico(0,(xmax-xmin)*dt/dpt,vmin,vmax,FALSE);
  MoveTo(0,0);
  OutText('CAPZ - '+rede+' - '+titulo);
  OutTextXY(xmin+2,ymin,'Vi,Vo(V)');
  OutTextXY(xmax-32,ymax-8,'t(s)');
  w:=0; h:=xmin; k:=xmin; j:=Den.n*fases;
  REPEAT
    IF h>ultimo THEN BEGIN
      t:=0;
      p:=((h-xmin) div dpt) mod fases+1; {fase atual}
      Vi^[h]:=Vin(w);
      IF tipo=numglobal THEN
        WITH NumF[p]^ DO BEGIN
          FOR i:=0 TO n DO
            IF h+(i-j)*dpt>=xmin THEN
               t:=t+cf[i]*Vi^[h+(i-j)*dpt];
        END
      ELSE IF p=a THEN
        WITH Numx DO BEGIN
          FOR i:=0 TO n DO
            IF h+(i-j)*dpt>=xmin THEN
               t:=t+cf[i]*Vi^[h+(i-j)*dpt];
        END;
      IF (tipo=numglobal) or (a=p) THEN
        WITH Den DO
          FOR i:=0 TO n-1 DO
            IF h+(i*fases-j)*dpt>=xmin THEN
              t:=t-cf[i]*Vo^[h+(i*fases-j)*dpt];
      Vo^[h]:=t;
      Tempo^[h]:=w;
    END;
    IF h>xmin THEN BEGIN
      MoveTo(h-dpt+1,Limite(Vi^[h-dpt]));
      SetColor(cor3);
      LineTo(h,GetY);
      LineTo(h,Limite(Vi^[h]));
      SetColor(cor1);
      IF amostrar THEN BEGIN
        MoveTo(h-dpt,Limite(Vo^[h-dpt]));
        LineTo(h,GetY);
        LineTo(h,Limite(Vo^[h]));
      END
      ELSE Line(h,Limite(0),h,Limite(Vo^[h]))
    END;
    IF KeyPressed THEN BEGIN
      IF h>ultimo THEN ultimo:=h;
      GoTo Cursor;
    END;
   Continuar:
    w:=w+dt;
    h:=h+dpt
  UNTIL h>xmax;
  h:=xmax; ultimo:=xmax;
 Cursor:
  dc:=dpt;
  REPEAT
    CASE UpCase(ReadKey) OF
      'G':BEGIN
            grade:=not grade;
            GoTo Retracar
          END;
      #0:CASE ReadKey OF
           'K':IF k>=xmin+dc THEN k:=k-dc;
           'M':IF k<=h-dc THEN k:=k+dc;
           'H':BEGIN
                 t:=(vmax-vmin)/2;
                 vmin:=vmin+t;
                 vmax:=vmax+t;
                 GoTo Retracar;
               END;
           'P':BEGIN
                 t:=(vmax-vmin)/2;
                 vmin:=vmin-t;
                 vmax:=vmax-t;
                 GoTo Retracar;
               END;
           'I':dc:=10*dpt;
           'Q':dc:=dpt;
         END;
     '-':BEGIN
           vmax:=2*vmax-vmin;
           GoTo Retracar;
         END;
     '+':BEGIN
           vmax:=(vmax+vmin)/2;
           GoTo Retracar;
         END;
     #13:IF h<xmax THEN GoTo Continuar;
     #27:BEGIN
           RestoreCrtMode;
           WriteLn(tl,'[Transient response computation options:]');
           REPEAT
             WriteLn(tl,#10'- change [P]arameters');
             WriteLn(tl,'- save table in [R]eport');
             WriteLn(tl,'- redraw [G]raph');
             WriteLn(tl,'- [C]ontinue analysis');
             REPEAT ch:=UpCase(ReadKey) UNTIL ch in ['P','R','G','C'];
             CASE ch OF
               'P':BEGIN MudarParametros; GoTo Retracar END;
               'R':EscreverTabela;
               'G':GoTo Retracar;
               'C':GoTo Fim;
             END;
           UNTIL FALSE;
         END;
    END;
    PutImage(colcsr,ymin,csr^,XORPut);
    colcsr:=k;
    PutImage(colcsr,ymin,csr^,XORPut);
    Bar(0,0,GetMaxX,9);
    MoveTo(0,0);
    Str(Tempo^[k]:9:5,txt);
    OutText('t:'+txt);
    Str(((colcsr-xmin) div dpt) mod fases+1,txt);
    OutText(' p:'+txt);
    Str(Vi^[k]:8:5,txt);
    OutText(' Vi:'+txt);
    Str(Vo^[k]:8:5,txt);
    OutText(' Vo:'+txt);
  UNTIL FALSE;
 Fim:
 Dispose(Tempo); Dispose(Vi); Dispose(Vo);
END;

PROCEDURE PlotarModuloFase(VAR Num:polinomio_longo);
LABEL
  Continuar,Retracar,Cursor,Fim;
VAR
  ag,bg,af,bf,dw:REAL;
  colcsr,dc,ultimo:INTEGER;
  Gan,Ang,Frq:^grafico;

  PROCEDURE CalcularConstantes;
  BEGIN
    ag:=(ymax-ymin)/(gmin-gmax);
    bg:=ymax-ag*gmin;
    af:=-(ymax-ymin)/360;
    bf:=ymax+af*180;
    IF log THEN dw:=Ex(wmax/wmin,dpm/(xmax-xmin)) ELSE dw:=dpm*(wmax-wmin)/(xmax-xmin);
    colcsr:=-10; {para o cursor}
  END;

  PROCEDURE Avaliar(pol:ptr_longo; VAR ta,tb:REAL; dexp:INTEGER);
  BEGIN
    WITH pol^ DO BEGIN
      z:=w/freqchav/dexp;
      IF not rads THEN z:=2*Pi*z;
      za:=Cos(z); zb:=Sin(z);
      ta:=0; tb:=0;
      FOR i:=n DOWNTO 0 DO BEGIN
        t:=ta*za-tb*zb+cf[i];
        tb:=ta*zb+tb*za;
        ta:=t;
      END;
    END;
  END;

  FUNCTION Modulo(x:INTEGER):INTEGER;
  VAR
    t:REAL;
  BEGIN
    t:=ag*Gan^[x]+bg;
    IF t>ymax THEN t:=ymax
    ELSE IF t<ymin THEN t:=ymin;
    Modulo:=Round(t);
  END;

  PROCEDURE MudarParametros;
  BEGIN
    Write(#10'Frequencies in rad/s'); LerBool(rads);
    Write('Logarithmic scale'); LerBool(log);
    Write('Minimum frequency (',unid[rads],')'); LerReal(wmin);
    Write('Maximum frequency (',unid[rads],')'); LerReal(wmax);
    Write('Minimum gain (dB)'); LerReal(gmin);
    Write('Maximum gain (dB)'); LerReal(gmax);
    Write('Switching frequency (Hz)'); LerReal(freqchav);
    Write('Output sample-and-hold'); LerBool(amostrar);
    IF amostrar THEN BEGIN
      Write('Hold time between phases (phases)'); LerReal(hold)
    END;
    Write('Pixels per point'); LerInt(dpm);
    ultimo:=-1;
  END;

  PROCEDURE EscreverTabela;
  BEGIN
    IF not relatorio THEN BEGIN
      Write(tl,#10'[*] No report open. Open one now'); LerBool(relatorio);
      IF not relatorio THEN Exit;
      AbrirSaida;
    END;
    i:=xmin;
    Write(saida,#13#10'Frequency response; ',titulo,'; Sw. freq.=',Cpct(freqchav),' Hz');
    IF amostrar THEN WriteLn(saida,'; S/H (',Cpct(hold),' ph.)') ELSE WriteLn(saida);
    WriteLn(saida,#13#10,'Freq. ('+unid[rads]+')':dig,'Gain':dig,'Phase':dig,#13#10);
    REPEAT
      WriteLn(saida,Frq^[i]:dig:dec,Gan^[i]:dig:dec,Ang^[i]:dig:dec);
      i:=i+dpm;
    UNTIL i>ultimo;
    WriteLn(tl,#10'[*] Table written.');
  END;

BEGIN
  New(Gan); New(Ang); New(Frq);
  ultimo:=xmin-1;
 Retracar:
  CalcularConstantes;
  IniciarGrafico(wmin,wmax,gmin,gmax,log);
  MoveTo(0,0);
  OutText('CAPZ - '+rede+' - '+titulo);
  MoveTo(xmin+2,ymin); OutText('dB'); IF plotarfase THEN OutText(',deg.');
  OutTextXY(xmax-32,ymax-8,unid[rads]);
  w:=wmin; h:=xmin; k:=xmin;
  REPEAT
    IF h>ultimo THEN BEGIN
      Avaliar(@Num,ta,tb,fases);
      Avaliar(@Den,da,db,1);
      IF (da=0) or (db=0) THEN BEGIN
        t:=Sqr(da)+Sqr(db);
        pa:=(ta*da+tb*db)/t; pb:=(tb*da-ta*db)/t;
      END
      ELSE BEGIN
        t:=da/db+db/da;
        pa:=(ta/db+tb/da)/t; pb:=(tb/db-ta/da)/t
      END;
      IF amostrar THEN BEGIN
        t:=w/freqchav;
        IF not rads THEN t:=2*Pi*t;
        z:=t/fases*hold;
        IF z=0 THEN BEGIN ta:=hold/fases; tb:=0 END
        ELSE BEGIN ta:=Sin(z)/t; tb:=(Cos(z)-1)/t END;
        pa:=Cmult(pa,pb,ta,tb); pb:=Imag;
      END
      ELSE BEGIN
        pa:=pa/fases;
        pb:=pb/fases
      END;
      IF pa=0 THEN BEGIN
        IF pb=0 THEN pb:=1e-11;
        pa:=pb*1e-11
      END;
      Ang^[h]:=Arctan(pb/pa)*57.29577951;
      Gan^[h]:=Ln(Sqr(pa)+Sqr(pb))*4.342944819;
      IF pa<0 THEN
        IF pb>0 THEN Ang^[h]:=180+Ang^[h] ELSE Ang^[h]:=Ang^[h]-180;
      Frq^[h]:=w
    END;
    IF h>xmin THEN BEGIN
      IF plotarfase THEN BEGIN
        SetColor(cor3);
        Line(h-dpm,Round(af*Ang^[h-dpm]+bf),h,Round(af*Ang^[h]+bf));
        SetColor(cor1)
      END;
      Line(h-dpm,Modulo(h-dpm),h,Modulo(h));
    END;
    IF KeyPressed THEN BEGIN
      IF h>ultimo THEN ultimo:=h;
      GoTo Cursor;
    END;
   Continuar:
    IF log THEN w:=w*dw ELSE w:=w+dw;
    h:=h+dpm
  UNTIL h>xmax;
  h:=xmax; ultimo:=xmax;
 Cursor:
  dc:=dpm;
  REPEAT
    CASE UpCase(ReadKey) OF
      'G':BEGIN
            grade:=not grade;
            GoTo Retracar
          END;
      'F':BEGIN
            plotarfase:=not plotarfase;
            GoTo Retracar
          END;
      #0:CASE ReadKey OF
           'K':IF k>=xmin+dc THEN k:=k-dc;
           'M':IF k<=h-dc THEN k:=k+dc;
           'H':BEGIN
                 t:=(gmax-gmin)/2;
                 gmin:=gmin+t;
                 gmax:=gmax+t;
                 GoTo Retracar;
               END;
           'P':BEGIN
                 t:=(gmax-gmin)/2;
                 gmin:=gmin-t;
                 gmax:=gmax-t;
                 GoTo Retracar;
               END;
           'I':dc:=10*dpm;
           'Q':dc:=dpm;
         END;
     '-':BEGIN
           gmax:=2*gmax-gmin;
           GoTo Retracar;
         END;
     '+':BEGIN
           gmax:=(gmax+gmin)/2;
           GoTo Retracar;
         END;
     #13:IF h<xmax THEN GoTo Continuar;
     #27:BEGIN
           RestoreCrtMode;
           WriteLn(tl,'[Frequency response computation options:]');
           REPEAT
             WriteLn(tl,#10'- change [P]arameters');
             WriteLn(tl,'- save table in [R]eport');
             WriteLn(tl,'- redraw [G]raph');
             WriteLn(tl,'- [C]ontinue analysis');
             REPEAT ch:=UpCase(ReadKey) UNTIL ch in ['P','R','G','C'];
             CASE ch OF
               'P':BEGIN MudarParametros; GoTo Retracar END;
               'R':EscreverTabela;
               'G':GoTo Retracar;
               'C':GoTo Fim;
             END;
           UNTIL FALSE;
         END;
    END;
    PutImage(colcsr,ymin,csr^,XORPut);
    colcsr:=k;
    PutImage(colcsr,ymin,csr^,XORPut);
    Bar(0,0,GetMaxX,9);
    MoveTo(0,0);
    Str(Frq^[k]:10:4,txt);
    OutText('Fr:'+txt);
    Str(Gan^[k]:10:4,txt);
    OutText(' Ga:'+txt);
    Str(Ang^[k]:9:4,txt);
    OutText(' Ph:'+txt);
  UNTIL FALSE;
 Fim:
 Dispose(Frq); Dispose(Ang); Dispose(Gan);
END;

PROCEDURE Inicializar;

  PROCEDURE AbrirEntrada;
  BEGIN
    ok:=FALSE;
    REPEAT
      Write(tl,#10']File with the circuit description (.net) or ?: ');
      txt:=rede; EditarLinha(txt,WhereX,WhereY,1); WriteLn;
      IF txt='?' THEN Diretorio
      ELSE BEGIN
        IF Pos('.',txt)=0 THEN txt:=txt+'.net';
        rede:=Copy(txt,1,Pos('.',txt)-1);
        Assign(entrada,txt);
        {$I-} Reset(entrada) {$I+};
        ok:=(IOresult=0);
        IF not ok THEN WriteLn(tl,#10'[*] File [',txt,'] inexist.')
      END
    UNTIL ok;
  END;

BEGIN
  ClrScr;
  WriteLn(tl,'[…ÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕª');
  WriteLn(tl,'∫     CAPZ] - Switched capacitor filter analysis in z-transform     [∫');
  WriteLn(tl,'∫]                Antìnio Carlos MoreirÑo de Queiroz                [∫');
  WriteLn(tl,'∫]   COPPE - Universidade Federal do Rio de Janeiro - 1984, 1991    [∫');
  WriteLn(tl,'»ÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕº]');
  WriteLn('Version ',versao,' - ',precisao,' precision');
  AbrirEntrada;
  ReadLn(entrada,nos);
  WriteLn(#10'Number of nodes: ',nos);
  Write(#10'Number of phases'); LerInt(fases);
  Write('Radius of the interpolation circle'); LerReal(raio);
  Write('Dispersion among polynomial coefficients'); LerReal(dispersao);
  Write('Generate report'); LerBool(relatorio);
  IF relatorio THEN BEGIN
    Write('Save partial numerators'); LerBool(parciais);
    Write('Save phase numerators'); LerBool(dasfases);
    AbrirSaida;
  END;
  linhas:=fases*nos;
  fasxnos:=linhas;
  FOR i:=-1 TO fasxnos DO BEGIN C[i]:=i; L[i]:=i; END;
  poloscalculados:=FALSE;
  WriteLn;
  FOR a:=1 TO fases DO
    FOR b:=1 TO fases DO New(NumP[a,b]);
  FOR a:=1 TO fases DO New(NumF[a]);
  New(HZ)
END;

PROCEDURE LerDescricao;
VAR
  ligado:ARRAY[1..fasmax] OF BOOLEAN;

  PROCEDURE Curto;
  BEGIN
    Interromper('Forbidden circuit (short-circuit); verify description',TRUE);
  END;

  PROCEDURE Testarfase(f:INTEGER);
  BEGIN
    IF (f<1) or (f>fases) THEN Interromper('Invalid phase',TRUE);
  END;

  PROCEDURE Somar(VAR P:apontador; a,b,f:INTEGER);
  BEGIN
    IF a>0 THEN a2:=a+(f-1)*nos ELSE a2:=a;
    IF b>0 THEN b2:=b+(f-1)*nos ELSE b2:=b;
    IF P[a2]<P[b2] THEN BEGIN a1:=P[a2]; b1:=P[b2] END
    ELSE BEGIN a1:=P[b2]; b1:=P[a2] END;
    IF a1=b1 THEN Curto;
    FOR i:=1 TO fasxnos DO BEGIN
      IF P[i]=b1 THEN P[i]:=a1;
      IF P[i]>b1 THEN P[i]:=P[i]-1;
    END;
  END;

BEGIN
  FOR i:=0 TO nos DO
    FOR j:=0 TO nos DO HZ^[i,j]:=0;
  ClrScr;
  WriteLn(tl,'[Circuit description:]'#10);
  IF relatorio THEN WriteLn(saida,#13#10'Circuit description:'#13#10);
  WHILE not SeekEof(entrada) DO BEGIN
    txt:='';
    REPEAT
      Read(entrada,ch);
      IF ch<>' ' THEN txt:=txt+ch;
    UNTIL ch=' ';
    CASE UpCase(txt[1]) of
      'C':BEGIN
            ReadLn(entrada,a,b,t);
            txt:='Capacitor '+txt+'; '+Si(a)+' to '+Si(b)+', '+Sr(t)+' unit';
            HZ^[a,a]:=HZ^[a,a]+t;
            HZ^[b,b]:=HZ^[b,b]+t;
            HZ^[a,b]:=HZ^[a,b]-t;
            HZ^[b,a]:=HZ^[b,a]-t;
          END;
      'S':BEGIN
            Read(entrada,a,b);
            txt:='Switch '+txt+'; '+Si(a)+' to '+Si(b)+', closed in phase(s)';
            WHILE not SeekEoln(entrada) DO BEGIN
              Read(entrada,f);
              txt:=txt+' '+Si(f);
              TestarFase(f);
              Somar(C,a,b,f);
              Somar(L,a,b,f);
              linhas:=linhas-1;
            END;
          END;
      'P':BEGIN
            FOR i:=1 TO fases DO ligado[i]:=FALSE;
            Read(entrada,a,b,p);
            txt:='Toggle switch '+txt+' from '+Si(p)+' to '+Si(a)+' or '+Si(b)+'; to '+Si(a)+' in(s) phase(s)';
            IF SeekEoln(entrada) THEN BEGIN ligado[1]:=TRUE; txt:=txt+' 1' END;
            WHILE not SeekEoln(entrada) DO BEGIN
              Read(entrada,f);
              txt:=txt+' '+Si(f);
              TestarFase(f);
              ligado[f]:=TRUE;
            END;
            FOR f:=1 TO fases DO
              IF ligado[f] THEN BEGIN
                Somar(C,p,a,f);
                Somar(L,p,a,f);
                linhas:=linhas-1;
              END
              ELSE BEGIN
                Somar(C,p,b,f);
                Somar(L,p,b,f);
                linhas:=linhas-1;
              END;
          END;
  'A','O':BEGIN
            ReadLn(entrada,a,b,p);
            txt:='Operational amp. '+txt+'; '+Si(a)+' (-), '+Si(b)+' (+), and '+Si(p)+' (output)';
            FOR f:=1 TO fases DO BEGIN
              Somar(C,a,b,f);
              Somar(L,0,p,f);
              linhas:=linhas-1;
            END;
          END;
      'V':BEGIN
            ReadLn(entrada,a);
            txt:='Source '+txt+' connected to node '+Si(a);
            FOR f:=1 TO fases DO BEGIN
              Somar(C,a,-1,f);
              Somar(L,a,0,f);
              linhas:=linhas-1;
            END;
          END;
      ELSE Interromper('Unknown element: ['+txt+']',FALSE);
    END;
    WriteLn(txt);
    IF relatorio THEN WriteLn(saida,txt);
  END;
  Close(entrada);
  grau:=1; ordem:=0; colunas:=linhas+fases;
  WriteLn(tl,#10'System order:[ ',linhas,']');
  k:=linhas div fases; IF Frac(linhas/fases)<>0 THEN k:=k+1;
  Write(#10'Estimated degree for denominator'); LerInt(k);
  WHILE grau<=k DO BEGIN grau:=grau*2; ordem:=ordem+1 END;
  WriteLn(tl,#10'Interpolation degree: [',grau,']');
  IF relatorio THEN WriteLn(saida,#13#10'System order: ',linhas,'; Interpolation degree: ',grau);
  IF linhas>linmax THEN Interromper('Excessive system order (Max=['+Si(linmax)+'])',FALSE);
  IF grau>gramax THEN Interromper('Excessive interpolation degree (Max=['+Si(gramax)+'])',FALSE);
END;

PROCEDURE ReduzirSistema;
BEGIN
  FOR i:=0 TO linhas DO
    FOR j:=0 TO colunas DO Z1[i,j]:=0;
  FOR f:=1 TO fases DO BEGIN
    C2[f]:=0; L2[f]:=0;
    {C1 e L1 comeáam de 1 e terminam antes do pr¢ximo C2, L2}
  END;
  FOR f:=1 TO fases DO BEGIN
    k:=(f-1)*nos;
    FOR i:=1 TO nos DO BEGIN
      a:=L[k+i];
      a1:=L[1+(k+i+nos-1) MOD fasxnos];
      IF a>L2[f] THEN L2[f]:=a;
      b:=C[k+i];
      IF b>C2[f] THEN C2[f]:=b;
      FOR j:=1 TO nos DO BEGIN
        b:=C[j+k];
        IF b=-1 THEN BEGIN
          Z1[a,linhas+f]:=Z1[a,linhas+f]-HZ^[i,j];   {Diagonal principal da excitaáÑo}
          Z1[a1,linhas+f]:=Z1[a1,linhas+f]+HZ^[i,j]; {Diagonal inferior da excitaáÑo}
        END
        ELSE BEGIN
          Z1[a,b]:=Z1[a,b]+HZ^[i,j];   {Diagonal principal de submatrizes}
          Z1[a1,b]:=Z1[a1,b]-HZ^[i,j]; {Diagonal inferior de submatrizes}
        END
      END;
    END;
    C1[1]:=1; L1[1]:=1;
    FOR i:=2 TO fases DO BEGIN C1[i]:=C2[i-1]+1; L1[i]:=L2[i-1]+1 END;
  END;
{Transferància do sistema reduzido para a posiáÑo final}
  FOR i:=1 TO linhas DO
    FOR j:=1 TO colunas DO HZ^[i,j]:=Z1[i,j];
END;

PROCEDURE AvaliarSistema;
BEGIN
  txt:='';
  Write(tl,#10'Analyzing...[');
  FOR h:=0 TO grau div 2 DO BEGIN
    Write(grau div 2-h,' ');
    r1:=Ex(raio,1/fases); z:=2*Pi*h/grau; za:=r1*Cos(z/fases); zb:=r1*Sin(z/fases);
    {Montagem do sistema de equaáîes}
    FOR i:=1 TO linhas DO BEGIN
      FOR j:=1 TO colunas DO BEGIN
        Z1[i,j]:=HZ^[i,j];
        Z2[i,j]:=0;
      END
    END;
    FOR f:=1 TO fases DO BEGIN
      k:=linhas+f;
      FOR i:=L1[f] TO L2[f] DO BEGIN
        {Observar que Z1,Z2 e real puro. Pode ser mais simples}
        {Multiplicar por z^1/f os subvetores da diagonal da excitaáÑo}
        Z1[i,k]:=Cmult(Z1[i,k],Z2[i,k],za,zb);
        Z2[i,k]:=Imag;
        {Multiplicar por z^1/f as submatrizes na diagonal da matriz}
        FOR j:=C1[f] TO C2[f] DO BEGIN
          Z1[i,j]:=Cmult(Z1[i,j],Z2[i,j],za,zb);
          Z2[i,j]:=Imag;
        END;
      END;
    END;
    {ResoluáÑo do sistema de equaáîes}
    da:=1.0; db:=0;
    FOR i:=1 TO linhas DO BEGIN
      ta:=0; tb:=0; u:=i;
      FOR k:=i TO linhas DO
        IF Abs(Z1[k,i])+Abs(Z2[k,i])>Abs(ta)+Abs(tb) THEN BEGIN
          u:=k; ta:=Z1[k,i]; tb:=Z2[k,i]
        END;
      IF i<>u THEN BEGIN
        da:=-da; db:=-db;
        FOR k:=i TO colunas DO BEGIN
          d:=Z1[i,k]; Z1[i,k]:=Z1[u,k]; Z1[u,k]:=d;
          d:=Z2[i,k]; Z2[i,k]:=Z2[u,k]; Z2[u,k]:=d;
        END;
      END;
      d:=da*ta-db*tb;
      db:=da*tb+db*ta;
      da:=d;
      FOR j:=colunas DOWNTO i+1 DO BEGIN
        d:=ta*ta+tb*tb;
        IF Abs(d)<1E-20 THEN Interromper(
          'Solution impossible. Some possible causes:'#13#10+
          '[-] Floating subcircuit in some phase (add switches).'#13#10+
          '[-] Analysis in a natural frequency (change circle radius)',TRUE);
        t:=(Z1[i,j]*ta+Z2[i,j]*tb)/d;
        pb:=(Z2[i,j]*ta-Z1[i,j]*tb)/d; Z2[i,j]:=pb;
        pa:=t; Z1[i,j]:=t;
        FOR k:=1 TO linhas DO
          IF i<>k THEN BEGIN
            Z1[k,j]:=Z1[k,j]-(Z1[k,i]*pa-Z2[k,i]*pb);
            Z2[k,j]:=Z2[k,j]-(Z1[k,i]*pb+Z2[k,i]*pa);
          END;
      END;
    END;
    {Guardar denominadores}
    {CorreáÑo para que o denominador possua potàncias inteiras de Z}
    t:=Frac(linhas/fases);
    IF t<>0 THEN t:=1-t; {Potencia de Z que corrige}
    r1:=Ex(raio,t);
    da:=Cmult(da,db,r1*Cos(z*t),r1*Sin(z*t));
    db:=Imag;
    D1[h]:=da; D2[h]:=db;
    {Guardar os numeradores}
    {Os das fases i/i estao corretos pois as potencias fracionarias se
     cancelam com as do denominador. Os demais devem ser multiplicados
     por z^t, como abaixo}
    FOR b:=1 TO fases DO {entradas}
      FOR a:=1 TO fases DO BEGIN {sa°das}
        IF a<>b THEN BEGIN
          t:=-((b-a+fases) mod fases)/fases;
          r1:=Ex(raio,t);
          ta:=r1*Cos(z*t); tb:=r1*Sin(z*t);
        END;
        FOR i:=L1[a] TO L2[a] DO BEGIN {subvetores}
          pa:=Cmult(Z1[i,linhas+b],Z2[i,linhas+b],da,db); pb:=Imag;
          IF a<>b THEN BEGIN pa:=Cmult(ta,tb,pa,pb); pb:=Imag END;
          k:=(i-1)*fases+b-1;
          E1^[k,h]:=pa;
          E2^[k,h]:=pb;
        END;
      END;
  END;
  WriteLn;
  Dispose(HZ);
END;

FUNCTION Inverso(x:INTEGER):INTEGER;
VAR
  i,u:INTEGER;
BEGIN
  u:=0;
  i:=grau shr 1;
  REPEAT
    IF Odd(x) THEN u:=u+i;
    i:=i shr 1;
    x:=x shr 1
  UNTIL x=0;
  Inverso:=u
END;

PROCEDURE FFT;
VAR
  k1,m,k,j,u:INTEGER;
  x1,y1,t:REAL;
BEGIN
  FOR k:=ordem-1 DOWNTO 0  DO BEGIN
    k1:=1 shl k;
    m:=0;
    REPEAT
      j:=Inverso(m div k1);
      x1:=Cos(2*Pi*j/grau); y1:=-Sin(2*Pi*j/grau);
      FOR j:=0 TO k1-1 DO BEGIN
        u:=j+m; i:=u+k1;
        t:=Cmult(X[i],Y[i],x1,y1);
        X[u]:=X[u]+t; Y[u]:=Y[u]+Imag;
        X[i]:=X[u]-t-t;
        Y[i]:=Y[u]-Imag-Imag
      END;
      m:=m+k1 shl 1
    UNTIL m>grau-1
  END;
  FOR i:=0 TO grau-1 DO BEGIN
    j:=Inverso(i);
    IF j>i THEN BEGIN
      x1:=X[i]; X[i]:=X[j]; X[j]:=x1
    END
  END;
  FOR i:=0 TO grau-1 DO X[i]:=X[i]/grau;
END; {FFT}

PROCEDURE Limpar(pol:ptr_longo);
BEGIN
  WITH pol^ DO BEGIN
    t:=0;
    FOR i:=0 TO n DO
      IF Abs(cf[i])>t THEN t:=Abs(cf[i]);
    t:=t/dispersao;
    IF t=0 THEN n:=0
    ELSE BEGIN
      WHILE Abs(cf[n])<t DO n:=n-1;
      FOR i:=0 TO n DO
        IF Abs(cf[i])<t THEN cf[i]:=0
    END
  END
END;

FUNCTION Expoente(n,d:INTEGER):STRING;
VAR i,f:INTEGER;
  BEGIN
    i:=n div d; f:=n mod d;
    IF (i>0) and (f>0) THEN txt:=Si(i)+' '+Si(f)+'/'+Si(d)
    ELSE IF (i=0) and (f>0) THEN txt:=Si(f)+'/'+Si(d)
      ELSE IF f=0 THEN txt:=Si(i)
        ELSE txt:='0';
    WHILE Length(txt)<8 DO txt:=txt+' ';
    Expoente:=txt;
  END;

PROCEDURE PrepararNumerador(VAR pol:polinomio_longo);
BEGIN
  WITH pol DO BEGIN
    n:=(grau-1)*fases;
    FOR i:=0 TO grau*fases-1 DO cf[i]:=0;
  END
END;

PROCEDURE Listar(Pol:ptr_longo; tt:STRING; tipo:tipodepolinomio; completo:BOOLEAN);
VAR
  Poll:polinomio_longo;
BEGIN
  titulo:=tt;
  IF tipo<numfase THEN WITH Pol^ DO BEGIN
    PrepararNumerador(Poll);
    FOR i:=0 TO n DO
      Poll.cf[i*fases+minpot]:=cf[i];
    Poll.n:=n*fases+minpot;
    Limpar(@Poll);
  END
  ELSE Poll:=Pol^;
  WITH Poll DO BEGIN
    Write(tl,#10'[',titulo,']:',' ':12-Length(titulo));
    IF (n=0) and (cf[0]=0) THEN WriteLn(tl,'[Zero]')
    ELSE BEGIN
      IF tipo<>denominador THEN WriteLn(tl,'[Cst]:',cf[n]:dig+10:dec)
      ELSE WriteLn;
      j:=0;
      FOR i:=0 TO n DO
        IF (cf[i]<>0) or completo THEN BEGIN
          WriteLn(tl,' ':13,'z^([',Expoente(i,fases),']): ',cf[i]/cf[n]:dig:dec);
          Inc(j);
          IF (j=20) and (i<>n) THEN BEGIN Write('More...'#13); j:=0; ch:=ReadKey END
        END
    END;
    REPEAT
      Write(tl,#10'[R]oots ');
      IF tipo<>denominador THEN Write(tl,'[F]requency response, [T]ransient esponse, ');
      WriteLn(tl,'[C]ontinue');
      REPEAT ch:=UpCase(ReadKey) UNTIL (ch in ['R','C']) or (tipo<>denominador) and (ch in ['F','T']);
      CASE ch OF
        'R':IF tipo=denominador THEN Biv(@Pol^,Polos,tipo)
            ELSE IF tipo=numparcial THEN Biv(@Pol^,Zeros,tipo)
            ELSE Biv(@Poll,Zeros,tipo);
        'F':PlotarModuloFase(Poll);
        'T':PlotarTempo(Poll,tipo);
        'C':Exit;
      END
    UNTIL FALSE
  END
END;

PROCEDURE Apresentar;
BEGIN
  REPEAT
    WriteLn(tl,#10'[D]enominator [N]umerator [C]ontinue');
    REPEAT ch:=UpKey UNTIL ch in ['D','N','C'];
    CASE ch OF
      'D':Listar(@Den,'Denominator',denominador,FALSE);
      'N':BEGIN
            WriteLn(tl,#10'[P]artial p[H]ase [G]lobal [C]ontinue');
            REPEAT ch:=UpKey UNTIL ch in ['P','H','G','C'];
            CASE ch OF
              'P':FOR a:=1 TO fases DO
                    FOR b:=1 TO fases DO
                      Listar(@NumP[a,b]^,'T('+Si(ns)+','+Si(a)+','+Si(b)+')',numparcial,FALSE);
              'H':FOR a:=1 TO fases DO Listar(@NumF[a]^,'T('+Si(ns)+','+Si(a)+')',numfase,FALSE);
              'G':Listar(@NumG,'T('+Si(ns)+')',numglobal,TRUE);
            END
          END;
      'C':Exit
    END
  UNTIL FALSE
END;

PROCEDURE Salvar_polinomio(pol:ptr_longo; tipo:tipodepolinomio; titulo:STRING; completo:BOOLEAN);
BEGIN
  WITH pol^ DO BEGIN
    IF tipo<>denominador THEN titulo:='Numerator of '+titulo;
    Write(saida,#13#10,titulo,': ');
    IF (n=0) and (cf[0]=0) THEN Write(saida,'Zero')
    ELSE BEGIN
      IF tipo<>denominador THEN WriteLn(saida,'Cst: ',cf[n]:dig:dec)
      ELSE WriteLn(saida);
      j:=0;
      FOR i:=0 TO n DO
        IF completo or (cf[i]<>0) THEN BEGIN
          IF tipo<numfase THEN k:=i*fases+minpot ELSE k:=i;
          Write(saida,cf[i]/cf[n]:dig:dec,' z^(',Expoente(k,fases),')');
          IF Odd(j) and (i<>n) THEN WriteLn(saida);
          Inc(j)
        END
    END
  END;
  WriteLn(saida);
END;

PROCEDURE CalcularDenominador;
BEGIN
  WriteLn(tl,#10']Computing denominator...');
  FOR i:=0 TO grau div 2 DO BEGIN
    h:=(grau-i);
    X[i]:=D1[i]; X[h]:=D1[i];
    Y[i]:=D2[i]; Y[h]:=-D2[i];
  END;
  FFT;
  WITH Den DO BEGIN
    FOR i:=0 TO grau-1 DO cf[i]:=X[i]/Ex(raio,i);
    n:=grau-1;
    Limpar(@Den);
    cted:=cf[n];
    FOR i:=0 TO n DO cf[i]:=cf[i]/cted;
    minpot:=0;
  END;
  IF relatorio THEN Salvar_polinomio(@Den,denominador,'Denominator',TRUE);
END;

PROCEDURE CalcularNumeradores;
VAR
  outra:BOOLEAN;
BEGIN
  ns:=1; outra:=TRUE;
  REPEAT
    Write(#10'Output node'); LerInt(ns);
    IF (ns<=nos) and (ns>0) THEN BEGIN
      WriteLn(#10'Computing partial numerators...');
      IF relatorio THEN WriteLn(saida,#13#10'Output node: ',ns);
      FOR a:=1 TO fases DO BEGIN
        Write(tl,'Output in phase [',a,']...[');
        FOR b:=1 TO fases DO WITH NumP[a,b]^ DO
          BEGIN n:=0; cf[0]:=0; minpot:=(b-a+fases) mod fases END;
        a2:=C[ns+nos*(a-1)];
        IF a2=0 THEN Write('connection to ground')
        ELSE IF a2=-1 THEN BEGIN
          Write('connection to the input');
          NumP[a,a]^:=Den
        END
        ELSE {NÑo aterrado}
          FOR b:=1 TO fases DO BEGIN
            Write('N(',a,',',b,') ');
            FOR i:=0 TO grau div 2 DO BEGIN
              h:=grau-i; j:=(a2-1)*fases+b-1;
              X[h]:=E1^[j,i]; X[i]:=E1^[j,i];
              Y[h]:=-E2^[j,i]; Y[i]:=E2^[j,i];
            END;
            FFT;
            FOR i:=0 TO grau-1 DO NumP[a,b]^.cf[i]:=X[i]/(Ex(raio,i)*cted);
            NumP[a,b]^.n:=grau-1;
            Limpar(@NumP[a,b]^);
            IF relatorio and parciais THEN Salvar_polinomio(@NumP[a,b]^,numparcial,'T('+Si(ns)+','+Si(a)+','+Si(b)+')',FALSE);
          END;
        WriteLn(tl,']');
      END;
      Write(tl,'Computing phase and global numerators...[');
      PrepararNumerador(NumG);
      FOR a:=1 TO fases DO BEGIN
        Write('N(',a,') ');
        PrepararNumerador(NumF[a]^);
        FOR b:=1 TO fases DO WITH NumP[a,b]^ DO
          FOR i:=0 TO n DO BEGIN
            j:=minpot+i*fases;
            NumF[a]^.cf[j]:=NumF[a]^.cf[j]+NumP[a,b]^.cf[i];
            NumG.cf[j]:=NumG.cf[j]+NumP[a,b]^.cf[i]
          END;
        Limpar(@NumF[a]^);
        IF relatorio and dasfases THEN Salvar_polinomio(@NumF[a]^,numfase,'T('+Si(ns)+','+Si(a)+')',FALSE);
      END;
      WriteLn(tl,']');
      Limpar(@NumG);
      IF relatorio THEN Salvar_polinomio(@NumG,numglobal,'T('+Si(ns)+')',TRUE);
      Apresentar
    END
    ELSE WriteLn(tl,#10'[*] Invalid node.');
    Write(tl,#10'Another output node'); LerBool(outra);
  UNTIL not outra;
END;

PROCEDURE Encerrar;
BEGIN
  FOR a:=fases DOWNTO 1 DO Dispose(NumF[a]);
  FOR a:=fases DOWNTO 1 DO FOR b:=fases DOWNTO 1 DO Dispose(NumP[a,b]);
  ok:=FALSE;
  Write(#10'Another analysis'); LerBooL(ok);
  IF relatorio THEN BEGIN
  WriteLn(saida,#13#10'End of analysis.'); Close(saida) END;
END;

BEGIN
  InicializarParametros;
  REPEAT
    Inicializar;
    LerDescricao;
    ReduzirSistema;
    AvaliarSistema;
    CalcularDenominador;
    CalcularNumeradores;
    Encerrar;
  UNTIL not ok
END.

