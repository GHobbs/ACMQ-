PROGRAM Desvio;
{$I graph.p}
CONST
  xmin=0;
  xmax=319;
  ymin=0;
  ymax=199;
  maxerros=40;
VAR
  n,d,i,j,somas:INTEGER;
  Vr,Vi:ARRAY[1..maxerros] of REAL;
  fim:BOOLEAN;
  emax,rmin,rmax,imin,imax:REAL;
  ax,bx,ay,by,fator:REAL;
  r:CHAR;
  alea:BOOLEAN;

FUNCTION Normal:REAL;
VAR
  i:INTEGER;
  t:REAL;
BEGIN
  { ((R1+...+Rn)/n+0.5)*(1/3)/(1/Sqrt(12*n)) para 3å=1 e media 0 }
  t:=0;
  FOR i:=1 TO somas DO t:=t+Random;
  Normal:=(t/somas-0.5)*fator;
END;

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

FUNCTION X(re:REAL):INTEGER;
BEGIN
  X:=Round(ax*re+bx);
END;

FUNCTION Y(im:REAL):INTEGER;
BEGIN
  Y:=Round(ay*im+by);
END;

PROCEDURE Square(x1,y1,x2,y2,c:INTEGER);
BEGIN
  Draw(x1,y1,x1,y2,c);
  Draw(x1,y2,x2,y2,c);
  Draw(x2,y2,x2,y1,c);
  Draw(x2,y1,x1,y1,c)
END;

PROCEDURE Inicializar;
BEGIN
  ClrScr;
  WriteLn('Teste para desvios estatisticos de polos e zeros');
  WriteLn('ACMQ - Versao 1.0 de 9/11/88');
  WriteLn;
  Randomize;
  fim:=FALSE;
  rmax:=10;
  imax:=10;
  rmin:=-10;
  imin:=-10;
  emax:=5;
  ax:=(xmax-xmin)/(rmax-rmin);
  bx:=xmin-ax*rmin;
  ay:=(ymax-ymin)/(imin-imax);
  by:=ymin-ay*imax;
  n:=3;
  FOR i:=1 TO maxerros DO BEGIN
    Vr[i]:=0;
    Vi[i]:=0;
  END;
  d:=200;
  alea:=TRUE;
  somas:=3;
END;

PROCEDURE GerarErros;
BEGIN
  Write('Numero de vetores a gerar: (',n,') '); ReadLn(n);
  Write('Vetores aleat¢rios?  ');
  IF alea THEN Write('(S) ') ELSE Write('(N) ');
  ReadLn(r);
  IF UpCase(r)='S' THEN alea:=TRUE;
  IF UpCase(r)='N' THEN alea:=FALSE;
  IF not alea THEN
    FOR i:=1 TO n DO BEGIN
      Write('Erro ',i,': (',Vr[i]:5:2,' ',Vi[i]:5:2,') ');
      ReadLn(Vr[i],Vi[i]);
    END
  ELSE BEGIN
    Write('M¢dulo m ximo: (',emax:5:2,') '); ReadLn(emax);
    FOR i:=1 TO n DO BEGIN
      Vr[i]:=(Random-0.5)*2*emax;
      Vi[i]:=(Random-0.5)*2*emax;
    END;
  END;
  Write('Somas de Random na distribui‡„o: (',somas,') ');
  ReadLn(somas);
  fator:=(1/3)/(1/Sqrt(12*somas));
  Write('Numero de erros a simular: (',d,') ');
  ReadLn(d);
END;

PROCEDURE MontarTela;
BEGIN
  GraphColorMode; Palette(3); TextColor(3);
  Square(xmin,ymin,xmax,ymax,3);
  Draw(xmin,Y(0),xmax,Y(0),2);
  Draw(X(0),ymin,X(0),ymax,2);
END;

PROCEDURE PlotarErros;
BEGIN
  FOR i:=1 TO n DO Draw(X(0),Y(0),X(Vr[i]),Y(Vi[i]),3);
END;

PROCEDURE PlotarPontos;
VAR
  dr,di,v:REAL;
BEGIN
  FOR i:=1 TO d DO BEGIN
    dr:=0; di:=0;
    FOR j:=1 TO n DO BEGIN
      v:=Normal;
      dr:=dr+v*Vr[j];
      di:=di+v*Vi[j];
    END;
    Plot(X(dr),Y(di),3);
  END;
END;

PROCEDURE PlotarDesvios;
VAR
  vx,vy:REAL;
BEGIN
  vx:=0;
  vy:=0;
  FOR i:=1 TO n DO BEGIN
    vx:=vx+Sqr(Vr[i]);
    vy:=vy+Sqr(Vi[i]);
  END;
  vx:=Sqrt(vx);
  vy:=Sqrt(vy);
  Square(X(-vx),Y(-vy),X(vx),Y(vy),2);
END;

PROCEDURE PlotarElipse;
VAR
  t,a,b,cost,sint,r,t0,t1,dt,x1,y1,x2,y2:REAL;
BEGIN
  b:=0; a:=0;
  FOR i:=1 TO n DO BEGIN
    r:=Sqr(Vr[i])+Sqr(Vi[i]);
    t:=Angle(Vr[i],vi[i]);
    t0:=r*Cos(t);
    t1:=r*Sin(t);
    x1:=a+t0;
    y1:=b+t1;
    x2:=a-t0;
    y2:=b-t1;
    IF Sqr(x1)+Sqr(y1)>Sqr(x2)+Sqr(y2) THEN BEGIN
      a:=x1;
      b:=y1;
    END
    ELSE BEGIN
      a:=x2;
      b:=y2;
    END;
  END;
  t:=Angle(a,b);
  cost:=Cos(t);
  sint:=Sin(t);
  a:=0; b:=0;
  FOR i:=1 TO n DO BEGIN
    a:=a+Sqr(Vr[i]*cost+Vi[i]*sint);
    b:=b+Sqr(-Vr[i]*sint+Vi[i]*cost);
  END;
  a:=Sqrt(a);
  b:=Sqrt(b);
  Draw(X(-a*cost),Y(-a*sint),X(a*cost),Y(a*sint),1);
  dt:=pi/40;
  FOR i:=1 TO 81 DO BEGIN
    t0:=i*dt;
    t1:=t0-t;
    r:=a*b*Sqrt(1/(Sqr(a*Sin(t1))+Sqr(b*Cos(t1))));
    x2:=r*Cos(t0);
    y2:=r*Sin(t0);
    IF i>1 THEN Draw(X(x1),Y(y1),X(x2),Y(y2),3);
    x1:=x2;
    y1:=y2;
  END;
  GoToXY(2,22); Write('r maior=',a:6:2);
  GoToXY(2,23); Write('r menor=',b:6:2);
  GoToXY(2,24); Write('angulo= ',t*180/pi:6:2);
END;

PROCEDURE TestarFim;
BEGIN
  Read(Kbd,r);
  IF r=#27 THEN fim:=TRUE;
END;

BEGIN
  Inicializar;
  REPEAT
    GerarErros;
    MontarTela;
    PlotarErros;
    PlotarPontos;
    PlotarDesvios;
    PlotarElipse;
    TestarFim;
    TextMode;
  UNTIL fim;
END.
