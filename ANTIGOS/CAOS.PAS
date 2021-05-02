USES Graph,Tela,Crt,Dos;

VAR
  xini,x,r,minr,maxr,minx,maxx,ax,bx,ay,by:REAL;
  placa,modo,xmin,xmax,ymin,ymax,i,j,espera,pontos:INTEGER;
  c:CHAR;
  grade:BOOLEAN;

LABEL
  repetir;

  PROCEDURE InicializarGrafico(x1,x2,y1,y2:REAL; xlog:BOOLEAN);
  VAR
    t1,t2:REAL;
    txt:STRING;
  BEGIN
    placa:=detect;
    InitGraph(placa,modo,GetEnv('TPBGI'));
    xmin:=TextWidth('x.xxxx'); xmax:=GetMaxX;
    ymin:=0; ymax:=GetMaxY-TextHeight('X')-1;
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
      SetColor(2);
      IF xlog and (x2-x1>x1) THEN t1:=x1
      ELSE t1:=x2-x1;
      t1:=Exp(Ln(10)*Round(Ln(t1)/Ln(10)-0.499999));
      t2:=Round(x1/t1+0.5)*t1;
      WHILE t2<x2 DO
        IF xlog THEN BEGIN
          IF Round(t2/t1)=10 THEN BEGIN
            t1:=10*t1;
	    SetColor(1);
          END;
          i:=Round(ax*Ln(t2)+bx);
          Line(i,ymin,i,ymax);
          t2:=t2+t1;
	  SetColor(2);
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
    SetColor(1);
    Rectangle(xmin,ymin,xmax,ymax);
    Str(y2:6:4,txt); OutTextXY(0,ymin,txt);
    Str(y1:6:4,txt); OutTextXY(0,ymax-TextHeight(txt),txt);
    Str(x2:6:4,txt); OutTextXY(xmax-TextWidth(txt),ymax+1,txt);
    Str(x1:6:4,txt); OutTextXY(xmin,ymax+1,txt);
  END;

BEGIN
  minr:=3.4; maxr:=4; xini:=0.3;
  espera:=10; pontos:=30;
  minx:=0; maxx:=1; grade:=TRUE;
  ClrScr;
  WriteLn('Caos na equa‡„o x(n+1)=r*x(n)*(1-x(n))');
  WriteLn('--------------------------------------');
  WriteLn;
  WriteLn('Para r>3.56994571869 x(i) nunca se  re-');
  WriteLn('pete, resultando em um sistema ca¢tico.');
  WriteLn;
  WriteLn('ACMQ - 14/2/90');
  WriteLn;
  repetir:
  Write('Usar grade'); LerBool(grade);
  Write('Minimo r'); LerReal(minr);
  Write('M ximo r'); LerReal(maxr);
  Write('M¡nimo x'); LerReal(minx);
  Write('M ximo x'); LerReal(maxx);
  Write('Itera‡”es de espera'); LerInt(espera);
  Write('Itera‡”es plotadas'); LerInt(pontos);
  InicializarGrafico(minx,maxx,minr,maxr,FALSE);
  x:=xini;
  FOR j:=ymax DOWNTO ymin DO BEGIN
    r:=(j-by)/ay;
    FOR i:=1 TO espera DO x:=r*x*(1-x);
    FOR i:=1 TO pontos DO BEGIN
      x:=r*x*(1-x);
      PutPixel(Round(ax*x+bx),j,3)
    END;
    IF KeyPressed THEN BEGIN TextMode(80); GoTo repetir END
  END;
  c:=ReadKey;
  TextMode(80);
  GoTo repetir
END.
