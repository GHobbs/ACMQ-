{Plotador de Gr ficos Tridimensionais}

USES Crt,Graph,Dos;

CONST
  placa:INTEGER=0;
  modo:INTEGER=0;
  max=50;
  versao='1.1 de 08/04/89';

TYPE
  g3d=ARRAY[-max..max,-max..max] OF REAL;

VAR
  ponto:g3d;
  xmin,xmax,ymin,ymax:INTEGER;
  zmin,zmax:REAL;

PROCEDURE LerPontos;
VAR
  t:REAL;
  i,j:INTEGER;
  arquivo:TEXT;
  nome:STRING;

BEGIN
  ClrScr;
  IF ParamCount=0 THEN BEGIN
    WriteLn('Plotador de gr ficos tridimensionais');
    WriteLn('------------------------------------');
    WriteLn('ACMQ - Vers„o ',versao);
    WriteLn;
    WriteLn('Formato do arquivo de entrada:');
    WriteLn('1a. linha: Xm¡nimo Ym¡nimo Xm ximo Ym ximo (inteiros) Zm¡nimo Zm ximo (reais)');
    WriteLn('Linhas seguintes:');
    WriteLn('Para X de Xm¡nimo at‚ Xm ximo,');
    WriteLn('   Para Y de Ym¡nimo at‚ Ym ximo,');
    WriteLn('      Valor de Z(X,Y), em qualquer formato.');
    WriteLn('Obs: X e Y entre -50 e +50, no m ximo.');
    WriteLn('     O nome do arquivo de entrada pode ser passado na linha de comando.');
    WriteLn;
    WriteLn('Comandos aceitos:');
    WriteLn('Setas horizontais: Mudar ƒngulo de rota‡„o horizontal (0 a 90 graus)');
    WriteLn('Setas verticais:   Mudar ƒngulo de rota‡„o vertical (0 a 180 graus)');
    WriteLn('Page Up/Down: Deslocar para cima/para baixo');
    WriteLn('Home/End: Ampliar/Reduzir Z');
    WriteLn('+/-: Ampliar/Reduzir o desenho todo');
    WriteLn('Espa‡o: Ativar cursor (mover com as setas)');
    WriteLn('Return: Desativar cursor');
    WriteLn('Escape: Terminar');
    WriteLn;
    Write('Arquivo com os pontos: ');
    ReadLn(nome)
  END
  ELSE nome:=ParamStr(1);
  Assign(arquivo,nome);
  {$I-} Reset(arquivo); {$I+}
  IF not IOResult=0 THEN BEGIN
    WriteLn('* Arquivo ',nome,' inexistente *');
    Halt
  END;
  WriteLn('Lendo arquivo ',nome,'...');
  ReadLn(arquivo,xmin,ymin,xmax,ymax,zmin,zmax);
  FOR i:=xmin TO xmax DO
    FOR j:=ymin TO ymax DO
      Read(arquivo,ponto[i,j]);
  Close(arquivo);
END;

PROCEDURE Grafico3D;
CONST
  seta:ARRAY[1..8] OF PointType=((x:0;y:0),(x:8;y:0),(x:6;y:2),(x:8;y:4),
                                 (x:4;y:8),(x:2;y:6),(x:0;y:8),(x:0;y:0));
VAR
  aspecto,k,t,a1,a2,a,bx,cx,dx,by,cy,dy,ey:REAL;
  xcursor,ycursor,xcentro0,ycentro0,cor,
  xcentro,ycentro,xc,yc,xt,yt,xant:INTEGER;
  r:CHAR;
  fim:BOOLEAN;
  cursor:POINTER;
  tamanho:WORD;
  texto:STRING;

PROCEDURE Inicializar;
BEGIN
  InitGraph(placa,modo,GetEnv('TPBGI'));
  xcentro0:=GetMaxX div 2;
  ycentro0:=GetMaxY div 2;
  aspecto:=GetMaxX/GetMaxY;
  a1:=30;
  a2:=60;
  IF Abs(ymax-ymin)>Abs(xmax-xmin) THEN a:=ymax-ymin ELSE a:=xmax-xmin;
  k:=a/(zmax-zmin);
  a:=GetMaxY/1.5/a;
  xcentro:=xcentro0;
  ycentro:=ycentro0;
  cor:=GetMaxColor;
  SetFillStyle(solidfill,cor-1);
  FillPoly(SizeOf(seta) div SizeOf(PointType),seta);
  tamanho:=ImageSize(0,0,10,10);
  GetMem(cursor,tamanho);
  GetImage(0,0,10,10,cursor^);
  SetFillStyle(emptyfill,cor);
  fim:=FALSE;
END {Inicializar};

PROCEDURE Plotar;
VAR
  ulinhax,ulinhay:ARRAY[-max..max] OF INTEGER;
  pixelalto,pixelbaixo:ARRAY[-500..2000] OF INTEGER;
  acima,abaixo:BOOLEAN;
  i,j:INTEGER;

LABEL
  Testar,Continuar;

PROCEDURE PutSprite(x,y:INTEGER);
BEGIN
  PutImage(xcursor,ycursor,cursor^,XORput);
  xcursor:=x;
  ycursor:=y;
  PutImage(xcursor,ycursor,cursor^,XORput);
END;

PROCEDURE Projetar(x,y:INTEGER; z:REAL);
BEGIN
  xt:=Round(bx-cx*x-dx*y);
  yt:=Round(by-cy*x-dy*y+ey*z);
END;

PROCEDURE Plot2(x,y:INTEGER);
BEGIN
  acima:=y>pixelalto[x];
  abaixo:=y<pixelbaixo[x];
  IF acima or abaixo or (x=xant) THEN BEGIN  {Linhas verticais at‚ o fim}
    PutPixel(x,y,cor);
    IF acima THEN pixelalto[x]:=y;
    IF abaixo THEN pixelbaixo[x]:=y;
    xant:=x;
  END
END;

PROCEDURE Draw2(x1,y1,x2,y2:INTEGER);
VAR
  x,y,d:INTEGER;
  tg:REAL;
BEGIN
  xant:=-100;
  IF (x1=x2) and (y1=y2) THEN Plot2(x1,y1)
  ELSE
  IF Abs(x2-x1)>Abs(y2-y1) THEN BEGIN
    tg:=(y2-y1)/(x2-x1);
    IF x2>x1 THEN d:=1 ELSE d:=-1;
    x:=x1;
    WHILE x<>x2 DO BEGIN
      y:=Round((x-x1)*tg+y1); {Fica melhor com Round}
      Plot2(x,y);
      x:=x+d;
    END;
  END
  ELSE BEGIN
    tg:=(x2-x1)/(y2-y1);
    IF y2>y1 THEN d:=1 ELSE d:=-1;
    x:=y1;
    WHILE x<>y2 DO BEGIN
      y:=Trunc((x-y1)*tg+x1); {Aqui tem que ser Trunc}
      Plot2(y,x);
      x:=x+d;
    END;
  END
END {Draw2};

PROCEDURE Medir;
VAR
  temp:STRING;
BEGIN
  REPEAT
    Projetar(xc,yc,ponto[xc,yc]);
    PutSprite(xt,yt);
    Str(xc:3,temp);
    texto:='x:'+temp;
    Str(yc:3,temp);
    texto:=texto+' y:'+temp;
    Str(ponto[xc,yc]:8:4,temp);
    texto:=texto+' z:'+temp;
    Bar(3,GetMaxY-9,200,GetMaxY-1);
    OutTextXY(3,GetMaxY-9,texto);
    r:=ReadKey;
    IF r=#0 THEN
      CASE ReadKey OF
        'P':IF yc<ymax THEN yc:=yc+1;
        'H':IF yc>ymin THEN yc:=yc-1;
        'K':IF xc<xmax THEN xc:=xc+1;
        'M':IF xc>i    THEN xc:=xc-1;
      END;
  UNTIL r=#13;
  PutSprite(-10,-10);
  Bar(3,GetMaxY-9,200,GetMaxY-1);
END {Medir};

PROCEDURE CalcularConstantes;
VAR
  t,aa1,aa2:REAL;
  i:INTEGER;
BEGIN
  aa1:=a1*Pi/180;
  aa2:=a2*Pi/180;
  cx:=a*aspecto*Cos(aa1);
  dx:=-a*aspecto*Sin(aa1);
  cy:=-a*Sin(aa1)*Cos(aa2);
  dy:=-a*Cos(aa1)*Cos(aa2);
  ey:=-a*k*Sin(aa2);
  bx:=0; by:=0;
  Projetar((xmax+xmin) div 2,(ymax+ymin) div 2,(zmax+zmin)/2);
  bx:=xcentro-xt;
  by:=ycentro-yt;
  xc:=xmax;
  yc:=ymax;
  xcursor:=-10;
  ycursor:=-10;
  FOR i:=0 TO GetMaxX DO BEGIN
    pixelalto[i]:=-1000;
    pixelbaixo[i]:=1000;
  END;
END {CalcularConstantes};

PROCEDURE Cubo;
VAR
  x1,y1,x2,y2,x3,y3,x4,y4,x5,y5,x6,y6,x7,y7,x8,y8:INTEGER;
BEGIN
Projetar(xmin,ymin,zmin); x1:=xt; y1:=yt;
Projetar(xmin,ymax,zmin); x2:=xt; y2:=yt;
Projetar(xmax,ymax,zmin); x3:=xt; y3:=yt;
Projetar(xmax,ymin,zmin); x4:=xt; y4:=yt;
Projetar(xmin,ymin,zmax); x5:=xt; y5:=yt;
Projetar(xmin,ymax,zmax); x6:=xt; y6:=yt;
Projetar(xmax,ymax,zmax); x7:=xt; y7:=yt;
Projetar(xmax,ymin,zmax); x8:=xt; y8:=yt;
SetColor(GetMaxColor-2);
MoveTo(x1,y1);
LineTo(x2,y2);
LineTo(x3,y3);
LineTo(x4,y4);
LineTo(x1,y1);
LineTo(x5,y5);
LineTo(x6,y6);
LineTo(x2,y2);
MoveTo(x5,y5);
LineTo(x8,y8);
LineTo(x4,y4);
SetColor(GetMaxColor);
END;

BEGIN
  REPEAT
    CalcularConstantes;
    ClearDevice;
    Rectangle(0,0,GetMaxX,GetMaxY);
    Str(a1:5:1,texto);
    OutTextXY(3,2,'H: '+texto);
    Str(a2:5:1,texto);
    OutTextXY(3,10,'V: '+texto);
    OutTextXY(3,GetMaxY-9,GetModeName(modo));
    Cubo;
    FOR i:=xmax DOWNTO xmin DO BEGIN
      FOR j:=ymax DOWNTO ymin DO BEGIN
        Projetar(i,j,ponto[i,j]);
        IF i<>xmax THEN Draw2(ulinhax[j],ulinhay[j],xt,yt);
        IF j<>ymax THEN Draw2(ulinhax[j+1],ulinhay[j+1],xt,yt);
        ulinhax[j]:=xt;
        ulinhay[j]:=yt;
      END;
      IF KeyPressed THEN GoTo Testar;
     Continuar:
    END;
   Testar:
    CASE ReadKey OF
      #0:CASE ReadKey OF
           'H':IF a2<180 THEN a2:=a2+10;
           'P':IF a2>0 THEN a2:=a2-10;
           'K':IF a1<90 THEN a1:=a1+10;
           'M':IF a1>0 THEN a1:=a1-10;
           #81:ycentro:=ycentro+20;
           #73:ycentro:=ycentro-20;
           #71:k:=k*Sqrt(2);
           #79:k:=k/Sqrt(2);
           ELSE IF i<>xmin THEN GoTo Continuar ELSE GoTo Testar
          END;
      '-':a:=a/Sqrt(2);
      '+':a:=a*Sqrt(2);
      #27:fim:=TRUE;
      ' ':BEGIN
            Medir;
            IF i<>xmin THEN GoTo Continuar ELSE GoTo Testar
          END;
      ELSE IF i<>xmin THEN GoTo Continuar ELSE GoTo Testar
    END
  UNTIL fim
END {Plotar};

PROCEDURE Encerrar;
BEGIN
  FreeMem(cursor,tamanho);
  CloseGraph
END;

BEGIN
  Inicializar;
  Plotar;
  Encerrar;
END {Grafico3D};

BEGIN
  LerPontos;
  Grafico3D;
END.
