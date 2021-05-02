PROGRAM Lissajous;

USES Graph,Crt;

VAR
  placa,modo,xmin,xmax,ymin,ymax,x,y:INTEGER;
  wx,wy,wr,ax,bx,ay,by,x1,y1,x2,y2,delta,teta,alfa,sinalfa,cosalfa,wmax,fator:REAL;
  xasp,yasp:WORD;
  plotar:BOOLEAN;
  ch:CHAR;
  txt:STRING;

BEGIN
REPEAT
  TextMode(80);
  WriteLn('Figuras de Lissajous girat¢rias');
  WriteLn('-------------------------------');
  WriteLn('ACMQ - 29/12/89');
  WriteLn;
  WriteLn('Entre a propor‡„o entre as freqˆncias horizontal, vertical e de rota‡„o');
  Write('(Por exemplo: "1 1 1"): ');
  ReadLn(wx,wy,wr);
  placa:=detect;
  InitGraph(placa,modo,'');
  MoveTo(0,0);
  Str(wx:4:2,txt); OutText(txt);
  Str(wy:4:2,txt); OutText(','+txt);
  Str(wr:4:2,txt); OutText(','+txt);
  wy:=wy/wx; wr:=wr/wx;
  wmax:=1;
  IF wy>wmax THEN wmax:=wy;
  IF wr>wmax THEN wmax:=wr;
  GetAspectRatio(xasp,yasp); fator:=yasp/xasp;
  xmin:=0; xmax:=GetMaxX;
  ymin:=0; ymax:=GetMaxY;
  y1:=-Sqrt(2); y2:=-y1;
  ay:=(ymax-ymin)/(y1-y2);
  by:=ymax-ay*y1;
  ax:=-ay*fator;
  bx:=(xmin+xmax)/2;
  x2:=(xmax-bx)/ax; x1:=-x2;
  delta:=Pi/20/wmax; teta:=0;
  plotar:=FALSE;
  REPEAT
    x1:=Sin(teta);
    y1:=Sin(wy*teta);
    alfa:=wr*teta;
    cosalfa:=Cos(alfa);
    sinalfa:=Sin(alfa);
    x2:=x1*cosalfa-y1*sinalfa;
    y2:=y1*cosalfa+x1*sinalfa;
    x:=Round(bx+ax*x2);
    y:=Round(by+ay*y2);
    IF plotar THEN LineTo(x,y) ELSE BEGIN
      plotar:=TRUE;
      MoveTo(x,y);
    END;
    teta:=teta+delta;
  UNTIL KeyPressed;
  ch:=ReadKey;
UNTIL ch=#27;
END.

