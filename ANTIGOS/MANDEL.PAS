USES Crt,Graph3,Sprites;

CONST x0=45;
      y0=45;
      xm=145;
      ym=145;
      d0=100;

TYPE dados=RECORD
           contagem:ARRAY[x0..xm,y0..ym] of BYTE;
           calcular:ARRAY[x0..xm] of BOOLEAN;
           x1,x2,y1,y2:REAL;
           iter:INTEGER
           END;

VAR xc,yc,xc0,yc0,t1,t2,ax,bx,ay,by:REAL;
    x,y,d:INTEGER;
    c:CHAR;
    fator,i,cor:BYTE;
    mudou:BOOLEAN;
    desenho:dados;
    arquivo:FILE of dados;
    nome:STRING[20];

LABEL Inicio;

PROCEDURE Escalar;
   BEGIN
   WITH desenho DO
      BEGIN
      ax:=(x2-x1)/(xm-x0);
      bx:=x1-ax*x0;
      ay:=(y1-y2)/(ym-y0);
      by:=y2-ay*y0
      END
   END;

PROCEDURE Preparar;
   BEGIN
   FOR x:=x0 TO xm DO desenho.calcular[x]:=TRUE
   END;

PROCEDURE Desenhar;
   BEGIN
   WITH desenho DO
      BEGIN
      GoToXY(1,1);
      WriteLn(' x:',x1:13:8,' a',x2:13:8);
      WriteLn(' y:',y1:13:8,' a',y2:13:8);
      WriteLn(' No. maximo de iteracoes: ',iter);
      WriteLn(' Fator para coloracao: ',fator);
      FOR x:=x0 TO xm DO
         BEGIN
         xc0:=ax*x+bx;
         FOR y:=y0 TO ym DO
            BEGIN
            IF calcular[x] THEN
               BEGIN
               yc0:=ay*y+by;
               xc:=xc0;
               yc:=yc0;
               i:=0;
               REPEAT
                  t1:=xc*xc;
                  t2:=yc*yc;
                  yc:=2*xc*yc+yc0;
                  xc:=t1-t2+xc0;
                  i:=i+1
               UNTIL (i=iter) or (t1+t2>4);
               contagem[x,y]:=i;
               END;
            cor:=contagem[x,y] div fator mod 4;
            Plot(x,y,cor);
            END;
         Calcular[x]:=FALSE;
         IF KeyPressed THEN Exit
         END
      END
   END;

PROCEDURE Inicializar;
   BEGIN
   ClrScr;
   WriteLn('Graficos do conjunto de MandelBrot');
   WriteLn('----------------------------------');
   WriteLn('Por ACMQ');
   WriteLn;
   WriteLn('Carregar desenho de arquivo? (s/n)');
   c:=ReadKey;
   IF UpCase(c)='S' THEN
      BEGIN
      Write('Nome do arquivo: '); ReadLn(nome);
      Assign(arquivo,nome);
      Reset(arquivo);
      Read(arquivo,desenho)
      END
   ELSE WITH desenho DO
      BEGIN
      x1:=-2.00; x2:=0.5;
      y1:=-1.25; y2:=1.25;
      Write('x minimo maximo: '); ReadLn(x1,x2);
      Write('y minimo maximo: '); ReadLn(y1,y2);
      Write('Maximo numero de iteracoes: '); ReadLn(iter);
      Preparar;
      END;
   Write('Fator para coloracao: '); ReadLn(fator);
   Escalar
   END;

BEGIN
Inicio:
Inicializar;
REPEAT
   GraphColorMode; ColorTable(3,2,1,0); TextColor(3); Palette(3);
   SpriteMode;
   Sprite(0,#255#128#128#128#128#128#128#128);
   Sprite(1,#1#1#1#1#1#1#1#255);
   Square(x0-1,y0-1,xm+1,ym+1,3);
   Desenhar;
   GoToXY(2,22); Write('Marcar: [setas, <>]; [S]alvar; [M]udar');
   GoToXY(2,23); Write('[R]ecomecar; [T]erminar');
   x:=x0; y:=y0; d:=d0;
   mudou:=FALSE;
   REPEAT
      c:=UpCase(ReadKey);
      CASE c OF
         #0:CASE ReadKey OF
               'M':IF x+d<xm THEN x:=x+1;
               'K':IF x>x0 THEN x:=x-1;
               'H':IF y>y0 THEN y:=y-1;
               'P':IF y+d<ym THEN y:=y+1;
            END;
         '>','.':IF (x+d<xm) and (y+d<ym) THEN d:=d+1;
         '<',',':IF d>8 THEN d:=d-1;
         'M':BEGIN
             GoToXY(1,1); ClrEolG; Write(' Novo No. maximo de iteracoes: '); ReadLn(desenho.iter);
             ClrEolG; Write(' Novo fator para coloracao: '); Read(fator)
             END;
         'S':BEGIN
             GoToXY(1,1);
             ClrEolG; Write(' Arquivo onde salvar: ');
             ReadLn(nome);
             Assign(arquivo,nome);
             ReWrite(arquivo);
             Write(arquivo,desenho);
             Close(arquivo);
             ClrEolG; Write(' Desenho salvo');
             END
         END;
      IF c in [#0,'>','<',',','.'] THEN
         BEGIN
         mudou:=TRUE;
         PutSprite(0,x,y);
         PutSprite(1,x+d-7,y+d-7)
         END
   UNTIL c in ['T','R','M',' ',#13];
   IF mudou THEN
      WITH desenho DO
         BEGIN
         x1:=ax*x+bx;
         x2:=ax*(x+d)+bx;
         y1:=ay*(y+d)+by;
         y2:=ay*y+by;
         Preparar;
         Escalar
         END
UNTIL (c='T') or (c='R');
TextMode(80);
IF c='R' THEN GoTo Inicio
END.