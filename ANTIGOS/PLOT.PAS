PROGRAM Plota;

{**************************************
 * Gr fico de uma fun‡„o qualquer     *
 * Ant“nio Carlos M. de Queiroz       *
 * Vers„o 1.4  de 18/07/88            *
 * Vers„o 1.5  de 8/6/90 Turbo 5.5    *
 **************************************}

USES Crt,Graph3;

CONST minx=-2; {Limites iniciais}
      maxx=2;
      miny=-5;
      maxy=5;

{$I sprites.p}

FUNCTION Funcao(w:REAL):REAL;
CONST
   b1=1.07;
   c1=0.334;
   b2=0.825;
   c2=0.756;
   BEGIN
   Funcao:=2*( {b1*(c1+Sqr(w)) / ( Sqr(c1-Sqr(w)) + Sqr(w*b1) ) +}
               b2*(c2+Sqr(w)) / ( Sqr(c2-Sqr(w)) + Sqr(w*b2) ) );
   END; {Funcao}

PROCEDURE Grafico;
   CONST x0=131;
         xm=319;
         x01=127;
         mx1=178;
         mx2=225;
         mx3=272;
         y0=0;
         ym=190;
   VAR x1,y1,x2,y2,ax,bx,ay,by,kk,w,d,a1,a2,b1,b2:REAL;
       j,xg,xa,ya:INTEGER;
       ponto:ARRAY[x0..xm] of REAL;
       calculado:ARRAY[x0..xm] of BOOLEAN;
       r:CHAR;
   LABEL atualizar;

   FUNCTION Limx(x:REAL):INTEGER;
      BEGIN
      x:=ax*x+bx;
      IF x>xm THEN Limx:=xm
      ELSE IF x<x0 THEN Limx:=x0
           ELSE Limx:=Round(x)
      END; {Limx}

   FUNCTION Limy(y:REAL):INTEGER;
      BEGIN
      y:=ay*y+by;
      IF y>ym THEN Limy:=ym
      ELSE IF y<y0 THEN Limy:=y0
           ELSE Limy:=Round(y)
      END; {Limy}

   PROCEDURE Medir;
      VAR db,it:BOOLEAN;
          integral:REAL;
          j:INTEGER;
      BEGIN
      db:=FALSE; it:=FALSE;
      xg:=x0;
      GoToXY(1,14);
      WriteLn('Cur: mover');
      WriteLn('D: y em dB');
      WriteLn('I: integr.');
      WriteLn('Esc: volta');
      Square(0,104,80,135,3);
      REPEAT
      PutSprite(0,xg,Limy(ponto[xg]));
      GoToXY(1,19);
      WriteLn('x:',(xg-bx)/ax:7:4);
      WriteLn('y:',ponto[xg]:7:4);
      IF it THEN WriteLn('I:',integral:8:5) ELSE WriteLn('           ');
      IF db and (ponto[xg]>0) THEN Write(Ln(ponto[xg])*8.685889638:7:4,'dB') ELSE WriteLn('           ');
      r:=UpCase(ReadKey);
      CASE r OF
          #0:BEGIN
             CASE ReadKey OF
                'M':IF (xg<xm) THEN
                       IF calculado[xg+1] THEN
                          BEGIN
                          if it THEN
                             integral:=integral+(ponto[xg+1]+ponto[xg])/ax/2;
                          xg:=xg+1;
                         END;
                'K':IF (xg>x0) THEN
                       IF calculado[xg-1] THEN
                          BEGIN
                          if it THEN
                             integral:=integral-(ponto[xg]+ponto[xg-1])/ax/2;
                          xg:=xg-1;
                          END;
                END;
             END;
         'D':db:=not db;
         'I':BEGIN
             integral:=0;
             it:=not it
             END;
         END;
      UNTIL r=#27;
      PutSprite(0,-10,-10);
      GoToXY(1,13); FOR j:=1 TO 10 DO WriteLn('           ');
      END; {Medir}

   PROCEDURE Tabela;
      VAR arquivo:TEXT;
          nome:STRING[20];
          i:INTEGER;
      BEGIN
      Write('Arquivo onde salvar tabela: ');
      ReadLn(nome);
      Assign(arquivo,nome);
      ReWrite(arquivo);
      WriteLn(arquivo,xm-x0+1);
      FOR i:=x0 TO xm DO
         BEGIN
         Write(arquivo,(i-bx)/ax);
         IF calculado[i] THEN WriteLn(arquivo,ponto[i]) ELSE WriteLn(arquivo,0)
         END;
      Close(arquivo)
      END; {Tabela}

   PROCEDURE Serie;
      VAR T:REAL;
          a,b:ARRAY[1..20] of REAL;
          a0,y,k,k1:REAL;
          n,i,j:INTEGER;
      BEGIN
      WriteLn('O grafico completo deve ter sido plotado para calculo correto');
      n:=20;
      Write(#10'Numero de harmonicos a calcular: (maximo 20) ');
      ReadLn(n);
      WriteLn(#10'Calculando... (ate 319)'#10);
      T:=(xm-x0)/ax;
      FOR j:=1 TO n DO
         BEGIN a[j]:=0; b[j]:=0 END;
      a0:=0;
      k:=2*pi/T/ax;
      FOR i:=x0 TO xm DO
         BEGIN
         Write(i,#13);
         y:=ponto[i];
         IF (i>x0) and (i<xm) THEN y:=2*y;
         a0:=a0+y;
         k1:=k*(i-bx);
         FOR j:=1 TO n DO
            BEGIN
            a[j]:=a[j]+y*Cos(j*k1);
            b[j]:=b[j]+y*Sin(j*k1)
            END;
         END;
      a0:=a0/T/ax/2;
      FOR i:=1 TO n DO
         BEGIN a[i]:=a[i]/ax/T; b[i]:=b[i]/ax/T END;
      ClrScr;
      WriteLn('Termos da serie de Fourier: ');
      WriteLn(#10'a( 0)=',a0:15:10);
      FOR i:=1 TO n DO
         WriteLn('a(',i:2,')=',a[i]:15:10,'  b(',i:2,')=',b[i]:15:10);
      r:=ReadKey;
      END; {Serie}

   PROCEDURE Outros;
      BEGIN
      TextMode(80);
      WriteLn('T: Gerar tabela de pontos em arquivo');
      WriteLn('S: Calcular termos da serie de Fourier');
      r:=ReadKey;
      ClrScr;
      CASE UpCase(r) OF
         'T':Tabela;
         'S':Serie;
         END;
      END; {Outros}

   BEGIN {Grafico}
   x1:=minx;
   x2:=maxx;
   y1:=miny;
   y2:=maxy;
   FOR j:=x0 TO xm DO calculado[j]:=FALSE;
   SpriteMode;
   Sprite(0,#$FF+#$FE+#$FC+#$FE+#$FF+#$FE+#$DC+#$88);
   REPEAT
      GraphColorMode; Palette(2); ColorTable(3,2,1,0); TextColor(3);
      Square(x0,y0,xm,ym,1);
      ay:=(y0-ym)/(y2-y1); by:=ym-ay*y1;
      ax:=(xm-x0)/(x2-x1); bx:=x0-ax*x1;
      Draw(x0,Limy(0),xm,Limy(0),1);
      Draw(Limx(0),y0,Limx(0),ym,1);
      IF KeyPressed THEN GoTo atualizar;
      GoToXY(1,1);
      WriteLn('X1:',x1:7:4);
      WriteLn('X2:',x2:7:4);
      WriteLn('Y1:',y1:7:4);
      WriteLn('Y2:',y2:7:4);
      FOR xg:=x0 TO xm DO
         BEGIN
         IF not calculado[xg] THEN
            BEGIN
            w:=(xg-bx)/ax;
            ponto[xg]:=Funcao(w);
            calculado[xg]:=TRUE
            END;
         IF xg>x0 THEN
            Draw(xa,Limy(ponto[xg-1]),xg,Limy(ponto[xg]),3);
         xa:=xg;
         IF KeyPressed THEN GoTo atualizar;
         END;
      GoToXY(1,5);
      WriteLn('+ amplia Y');
      WriteLn('- reduz  Y');
      WriteLn('> amplia X');
      WriteLn('< reduz  X');
      WriteLn('" " Medir');
      WriteLn('Cur. move');
      WriteLn('Esc volta');
      WriteLn('"O" outros');
      atualizar:
      r:=UpCase(ReadKey);
      CASE r OF
         '-':y2:=2*(y2-y1)+y1;
         '+':y2:=(y2-y1)/2+y1;
         '>':BEGIN
             x2:=2*(x2-x1)+x1;
             FOR j:=x0 TO mx2 DO
                BEGIN
                xg:=2*j-x0;
                ponto[j]:=ponto[xg];
                calculado[j]:=calculado[xg]
                END;
             FOR j:=mx2+1 TO xm DO calculado[j]:=FALSE
             END;
         '<':BEGIN
             x2:=(x2-x1)/2+x1;
             FOR j:=mx2 DOWNTO x0 DO
                BEGIN
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
                    d:=(x2-x1)*0.25; x1:=x1+d ; x2:=x2+d;
                    FOR j:=x0 TO mx3 DO
                       BEGIN
                       xg:=j-x0+mx1;
                       ponto[j]:=ponto[xg];
                       calculado[j]:=calculado[xg]
                       END;
                    FOR j:=mx3+1 TO xm DO calculado[j]:=FALSE;
                    END;
                'K':BEGIN d:=(x2-x1)*0.25; x1:=x1-d; x2:=x2-d;
                    FOR j:=xm DOWNTO mx1 DO
                       BEGIN
                       xg:=j-mx1+x0;
                       ponto[j]:=ponto[xg];
                       calculado[j]:=calculado[xg]
                       END;
                    FOR j:=x0 TO mx1-1 DO calculado[j]:=FALSE;
                    END;
                END;
             END;
         ' ':BEGIN Medir; GoTo atualizar END;
         'O':Outros;
         END;
      UNTIL r=#27;
   TextMode(80);
   END; {Grafico}

BEGIN {Principal}
Grafico
END. {Plot}