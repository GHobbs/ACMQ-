PROGRAM Montanha;

USES Crt,Turbo3,Graph3;

VAR x,y:ARRAY[1..20000] of BYTE;
    forclr,b0,li,a,b,i,j,t1,t2,t3,p1,p2,n,l:INTEGER;
    c:CHAR;
    d:INTEGER;
LABEL inicio;

FUNCTION R:INTEGER;
   BEGIN
   R:=Random(d)-d shr 1
   END;

PROCEDURE Plotar;
   BEGIN
   p1:=1+a;
   p2:=2+a;
   FOR i:=1 TO li DO
      BEGIN
      FOR j:=0 TO i-1 DO
         BEGIN
         t1:=p1+j;
         t2:=p2+j;
         t3:=t2+1;
         Draw(x[t1],y[t1],x[t2],y[t2],forclr);
         Draw(x[t1],y[t1],x[t3],y[t3],forclr);
         Draw(x[t2],y[t2],x[t3],y[t3],forclr);
         END;
      p1:=p2;
      p2:=p2+i+1;
      END;
   END; {Plotar}

PROCEDURE Expandir;
   BEGIN
   p1:=a+1;
   p2:=a+2;
   b:=b+1;
   x[b]:=x[p1];
   y[b]:=y[p1];
   FOR i:=1 TO li DO
      BEGIN
      FOR j:=0 TO i-1 DO
         BEGIN
         t1:=p1+j;
         t2:=p2+j;
         b:=b+1;
         x[b]:=(x[t1]+x[t2]) shr 1;
         y[b]:=(y[t1]+y[t2]) shr 1+R;
         t2:=t2+1;
         b:=b+1;
         x[b]:=(x[t1]+x[t2]) shr 1;
         y[b]:=(y[t1]+y[t2]) shr 1+R;
         END;
      b:=b+1;
      x[b]:=x[p2];
      y[b]:=y[p2];
      FOR j:=0 TO i-1 DO
         BEGIN
         t1:=p2+j;
         t2:=t1+1;
         b:=b+1;
         x[b]:=(x[t1]+x[t2]) shr 1;
         y[b]:=(y[t1]+y[t2]) shr 1+R;
         b:=b+1;
         x[b]:=x[t2];
         y[b]:=y[t2];
         END;
      p1:=p2;
      p2:=p2+i+1;
      END;
   END; {Expandir}

BEGIN
inicio:
ClrScr;
forclr:=3;
Write('Maxima ordem? (1-8) ');
ReadLn(n);
Write('Grau de irregularidade? (1-255) ');
ReadLn(d);
a:=0; b:=3;
li:=1;
x[1]:=128; y[1]:=10;
x[2]:=0;   y[2]:=160;
x[3]:=255; y[3]:=160;
FOR l:=1 TO n DO
   BEGIN
   GraphColorMode; Palette(3);
   WriteLn('Ordem ',l);
   Plotar;
   Read(Kbd,c);
   IF l<>n THEN
      BEGIN
      b0:=b;
      Expandir;
      li:=li*2;
      a:=b0;
      IF d>1 THEN d:=d shr 1;
      END
   END;
TextMode(80);
Write('Outro? [s/n] ');
Read(Kbd,c);
IF UpCase(c)='S' THEN GoTo inicio;
END.