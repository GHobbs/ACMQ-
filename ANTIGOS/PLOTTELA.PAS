PROGRAM PlotTela;

{$M 4096,0,0}

USES Crt,Graph3,Dos;

VAR
  onde:STRING;
  i,xmax,ymax,cores:INTEGER;
  r:CHAR;
  hi:BOOLEAN;

PROCEDURE PlotterDump; Interrupt;
  VAR
    cor,x0,y0,x,y,x1,y1,i,iant,k:INTEGER;
    halinha:BOOLEAN;
    saida:TEXT;
  CONST
    px:ARRAY[0..7] of INTEGER = (1,1,0,-1,-1,-1,0,1);
    py:ARRAY[0..7] of INTEGER = (0,1,1,1,0,-1,-1,-1);
  LABEL
    Fim;

  PROCEDURE SeguirLinha;
  BEGIN
    Plot(x0,y0,0);
    Write(saida,'PA',x0,',',ymax+1-y0,';PD;');
    x:=x0; y:=y0;
    iant:=0;
    REPEAT
      i:=iant;
      REPEAT
        x1:=x+px[i];
        y1:=y+py[i];
        halinha:=GetDotColor(x1,y1)=cor;
        IF not halinha THEN i:=(i+1) and 7;
      UNTIL halinha or ((i=iant) and not halinha);
      IF halinha THEN BEGIN
        x:=x1; y:=y1;
        Plot(x,y,0);
        Write(saida,'PA',x,',',ymax+1-y,';');
        iant:=(i-1) and 7;
      END
    UNTIL not halinha;
    Write(saida,'PU;')
  END;

  PROCEDURE Beep(f:WORD);
  BEGIN
    Sound(f);
    Delay(50);
    NoSound
  END;

BEGIN
  InLine($FB);
  Beep(1000);
  Assign(saida,onde);
  ReWrite(saida);
  Write(saida,'DF;PU;SC0,',xmax,',0,',ymax,';');
  FOR cor:=1 TO cores DO BEGIN
    Write(saida,'SP',cor,';');
    FOR x0:=0 TO xmax DO BEGIN
      IF KeyPressed THEN BEGIN
        Beep(400);
        IF ReadKey=#27 THEN GoTo Fim
      END;
      FOR y0:=0 TO ymax DO
        IF GetDotColor(x0,y0)=cor THEN BEGIN
          SeguirLinha;
          FOR k:=0 TO 7 DO
            IF GetDotColor(x0+px[k],y0+py[k])=cor THEN SeguirLinha;
        END
    END
  END;
 Fim:
  Write(saida,'PA',xmax,',',ymax,';SP0;');
  Close(saida);
  Beep(1500);
END;

BEGIN
  ClrScr;
  TextBackGround(yellow); TextColor(black);
  WriteLn(' Este programa instala uma rotina residente que desenha   ');
  WriteLn(' telas gr ficas (CGA) em um plotter que use HP-GL.        ');
  WriteLn(' Vers„o 1.1 de 13/02/89, por Ant“nio Carlos M. de Queiroz ');
  WriteLn;
  TextColor(white); TextBackGround(black); LowVideo;
  Write('Modo gr fico a usar: 320x200 (1) ou 640x200 (2)? ');
  REPEAT r:=ReadKey UNTIL r in ['1','2'];
  HighVideo; WriteLn(r); LowVideo;
  hi:=r='2';
  IF hi THEN BEGIN
    xmax:=639; cores:=1
  END
  ELSE BEGIN
    xmax:=319; cores:=3
  END;
  ymax:=199;
  WriteLn;
  Write('Enviar a sa¡da para: (COM1 (normal), CON, NUL,.. ou arquivo) ');
  HighVideo; ReadLn(onde);
  WriteLn;
  IF hi THEN WriteLn('- Monte a pena 1 no plotter.')
  ELSE WriteLn('- Monte as penas 1, 2 e 3 no plotter (cores 1,2 e 3 da tela).');
  WriteLn('- Delimite o tamanho desejado no papel com P1 e P2 (opcional).');
  WriteLn('- P1 = canto superior esquerdo; P2 = canto inferior direito.');
  WriteLn('- Acione com PrtSc, com o plotter e o desenho prontos.');
  WriteLn('- Se necess rio, interrompa com ESC.');
  LowVideo;
  WriteLn(#10'Este programa pode n„o funcionar junto com certos programas.');
  WriteLn('Recomenda-se salvar tudo antes de tentar com um novo programa.');
  WriteLn(#10'Toque uma tecla para instalar, ESC para interromper.');
  r:=ReadKey;
  IF r=#27 THEN Halt;
  IF hi THEN HiRes ELSE GraphColorMode;
  SetIntVec(5,@PlotterDump);
  WriteLn('PlotTela instalado');
  WriteLn('------------------');
  Keep(1)
END.

