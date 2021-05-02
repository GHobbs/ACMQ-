{Leitura de BitMap do Windows}
{Versao 1.0 de 8/4/93}

PROGRAM LeBitMap;
USES Crt,Dos,Graph;
VAR
  arquivo:FILE of WORD;
  b1,b2,b3,b4:BYTE;
  w1:WORD absolute b1;
  w2:WORD absolute b3;
  dw:LONGINT absolute b1;
  placa,modo:INTEGER;
  nome:STRING;
  r:CHAR;
  biBitCount:WORD;
  biClrUsed,biHeigth,biWidth:LONGINT;
  i,j,k:LONGINT;
  pal:ARRAY[0..15] OF RECORD
    r,g,b:INTEGER
  END;
BEGIN
  ClrScr;
  IF ParamCount>0 THEN nome:=ParamStr(1)
  ELSE BEGIN
    Write('Arquivo de bitmap: ');
    ReadLn(nome)
  END;
  Assign(arquivo,nome);
  {$I-} Reset(arquivo); {$I+}
  IF IOResult<>0 THEN BEGIN
    WriteLn('Arquivo nao encontrado');
    Halt
  END;
  WriteLn('BITMAPFILEHEADER');
  Read(arquivo,w1);
  WriteLn('bfType: ',Char(b1),Char(b2));
  Read(arquivo,w1,w2);
  WriteLn('bfSize: ',dw);
  Read(arquivo,w1,w2);
  WriteLn('bfReserved1: ',w1);
  WriteLn('bfReserved2: ',w2);
  Read(arquivo,w1,w2);
  WriteLn('bfOffBits: ',dw);
  Read(arquivo,w1,w2);
  WriteLn('biSize: ',dw);
  Read(arquivo,w1,w2); biWidth:=dw;
  WriteLn('biWidth: ',biWidth);
  Read(arquivo,w1,w2); biHeigth:=dw;
  WriteLn('biHeigth: ',biHeigth);
  Read(arquivo,w1);
  WriteLn('biPlanes: ',w1);
  Read(arquivo,biBitCount);
  WriteLn('biBitCount: ',biBitCount);
  Read(arquivo,w1,w2);
  WriteLn('biCompression: ',dw);
  Read(arquivo,w1,w2);
  WriteLn('biSizeImage: ',dw);
  Read(arquivo,w1,w2);
  WriteLn('biXPelsPerMeter: ',dw);
  Read(arquivo,w1,w2);
  WriteLn('biYPelsPerMeter: ',dw);
  Read(arquivo,w1,w2); biClrUsed:=dw;
  WriteLn('biClrUsed: ',biClrUsed);
  Read(arquivo,w1,w2);
  WriteLn('biClrImportant: ',dw);
  Write('Mais...'#13);
  r:=ReadKey;
  IF biClrUsed<>0 THEN k:=biClrUsed
  ELSE BEGIN
    k:=1;
    FOR i:=1 TO biBitCount DO k:=2*k
  END;
  IF k<>16 THEN BEGIN
    WriteLn('Somente bitmaps de 16 cores suportados');
    Halt
  END;
   FOR i:=1 TO k DO BEGIN
    Write('RGBQUAD ',i-1:3,': ');
    Read(arquivo,w1,w2);
    Write('rgbBlue:  ',Lo(w1):3);
    Write(' rgbGreen: ',Hi(w1):3);
    Write(' rgbRed:   ',Lo(w2):3);
    WriteLn(' rgbReserved: ',Hi(w2):3);
    WITH pal[i-1] DO BEGIN
      {tem que ser assim}
      r:=Lo(w2) shr 2;
      g:=Hi(w1) shr 2;
      b:=Lo(w1) shr 2
    END
  END;
  WriteLn('Segue o BitMap:');
  r:=ReadKey;
  placa:=detect;
  InitGraph(placa,modo,GetEnv('TPBGI'));
  FOR i:=0 TO k-1 DO BEGIN
    WITH pal[i] DO SetRGBPalette(i,r,g,b);
    SetPalette(i,i)
  END;
  FOR i:=1 TO biHeigth DO BEGIN
    k:=0; j:=480-i;
    WHILE k<biWidth DO BEGIN
      Read(arquivo,w1,w2);
      PutPixel(k,j,b1 shr 4);
      IF k+1<biWidth THEN PutPixel(k+1,j,b1 and 15);
      IF k+2<biWidth THEN PutPixel(k+2,j,b2 shr 4);
      IF k+3<biWidth THEN PutPixel(k+3,j,b2 and 15);
      IF k+4<biWidth THEN PutPixel(k+4,j,b3 shr 4);
      IF k+5<biWidth THEN PutPixel(k+5,j,b3 and 15);
      IF k+6<biWidth THEN PutPixel(k+6,j,b4 shr 4);
      IF k+7<biWidth THEN PutPixel(k+7,j,b4 and 15);
      Inc(k,8)
    END
  END;
  Close(arquivo);
  r:=ReadKey;
END.
