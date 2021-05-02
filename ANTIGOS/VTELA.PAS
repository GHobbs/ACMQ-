PROGRAM Vtela;
VAR ok : BOOLEAN;
    nome : STRING[20];
    arquivo : TEXT;
    c : CHAR;
    i,j : INTEGER;
BEGIN
REPEAT
   ClrScr;
   Write('Arquivo contendo a tela (GrafXY vertical): ');
   REPEAT
      ReadLn(nome);
      Assign(arquivo,nome);
      {$I-} Reset(arquivo); {$I+}
      ok:=(IOresult=0);
      IF NOT ok then Write('Arquivo inexistente. Tente outro: ');
   UNTIL ok;
   Read(arquivo,c,c,c,c,c);
   IF Ord(c)<>10 THEN BEGIN WriteLn('O arquivo nao e do tipo correto'); Halt END;
   HiRes;
   i:=-1;
   WHILE not Eof(arquivo) DO {I=0,79 para tela completa}
      BEGIN
      i:=i+1;
      Read(arquivo,c,c,c,c,c,c,c,c,c,c,c,c,c,c,c);
      j:=7920+i;
      REPEAT
         Read(arquivo,c,c);
         Mem[$B800:j+8192]:=Ord(c);
         Read(arquivo,c,c);
         Mem[$B800:j]:=Ord(c);
         j:=j-80
      UNTIL j=i-80;
      Read(arquivo,c,c)
      END;
   REPEAT Read(Kbd,c) UNTIL c in [#27,#13];
   TextMode
UNTIL c=#27
END.