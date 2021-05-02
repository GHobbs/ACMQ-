{Editor dos desenhos do EdFil}

USES Crt;

CONST
  digito:ARRAY[0..15] of CHAR=('0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F');
VAR
  arquivo:TEXT;
  nome:STRING[20];
  padrao:ARRAY[1..16,1..16] of CHAR;
  valor:ARRAY[1..16] of INTEGER;
  hex:ARRAY[1..16] of STRING[4];
  r:CHAR;
  x,y,k:INTEGER;
  fim:BOOLEAN;
LABEL
  inicio;

BEGIN
  inicio:
  fim:=FALSE;
  ClrScr;
  WriteLn('[L]er arquivo');
  WriteLn('[N]ovo arquivo');
  WriteLn('[F]im');
  r:=ReadKey;
  IF UpCase(r)='F' THEN Halt;
  IF UpCase(r)='L' THEN BEGIN
    Write('Nome do arquivo: ');
    ReadLn(nome);
    Assign(arquivo,nome);
    Reset(arquivo);
    ReadLn(arquivo);
    FOR y:=1 TO 16 DO BEGIN
      FOR x:=1 TO 16 DO Read(arquivo,padrao[x,y]);
      ReadLn(arquivo);
    END;
    Close(arquivo);
  END
  ELSE
    FOR y:=1 TO 16 DO
      FOR x:=1 TO 16 DO
        padrao[x,y]:='.';
  ClrScr;
  FOR y:=1 TO 16 DO BEGIN
    FOR x:=1 TO 16 DO
      Write(padrao[x,y]);
    WriteLn;
  END;
  x:=1; y:=1;
  REPEAT
    GoToXY(x,y);
    r:=ReadKey;
    CASE UpCase(r) OF
      'X':BEGIN
            padrao[x,y]:='x';
            Write('x');
          END;
      '.':BEGIN
            padrao[x,y]:='.';
            Write('.');
          END;
      #0:BEGIN
           r:=ReadKey;
           CASE r OF
             'H':IF y>1 THEN y:=y-1;
             'P':IF y<16 THEN y:=y+1;
             'K':IF x>1 THEN x:=x-1;
             'M':IF x<16 THEN x:=x+1;
           END
         END;
      #13:fim:=TRUE;
    END;
  UNTIL fim;
  GoToXY(1,18);
  FOR y:=16 DOWNTO 1 DO BEGIN
    valor[y]:=0;
    k:=1;
    FOR x:=16 DOWNTO 1 DO BEGIN
      IF padrao[x,y]='x' THEN valor[y]:=valor[y]+k;
      k:=k shl 1;
    END;
    hex[y]:='';
    k:=valor[y] shr 12;
    hex[y]:=hex[y]+digito[k];
    k:=valor[y] and $0F00 shr 8;
    hex[y]:=hex[y]+digito[k];
    k:=valor[y] and $00F0 shr 4;
    hex[y]:=hex[y]+digito[k];
    k:=valor[y] and $F;
    hex[y]:=hex[y]+digito[k];
    Write('$',hex[y],',');
    IF y mod 4=1 THEN WriteLn;
  END;
  WriteLn;
  Write('Salvar? (nome ou CR) ');
  ReadLn(nome);
  IF nome='' THEN GoTo inicio;
  Assign(arquivo,nome);
  ReWrite(arquivo);
  WriteLn(arquivo,'{');
  FOR y:=1 TO 16 DO BEGIN
    FOR x:=1 TO 16 DO
      Write(arquivo,padrao[x,y]);
    WriteLn(arquivo);
  END;
  WriteLn(arquivo,'}');
  FOR y:=16 DOWNTO 1 DO BEGIN
    Write(arquivo,'$',hex[y],',');
    IF y mod 4=1 THEN WriteLn(arquivo);
  END;
  Close(arquivo);
  GoTo inicio;
END.

