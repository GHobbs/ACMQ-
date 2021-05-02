{Editor para desenhos do EdFil}
{Versao 2.0 29/10/94}

USES Crt;

CONST
  digito:STRING[16]=('0123456789ABCDEF');
VAR
  arquivo:TEXT;
  nome:STRING;
  teste:STRING;
  padrao:ARRAY[1..16,1..16] of CHAR;
  valor:ARRAY[1..16] of INTEGER;
  hex:ARRAY[1..16] of STRING[4];
  r:CHAR;
  linha:LONGINT;
  x,y,k,base:INTEGER;
  ok,fim:BOOLEAN;
LABEL
  inicio;

PROCEDURE Erro;
BEGIN
  WriteLn('Erro de leitura no arquivo.');
  Close(arquivo);
  Halt;
END;

BEGIN
  inicio:
  fim:=FALSE;
  ClrScr;
  Write('Elemento a editar no EdFil (Inicial ou .): ');
  ReadLn(r);
  IF r='.' THEN Exit;
  teste:='tipo:'''+r+'''';
  Assign(arquivo,'edfil.pas');
  {$I-} Reset(arquivo); {$I+}
  IF IoResult<>0 THEN BEGIN
    WriteLn('Arquivo edfil.pas nao encontrado.');
    Halt
  END;
  REPEAT
    ReadLn(arquivo,nome);
    ok:=pos(teste,nome)<>0;
  UNTIL ok or seekeof(arquivo);
  IF not ok THEN Erro;
  WriteLn('Descricao:');
  FOR x:=1 TO 16 DO BEGIN
    REPEAT
      Read(arquivo,r)
    UNTIL r='$';
    Read(arquivo,hex[x]);
    Write('$',hex[x],',');
    IF x mod 4=0 THEN WriteLn
  END;
  Close(arquivo);
  WriteLn('Imagem:');
  FOR y:=1 TO 16 DO BEGIN
    linha:=4096*(pos(hex[y,1],digito)-1)+
            256*(pos(hex[y,2],digito)-1)+
             16*(pos(hex[y,3],digito)-1)+
                (pos(hex[y,4],digito)-1);
    FOR x:=16 DOWNTO 1 DO BEGIN
      IF Odd(linha) THEN padrao[x,17-y]:='x' ELSE padrao[x,17-y]:='.';
      linha:=linha shr 1
    END
  END;
  base:=WhereY;
  FOR y:=1 TO 16 DO BEGIN
    FOR x:=1 TO 16 DO
      Write(padrao[x,y]);
    WriteLn;
  END;
  x:=1; y:=1;
  REPEAT
    GoToXY(x,base-1+y);
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
       #0:IF KeyPressed THEN BEGIN
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
  GoToXY(1,3);
  FOR y:=16 DOWNTO 1 DO BEGIN
    valor[y]:=0;
    k:=1;
    FOR x:=16 DOWNTO 1 DO BEGIN
      IF padrao[x,y]='x' THEN valor[y]:=valor[y]+k;
      k:=k shl 1;
    END;
    hex[y]:='';
    k:=valor[y] shr 12;
    hex[y]:=hex[y]+digito[k+1];
    k:=valor[y] and $0F00 shr 8;
    hex[y]:=hex[y]+digito[k+1];
    k:=valor[y] and $00F0 shr 4;
    hex[y]:=hex[y]+digito[k+1];
    k:=valor[y] and $F;
    hex[y]:=hex[y]+digito[k+1];
    Write('$',hex[y],',');
    IF y mod 4=1 THEN WriteLn;
  END;
  Write('Salvar? (nome ou Enter) ');
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

