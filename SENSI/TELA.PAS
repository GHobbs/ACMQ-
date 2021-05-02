UNIT Tela;

{14/03/90: Edi‡„o de linha}
{20/04/90: N£meros reais compactos}
{07/11/91: Edi‡„o mais usual (feito de novo a partir da tela_e}
{11/06/93: Overflows}

{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}

INTERFACE

USES Dos,Crt;

{$IFDEF DOUBLE}
  TYPE REAL= {$IFDEF EXTENDED} EXTENDED {$ELSE} DOUBLE {$ENDIF};
{$ENDIF}

CONST
  precisao=
{$IFDEF DOUBLE}
  {$IFDEF EXTENDED} 'extendida' {$ELSE} 'dupla' {$ENDIF}
{$ELSE} 'simples' {$ENDIF};
  procmodo={$IFDEF DPMI}'protegido'{$ELSE}'real'{$ENDIF};

VAR tl:TEXT;

FUNCTION UpKey:CHAR;
PROCEDURE EditarLinha(VAR linha:STRING; x,y,cursor:INTEGER);
FUNCTION Cpct(x:REAL):STRING;
PROCEDURE LerReal(VAR x:REAL);
PROCEDURE LerInt(VAR x:INTEGER);
PROCEDURE LerBool(VAR x:BOOLEAN);
PROCEDURE Diretorio;

IMPLEMENTATION

FUNCTION Cpct(x:REAL):STRING;
VAR
  txt:STRING;
  e,z,d:INTEGER;
BEGIN
  Str(x,txt);
  IF txt[1]=' ' THEN txt:=Copy(txt,2,255);
  e:=Pos('E',txt);
  z:=e+2;
  WHILE (z<=Length(txt)) and (txt[z]='0') DO Inc(z);
  d:=e-1;
  IF z>Length(txt) THEN e:=z;
  WHILE txt[d]='0' DO Dec(d);
  IF txt[d]='.' THEN Dec(d);
  Cpct:=Copy(txt,1,d)+Copy(txt,e,2)+Copy(txt,z,4);
END;

FUNCTION UpKey:CHAR;
BEGIN
  UpKey:=UpCase(ReadKey);
END;

PROCEDURE EditarLinha(VAR linha:STRING; x,y,cursor:INTEGER);
CONST
  max=255;
VAR
  base,tlinha:INTEGER;
  inserir,primeira:BOOLEAN;
  r:CHAR;
BEGIN
  base:=1; primeira:=TRUE;
  tlinha:=80-x;
  inserir:=FALSE;
  REPEAT
    GoToXY(x,y);
    Write(tl,'[',Copy(linha,base,tlinha),']'); ClrEol;
    GoToXY(x+cursor-base,y);
    r:=ReadKey;
    CASE r OF
      #0:CASE ReadKey OF
           'K':IF cursor>1 THEN Dec(cursor);
           'M':IF (cursor<=Length(linha)) and (cursor<max) THEN cursor:=cursor+1;
           'G':cursor:=1;
           'O':cursor:=Length(linha)+1;
           'R':inserir:=not inserir;
           'S':linha:=Copy(linha,1,cursor-1)+Copy(linha,cursor+1,max)
         END;
      #8:IF cursor>1 THEN BEGIN
           linha:=Copy(linha,1,cursor-2)+Copy(linha,cursor,max);
           Dec(cursor)
         END;
      #10,#27:;
      #13:Exit
      ELSE BEGIN
        IF primeira THEN BEGIN linha:=r; cursor:=1 END
        ELSE
          IF inserir THEN linha:=Copy(linha,1,cursor-1)+r+Copy(linha,cursor,max)
          ELSE linha:=Copy(linha,1,cursor-1)+r+Copy(linha,cursor+1,max);
        IF cursor<max THEN Inc(cursor)
      END
    END;
    IF cursor<base THEN base:=cursor
    ELSE
      IF cursor>=base+tlinha THEN base:=cursor-tlinha+1;
    primeira:=FALSE
  UNTIL FALSE
END;

PROCEDURE LerReal(VAR x:REAL);
VAR
  csr,ptx,pty:INTEGER;
  txt:STRING;
BEGIN
  Write(': ');
  txt:=Cpct(x); csr:=1; ptx:=WhereX; pty:=WhereY;
  REPEAT
    EditarLinha(txt,ptx,pty,csr);
    Val(txt,x,csr);
  UNTIL csr=0;
  WriteLn;
END;

PROCEDURE LerInt(VAR x:INTEGER);
VAR
  csr,ptx,pty:INTEGER;
  txt:STRING;
BEGIN
  Write(': ');
  Str(x,txt); csr:=1; ptx:=WhereX; pty:=WhereY;
  REPEAT
    EditarLinha(txt,ptx,pty,csr);
    Val(txt,x,csr);
  UNTIL csr=0;
  WriteLn;
END;

PROCEDURE LerBool(VAR x:BOOLEAN);
VAR
  r:CHAR;
BEGIN
  IF x THEN r:='S' ELSE r:='N';
  Write(tl,'? ([',r,']) [');
  REPEAT r:=UpKey UNTIL r in ['S','N',#13];
  IF r='S' THEN x:=TRUE
  ELSE IF r='N' THEN x:=FALSE;
  IF x THEN r:='S' ELSE r:='N';
  WriteLn(r);
  Write(tl,']');
END;

PROCEDURE Diretorio;

TYPE
  filename=STRING[12];
VAR
  path:STRING;
  srec:SearchRec;

  PROCEDURE EscreverNome(nome:filename);
  VAR
    dotpos:INTEGER;
    ext:STRING[3];
  BEGIN
    dotpos:=Pos('.',nome);
    IF dotpos<>0 THEN BEGIN
      ext:=Copy(nome,dotpos+1,Length(nome)-dotpos);
      Delete(nome,dotpos,1+Length(nome)-dotpos)
    END
    ELSE ext:='';
    Write(nome:9,'.',ext:3);
  END;

BEGIN
  LowVideo;
  WriteLn;
  Write('M scara para diret¢rio: ');
  path:='*.*'; EditarLinha(path,WhereX,WhereY,1); WriteLn; WriteLn;
  FindFirst(path,AnyFile,srec);
  WHILE DosError=0 DO BEGIN
    EscreverNome(srec.Name);
    IF WhereX>30 THEN WriteLn;
    FindNext(srec)
  END;
  IF WhereX>1 THEN WriteLn
END;

VAR SaidaNormal:POINTER;

{$F+}
FUNCTION SaidaInOut(VAR F:TextRec):INTEGER;
VAR p:WORD;
BEGIN
  WITH TextRec(F) DO BEGIN
    p:=0;
    WHILE p<BufPos DO BEGIN
      CASE BufPtr^[p] of
        '[':TextColor(14);
        ']':TextColor(7);
        ELSE Write(BufPtr^[p])
      END;
      Inc(p)
    END;
    BufPos:=0;
  END;
  SaidaInOut:=0;
END;

FUNCTION SaidaClose(Var F:TextRec):INTEGER;
BEGIN
  SaidaClose:=0;
END;

FUNCTION SaidaOpen(Var F:TextRec):INTEGER;
BEGIN
  WITH TextRec(F) DO
    IF Mode<>fmInput THEN BEGIN
      InOutFunc:=@SaidaInOut;
      FlushFunc:=@SaidaInOut;
      CloseFunc:=@SaidaClose;
      Mode:=fmOutput;
      SaidaOpen:=0;
    END
  ELSE SaidaOpen:=5;
END;

PROCEDURE MinhaSaida;
BEGIN
  ExitProc:=SaidaNormal;
  IF ExitCode<>0 THEN BEGIN
    {$IFNDEF DEBUG}
    TextMode(80);
    HighVideo;
    {$ENDIF}
    CASE ExitCode OF
      202:WriteLn('"Stack overflow"');
      203:WriteLn('"Heap overflow"');
      106:WriteLn('Formato num‚rico impr¢prio');
      200:WriteLn('Divis„o por zero');
      205:WriteLn('"Overflow"');
      207:WriteLn('Opera‡„o num‚rica inv lida');
      255:WriteLn('Interrompido');
      ELSE WriteLn('Erro no. ',ExitCode);
    END;
    WriteLn
  END;
  {$IFNDEF DEBUG}
  ErrorAddr:=nil
  {$ENDIF}
END; {MinhaSaida}
{$F-}

BEGIN
  SaidaNormal:=ExitProc;
  ExitProc:=@MinhaSaida;
  WITH TextRec(tl) DO BEGIN
    Mode:=fmClosed;
    BufSize:=SizeOf(Buffer);
    BufPtr:=@Buffer;
    OpenFunc:=@SaidaOpen;
    Name[0]:=#0
  END;
  ReWrite(tl)
END.
