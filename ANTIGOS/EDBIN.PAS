PROGRAM EdBin;
CONST versao='1.7 de 30/07/88 (PC)';
      lpp=23;
      cpl=22;
      cpl1=21;
      base=$100;
      maximo=$7fff;
      xh=2;
      atraso=1500;
      hexadecimal:SET of CHAR=['0'..'9','A'..'F'];
TYPE hex2=STRING[2];
     hex4=STRING[4];
VAR arquivo:FILE;
    nome,temp:STRING[12];
    texto:STRING[50];
    xa,cursor,i,j,k,pag,car,cpp,final:INTEGER;
    c:CHAR;
    buffer:ARRAY[base..maximo] of CHAR;
    ascii,escape,haparametro:BOOLEAN;
LABEL inicio,continuar,ler_txt,ler_end;

PROCEDURE ClrStatus;
   BEGIN
   GoToXY(1,1);
   ClrEol;
   GoToXY(2,1)
   END; {ClrStatus}

FUNCTION Hex(b:BYTE):hex2;
   VAR h,l:BYTE;
   BEGIN
   h:=(b and $F0) shr 4;
   l:=(b and $0F);
   IF h>9 THEN h:=h+55 ELSE h:=h+48;
   IF l>9 THEN l:=l+55 ELSE l:=l+48;
   Hex:=Chr(h)+Chr(l)
   END; {Hex}

FUNCTION HexWord(x:INTEGER):hex4;
   BEGIN
   HexWord:=Hex(Hi(x))+Hex(Lo(x))
   END; {Hex}

FUNCTION Dec(c:CHAR):BYTE;
   BEGIN
   IF c>'@' THEN Dec:=Ord(c)-55
   ELSE Dec:=Ord(c)-48
   END; {Dec}

PROCEDURE LerResposta;
   BEGIN
   REPEAT
      Read(Kbd,c);
      c:=UpCase(c)
   UNTIL c in ['S','N'];
   WriteLn(c)
   END; {LerResposta}

PROCEDURE EscreverCursor;
   BEGIN
   GoToXY(12,1); Write(HexWord(cursor));
   END; {EscreverCursor}

PROCEDURE Cabecalho;
   BEGIN
   ClrStatus;
   Write('Posicao:       Final:',HexWord(final));
   GoToXY(67,1); Write(nome);
   EscreverCursor
   END; {Cabecalho}

PROCEDURE EscreverCaracter;
   BEGIN
   IF (c>#31) and (c<#127) THEN Write(c)
   ELSE Write('.')
   END; {EscreverCaracter}

PROCEDURE PosicionarCursor;
   VAR x,y:BYTE;
   BEGIN
   k:=cursor-pag;
   y:=3+k div cpl;
   x:=k mod cpl;
   IF ascii THEN GoToXY(xa+x,y)
   ELSE GoToXY(xh+(x shr 1)*5+((x and 1) shl 1),y)
   END; {PosicionarCursor}

PROCEDURE EscreverLinha;
   BEGIN
   LowVideo;
   {Write('  ');}
   i:=car; k:=car+cpl1;
   REPEAT
      Write(' ',Hex(Ord(buffer[i])),Hex(Ord(buffer[i+1])));
      i:=i+2
   UNTIL i>k;
   Write(' ');
   FOR i:=car TO car+cpl1 DO
      BEGIN
      c:=buffer[i];
      EscreverCaracter
      END;
   HighVideo;
   END; {EscreverLinha}

PROCEDURE EscreverPagina;
   BEGIN
   car:=pag;
   GoToXY(2,2);
   FOR j:=1 TO lpp DO
      BEGIN
      WriteLn;
      EscreverLinha;
      car:=car+cpl
      END;
   END; {EscreverPagina}

PROCEDURE MudarModo;
   BEGIN
   ascii:=not ascii;
   PosicionarCursor;
   END; {MudarModo}

CONST codigo:STRING[14]='Gfjup!qps!BDNR';

PROCEDURE MoverCursor(n:INTEGER);
   VAR t:INTEGER;
   BEGIN
   t:=cursor+n;
   IF (t>=base) and (t<=maximo) THEN
      BEGIN
      IF t<pag THEN
         BEGIN
         GoToXY(1,3);
         InsLine;
         pag:=pag-cpl;
         car:=pag;
         EscreverLinha
         END
      ELSE
         IF t>=pag+cpp THEN
            BEGIN
            GoToXY(1,3);
            DelLine;
            car:=pag+cpp;
            pag:=pag+cpl;
            GoToXY(1,lpp+2);
            EscreverLinha
            END;
      cursor:=t
      END
   END; {MoverCursor}

PROCEDURE AcharTexto;
   BEGIN
   k:=Length(texto);
   IF k>0 THEN
      BEGIN
      i:=cursor+1; j:=1;
      WHILE (i<=final) and (j<=k) DO
         BEGIN
         IF buffer[i]=texto[j] THEN j:=j+1 ELSE j:=1;
         i:=i+1
         END;
      IF (j>k) and (k>0) THEN
         BEGIN
         cursor:=i-k;
         IF cursor>=pag+cpp THEN
            BEGIN
            pag:=((cursor-base) div cpl)*cpl+base;
            EscreverPagina
            END
         END
      ELSE
         BEGIN
         ClrStatus; Write('* Nao encontrado *');
         Delay(atraso)
         END
      END;
   Cabecalho
   END; {AcharTexto}

PROCEDURE EscreverManual;
   BEGIN
   WriteLn(' ‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹‹');
   WriteLn(' ›Setas:  Movimentar cursor           ﬁ');
   WriteLn(' ›        (Com "scroll" se necess†rio)ﬁ');
   WriteLn(' ›Tab:    Mudar modo texto/hexadecimalﬁ');
   WriteLn(' ›Esc:    Encerrar ediáÑo, instruáîes ﬁ');
   WriteLn(' ›PgDn:   Avanáar uma p†gina          ﬁ');
   WriteLn(' ›PgUp:   Voltar uma p†gina           ﬁ');
   WriteLn(' ›Ctrl-Q: Procurar seqÅància de bytes ﬁ');
   WriteLn(' ›        (Em texto ou hexadecimal)   ﬁ');
   WriteLn(' ›Crtl-L: Continuar a procurar        ﬁ');
   WriteLn(' ›Ctrl-S: Mover cursor p/endereáo     ﬁ');
   WriteLn(' ﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂﬂ');
   END; {EscreverManual}

PROCEDURE Erro(numero,endereco: INTEGER);
   BEGIN
   ClrScr;
   CASE Hi(numero) OF
      0: WriteLn('Interrompido');
      1: Writeln('Erro de E/S (',Hex(Lo(numero)),')');
      2: WriteLn('Erro de execuáao (',Hex(Lo(numero)),')');
      END;
   WriteLn;
   WriteLn('PC=',HexWord(endereco));
   Halt
   END; {Erro}

BEGIN
ErrorPtr:=Ofs(Erro);
cpp:=cpl*lpp;
xa:=xh+(cpl shr 1)*5;
haparametro:=(ParamCount<>0);
inicio:
ascii:=TRUE;
ClrScr;
WriteLn(' Editor de Arquivos Bin†rios');
WriteLn(' ---------------------------');
WriteLn(' Antìnio Carlos M. de Queiroz');
WriteLn(' VersÑo ',versao);
WriteLn;
EscreverManual;
IF haparametro THEN nome:=ParamStr(1)
ELSE
   BEGIN
   Write(#10' Arquivo a editar: ');
   ReadLn(nome)
   END;
Assign(arquivo,nome);
{$I-} Reset(arquivo); {$I+}
IF IOResult<>0 THEN
   BEGIN
   WriteLn(#10' O arquivo ',nome,' nÑo existe');
   Delay(atraso); haparametro:=FALSE;
   GoTo inicio
   END;
IF FileSize(arquivo)*128.0>SizeOf(buffer) THEN
   BEGIN
   WriteLn(#10' O arquivo ',nome,' Ç grande demais');
   Delay(atraso); haparametro:=FALSE;
   GoTo inicio
   END;
final:=base+FileSize(arquivo)*128-1;
WriteLn(#10' Lendo arquivo ',nome);
BlockRead(arquivo,buffer,FileSize(arquivo));
Close(arquivo);
FOR i:=final+1 TO maximo DO buffer[i]:=#0;
pag:=base; cursor:=base;
continuar:
ClrScr;
HighVideo;
Cabecalho;
EscreverPagina;
PosicionarCursor;
escape:=FALSE;
REPEAT
   Read(Kbd,c);
   IF (c>=' ') THEN
      BEGIN
      IF ascii THEN
         BEGIN
         buffer[cursor]:=c;
         EscreverCaracter;
         MudarModo;
         Write(Hex(Ord(c)));
         MudarModo;
         MoverCursor(1)
         END
      ELSE
         BEGIN
         c:=UpCase(c);
         IF c in hexadecimal THEN
            BEGIN
            Write(c);
            i:=Dec(c) shl 4;
            REPEAT
               Read(Kbd,c);
               c:=UpCase(c)
            UNTIL c in hexadecimal;
            Write(c);
            c:=Chr(i or Dec(c));
            buffer[cursor]:=c;
            MudarModo;
            EscreverCaracter;
            MudarModo;
            MoverCursor(1)
            END
         END
      END
   ELSE
      CASE c OF
        #27:IF KeyPressed THEN
               BEGIN
               Read(Kbd,c);
               CASE c OF
                  'Q':IF pag+cpp<=final THEN
                         BEGIN
                         pag:=pag+cpp;
                         cursor:=pag;
                         EscreverPagina
                         END;
                  'I':BEGIN
                      IF pag-cpp>=base THEN pag:=pag-cpp
                      ELSE pag:=base;
                      EscreverPagina;
                      cursor:=pag
                      END;
                  'M':MoverCursor(1);
                  'K':MoverCursor(-1);
                  'H':MoverCursor(-cpl);
                  'P':MoverCursor(cpl)
                  END
               END
            ELSE escape:=TRUE;
         ^I:MudarModo;
         ^Q:BEGIN
            ler_txt:
            ClrStatus; Write('Procurar: ');
            buflen:=46; ReadLn(texto);
            IF not ascii THEN
               BEGIN
               IF Odd(Length(texto)) THEN texto:='0'+texto;
               i:=1; k:=1;
               WHILE i<=Length(texto) DO
                  BEGIN
                  c:=UpCase(texto[i]);
                  IF c in hexadecimal THEN
                     BEGIN
                     j:=Dec(c) shl 4;
                     c:=UpCase(texto[i+1]);
                     IF c in hexadecimal THEN
                        texto[k]:=Chr(j or Dec(c))
                     ELSE GoTo ler_txt
                     END
                  ELSE GoTo ler_txt;
                  i:=i+2; k:=k+1
                  END;
               texto[0]:=Chr(Length(texto) shr 1);
               END;
            AcharTexto
            END;
         ^L:AcharTexto;
         ^S:BEGIN
            ler_end:
            ClrStatus;
            Write('Colocar cursor em (hexa): ');
            buflen:=4; ReadLn(temp);
            IF Length(temp)>0 THEN
               BEGIN
               IF Length(temp)>4 THEN GoTo ler_end;
               i:=1; j:=0;
               REPEAT
                  c:=UpCase(temp[i]);
                  IF c in hexadecimal THEN
                     BEGIN
                     j:=j shl 4 or Dec(c);
                     i:=i+1;
                     END
                  ELSE GoTo ler_end
               UNTIL i>Length(temp);
               IF (j<base) or (j>final) THEN GoTo ler_end;
               cursor:=j;
               pag:=((j-base) div cpl)*cpl+base;
               EscreverPagina
               END;
            Cabecalho
            END;
         #2:BEGIN
            ClrStatus;
            FOR i:=1 TO Length(codigo) DO Write(Chr(Ord(codigo[i])-1));
            Delay(atraso);
            Cabecalho
            END
         END;
   IF cursor>final THEN
      IF final+128<maximo THEN
         BEGIN
         ClrStatus;
         Write('Fim do arquivo. Expandir? (s/n) ');
         LerResposta;
         IF c='S' THEN final:=final+128 ELSE cursor:=final;
         Cabecalho;
         END
      ELSE cursor:=final;
   EscreverCursor;
   PosicionarCursor
UNTIL escape;
ClrScr;
EscreverManual;
Write(#10' Salvar arquivo modificado? (s/n) ');
LerResposta;
IF c='S' THEN
   BEGIN
   Write(#10' Nome a dar? (',nome,') ');
   ReadLn(temp);
   IF Length(temp)=0 THEN temp:=nome;
   Assign(arquivo,temp);
   ReWrite(arquivo);
   BlockWrite(arquivo,buffer,(final-base) div 128+1);
   Close(arquivo);
   WriteLn(#10' Arquivo ',temp,' criado')
   END;
Write(#10' Continuar a ediáÑo? (s/n) ');
LerResposta;
IF c='S' THEN GoTo continuar;
Write(#10' Editar outro arquivo? (s/n) ');
LerResposta;
haparametro:=FALSE;
IF c='S' THEN GoTo inicio;
ClrScr
END.
