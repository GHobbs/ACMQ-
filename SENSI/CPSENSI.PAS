PROGRAM CpSensi;
{******************************************************************************
 * ComparaáÑo de tabelas de sensibilidade                                     *
 * Antìnio Carlos MoreirÑo de Queiroz - COPPE/UFRJ                            *
 * V. 1.5  de 27/07/88                                                        *
 * V. 1.6  de 30/09/88 Fim com confirmaáÑo, sem acentos                       *
 * V. 1.7  de 11/01/89 Turbo 5.0, tudo em funáÑo da tela                      *
 * V. 1.8  de 28/07/89 Novos gr†ficos                                         *
 * V. 1.8a de 22/08/89 ViewPort acrescentada                                  *
 * V. 1.9  de 24/09/89 Leitura de arquivos do AnaFil                          *
 * V. 2.0  de 29/07/90 Mudada leitura de tabelas, reformulaáÑo geral          *
 * V. 2.1  de 01/08/91 Gr†ficos referenciados por freqÅància                  *
 * V. 2.2  de 17/08/91 Compat°vel com o novos SENSI, IFFT e ANAFIL            *
 * V. 2.2a de 07/11/91 Corrigido cursor, aceitas tabelas mais simples         *
 * V. 2.2b de 03/01/92 Cores sem EGA                                          *
 * V. 2.2c de 19/01/92 TPBGI                                                  *
 * V. 2.2d de 07/11/92 Instrucao errada retirada                              *
 * V. 2.3  de 26/08/95 Mais tabelas                                           *
 * V. 2.4  de 30/06/11 Mais pontos                                            *
 ******************************************************************************}
USES Dos,Crt,Graph,Tela;

{$I seta.p}

CONST
  maxmax=1000;
  versao='2.4 de 30/06/11';
  mp=1001;
  forte=1; media=2; fraca=9;
TYPE
  tabela=
    RECORD
      nome:STRING;
      nf:INTEGER;
      Fr,Mo,Fa,Tg,Dm,Df:ARRAY[0..mp] of REAL;
      opcao:INTEGER;
    END;
VAR
  cor:ARRAY[1..maxmax] OF BYTE;
  Tab:ARRAY [1..maxmax] of ^tabela;
  maxtab,curva,modo,placa,xmin,xmax,ymin,ymax,i,k:INTEGER;
  ch:CHAR;
  txt,rede:STRING;
  ok,fim,redesenhar:BOOLEAN;

PROCEDURE ErroFatal(texto:STRING);
BEGIN
  TextMode(80);
  WriteLn(tl,#10'[Erro]: '+texto);
  WriteLn(#10'Toque uma tecla...');
  ch:=ReadKey;
  Halt
END;

FUNCTION Proxima(curva:INTEGER):INTEGER;
BEGIN
  i:=curva;
  REPEAT
    Inc(curva);
    IF curva>maxtab THEN curva:=1
  UNTIL (Tab[curva]^.nf>=0) or (curva=i);
  IF k>Tab[curva]^.nf THEN k:=Tab[curva]^.nf;
  Proxima:=curva;
  IF curva=i THEN fim:=TRUE
END;

PROCEDURE LerTabela;
VAR
  arquivo:TEXT;
  ch:CHAR;

BEGIN
  REPEAT
    ok:=FALSE;
    REPEAT
      txt:=rede;
      Write(tl,#10'Tabela a ler (.tab) ou [?]: ');
      EditarLinha(txt,WhereX,WhereY,1);
      WriteLn;
      IF txt='' THEN Exit;
      IF txt='?' THEN Diretorio
      ELSE BEGIN
        IF Pos('.',txt)=0 THEN txt:=txt+'.tab';
        rede:=Copy(txt,1,Pos('.',txt)-1);
        Assign(arquivo,txt);
        {$I-} Reset(arquivo) {$I+};
        ok:=(IOresult=0);
        IF not ok THEN WriteLn(tl,#10'[*] Arquivo [',txt,'] inexistente.')
      END
    UNTIL ok;
    i:=1;
    REPEAT
      WHILE (Tab[i]^.nf>=0) and (i<maxtab) DO Inc(i);
      IF Tab[i]^.nf>=0 THEN BEGIN
        WriteLn(tl,'[*] N£mero m†ximo de tabelas excedido');
        ok:=FALSE;
      END;
      IF ok THEN BEGIN
        ok:=FALSE;
        REPEAT
          ReadLn(arquivo,txt);
          ok:=((txt[1]='R') or (txt[1]='#')) and (Length(txt)>0);
        UNTIL ok or SeekEof(arquivo);
        IF not ok THEN WriteLn(tl,'[*] Fim do arquivo')
        ELSE BEGIN
          WITH Tab[i]^ DO BEGIN
            opcao:=5;
            nome:=rede;
            REPEAT
              Inc(nf);
              {$I-}
              Read(arquivo,Fr[nf],Mo[nf]);
              IF not SeekEoln(arquivo) THEN Read(arquivo,Fa[nf]) ELSE Fa[nf]:=0;
              IF not SeekEoln(arquivo) THEN Read(arquivo,Tg[nf]) ELSE Tg[nf]:=0;
              IF not SeekEoln(arquivo) THEN Read(arquivo,Dm[nf]) ELSE BEGIN opcao:=1; Dm[nf]:=0; END;
              IF not SeekEoln(arquivo) THEN Read(arquivo,Df[nf]) ELSE Df[nf]:=0;
              ReadLn(arquivo);
              {$I+}
              ok:=IOResult=0
            UNTIL SeekEoln(arquivo) or not ok or (nf=mp);
            IF ok THEN
              WriteLn(tl,'[*] Lida tabela no. ',i,', com ',nf+1,' pontos.');
          END;
          IF not ok THEN WriteLn(tl,'[*] Formato impr¢prio.');
        END
      END
    UNTIL not ok;
    Close(arquivo);
    Write(#10'Mais tabelas'); LerBool(ok);
  UNTIL not ok
END;

PROCEDURE EliminarTabela;
BEGIN
  Tab[curva]^.nf:=-1;
  redesenhar:=TRUE;
  curva:=Proxima(curva)
END;

PROCEDURE Inicializar;
BEGIN
  DetectGraph(placa,modo);
  IF (placa=CGA) THEN modo:=CGAC1;
  IF paramcount=2 THEN BEGIN
    Val(ParamStr(1),placa,i);
    Val(ParamStr(2),modo,i);
  END;
  InitGraph(placa,modo,GetEnv('TPBGI'));
  IF placa>0 THEN BEGIN
    IF placa<>CGA THEN BEGIN
      cor[1]:=White;
      cor[2]:=Yellow;
      cor[3]:=LightRed;
      cor[4]:=LightGreen;
      cor[5]:=LightMagenta;
      cor[6]:=LightCyan;
      cor[7]:=Magenta;
      cor[8]:=LightBlue;
      cor[9]:=LightGray;
      cor[10]:=Brown;
      FOR i:=11 TO maxmax DO cor[i]:=Random(15)+1
    END
    ELSE FOR i:=1 TO maxmax DO
      CASE i mod 3 OF
        0:cor[i]:=2;
        1:cor[i]:=1;
        2:cor[i]:=3
      END;
    InitSprite(cor[forte],cor[media]);
    xmin:=85;
    xmax:=GetMaxX;
    ymin:=0;
    ymax:=GetMaxY-9;
  END;
  i:=GraphResult; IF i<>GrOk THEN ErroFatal(GraphErrorMsg(i));
  fim:=FALSE;
  rede:='';
  TextMode(80);
  WriteLn(tl,'[ComparaáÑo de Respostas em FreqÅància]');
  WriteLn(    '-------------------------------------');
  WriteLn('Antìnio Carlos M. de Queiroz - COPPE/UFRJ');
  WriteLn('VersÑo ',versao);
  WriteLn;
  WriteLn(tl,'Este programa [compara tabelas] geradas pelo programa [SENSI], e outros.');
  WriteLn('O programa espera encontrar nos arquivos uma ou mais tabelas contendo:');
  WriteLn(tl,'<[frequencia]> <[m¢dulo]> <[fase]> <[atraso de grupo]> <[desv. m¢dulo]> <[desv. fase]>');
  WriteLn(tl,'em colunas separadas. Tabelas comeáam com um "[#]" (ou "R") na 1a. coluna,');
  WriteLn('e terminam com uma linha em branco. Valores nÑo existentes sÑo ignorados.');
  WriteLn(tl,'AtÇ [',mp+1,'] pontos sÑo aceitos.');
  WriteLn('No gr†fico, os comandos sÑo:');
  WriteLn(tl,'[Ins]: Inclu°r as tabelas de um arquivo');
  WriteLn(tl,'[Del]: Eliminar a tabela atual (cursor)');
  WriteLn(tl,'[Tab]: Selecionar curva');
  WriteLn(tl,'[O]  : Selecionar opáîes');
  WriteLn(tl,'[Cr] : Especificar limites');
  WriteLn(tl,'[" "]: Ligar/desligar cursor');
  WriteLn(tl,'[G]  : Ligar/desligar grade');
  WriteLn(tl,'[L]  : Mudar escala horizontal entre log./linear');
  WriteLn(tl,'[cursor,A,R,+,-]: mover, ampliar, reduzir escalas');
  WriteLn(tl,'[Esc]: Terminar');
  maxtab:=0;
  WHILE (MaxAvail>SizeOf(tabela)) and (maxtab<maxmax) DO BEGIN
    Inc(maxtab);
    New(Tab[maxtab]);
  END;
  WriteLn(tl,'Mem¢ria suficiente para [',maxtab,'] tabelas.');
  FOR i:=1 TO maxtab DO Tab[i]^.nf:=-1;
END;

PROCEDURE Plotar;

VAR
  lim1,lim2,x,j,l,m:INTEGER;
  kr,f1,f2,y1,y2,ay,by,af,bf,t,t1,t2:REAL;
  grade,log:BOOLEAN;
LABEL
  atualizar;

  FUNCTION LimY(x:REAL):INTEGER;
  BEGIN
    x:=ay*x+by;
    IF x<lim1 THEN LimY:=lim1
    ELSE IF x>lim2 THEN LimY:=lim2
         ELSE LimY:=Round(x)
  END;

  FUNCTION LimX(x:REAL):INTEGER;
  BEGIN
    IF log THEN LimX:=Round(af*Ln(x)+bf)
    ELSE LimX:=Round(af*x+bf)
  END;

  PROCEDURE Escalar(fator:REAL);
  BEGIN
    t:=(y2-y1)*fator;
    y2:=y1+t
  END;

  PROCEDURE TodaTela;
  BEGIN
    SetViewPort(0,0,GetMaxX,GetMaxY,ClipOn);
  END;

  PROCEDURE Medir;
  CONST
    x0=0;
    y0=16;
  VAR
    sair:BOOLEAN;

  FUNCTION Indice(f:REAL):INTEGER;
    BEGIN
      i:=0;
      WITH Tab[curva]^ DO BEGIN
        WHILE ((Fr[i]<f) or (Fr[i]<f1)) and (i<nf) DO Inc(i);
        IF (Fr[i]>f2) and (i>0) THEN Dec(i)
      END;
      Indice:=i
    END;

  BEGIN
    TodaTela;
    lim1:=ymin; lim2:=ymax;
    k:=Indice(f1);
    sair:=FALSE; redesenhar:=FALSE;
    REPEAT
      WITH Tab[curva]^ DO BEGIN
        SetColor(cor[forte]);
        Bar(x0,y0,x0+79,y0+64);
        OutTextXY(x0,y0,nome);
        Str(curva,txt); MoveTo(x0,y0+8); OutText('#'+txt);
        CASE opcao OF
          1,5,8:BEGIN t:=Mo[k]; l:=23; txt:='Modl' END;
              2:BEGIN t:=Dm[k]; l:=31; txt:='VeMo' END;
            3,6:BEGIN t:=Fa[k]; l:=39; txt:='Fase' END;
              4:BEGIN t:=Df[k]; l:=47; txt:='VeFa' END;
              7:BEGIN t:=Tg[k]; l:=55; txt:='AtGr' END
        END;
        IF (Fr[k]>=f1) and (Fr[k]<=f2) THEN PutSprite(LimX(Fr[k])+xmin,LimY(t)) ELSE PutSprite(-10,-10);
        OutText(' '+txt);
        Str(Fr[k]:10:4,txt); OutTextXY(x0,y0+16,txt);
        Str(Mo[k]:10:4,txt); OutTextXY(x0,y0+24,txt);
        Str(Dm[k]:10:4,txt); OutTextXY(x0,y0+32,txt);
        Str(Fa[k]:10:4,txt); OutTextXY(x0,y0+40,txt);
        Str(Df[k]:10:4,txt); OutTextXY(x0,y0+48,txt);
        Str(Tg[k]:10:4,txt); OutTextXY(x0,y0+56,txt);
        SetColor(cor[media]);
        Rectangle(x0,y0+l,x0+79,y0+l+8);
        CASE ReadKey OF
           #0:CASE ReadKey OF
                'M':IF (k+1<=nf) and (Fr[k+1]<=f2) THEN Inc(k);
                'K':IF (k-1>=0) and (Fr[k-1]>=f1) THEN Dec(k);
               #116:IF (k+10<=nf) and (Fr[k+10]<=f2) THEN Inc(k,10);
               #115:IF (k-10>=0) and (Fr[k-10]>=f1) THEN Dec(k,10);
                #83:EliminarTabela
              END;
           #9:BEGIN t:=Fr[k]; curva:=Proxima(curva); k:=Indice(t) END;
          ' ',#27:sair:=TRUE;
        END
      END;
    UNTIL sair or fim or redesenhar;
    PutSprite(-10,-10);
    Bar(x0,y0,x0+79,y0+64);
  END; {Medir}

  PROCEDURE AcharEscalas;
  BEGIN
    f1:=1e38; f2:=-1e38;
    FOR i:=1 TO maxtab DO WITH Tab[i]^ DO IF nf>=0 THEN BEGIN
      IF Fr[0]<f1 THEN f1:=Fr[0];
      IF Fr[nf]>f2 THEN f2:=Fr[nf]
    END
  END;

BEGIN
  grade:=TRUE; redesenhar:=TRUE; log:=TRUE;
  y1:=-80; y2:=10;
  curva:=Proxima(maxtab);
  AcharEscalas;
  WHILE not fim DO BEGIN
    IF redesenhar THEN BEGIN
      lim1:=-5000; lim2:=5000;
      IF (f1<=0) or (f2<=0) THEN log:=FALSE;
      IF (f2<=f1) or (y2<=y1) THEN grade:=FALSE;
      SetGraphMode(modo);
      SetFillStyle(EmptyFill,1);
      Str(y2:4:2,txt); OutTextXY(xmin-8*Length(txt),ymin,txt);
      Str(y1:4:2,txt); OutTextXY(xmin-8*Length(txt),ymax-6,txt);
      Str(f1:4:2,txt); OutTextXY(xmin,ymax+2,txt);
      Str(f2:4:2,txt); OutTextXY(xmax-8*Length(txt)+1,ymax+2,txt);
      IF KeyPressed THEN GoTo atualizar;
      SetViewPort(xmin,ymin,xmax,ymax,ClipOn);
      IF log THEN BEGIN
          af:=(xmax-xmin)/Ln(f2/f1);
          bf:=-af*Ln(f1)
        END
      ELSE BEGIN
        af:=(xmax-xmin)/(f2-f1);
        bf:=-af*f1
      END;
      ay:=(ymax-ymin)/(y1-y2); by:=-ay*y2;
      IF grade THEN BEGIN
        SetLineStyle(DottedLn,0,NormWidth);
        SetColor(cor[fraca]);
        IF (f2-f1>f1) and log THEN t1:=f1 ELSE t1:=f2-f1;
        t1:=Exp(Ln(10)*Round(Ln(t1)/Ln(10)-0.499999));
        t2:=Round(f1/t1+0.5)*t1;
        WHILE t2<f2 DO
          IF log THEN BEGIN
            IF Round(t2/t1)=10 THEN BEGIN
              t1:=10*t1;
              SetColor(cor[media]);
            END;
            i:=Round(af*Ln(t2)+bf);
            Line(i,0,i,ymax-ymin);
            t2:=t2+t1;
            SetColor(cor[fraca]);
          END
          ELSE BEGIN
            i:=Round(af*t2+bf);
            Line(i,0,i,ymax-ymin);
            t2:=t2+t1
          END;
        t1:=y2-y1;
        t1:=Exp(Ln(10)*Round(Ln(t1)/Ln(10)-0.5));
        t2:=Round(y1/t1+0.5)*t1;
        WHILE t2<y2 DO BEGIN
          i:=LimY(t2);
          Line(0,i,xmax-xmin,i);
          t2:=t2+t1
        END
      END;
      SetLineStyle(SolidLn,0,NormWidth);
      SetColor(cor[forte]);
      Rectangle(0,0,xmax-xmin,ymax-ymin);
      FOR i:=maxtab DOWNTO 1 DO WITH Tab[i]^ DO IF nf>=0 THEN BEGIN
        x:=0;
        WHILE (x<nf) and (Fr[x]<f1) DO Inc(x); IF x>0 THEN Dec(x);
        IF x<nf THEN BEGIN
          REPEAT
            Inc(x);
            SetColor(cor[i]);
            m:=LimX(Fr[x]);
            l:=LimX(Fr[x-1]);
            CASE opcao OF
              1:Line(l,LimY(Mo[x-1]),m,LimY(Mo[x]));
              2:Line(l,LimY(Dm[x-1]),m,LimY(Dm[x]));
              3:Line(l,LimY(Fa[x-1]),m,LimY(Fa[x]));
              4:Line(l,LimY(Df[x-1]),m,LimY(Df[x]));
              5:BEGIN
                  Line(l,LimY(Mo[x-1]),m,LimY(Mo[x]));
                  Line(l,LimY(Mo[x-1]+Dm[x-1]),m,LimY(Mo[x]+Dm[x]));
                  Line(l,LimY(Mo[x-1]-Dm[x-1]),m,LimY(Mo[x]-Dm[x]));
                END;
              6:BEGIN
                  Line(l,LimY(Fa[x-1]),m,LimY(Fa[x]));
                  Line(l,LimY(Fa[x-1]+Df[x-1]),m,LimY(Fa[x]+Df[x]));
                  Line(l,LimY(Fa[x-1]-Df[x-1]),m,LimY(Fa[x]-Df[x]))
                END;
              7:Line(l,LimY(Tg[x-1]),m,LimY(Tg[x]));
              8:BEGIN
                  Line(l,LimY(Mo[x-1]),m,LimY(Mo[x]));
                  PutPixel(m,Round(((ymin-ymax)/180*Fa[x]+ymax+ymin)/2),cor[i])
                END
            END;
          IF KeyPressed THEN GoTo atualizar;
          UNTIL (Fr[x]>=f2) or (x=nf);
       END
     END
   END;
  Atualizar:
   redesenhar:=TRUE;
   SetColor(cor[forte]);
   CASE UpCase(ReadKey) OF
     '-':Escalar(2);
     '+':Escalar(0.5);
     'R':IF log THEN f2:=f1*Sqr(f2/f1) ELSE f2:=f1+(f2-f1)*2;
     'A':IF log THEN f2:=f1*Sqrt(f2/f1) ELSE f2:=f1+(f2-f1)/2;
     #13:BEGIN
           TextMode(80);
           WriteLn('Tabelas:'#10);
           FOR i:=1 TO maxtab DO WITH Tab[i]^ DO IF nf>=0 THEN
             WriteLn(tl,'#',i,': [',nome,']; ',nf+1,' pontos; faixa: ',Cpct(Fr[0]),' a ',Cpct(Fr[nf]));
           WriteLn(#10'Novos limites:'#10);
           Write('FreqÅància m°nima'); LerReal(f1);
           Write('FreqÅància m†xima'); LerReal(f2);
           Write(#10'Y m°nimo'); LerReal(y1);
           Write('Y m†ximo'); LerReal(y2)
         END;
     #0:CASE ReadKey OF
          'H':BEGIN t:=(y2-y1)*0.5; y1:=y1+t ; y2:=y2+t END;
          'P':BEGIN t:=(y2-y1)*0.5; y1:=y1-t ; y2:=y2-t END;
          'M':IF log THEN BEGIN t:=Sqrt(Sqrt(f2/f1)); f1:=f1*t; f2:=f2*t END
              ELSE BEGIN t:=(f2-f1)/4; f1:=f1+t; f2:=f2+t END;
          'K':IF log THEN BEGIN t:=Sqrt(Sqrt(f2/f1)); f1:=f1/t; f2:=f2/t END
              ELSE BEGIN t:=(f2-f1)/4; f1:=f1-t; f2:=f2-t END;
          #82:BEGIN TextMode(80); LerTabela END;
          END;
      'O':BEGIN
            TextMode(80);
            WriteLn(tl,'[Opáîes de plotagem:]'#10);
            WriteLn(tl,'[1]-M¢dulo');
            WriteLn(tl,'[2]-Desvio do m¢dulo');
            WriteLn(tl,'[3]-Fase');
            WriteLn(tl,'[4]-Desvio da fase');
            WriteLn(tl,'[5]-M¢dulo+desvio');
            WriteLn(tl,'[6]-Fase+desvio');
            WriteLn(tl,'[7]-Atraso de grupo');
            WriteLn(tl,'[8]-M¢dulo e fase'#10);
            FOR i:=1 TO maxtab DO WITH Tab[i]^ DO IF nf>=0 THEN BEGIN
              REPEAT
                Write(tl,'#',i,': [',nome,']'); LerInt(opcao);
              UNTIL (opcao>0) and (opcao<9);
            END;
            ok:=FALSE;
            Write(#10'Manter as escalas atuais'); LerBool(ok);
            IF not ok THEN BEGIN
              AcharEscalas;
              CASE Tab[curva]^.opcao OF
                1,5,8:BEGIN y1:=-80; y2:=10 END;
                2:BEGIN y1:=0; y2:=5 END;
                3,6:BEGIN y1:=-180; y2:=180 END;
                4:BEGIN y1:=0; y2:=20 END;
                7:BEGIN y1:=0; y2:=20 END;
              END
            END
          END;
      'G':grade:=not grade;
      'L':log:=not log;
      ' ':Medir;
      #27:fim:=TRUE;
      ELSE GoTo atualizar
    END
  END;
  TextMode(80);
END; {Plotar}

BEGIN
  Inicializar;
  REPEAT
    LerTabela;
    Plotar;
    Write('Terminar'); LerBool(fim);
  UNTIL fim;
END.
