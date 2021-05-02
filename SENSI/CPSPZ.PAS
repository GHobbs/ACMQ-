PROGRAM CpSPZ;
{**************************************************************
 * Compara‡„o de sensibilidades de p¢los e zeros              *
 * Ant“nio Carlos Moreir„o de Queiroz                         *
 * V. 1.0  de 20/04/90                                        *
 * V. 1.1  de 23/08/91 Compat¡vel com novo SENSI              *
 * V. 1.1a de 03/01/91 Cores sem EGA                          *
 * V. 2.0  de 03/09/95 Tabelas maiores. Le ref. do IFFT       *
 **************************************************************}
USES Dos,Crt,Graph,Tela;

{$I seta.p}

CONST
  versao='2.0 de 03/09/95';
  maxs=30;
  maxmax=1000;
  forte=1; media=2; fraca=9;
  calculavel=TRUE;

TYPE
  tab=
    RECORD
      nome:STRING;
      polos,zeros:BOOLEAN;
      npz:INTEGER;
      pz:ARRAY[1..maxs] OF
        RECORD
          re,im,vre,vim,rma,rme,ang:REAL;
        END
     END;

VAR
  cor:ARRAY[1..maxmax] OF BYTE;
  tabela:ARRAY[1..maxmax] of ^tab;
  csr,ok,retangulos,elipses,redesenhar,fim:BOOLEAN;
  txt,rede:STRING;
  ch:CHAR;
  i,t,s,placa,modo,maxtab:INTEGER;
  f:REAL;

FUNCTION Sri(x:INTEGER):STRING;
VAR
  tmp:STRING;
BEGIN
  Str(x,tmp);
  Sri:=tmp
END;

FUNCTION Sre(x:REAL; c,d:INTEGER):STRING;
VAR
  tmp:STRING;
BEGIN
  Str(x:c:d,tmp);
  Sre:=tmp
END;

PROCEDURE ErroFatal(texto:STRING);
BEGIN
  TextMode(80);
  WriteLn(tl,#10'[Erro]: '+texto);
  WriteLn(#10'Toque uma tecla...');
  ch:=ReadKey;
  Halt
END;

PROCEDURE LerTabela;
VAR
  polos,zeros:BOOLEAN;
  arquivo:TEXT;
  ch:CHAR;

BEGIN
  REPEAT
    ok:=FALSE;
    REPEAT
      txt:=rede;
      Write(tl,#10'Tabela a ler (.tab) ou ?: ');
      EditarLinha(txt,WhereX,WhereY,1);
      WriteLn;
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
      polos:=FALSE;
      zeros:=FALSE;
      WHILE (tabela[i]^.zeros or tabela[i]^.polos) and (i<maxtab) DO Inc(i);
      IF tabela[i]^.polos or tabela[i]^.zeros THEN BEGIN
        WriteLn(tl,'[*] N£mero m ximo de tabelas excedido');
        ok:=FALSE;
      END;
      IF ok THEN BEGIN
        ok:=FALSE;
        REPEAT
          ReadLn(arquivo,txt);
          ok:=(Pos('Pol',txt)<>0) or (pos('Zer',txt)<>0)
        UNTIL ok or SeekEof(arquivo);
        IF not ok THEN WriteLn(tl,'[*] Fim do arquivo')
        ELSE BEGIN
          IF Pos('Pol',txt)<>0 THEN polos:=TRUE
          ELSE IF Pos('Zer',txt)<>0 THEN zeros:=TRUE
          ELSE ok:=FALSE;
          IF ok THEN WITH tabela[i]^ DO BEGIN
            npz:=0;
            REPEAT
              Inc(npz);
              WITH pz[npz] DO BEGIN
                {$I-}
                Read(arquivo,re,im);
                IF not SeekEoln(arquivo) THEN Read(arquivo,vre,vim,rma,rme,ang)
                ELSE BEGIN
                  vre:=0; vim:=0; rma:=0; rme:=0; ang:=0
                END;
                ReadLn(arquivo)
                {$I+}
              END;
              ok:=IOResult=0
            UNTIL SeekEoln(arquivo) or not ok
          END;
          IF not ok THEN WriteLn(tl,'[*] Formato impr¢prio.');
        END;
        IF ok THEN BEGIN
          tabela[i]^.zeros:=zeros;
          tabela[i]^.polos:=polos;
          tabela[i]^.nome:=rede;
          t:=i;
          s:=1;
          Write(tl,'[*] Lida tabela no. ',i,', de ');
          IF polos THEN WriteLn('p¢los')
          ELSE WriteLn('zeros');
        END
      END
    UNTIL not ok;
    Close(arquivo);
    Write(#10'Mais tabelas'); LerBool(ok);
  UNTIL not ok
END;

PROCEDURE EliminarTabela;
BEGIN
  Tabela[t]^.polos:=FALSE;
  Tabela[t]^.zeros:=FALSE;
  i:=1;
  WHILE (not tabela[i]^.zeros) and (not tabela[i]^.polos) and (i<maxtab) DO Inc(i);
  IF tabela[i]^.zeros or tabela[i]^.polos THEN t:=i ELSE t:=0;
  s:=1;
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
    SetTextStyle(SmallFont,HorizDir,4);
    IF GetMaxColor=1 THEN
      FOR i:=1 TO maxmax DO cor[i]:=1
    ELSE IF placa<>CGA THEN BEGIN
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
  END;
  i:=GraphResult; IF i<>GrOk THEN ErroFatal(GraphErrorMsg(i));
  retangulos:=TRUE;
  elipses:=TRUE;
  fim:=FALSE;
  TextMode(80);
  WriteLn(tl,'[Compara‡„o de sensibilidades de p¢los e zeros]');
  WriteLn(    '---------------------------------------------');
  WriteLn('Ant“nio Carlos M. de Queiroz - COPPE/UFRJ');
  WriteLn('Vers„o ',versao);
  WriteLn;
  WriteLn('Este programa compara tabelas de p¢los e zeros,');
  WriteLn('com desvios, geradas pelo programa Sensi e outros.');
  WriteLn;
  WriteLn('No gr fico, os comandos s„o:'#10);
  WriteLn(tl,'[Ins]: Inclu¡r as tabelas de um arquivo');
  WriteLn(tl,'[Del]: Eliminar a tabela atual');
  WriteLn(tl,'[Tab,Bs]: Selecionar p¢lo/zero');
  WriteLn(tl,'[Cr]: Selecionar tabela');
  WriteLn(tl,'[A/a]: Ampliar/reduzir os desvios');
  WriteLn(tl,'[c]: Ligar/desligar cursor');
  WriteLn(tl,'[r]: Ligar/desligar desvios das partes real e imagin ria (retƒngulos)');
  WriteLn(tl,'[e]: Ligar/desligar desvios com correla‡„o (elipses)');
  WriteLn(tl,'[" "]: Centrar p¢lo/zero selecionado');
  WriteLn(tl,'[cursor,+,-]: Mover, ampliar, reduzir escalas');
  WriteLn(tl,'[v/V]: Listar erros (acima/abaixo)');
  WriteLn(tl,'[Esc]: Terminar');
  maxtab:=0;
  WHILE (MaxAvail>SizeOf(tabela)) and (maxtab<maxmax) DO BEGIN
    Inc(maxtab);
    New(tabela[maxtab]);
  END;
  WriteLn(tl,'Mem¢ria suficiente para [',maxtab,'] tabelas.');
  FOR i:=1 TO maxtab DO BEGIN
    tabela[i]^.zeros:=FALSE;
    tabela[i]^.polos:=FALSE
  END;
  fim:=FALSE; csr:=TRUE;
  rede:='';
  t:=0; s:=1;
  LerTabela;
END;

PROCEDURE PlotarTabelas;
VAR
  remin,immin,delta,ay,by,ax,bx,w,t1,t2,d1,d2,z1,z2:REAL;
  xmax,ymax,base,i,j,x1,x2:INTEGER;
  xa,ya:WORD;

LABEL atualizar;

  FUNCTION LimX(x:REAL):INTEGER;
  BEGIN
    LimX:=Round(ax*x+bx)
  END;

  FUNCTION LimY(y:REAL):INTEGER;
  BEGIN
    LimY:=Round(ay*y+by)
  END;

  PROCEDURE Elipse(x0,y0,a,b,angulo: REAL; cor:INTEGER);
  CONST
    lados=40;
  VAR
    t,d:REAL;
    i,j:INTEGER;
  BEGIN
    SetColor(cor);
    IF a=0 THEN Exit;
    t:=a/lados;
    d:=b/a;
    d1:=Cos(angulo);
    d2:=Sin(angulo);
    FOR j:=-lados TO lados DO BEGIN
      z1:=j*t;
      z2:=d*Sqrt(Abs(Sqr(a)-Sqr(z1)));
      IF j>-lados THEN BEGIN
        Line(LimX(x0+t1*d1-t2*d2),LimY(y0+t1*d2+t2*d1),LimX(x0+z1*d1-z2*d2),LimY(y0+z1*d2+z2*d1));
        Line(LimX(x0+t1*d1+t2*d2),LimY(y0+t1*d2-t2*d1),LimX(x0+z1*d1+z2*d2),LimY(y0+z1*d2-z2*d1));
      END;
      t1:=z1;
      t2:=z2;
    END;
  END;

BEGIN
  f:=1;
  remin:=1;
  FOR i:=1 TO maxtab DO WITH tabela[i]^ DO
    IF polos or zeros THEN
      WITH pz[s] DO BEGIN
        IF Abs(re)>remin THEN remin:=Abs(re);
        IF Abs(im)>remin THEN remin:=Abs(im)
      END;
  remin:=-Exp(Ln(2)*(Trunc(Ln(remin)/Ln(2))+1));
  immin:=remin;
  delta:=-2*remin;
  REPEAT
    SetGraphMode(modo);
    SetTextStyle(SmallFont,HorizDir,4);
    RemoveSprite;
    SetFillStyle(EmptyFill,1);
    ymax:=GetMaxY;
    GetAspectRatio(xa,ya);
    xmax:=Trunc(ymax*ya/xa);
    base:=xmax+4;
    ay:=-ymax/delta; by:=ymax-ay*immin;
    ax:=xmax/delta; bx:=-ax*remin;
    SetColor(cor[forte]);
    OutTextXY(base,0,'Re:'+Sre(remin,10,-1));
    OutTextXY(base,8,'   '+Sre(remin+delta,10,-1));
    OutTextXY(base,16,'Im:'+Sre(immin,10,-1));
    OutTextXY(base,24,'   '+Sre(immin+delta,10,-1));
    OutTextXY(base,40,'Ampl: '+Sre(f,7,3));
    SetViewPort(0,0,xmax,ymax,ClipOn);
    SetLineStyle(DottedLn,0,NormWidth);
    SetColor(cor[fraca]);
    i:=Limx(0);
    Line(i,0,i,ymax);
    i:=Limy(0);
    Line(0,i,xmax,i);
    SetLineStyle(SolidLn,0,NormWidth);
    SetColor(cor[forte]);
    Rectangle(0,0,xmax,ymax);
    FOR i:=1 TO maxtab DO WITH tabela[i]^ DO
      IF polos or zeros THEN
        FOR j:=1 TO npz DO WITH pz[j] DO BEGIN
          x1:=LimX(re);
          x2:=LimY(im);
          IF (x1>=0) and (x1<=xmax) and (x2>=0) and (x2<=ymax) THEN BEGIN
            IF calculavel THEN BEGIN
              SetColor(cor[i]);
              IF (vre<>0) or (vim<>0) THEN BEGIN
                IF retangulos THEN Rectangle(LimX(re-f*vre),LimY(im-f*vim),LimX(re+f*vre),LimY(im+f*vim));
                IF elipses THEN Elipse(re,im,f*rma,f*rme,ang*Pi/180,cor[i]);
              END
            END;
            {SetColor(cor[forte]);}
            IF polos THEN BEGIN
              Line(x1-2,x2-2,x1+2,x2+2);
              Line(x1-2,x2+2,x1+2,x2-2)
            END
            ELSE Circle(x1,x2,4);
            IF KeyPressed THEN GoTo atualizar;
          END
        END;
    SetViewPort(0,0,GetMaxX,GetMaxY,ClipOn);
    SetColor(cor[forte]);
    REPEAT
      redesenhar:=TRUE;
      IF t>0 THEN WITH tabela[t]^ DO
        WITH pz[s] DO BEGIN
          x1:=LimX(re);
          x2:=LimY(im);
          IF csr and (x1>=0) and (x1<=xmax)
                 and (x2>0)  and (x2<=ymax)
            THEN PutsPrite(x1,x2) ELSE PutSprite(-100,-100);
          Bar(base,68,GetMaxX,GetMaxY);
          SetColor(cor[forte]);
          OutTextXY(base,68,nome);
          SetColor(cor[t]);
          OutTextXY(base,84,'Tabela '+Sri(t));
          SetColor(cor[media]);
          IF polos THEN
            OutTextXY(base,100,'Polo '+Sri(s))
          ELSE
            OutTextXY(base,100,'Zero '+Sri(s));
          OutTextXY(base,116,'Re:'+Sre(re,10,-1));
          OutTextXY(base,124,'Im:'+Sre(im,10,-1));
          w:=Sqrt(Sqr(re)+Sqr(im));
          OutTextXY(base,132,'w: '+Sre(w,10,-1));
          MoveTo(base,140); OutText('Q: ');
          IF re<>0 THEN OutText(Sre(-0.5*w/re,10,-1)) ELSE OutText(' infinito');
          IF calculavel THEN BEGIN
            SetColor(cor[forte]);
            OutTextXY(base,156,'VR:'+Sre(f*vre,10,-1));
            OutTextXY(base,164,'VI:'+Sre(f*vim,10,-1));
            OutTextXY(base,172,'Ra:'+Sre(f*rma,10,-1));
            OutTextXY(base,180,'Rb:'+Sre(f*rme,10,-1));
            OutTextXY(base,188,'Ang:'+Sre(ang,9,3))
          END
        END;
     atualizar:
      ch:=ReadKey;
      CASE ch OF
        'r':retangulos:=not retangulos;
        'e':elipses:=not elipses;
        'A':f:=2*f;
        'a':f:=f/2;
        #0:BEGIN
             ch:=ReadKey;
             CASE ch OF
               'M':remin:=remin+delta/4;
               'K':remin:=remin-delta/4;
               'H':immin:=immin+delta/4;
               'P':immin:=immin-delta/4;
               #82:BEGIN TextMode(80); LerTabela END;
               #83:EliminarTabela;
             END
           END;
       '-':BEGIN
             remin:=remin-delta/2;
             immin:=immin-delta/2;
             delta:=delta*2
           END;
       '+':BEGIN
             remin:=remin+delta/4;
             immin:=immin+delta/4;
             delta:=delta/2;
           END;
        ' ':BEGIN
              remin:=tabela[t]^.pz[s].re-delta/2;
              immin:=tabela[t]^.pz[s].im-delta/2
            END;
        'c':BEGIN
              csr:=not csr;
              IF not csr THEN PutSprite(-100,-100);
              redesenhar:=FALSE
            END;
        #13:IF t>0 THEN BEGIN
              REPEAT
                Inc(t);
                IF t>maxtab THEN t:=1
              UNTIL tabela[t]^.zeros or tabela[t]^.polos;
              IF s>tabela[t]^.npz THEN s:=tabela[t]^.npz;
              redesenhar:=FALSE;
            END;
        #9:BEGIN IF s<tabela[t]^.npz THEN Inc(s) ELSE s:=1; redesenhar:=FALSE END;
        #8:BEGIN IF s>1 THEN Dec(s) ELSE s:=tabela[t]^.npz; redesenhar:=FALSE END;
        'v','V':WITH tabela[t]^.pz[s] DO BEGIN
              SetColor(cor[forte]);
              i:=Limx(re+f*vre)+4;
              IF ch='v' THEN j:=Limy(im+f*vim)-3
              ELSE j:=Limy(im-f*vim)-57;
              putsprite(-100,-100);
              OutTextXY(i,j,'Re:'+Sre(re,10,-1));
              OutTextXY(i,j+8,'Im:'+Sre(im,10,-1));
              IF (vre<>0) or (vim<>0) THEN BEGIN
                OutTextXY(i,j+16,'VR:'+Sre(f*vre,10,-1));
                OutTextXY(i,j+24,'VI:'+Sre(f*vim,10,-1));
                OutTextXY(i,j+32,'Ra:'+Sre(f*rma,10,-1));
                OutTextXY(i,j+40,'Rb:'+Sre(f*rme,10,-1));
                OutTextXY(i,j+48,'Ang:'+Sre(ang,9,3));
              END;
              redesenhar:=FALSE
            END;
        #27:BEGIN
              Textmode(80);
              Write('Terminar'); LerBool(fim);
              IF not fim THEN BEGIN
                Write('Minima coordenada real'); LerReal(remin);
                Write('Minima coordenada imag'); LerReal(immin);
                Write('Largura real/imag'); LerReal(delta)
              END
            END
        ELSE redesenhar:=FALSE
      END
    UNTIL redesenhar or fim;
  UNTIL fim;
  TextMode(80);
END;

BEGIN
  Inicializar;
  REPEAT
    PlotarTabelas;
  UNTIL fim;
END.
