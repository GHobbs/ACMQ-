PROGRAM IFFT;
{******************************************************************************
 * C†lculo de Funáîes de Transferància Por "Fast Fourier Transform"           *
 * Autor: Antìnio Carlos MoreirÑo de Queiroz - COPPE/UFRJ 1984                *
 * V. 4.1 de  21/11/87: Modificado formato de entrada                         *
 * V. 4.2 de  03/02/88: Mudados comparaáÑo e gr†fico                          *
 * V. 4.3 de  25/05/88: Novo gr†fico, den. c/ cte=1, uso de grau, LeFdet, etc.*
 * V. 4.4 de  25/05/88: Modificada inclusÑo de funáîes                        *
 * V. 4.4a de 28/08/88: VersÑo PC com novos nomes G,Y e N                     *
 * V. 4.4b de 11/10/88: CorreáÑo na descriáÑo da VCCS                         *
 * V. 4.5 de  24/10/88: Incluidos Q e I, reorganizaáÑo, ediáÑo                *
 * V. 4.5a de 30/10/88: Gr†ficos de polos e zeros, etc.                       *
 * V. 4.5b de 20/11/88: w e Q de polos e zeros                                *
 * V. 4.5c de 27/11/88: Melhorado gr†fico de polos e zeros, corrigida cte.    *
 * V. 4.6 de  03/03/89: Turbo 5.0, melhor gr†fico, parÉmetro, tabela          *
 * V. 4.6a de 25/03/89: CorreáÑo na contagem no n£mero de polos               *
 * V. 4.7 de  19/07/89: Novos gr†ficos                                        *
 * V. 4.8 de  13/08/89: Novos gr†ficos, melhor tratamento de erro             *
 * V. 4.9 de  15/10/89: Ordem dos gr†ficos, normalizaáÑo Z, maior precisÑo    *
 * V. 5.0 de  21/11/89: VCCS no formato Spice, BJT c/ 3 terminais             *
 * V. 5.0a de 12/02/90: Cursor com Ctrl                                       *
 * V. 5.1 de  12/03/90: Transformador nÑo rec°proco, ediáÑo de texto          *
 * V. 5.2 de  08/04/90: Girador invertido                                     *
 * V. 5.2a de 16/04/90: Estrutura de dados reformulada                        *
 * V. 5.2b de 20/05/90: NormalizaáÑo modificada, ra°zes de pol. normalizado   *
 * V. 5.3 de  13/07/91: Implementado c†lculo de atraso de grupo               *
 * V. 5.4 de  16/08/91: Transistor MOS, tabela para CPSENSI, .net             *
 * V. 5.4a de 07/11/91: Tabelas com #                                         *
 * V. 5.4b de 03/01/92: GetEnv incluido, cores sem EGA                        *
 * V. 5.5  de 04/04/92: Calculo da ordem de complexidade por arvore normal    *
 * V. 5.5a de 31/05/92: Uso correto da norm em impedancia e graudefault       *
 * V. 5.5b de 17/07/92: Corrigida prioridade do girador na arvore normal      *
 * V. 5.6  de 22/10/92: F->Z, corrigido grafico de polos e zeros na CGA       *
 ******************************************************************************}

{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}

USES Dos,Crt,Graph,Tela;

{$I seta.p}

CONST
  Versao='5.6 de 22/10/92'; {VersÑo do programa}
  MaxEl=130;          {M†ximo n£mero de componentes}
{$IFDEF DOUBLE}
  MaxNos=34;
  xxmax=200;
{$ELSE}
  MaxNos=40;          {M†ximo n£mero de n¢s depois da reduáÑo}
  xxmax=300;          {M†ximo tamanho de gr†fico}
{$ENDIF}
  MaxNos1=MaxNos+1;   {MaxNos+1}
  MaxNosAntes=50;     {M†ximo n£mero de n¢s antes da reduáÑo}
  Gmax=31;            {M†xima ordem de complexidade - 1}
  Gmax2=2*Gmax;
  MeioGm=(Gmax+1) div 2;
  mfuncoes=4;         {N£mero m†ximo de funáîes no gr†fico}
  tamnome=5;          {M†ximo tamanho de nome}
  cor:ARRAY[1..mfuncoes] of INTEGER=(3,2,1,2);
  tmin:REAL=0;        {M°nimo atraso}
  tmax:REAL=30;       {M†ximo atraso}
  fmin:REAL=-180;     {M°nima fase}
  fmax:REAL=180;      {M†xima fase}
  awmin:REAL=0.2;     {M°nima freqÅància}
  awmax:REAL=5;       {M†xima freqÅància}
  nfun:INTEGER=1;     {N£mero de funáîes}
  dispersao:REAL=1e6;
  fatorw:REAL=1;
  fatorz:REAL=1;
  normalizar:BOOLEAN=TRUE;
  fase:BOOLEAN=TRUE;
  atraso:BOOLEAN=TRUE;
  alog:BOOLEAN=TRUE;
  rads:BOOLEAN=TRUE;
  grade:BOOLEAN=TRUE;
  modo1:BOOLEAN=TRUE;
TYPE
  polinomio=Array[0..Gmax] of REAL;
  raizes=Array[1..Gmax] of REAL;
  fdet=
    RECORD
      nome:STRING;
      ngrau,dgrau:INTEGER;
      Num:polinomio;
      Den:polinomio;
      cte,gmin,gmax,ag,bg:REAL;
      ga,fa,ta:INTEGER;
      Gan,Fas,Tg:ARRAY[0..xxmax] OF REAL;
    END;
  {A ordem aqui e na biblioteca determina a prioridade de inclusao na arvore normal}
  componente=(Capacitor,Resistor,FonteV,Amplificador,MOS,BJT,Girador,Indutor,Transformador,VCCS,FonteI,AmpOp);
  elemento=RECORD
    tipo:componente;
    nome:STRING[tamnome];
    no:ARRAY[1..4] of INTEGER;
    val:ARRAY[1..4] of REAL
  END;

CONST
  biblioteca:ARRAY[componente] of RECORD
    letra:CHAR;
    nnos:BYTE;
    nmno:ARRAY[1..4] of STRING[2];
    nval:BYTE;
    nmval:ARRAY[1..4] of STRING[3];
  END
  =(
    (letra:'C'; nnos:2; nmno:('a','b','',''); nval:1; nmval:('C','','','')),
    (letra:'R'; nnos:2; nmno:('a','b','',''); nval:1; nmval:('R','','','')),
    (letra:'Z'; nnos:2; nmno:('V-','V+','',''); nval:2; nmval:('Rs','Vs','','')),
    (letra:'A'; nnos:3; nmno:('e-','e+','s',''); nval:2; nmval:('GB','Ro','','')),
    (letra:'M'; nnos:3; nmno:('d','g','s',''); nval:2; nmval:('Gm','Gds','','')),
    (letra:'Q'; nnos:3; nmno:('c','b','e',''); nval:4; nmval:('hfe','hie','hre','hoe')),
    (letra:'Y'; nnos:4; nmno:('11','12','21','22'); nval:1; nmval:('Rg','','','')),
    (letra:'L'; nnos:2; nmno:('a','b','',''); nval:1; nmval:('L','','','')),
    (letra:'N'; nnos:4; nmno:('11','12','21','22'); nval:4; nmval:('L11','L22','M12','M21')),
    (letra:'G'; nnos:4; nmno:('I+','I-','V+','V-'); nval:1; nmval:('Gm','','','')),
    (letra:'I'; nnos:2; nmno:('I+','I-','',''); nval:1; nmval:('Is','','','')),
    (letra:'O'; nnos:3; nmno:('ea','eb','s',''); nval:0; nmval:('','','',''))
   );
  primeiro_tipo=Capacitor;
  ultimo_tipo=AmpOp;
VAR
  netlist:ARRAY[1..MaxEl] of elemento;
  Yr,Yi:ARRAY[0..MaxNos,0..MaxNos1] of REAL;
  Nr,Ni:ARRAY[1..MaxNos,0..MeioGm] of REAL;
  Dr,Di:ARRAY[0..MeioGm] of REAL;
  AX,BX:polinomio;
  C,L:ARRAY[0..MaxNosAntes] of INTEGER;
  Frq:ARRAY[0..xxmax] OF REAL;
  ReRaiz,ImRaiz:ARRAY[1..Gmax2] of REAL;
  vr,vi,f,fatord,Imag,tr,ti,t,t1,t2,sr,si,mden:REAL;
  amaxpt,npolos,graudefault,m,ii,ordem,graufft,ind,i,j,k,nos,nsaida,
  nosantes,numero,a1,b1,c1,xmin,xmax,ymin,ymax:INTEGER;
  placa,modo:INTEGER;
  prosseguir,recomecar,numerador,ok:BOOLEAN;
  rede,txt:STRING;
  sufixo:STRING[4];
  arquivo:TEXT;
  r:CHAR;
  funcao:ARRAY[1..mfuncoes] of fdet;
  DoisPi,LnDb,RadGraus:REAL;
LABEL
  CalcNum,CalcDen,Inicio,Pulo;

FUNCTION Sri(x:INTEGER):STRING;
VAR
  tmp:STRING;
BEGIN
  Str(x,tmp);
  Sri:=tmp
END;

FUNCTION Sre(x:REAL; t:INTEGER):STRING;
VAR
  tmp:STRING;
BEGIN
  Str(x:t,tmp);
  Sre:=tmp
END;

PROCEDURE ErroFatal(texto:STRING);
BEGIN
  WriteLn(tl,#13#10'[Erro]: '+texto);
  WriteLn(#10'Toque uma tecla...');
  r:=ReadKey;
  Halt
END;

PROCEDURE ImprimirTelaH;
VAR
  i,j,l,p:INTEGER;
  b7,b6,b5,b4,b3,b2,b1,b0,b,k:BYTE;
LABEL Fim;
BEGIN
  Write(arquivo,#27'@'#27'A'#8#27'l'#13#13);
  l:=0;
  REPEAT
    Write(arquivo,#27'L'#128#2);
    FOR i:=l TO l+79 DO BEGIN
      b7:=Mem[$b800:i];
      b6:=Mem[$b800:i+8192];
      b5:=Mem[$b800:i+80];
      b4:=Mem[$b800:i+8272];
      b3:=Mem[$b800:i+160];
      b2:=Mem[$b800:i+8352];
      b1:=Mem[$b800:i+240];
      b0:=Mem[$b800:i+8432];
      k:=128; j:=7;
      REPEAT
        b:=(b7 and k) shr j shl 7+(b6 and k) shr j shl 6+(b5 and k) shr j shl 5+
        +(b4 and k) shr j shl 4+(b3 and k) shr j shl 3
        +(b2 and k) shr j shl 2+(b1 and k) shr j shl 1+(b0 and k) shr j;
        IF l=7920 THEN b:=b and 224;
        Write(arquivo,Chr(b)); k:=k shr 1; Dec(j)
      UNTIL k<1;
    END;
    IF KeyPressed THEN BEGIN r:=ReadKey; GoTo Fim END;
    WriteLn(arquivo);
    l:=l+320
  UNTIL (l>7920);
 Fim:
  WriteLn(arquivo,#27'@');
END; {ImprimirTelaH}

PROCEDURE ImprimirTelaV;
VAR
  i,j:INTEGER;
LABEL Fim;
BEGIN
  Write(arquivo,#27'@'#27'A'#8#27'l'#7#13);
  FOR i:=0 TO 79 DO BEGIN
    Write(arquivo,#27'K'#144#1);
    j:=7920+i;
    REPEAT
      Write(arquivo,Chr(Mem[$B800:j+8192]),Chr(Mem[$B800:j+8192]),Chr(Mem[$B800:j]),Chr(Mem[$B800:j]));
      j:=j-80
    UNTIL j=i-80;
    IF KeyPressed THEN BEGIN r:=ReadKey; GoTo Fim END;
    WriteLn(arquivo);
  END;
 Fim:
  WriteLn(arquivo,#27'@');
END; {ImprimirTelaV}

FUNCTION Cmult(x1,x2,y1,y2:REAL):REAL;  {Multiplicacao complexa}
BEGIN
  Cmult:=x1*y1-x2*y2;
  Imag:=x1*y2+x2*y1
END; {Cmult}

FUNCTION Ex(x:REAL;t:REAL):REAL;
BEGIN Ex:=Exp(t*Ln(x)) END;

FUNCTION Inverso(x:INTEGER):INTEGER;  {Bit inverso}
VAR
  i,u:INTEGER;
BEGIN
  u:=0;
  i:=graufft shr 1;
  REPEAT
    IF Odd(x) THEN u:=u+i;
    i:=i shr 1;
    x:=x shr 1
  UNTIL x=0;
  Inverso:=u
END; {Inverso}

PROCEDURE FFT;  {"Fast Fourier Transform"}
VAR
  k1,m,k,j,u:INTEGER;
  x1,y1,t:REAL;
BEGIN
  FOR k:=ordem-1 DOWNTO 0  DO BEGIN
    k1:=Round(Ex(2,k));
    m:=0;
    REPEAT
      j:=Inverso(m div k1);
      x1:=Cos(DoisPi*j/graufft); y1:=-Sin(DoisPi*j/graufft);
      FOR j:=0 TO k1-1 DO BEGIN
        u:=j+m; i:=u+k1;
        t:=Cmult(AX[i],BX[i],x1,y1);
        AX[u]:=AX[u]+t; BX[u]:=BX[u]+Imag;
        AX[i]:=AX[u]-t-t;
        BX[i]:=BX[u]-Imag-Imag
      END;
      m:=m+k1 shl 1
    UNTIL m>graufft-1
  END;
  FOR i:=0 TO graufft-1 DO BEGIN
    j:=Inverso(i);
    IF j>i THEN BEGIN
      x1:=AX[i]; AX[i]:=AX[j]; AX[j]:=x1
    END
  END;
  FOR i:=0 TO graufft-1 DO AX[i]:=AX[i]/graufft;
END; {FFT}

PROCEDURE LeFdeT(x:INTEGER);
LABEL
  Denovo;

  PROCEDURE LePolinomio(nome:STRING; VAR grau:integer;
    VAR a:polinomio; VAR cte:REAL);
  BEGIN
    Assign(arquivo,nome);
    {$I-} Reset(arquivo); {$I+}
    ok:=(IOResult=0);
    IF not ok THEN BEGIN
      WriteLn(tl,#10'[*] Arquivo ["'+nome+'"] nÑo encontrado');
      Exit
    END;
    ReadLn(arquivo,grau);
    WriteLn(tl,'Grau: [',grau,']');
    FOR i:=0 TO grau DO BEGIN
      ReadLn(arquivo,a[i]);
      WriteLn(tl,'a([',i,']): ',a[i])
    END;
    IF not SeekEof(arquivo) THEN ReadLn(arquivo,cte)
    ELSE cte:=1;
    WriteLn(tl,'[Cte]:  ',cte);
    Close(arquivo);
  END; {LePolinomio}

BEGIN
  WITH funcao[x] DO BEGIN
    WriteLn(tl,#10'[InclusÑo] de uma curva no gr†fico:');
   Denovo:
    Write(tl,#10'[Nome],[?] ou [CR] (a £ltima): '); ReadLn(nome);
    IF nome='' THEN funcao[x]:=funcao[1]
    ELSE BEGIN
      IF nome='?' THEN BEGIN
        Diretorio;
        GoTo Denovo
      END;
      i:=nsaida;
      Write(#10'N¢ de sa°da desejado (ou 0)'); LerInt(i);
      IF i>0 THEN sufixo:='.n'+Sri(i)
      ELSE sufixo:='.n';
      WriteLn(tl,#10'[Numerador:]');
      LePolinomio(nome+sufixo,ngrau,Num,t1);
      IF not ok THEN Exit;
      WriteLn(tl,#10'[Denominador:]');
      LePolinomio(nome+'.d',dgrau,Den,t2);
      IF not ok THEN Exit;
      cte:=t1/t2;
      nome:=nome+sufixo
    END
  END
END; {LeFdeT}

PROCEDURE Lib(A:polinomio; n0:INTEGER; cte:REAL); {Acha raizes de um polinomio}
VAR
  n,nraizes:INTEGER;
  t,u,v,u1,v1,c1,c2,c3,d,t1:REAL;
  B:polinomio;
  Re,Im:raizes;

  PROCEDURE Let; {Là tolerÉncia}
  BEGIN
    t:=1.001*t1;
    Write(#10'TolerÉncia'); LerReal(t)
  END; {Let}

  PROCEDURE Resolve; {Calcula raizes de termo de 2o. grau}
  BEGIN
    d:=u*u-4*v;
    IF d>=0 THEN BEGIN
      Re[n]:=(-u+Sqrt(d))/2;
      Re[n-1]:=(-u-Sqrt(d))/2;
      Im[n]:=0; Im[n-1]:=0
    END
    ELSE BEGIN
      Re[n]:=-u/2; Re[n-1]:=-u/2;
      Im[n]:=Sqrt(-d)/2; Im[n-1]:=-Im[n]
    END;
    n:=n-2
  END; {Resolve}

  PROCEDURE PlotaRaizes;
  VAR
    immin,remin,delta,ay,by,ax,bx,w:REAL;
    base,xmax,ymax,x,y,csr:INTEGER;
    xa,ya:WORD;

    FUNCTION Limx(x:REAL):INTEGER;
    BEGIN
      IF x>=immin+delta THEN Limx:=xmax
      ELSE IF x<=immin THEN Limx:=0
        ELSE Limx:=Round(ax*x+bx)
    END;

    FUNCTION Limy(y:REAL):INTEGER;
    BEGIN
      IF y>=remin+delta THEN Limy:=0
      ELSE IF y<=remin THEN Limy:=ymax
        ELSE Limy:=Round(ay*y+by)
    END;

  BEGIN
    Window(1,1,80,25);
    immin:=0.1;
    FOR i:=1 TO nraizes DO BEGIN
      IF Abs(ReRaiz[i])>immin THEN immin:=Abs(ReRaiz[i]);
      IF Abs(ImRaiz[i])>immin THEN immin:=Abs(ImRaiz[i])
    END;
    immin:=-Ex(2,Trunc(Ln(immin)/Ln(2))+1);
    remin:=immin;
    delta:=-2*immin;
    csr:=1;
    REPEAT
      SetGraphMode(modo);
      SetTextStyle(SmallFont,HorizDir,4);
      ymax:=GetMaxY;
      GetAspectRatio(xa,ya);
      xmax:=Trunc(ymax*ya/xa);
      base:=xmax+4;
      ay:=-ymax/delta; by:=ymax-ay*remin;
      ax:=xmax/delta; bx:=-ax*immin;
      RemoveSprite;
      SetFillStyle(EmptyFill,1);
      SetLineStyle(DottedLn,0,NormWidth);
      SetColor(cor[2]);
      i:=Limx(0);
      Line(i,0,i,ymax);
      i:=Limy(0);
      Line(0,i,xmax,i);
      OutTextXY(base,0,'Re:'+Sre(immin,10));
      OutTextXY(base,8,'   '+Sre(immin+delta,10));
      OutTextXY(base,16,'Im:'+Sre(remin,10));
      OutTextXY(base,24,'   '+Sre(remin+delta,10));
      SetLineStyle(SolidLn,0,NormWidth);
      SetColor(cor[3]);
      Rectangle(0,0,xmax,ymax);
      OutTextXY(base,40,rede);
      IF numerador THEN OutTextXY(base,56,'No: '+Sri(nsaida));
      FOR i:=1 TO nraizes DO BEGIN
        x:=Limx(ReRaiz[i]);
        y:=Limy(ImRaiz[i]);
        SetColor(cor[3]);
        IF (i>npolos) THEN Circle(x,y,4)
        ELSE BEGIN
          SetColor(cor[1]);
          Line(x-2,y-2,x+2,y+2);
          Line(x-2,y+2,x+2,y-2)
        END
      END;
      REPEAT
        PutsPrite(Limx(ReRaiz[csr]),Limy(ImRaiz[csr]));
        Bar(base,151,GetMaxX,GetMaxY);
        SetColor(cor[1]);
        MoveTo(base,151); IF csr>npolos THEN OutText('Zero:') ELSE OutText('Polo:');
        OutTextXY(base,166,'R:'+Sre(ReRaiz[csr],11));
        OutTextXY(base,174,'I:'+Sre(ImRaiz[csr],11));
        w:=Sqrt(Sqr(ReRaiz[csr])+Sqr(ImRaiz[csr]));
        OutTextXY(base,182,'w:'+Sre(w,11));
        MoveTo(base,190); OutText('Q:');
        IF Abs(ReRaiz[csr])>1e-8 THEN BEGIN
          Str(-0.5*w/ReRaiz[csr]:11:3,txt);
          OutText(txt)
        END
        ELSE OutText(' infinito');
        r:=UpKey;
        CASE r OF
          #9,#13:IF csr<nraizes THEN Inc(csr) ELSE csr:=1;
          #8:IF csr>1 THEN Dec(csr) ELSE csr:=nraizes;
          #0:BEGIN
               r:=ReadKey;
               CASE r OF
                 'M':immin:=immin+delta/4;
                 'K':immin:=immin-delta/4;
                 'H':remin:=remin+delta/4;
                 'P':remin:=remin-delta/4
               END
             END;
         '-':BEGIN
               immin:=immin-delta/2;
               remin:=remin-delta/2;
               delta:=delta*2
             END;
         '+':BEGIN
               immin:=immin+delta/4;
               remin:=remin+delta/4;
               delta:=delta/2;
             END;
         'I','P':IF placa=CGA THEN BEGIN
               OutTextXY(base,72,'Imprimir:');
               OutTextXY(base,88,'Impressora');
               OutTextXY(base,96,'Arquivo');
               OutTextXY(base,104,'Nenhum');
               r:=UpKey;
               IF (r='I') or (r='A') THEN BEGIN
                 IF r='I' THEN txt:='Lst:'
                 ELSE txt:=rede+'.s'+Sri(nsaida);
                 Assign(arquivo,txt);
                 Rewrite(arquivo);
                 Bar(base,88,GetMaxX,112);
                 OutTextXY(base,88,'Horizontal');
                 OutTextXY(base,96,'Vertical');
                 r:=UpKey;
                 Bar(base,72,GetMaxX,104);
                 IF r='V' THEN ImprimirTelaV
                 ELSE ImprimirTelaH;
                 IF txt<>'Lst:' THEN BEGIN
                   OutTextXY(base,72,'Arquivo');
                   OutTextXY(base,80,txt);
                   OutTextXY(base,88,'escrito');
                   Delay(2000);
                 END;
                 Close(arquivo)
               END;
               Bar(base,72,GetMaxX,112);
               r:=' '
             END
        END
      UNTIL r in [#27,'M','K','H','P','+','-'];
    UNTIL r=#27;
    RestoreCrtMode;
  END; {PlotaRaizes}

  PROCEDURE ListaRaizes;
  BEGIN
    Write(tl,#10'[Ra°zes ]');
    IF normalizar THEN WriteLn('normalizadas') ELSE WriteLn; WriteLn;
    FOR i:=1 TO n0 DO BEGIN
      WriteLn(tl,'x([',i:2,'])=',Re[i]);
      IF Im[i]<>0 THEN
        WriteLn('      ',Im[i],'j')
    END;
    WriteLn
  END;

  PROCEDURE Termina; {Justamente isto}
  VAR
    Sair:BOOLEAN;
  BEGIN
    Sair:=FALSE;
    IF numerador THEN nraizes:=npolos+n0 ELSE
      BEGIN npolos:=n0; nraizes:=n0 END;
    FOR i:=1 TO n0 DO BEGIN
      j:=nraizes-n0+i;
      Re[i]:=Re[i]*fatord;
      Im[i]:=Im[i]*fatord;
      ReRaiz[j]:=Re[i];
      ImRaiz[j]:=Im[i]
    END;
    ListaRaizes;
    REPEAT
      WriteLn(tl,'[L]istar [S]alvar [P]lotar ra°zes [C]ontinuar');
      REPEAT r:=UpKey UNTIL r IN ['L','S','P','C'];
      CASE r OF
        'L':ListaRaizes;
        'S':BEGIN
              IF numerador THEN sufixo:='.z'+Sri(nsaida)
              ELSE sufixo:='.p';
              Assign(arquivo,rede+sufixo);
              ReWrite(arquivo);
              WriteLn(arquivo,n0);
              FOR j:=1 TO n0 DO WriteLn(arquivo,Re[j],' ',Im[j]);
              WriteLn(arquivo,cte);
              Close(arquivo);
              WriteLn(tl,#10'Ra°zes salvas como [',rede+sufixo,']'#10)
            END;
        'P':PlotaRaizes;
        'C':Sair:=TRUE;
      END;
    UNTIL Sair
  END; {Termina}

BEGIN
  t1:=1.0e-11; v:=1; u:=1.1;
  IF n0=0 THEN BEGIN WriteLn(#10'NÑo h† ra°zes finitas'); Exit END;
  IF n0>2 THEN Let;
  n:=n0;
  WHILE (A[0]=0) and (n>1) DO BEGIN
    Re[n]:=0; Im[n]:=0;
    Dec(n);
    For j:=0 TO n DO A[j]:=A[j+1]
  END;
  REPEAT
    IF n=1 THEN BEGIN
      Re[1]:=-A[0]/A[1]; Im[1]:=0;
      Termina;
      Exit
    END;
    IF n=2 THEN BEGIN
      u:=A[1]/A[2]; v:=A[0]/A[2];
      Resolve;
      Termina;
      Exit
    END;
    i:=0;
    REPEAT
      IF i>100 THEN BEGIN
        WriteLn(#10'Problemas de convergància:');
        Let; i:=0
      END;
      Inc(i);
      B[n]:=A[n]; c2:=B[n];
      B[n-1]:=A[n-1]-u*B[n];
      c1:=B[n-1]-u*c2;
      FOR j:=n-2 DOWNTO 1 DO BEGIN
        c3:=c2; c2:=c1;
        B[j]:=A[j]-u*B[j+1]-v*B[j+2];
        c1:=B[j]-u*c2-v*c3
      END;
      B[0]:=A[0]-u*B[1]-v*B[2];
      d:=c2*c2-c1*c3;
      u1:=(B[0]*c3-B[1]*c2)/d;
      v1:=(B[1]*c1-B[0]*c2)/d;
      u:=u-u1; v:=v-v1;
      t1:=Abs(u1)+Abs(v1);
    UNTIL t1<t;
    Resolve;
    FOR j:=0 TO n DO A[j]:=B[j+2]
  UNTIL FALSE;
END; {Lib}

PROCEDURE Grafico;
CONST
  unid:ARRAY[BOOLEAN] OF STRING[5]=('Hz','rad/s');
VAR
  ax,bx,af,bf,at,bt,aw,bw,dx,w,a1,a2,b1,b2,da1,da2,db1,db2,f,wmin,wmax:REAL;
  xa,xq,yq,atual,ultpt,maxpt,ix,csr:INTEGER;
  log:BOOLEAN;
LABEL
  MudarEscalas,Continuar,Retracar,Recalcular,Cursor;

  PROCEDURE ApagaMsg;
  BEGIN
    Bar(0,ymax+1,GetMaxX,GetMaxY)
  END;

  PROCEDURE TracarEscalas;
  BEGIN
    Bar(0,0,xmin-1,ymax);
    i:=xmin-TextWidth('xxx');
    j:=(ymax+ymin) div 2-4;
    IF atraso THEN BEGIN
      SetColor(cor[3]);
      Str(tmax:7:2,txt);
      OutTextXY(xmin-TextWidth(txt),ymin+16,txt);
      Str(tmin:7:2,txt);
      OutTextXY(xmin-TextWidth(txt),ymax-25,txt);
      OutTextXY(i,j-8,'s');
    END;
    IF fase THEN BEGIN
      SetColor(cor[4]);
      Str(fmax:7:2,txt);
      OutTextXY(xmin-TextWidth(txt),ymin+8,txt);
      Str(fmin:7:2,txt);
      OutTextXY(xmin-TextWidth(txt),ymax-17,txt);
      OutTextXY(i,j+8,'gr');
    END;
    SetColor(cor[1]);
    Str(funcao[atual].gmax:7:2,txt);
    OutTextXY(xmin-TextWidth(txt),ymin,txt);
    Str(funcao[atual].gmin:7:2,txt);
    OutTextXY(xmin-TextWidth(txt),ymax-9,txt);
    OutTextXY(i,j,'dB');
    SetColor(cor[1]);
    ApagaMsg;
    Str(wmin:11,txt);
    OutTextXY(xmin,ymax,txt);
    Str(wmax:11,txt);
    OutTextXY(xmax-TextWidth(txt),ymax,txt);
    OutTextXY((xmax+xmin-TextWidth(unid[rads])) div 2,ymax,unid[rads]);
  END; {TracarEscalas}

  PROCEDURE ImprimirTabela;
  BEGIN
    WITH funcao[1] DO BEGIN
      WriteLn(arquivo,'IFFT - Versao ',versao,' - Rede: ',rede);
      WriteLn(arquivo);
      WriteLn(arquivo,'# Resp. em freq. (',unid[rads],'): Saida ',nsaida,' (Frq, Mod, Fas, Atr)');
      FOR i:=0 TO ultpt DO BEGIN
        Write(arquivo,Frq[i]:14:9);
        WriteLn(arquivo,' ',Gan[i]:14:9,' ',Fas[i]:14:9,' ',Tg[i]:14:9);
      END;
      WriteLn(arquivo)
    END
  END {ImprimirTabela};

  PROCEDURE SalvarTela;
  BEGIN
    SetColor(cor[1]);
    ApagaMsg;
    OutTextXY(xmin,ymax,'Imprimir: Impressora Arquivo Nenhum');
    r:=UpKey;
    IF (r='I') or (r='A') THEN BEGIN
      IF r='I' THEN txt:='Lst:'
      ELSE txt:=rede+'.g'+Sri(nsaida);
      IF txt<>'Lst:' THEN BEGIN
        ApagaMsg;
        OutTextXY(xmin,ymax,'Criando arquivo '+txt);
        Delay(2000)
      END;
      Assign(arquivo,txt);
      Rewrite(arquivo);
      ApagaMsg;
      IF placa=CGA THEN BEGIN
        OutTextXY(xmin,ymax,'Horizontal Vertical Tabela');
        r:=UpKey;
        TracarEscalas;
        IF r='V' Then ImprimirTelaV
        ELSE IF r='H' THEN ImprimirTelaH
        ELSE ImprimirTabela
      END
      ELSE ImprimirTabela;
      Close(arquivo)
    END;
    TracarEscalas
  END; {SalvarTela}

  FUNCTION Limita(a,b,y:REAL):INTEGER;
  BEGIN
    y:=a*y+b;
    IF y<ymin THEN Limita:=ymin
    ELSE IF y>ymax THEN Limita:=ymax
      ELSE Limita:=Round(y)
  END; {Limita}

  FUNCTION Cdiv(a1,a2,b1,b2:REAL):REAL;
  BEGIN
    IF (b1=0) or (b2=0) THEN BEGIN
      t:=1/(Sqr(b1)+Sqr(b2));
      Cdiv:=(a1*b1+a2*b2)*t; Imag:=(a2*b1-a1*b2)*t
    END
    ELSE BEGIN
      t:=1/(b1/b2+b2/b1);
      Cdiv:=(a1/b2+a2/b1)*t; Imag:=(a2/b2-a1/b1)*t
    END;
  END;

BEGIN {Grafico}
  Window(1,1,80,25);
  wmin:=awmin; wmax:=awmax;
  maxpt:=amaxpt;
  log:=alog;
  ultpt:=-1;
  xq:=xmin+8; yq:=ymax-49;
  GoTo Recalcular;
 MudarEscalas:
  Write(#10'FreqÅàncias em Rad/s'); LerBool(rads);
  Write('Usar escala Logar°tmica'); LerBool(log);
  Write('Traáar grade'); LerBool(grade);
  Write('Plotar curvas de fase'); LerBool(fase);
  Write('Plotar curvas de atraso de grupo'); LerBool(atraso);
  Write(#10'M°nima freqÅància (',unid[rads],')'); LerReal(wmin);
  Write('M†xima freqÅància (',unid[rads],')'); LerReal(wmax);
  FOR i:=1 TO nfun DO WITH funcao[i] DO BEGIN
    Write(tl,#10'M°nimo ganho ([',i,']) (dB)'); LerReal(gmin);
    Write(tl,'M†ximo ganho ([',i,']) (dB)'); LerReal(gmax);
  END;
  Write(tl,#10'M°nima fase (gr)'); LerReal(fmin);
  Write(tl,'M†xima fase (gr)'); LerReal(fmax);
  Write(tl,#10'M°nimo atraso de grupo (s)'); LerReal(tmin);
  Write(tl,'M†ximo atraso de grupo (s)'); LerReal(tmax);
  Write(#10'N£mero de segmentos no gr†fico'); LerInt(maxpt);
 Recalcular:
  IF maxpt>xxmax THEN maxpt:=xxmax;
  IF maxpt<1 THEN maxpt:=1;
  IF (wmin<=0) or (wmax<=0) THEN log:=FALSE;
  IF not((wmin=awmin) and (wmax=awmax) and (maxpt=amaxpt) and (ultpt<>-1) and (log=alog)) THEN ultpt:=-1;
  awmin:=wmin; awmax:=wmax; amaxpt:=maxpt; alog:=log;
  IF log THEN BEGIN
    dx:=Ex(wmax/wmin,1/maxpt);
    aw:=(xmax-xmin)/Ln(wmax/wmin);
    bw:=xmax-aw*Ln(wmax)
  END
  ELSE BEGIN
    dx:=(wmax-wmin)/maxpt;
    aw:=(xmax-xmin)/(wmax-wmin);
    bw:=xmax-aw*wmax
  END;
  ax:=(xmax-xmin)/maxpt;
  bx:=xmin;
  atual:=1;
  csr:=0;
 Retracar:
  FOR i:=1 TO nfun DO WITH funcao[i] DO BEGIN
    ag:=(ymax-ymin)/(gmin-gmax);
    bg:=ymax-ag*gmin
  END;
  af:=(ymax-ymin)/(fmin-fmax);
  bf:=ymax-af*fmin;
  at:=(ymax-ymin)/(tmin-tmax);
  bt:=ymax-at*tmin;
  SetGraphMode(modo);
  SetFillStyle(emptyfill,1);
  SetTextStyle(SmallFont,HorizDir,4);
  IF grade THEN BEGIN
    SetLineStyle(DottedLn,0,NormWidth);
    SetColor(cor[2]);
    IF (wmax-wmin>wmin) and log THEN t1:=wmin ELSE t1:=wmax-wmin;
    t1:=Ex(10,Round(Ln(t1)/Ln(10)-0.499999)); {incremento inicial}
    t2:=Round(wmin/t1+0.5)*t1; {primeira freqÅància}
    WHILE t2<wmax DO
      IF log THEN BEGIN
        IF Round(t2/t1)=10 THEN BEGIN
          t1:=10*t1;
          SetColor(cor[3]);
        END;
        i:=Round(aw*Ln(t2)+bw);
        Line(i,ymin,i,ymax);
        t2:=t2+t1;
        SetColor(cor[2]);
      END
      ELSE BEGIN
        i:=Round(aw*t2+bw);
        Line(i,ymin,i,ymax);
        t2:=t2+t1
      END;
    WITH Funcao[atual] DO BEGIN
      t1:=gmax-gmin;
      t1:=Ex(10,Round(Ln(t1)/Ln(10)-0.5)); {incremento inicial}
      t2:=Round(gmin/t1+0.5)*t1; {primeiro ganho}
      WHILE t2<gmax DO BEGIN
        i:=Limita(ag,bg,t2);
        Line(xmin,i,xmax,i);
        t2:=t2+t1
      END
    END;
  END;
  SetLineStyle(SolidLn,0,NormWidth);
  SetColor(cor[1]);
  Rectangle(xmin,ymin,xmax,ymax);
  RemoveSprite;
  TracarEscalas;
  f:=wmin; ix:=0;
  REPEAT
    IF ix>ultpt THEN BEGIN
      IF rads THEN w:=f ELSE w:=DoisPi*f;
      FOR i:=1 TO nfun DO
        WITH funcao[i] DO BEGIN
          b1:=0; b2:=0; db1:=0; db2:=0;
          FOR j:=dgrau DOWNTO 0 DO
             BEGIN t:=b1*w; b1:=Den[j]-w*b2; b2:=t END;
          FOR j:=dgrau DOWNTO 1 DO
             BEGIN t:=db1*w; db1:=j*Den[j]-w*db2; db2:=t END;
          a1:=0; a2:=0; da1:=0; da2:=0;
          FOR j:=ngrau DOWNTO 0 DO
            BEGIN t:=a1*w; a1:=Num[j]-w*a2; a2:=t END;
          FOR j:=ngrau DOWNTO 1 DO
             BEGIN t:=da1*w; da1:=j*Num[j]-w*da2; da2:=t END;
          sr:=cte*Cdiv(a1,a2,b1,b2);
          si:=cte*Imag;
          IF sr=0 THEN BEGIN
            IF si=0 THEN si:=1e-11;
            sr:=si*1.e-11
          END;
          Fas[ix]:=Arctan(si/sr)*RadGraus;
          Gan[ix]:=Ln(Sqr(sr)+Sqr(si))*LnDb;
          Tg[ix]:=Cdiv(db1,db2,b1,b2)-Cdiv(da1,da2,a1,a2);
          IF sr<0 THEN
            IF si>0 THEN Fas[ix]:=180+Fas[ix] ELSE Fas[ix]:=Fas[ix]-180;
        END;
      Frq[ix]:=f
    END;
    j:=Round(ix*ax+bx);
    FOR i:=nfun DOWNTO 1 DO WITH funcao[i] DO BEGIN
      IF modo1 THEN SetColor(cor[1]) ELSE SetColor(cor[i]);
      k:=Limita(ag,bg,Gan[ix]);
      IF ix>0 THEN Line(xa,ga,j,k);
      ga:=k;
      IF fase THEN BEGIN
        IF modo1 THEN SetColor(cor[4]) ELSE SetColor(cor[i]);
        k:=Limita(af,bf,Fas[ix]);
        IF ix>0 THEN Line(xa,fa,j,k);
        fa:=k
      END;
      IF atraso THEN BEGIN
        IF modo1 THEN SetColor(cor[3]) ELSE SetColor(cor[i]);
        k:=Limita(at,bt,Tg[ix]);
        IF ix>0 THEN Line(xa,ta,j,k);
        ta:=k
      END;
    END;
    xa:=j;
    IF KeyPressed THEN BEGIN
      IF ix>ultpt THEN ultpt:=ix;
      GoTo Cursor;
    END;
   Continuar:
    IF log THEN f:=f*dx ELSE f:=f+dx;
    Inc(ix)
  UNTIL ix>maxpt;
  ix:=maxpt; ultpt:=ix;
 Cursor:
  REPEAT
    CASE UpKey OF
      #0:CASE ReadKey OF
           'K':IF csr>=1 THEN Dec(csr);
           #115:IF csr>=10 THEN Dec(csr,10);
           'M':IF csr<=ix-1 THEN Inc(csr);
           #116:IF csr<=ix-10 THEN Inc(csr,10);
           'H':BEGIN
                 FOR i:=1 TO nfun DO WITH funcao[i] DO BEGIN
                   t:=(gmax-gmin)/2;
                   gmin:=gmin+t;
                   gmax:=gmax+t
                 END;
                 GoTo Retracar
               END;
           'P':BEGIN
                 FOR i:=1 TO nfun DO WITH funcao[i] DO BEGIN
                   t:=(gmax-gmin)/2;
                   gmin:=gmin-t;
                   gmax:=gmax-t
                 END;
                 GoTo Retracar
               END
           ELSE GoTo Cursor
         END;
       '-':BEGIN
             FOR i:=1 TO nfun DO WITH funcao[i] DO gmax:=2*gmax-gmin;
             GoTo Retracar
           END;
       '+':BEGIN
             FOR i:=1 TO nfun DO WITH funcao[i] DO gmax:=(gmax+gmin)/2;
             GoTo Retracar
           END;
        #9:BEGIN IF atual<nfun THEN Inc(atual) ELSE atual:=1; TracarEscalas END;
        #8:BEGIN IF atual>1 THEN Dec(atual) ELSE atual:=nfun; TracarEscalas END;
       #27:BEGIN
             RestoreCrtMode;
             WriteLn(tl,'[M]udar escalas [C]ontinuar');
             REPEAT r:=UpKey UNTIL r in ['M','C'];
             IF r='M'THEN GoTo Mudarescalas;
             Exit
           END;
       #13:IF ix<maxpt THEN BEGIN PutSprite(-10,-10); GoTo Continuar END;
       'I','P':BEGIN SalvarTela; GoTo Cursor END;
       'G':BEGIN grade:=not grade; GoTo Retracar END;
       'F':BEGIN fase:=not fase; GoTo Retracar END;
       'T':BEGIN atraso:=not atraso; GoTo Retracar END;
       'L':BEGIN
            log:=not log;
            GoTo Recalcular
          END;
      'R':BEGIN
            IF log THEN wmax:=wmin*Sqr(wmax/wmin) ELSE wmax:=wmin+(wmax-wmin)*2;
            GoTo Recalcular
          END;
      'A':BEGIN
            IF log THEN wmax:=wmin*Sqrt(wmax/wmin) ELSE wmax:=wmin+(wmax-wmin)/2;
            GoTo Recalcular
          END;
      '>':BEGIN
            IF log THEN BEGIN t:=Sqrt(Sqrt(wmax/wmin)); wmin:=wmin*t; wmax:=wmax*t END
            ELSE BEGIN t:=(wmax-wmin)/4; wmin:=wmin+t; wmax:=wmax+t END;
            GoTo Recalcular
          END;
      '<':BEGIN
            IF log THEN BEGIN t:=Sqrt(Sqrt(wmax/wmin)); wmin:=wmin/t; wmax:=wmax/t END
            ELSE BEGIN t:=(wmax-wmin)/4; wmin:=wmin-t; wmax:=wmax-t END;
            GoTo Recalcular
          END;
      'C':BEGIN
            modo1:=not modo1;
            GoTo Retracar
          END
      ELSE GoTo Cursor
    END;
    WITH funcao[atual] DO BEGIN
      PutSprite(Round(ax*csr+bx),Limita(ag,bg,Gan[csr]));
      SetColor(cor[3]);
      Bar(xq-1,yq+1,xq+106,yq+43);
      Rectangle(xq-2,yq,xq+107,yq+44);
      SetColor(cor[1]);
      OutTextXY(xq,yq,nome+' ('+Sri(atual)+')');
      OutTextXY(xq,yq+8,Sre(Frq[csr],12)+' '+unid[rads]);
      Str(Gan[csr]:13:8,txt); OutTextXY(xq,yq+16,txt+' dB');
      Str(Fas[csr]:13:8,txt); OutTextXY(xq,yq+24,txt+' gr');
      Str(Tg[csr]:13:8,txt); OutTextXY(xq,yq+32,txt+' s')
    END
  UNTIL FALSE
END; {Grafico}

PROCEDURE Admitancia(a,b:REAL; n1,n2:INTEGER);
BEGIN
  a:=a*fatorz; b:=b*fatorz;
  Yr[L[n1],C[n1]]:=Yr[L[n1],C[n1]]+a;
  Yr[L[n2],C[n2]]:=Yr[L[n2],C[n2]]+a;
  Yr[L[n1],C[n2]]:=Yr[L[n1],C[n2]]-a;
  Yr[L[n2],C[n1]]:=Yr[L[n2],C[n1]]-a;
  Yi[L[n1],C[n1]]:=Yi[L[n1],C[n1]]+b;
  Yi[L[n2],C[n2]]:=Yi[L[n2],C[n2]]+b;
  Yi[L[n1],C[n2]]:=Yi[L[n1],C[n2]]-b;
  Yi[L[n2],C[n1]]:=Yi[L[n2],C[n1]]-b
END; {Admitancia}

PROCEDURE TransAdmitancia(a,b:REAL; n1,n2,n3,n4:INTEGER);
BEGIN
  a:=a*fatorz; b:=b*fatorz;
  Yr[L[n1],C[n3]]:=Yr[L[n1],C[n3]]+a;
  Yr[L[n2],C[n4]]:=Yr[L[n2],C[n4]]+a;
  Yr[L[n1],C[n4]]:=Yr[L[n1],C[n4]]-a;
  Yr[L[n2],C[n3]]:=Yr[L[n2],C[n3]]-a;
  Yi[L[n1],C[n3]]:=Yi[L[n1],C[n3]]+b;
  Yi[L[n2],C[n4]]:=Yi[L[n2],C[n4]]+b;
  Yi[L[n1],C[n4]]:=Yi[L[n1],C[n4]]-b;
  Yi[L[n2],C[n3]]:=Yi[L[n2],C[n3]]-b
END; {TransAdmitancia}

PROCEDURE MontarSistema;
BEGIN
  FOR i:=0 TO nos DO
    FOR j:=0 TO nos+1 DO BEGIN Yr[i,j]:=0; Yi[i,j]:=0 END;
  FOR i:=1 to numero DO
  WITH netlist[i] DO BEGIN
    CASE tipo OF
      Resistor:Admitancia(1/val[1],0,no[1],no[2]);
      Indutor:BEGIN
          t:=val[1]*(Sqr(sr)+Sqr(si));
          Admitancia(sr/t,-si/t,no[1],no[2])
        END;
      Capacitor:Admitancia(sr*val[1],si*val[1],no[1],no[2]);
      Amplificador:BEGIN
          { Y12=-GB/sRo; Y22=1/Ro }
          Admitancia(1/val[2],0,no[3],0);
          t:=val[1]/val[2]/(Sqr(sr)+Sqr(si));
          TransAdmitancia(t*sr,-t*si,0,no[3],no[2],no[1]);
        END;
      VCCS:TransAdmitancia(val[1],0,no[1],no[2],no[3],no[4]);
      FonteV:BEGIN {Fonte com resistor sÇrie}
          t:=val[2]/val[1];
          Yr[L[no[1]],nos+1]:=Yr[L[no[1]],nos+1]-t*fatorz;
          Yr[L[no[2]],nos+1]:=Yr[L[no[2]],nos+1]+t*fatorz;
          Admitancia(1/val[1],0,no[1],no[2])
        END;
      FonteI:BEGIN {Fonte de corrente}
          t:=val[1];
          Yr[L[no[1]],nos+1]:=Yr[L[no[1]],nos+1]-t*fatorz;
          Yr[L[no[2]],nos+1]:=Yr[L[no[2]],nos+1]+t*fatorz;
        END;
      Girador:BEGIN
          { Y12=1/R Y21=-1/R }
          t:=1/val[1];
          TransAdmitancia(t,0,no[4],no[3],no[1],no[2]);
          TransAdmitancia(t,0,no[1],no[2],no[3],no[4]);
        END;
      Transformador:BEGIN
          { Y11=L2/sDet(L) }
          { Y22=L1/sDet(L) }
          { Y12=-M12/sDet(L) }
          { Y21=-M21/sDet(L) }
          t:=(val[1]*val[2]-val[3]*val[4])*(Sqr(sr)+Sqr(si));
          t1:=val[2]/t;  {Y11}
          Admitancia(t1*sr,-t1*si,no[1],no[2]);
          t1:=val[1]/t;  {Y22}
          Admitancia(t1*sr,-t1*si,no[3],no[4]);
          t1:=-val[3]/t; {Y12}
          TransAdmitancia(t1*sr,-t1*si,no[1],no[2],no[3],no[4]);
          t1:=-val[4]/t; {Y21}
          TransAdmitancia(t1*sr,-t1*si,no[3],no[4],no[1],no[2]);
        END;
      MOS:BEGIN
            Transadmitancia(val[1],0,no[1],no[3],no[2],no[3]); {Gm}
            Admitancia(val[2],0,no[2],no[3]) {Gds}
          END;
      BJT:BEGIN
          Admitancia(1/val[2],0,no[2],no[3]); {hie}
          Admitancia(val[4],0,no[1],no[3]);   {hoe}
          TransAdmitancia(val[1]/val[2],0,no[1],no[3],no[2],no[3]);  {hfe/hie}
          TransAdmitancia(val[3]/val[2],0,no[3],no[2],no[1],no[3]);  {hre/hie}
          TransAdmitancia(val[3]*val[1]/val[2],0,no[1],no[3],no[3],no[1]); {hre*hfe/hie}
        END;
    END
  END
END; {MontarSistema}

PROCEDURE AcharOrdem;
VAR
  ok:BOOLEAN;
  temp:elemento;
  arvore:ARRAY[0..MaxNosAntes] OF INTEGER;
  marcado:ARRAY[1..MaxEl] OF WORD;
  nosarvore,e:INTEGER;
  tipo_em_teste:componente;

  PROCEDURE TentarIncluir(no1,no2,ramo:INTEGER);
  VAR
    i:INTEGER;
    um,dois:BOOLEAN;
  BEGIN
    IF (marcado[e] and ramo)=ramo THEN Exit;
    um:=FALSE; dois:=FALSE;
    FOR i:=0 TO nosarvore DO BEGIN
      IF arvore[i]=L[no1] THEN um:=TRUE;
      IF arvore[i]=L[no2] THEN dois:=TRUE
    END;
    IF um xor dois THEN BEGIN
      Inc(nosarvore);
      ok:=TRUE;
      IF um THEN arvore[nosarvore]:=L[no2]
      ELSE arvore[nosarvore]:=L[no1];
      Inc(marcado[e],ramo);
      WITH netlist[e] DO
        WriteLn(tl,'[',nome,'], n¢s ',no1,' e ',no2);
    END
  END;

BEGIN
  nosarvore:=0;
  arvore[0]:=0;
  FOR e:=1 TO numero DO marcado[e]:=0;
  WriteLn('Ramos da †rvore normal:');
  REPEAT
    tipo_em_teste:=primeiro_tipo;
    REPEAT
      e:=1; ok:=FALSE;
      REPEAT
        WITH netlist[e] DO IF (tipo=tipo_em_teste) THEN
          CASE tipo OF
            Resistor,Indutor,Capacitor,FonteV,FonteI,VCCS,Girador,Transformador:BEGIN
                TentarIncluir(no[1],no[2],1);
                IF tipo in [VCCS,Girador,Transformador] THEN TentarIncluir(no[3],no[4],2)
              END;
            Amplificador:TentarIncluir(0,no[3],1);
            BJT,MOS:BEGIN
              TentarIncluir(no[1],no[3],1);
              IF tipo=BJT THEN TentarIncluir(no[2],no[3],2)
            END
          END;
        Inc(e)
      UNTIL (e>numero) or ok;
      Inc(tipo_em_teste);
    UNTIL ok or (tipo_em_teste>FonteI);
    IF not ok and (tipo_em_teste>FonteI) THEN ErroFatal('Parte da rede nao esta aterrada');
  UNTIL nosarvore=nos;
  graudefault:=0; ind:=0;
  FOR e:=1 TO numero DO WITH NetList[e] DO CASE tipo OF
    Capacitor:IF marcado[e]=1 THEN BEGIN
      Inc(graudefault)
    END;
    Indutor:BEGIN
      Inc(ind);
        IF marcado[e]=0 THEN BEGIN
          Inc(graudefault)
        END
      END;
    Amplificador:BEGIN
      Inc(graudefault); Inc(ind)
    END;
    Transformador:BEGIN
      IF marcado[e]=0 THEN Inc(graudefault,2)
      ELSE IF marcado[e]<3 THEN Inc(graudefault);
      Inc(ind,2)
    END;
    {VCCS,Girador,FonteI:IF marcado[e]>0 THEN ttysw_output(ttymsg,'* '+nome+' pode tornar o circuito singular'+fl);}
  END;
  WriteLn(tl,'M†xima ordem de complexidade: [',graudefault,']');
  WriteLn(tl,'N£mero de elementos em 1/s: [',ind,']');
END;

PROCEDURE LerCircuito;
VAR
  leutudo:BOOLEAN;
  cp:componente;

LABEL Achou;

BEGIN
  ReadLn(arquivo,nosantes); nos:=nosantes;
  WriteLn(tl,#10'N£mero de n¢s: [',nosantes,']');
  IF nosantes>MaxNosAntes THEN ErroFatal('O m†ximo n£mero de n¢s Ç ['+Sri(MaxNosAntes)+']');
  FOR i:=0 TO nosantes DO BEGIN C[i]:=i; L[i]:=i END;
  WriteLn(tl,#10'[DescriáÑo do circuito:]'#10);
  numero:=1;
  REPEAT
    IF numero>MaxEl THEN ErroFatal('O m†ximo n£mero de elementos efetivos Ç ['+Sri(MaxEl)+']');
    WITH netlist[numero] DO BEGIN
      nome:='';
      REPEAT
        Read(arquivo,r);
        IF r<>' ' THEN nome:=nome+UpCase(r)
      UNTIL (r=' ') or (Length(nome)=tamnome);
      nome[1]:=UpCase(nome[1]);
      Write(tl,'[',nome,']: ');
      FOR cp:=primeiro_tipo TO ultimo_tipo DO
        WITH biblioteca[cp] DO
          IF nome[1]=letra THEN BEGIN
            leutudo:=TRUE;
            tipo:=cp;
            FOR i:=1 TO nnos DO Read(arquivo,no[i]);
            FOR i:=1 TO nval DO
              IF not SeekEoln(arquivo) THEN Read(arquivo,val[i])
              ELSE leutudo:=FALSE;
            ReadLn(arquivo);
            IF not leutudo THEN CASE tipo OF
              FonteV:val[2]:=1;
              Transformador:val[4]:=val[3]
            END;
            FOR i:=1 TO nnos DO Write(tl,'[',no[i],'](',nmno[i],') ');
            FOR i:=1 TO nval DO Write(nmval[i],':',val[i]:11,' ');
            WriteLn;
            GoTo Achou
          END;
      ErroFatal('Elemento desconhecido');
     Achou:
      IF tipo<>AmpOp THEN Inc(numero)
      ELSE BEGIN
        IF (C[no[1]]>C[no[2]]) THEN BEGIN a1:=C[no[2]]; b1:=C[no[1]] END
        ELSE BEGIN a1:=C[no[1]]; b1:=C[no[2]] END;
        c1:=L[no[3]];
        IF (a1=b1) OR (c1=0) THEN ErroFatal('Circuito inv†lido');
        FOR i:=1 TO nosantes DO BEGIN
          IF C[i]=b1 THEN C[i]:=a1;
          IF C[i]>b1 THEN Dec(C[i]);
          IF L[i]=c1 THEN L[i]:=0;
          IF L[i]>c1 THEN Dec(L[i])
        END;
        Dec(nos)
      END
    END
  UNTIL SeekEof(arquivo);
  Close(arquivo);
  Dec(numero);
  WriteLn(tl,#10'N£mero de elementos efetivos: [',numero,']');
  WriteLn(tl,'N£mero de n¢s independentes: [',nos,']');
  IF nos>MaxNos THEN ErroFatal('O m†ximo de (n£mero de n¢s-n£mero de a. o. ideais) Ç ['+Sri(MaxNos)+']');
  AcharOrdem;
END; {LerCircuito}

PROCEDURE ResolverSistema;
VAR
  qr,qi:REAL;
BEGIN
  vr:=Cos(ind*f); vi:=Sin(ind*f);
  FOR i:=1 TO nos DO BEGIN
    tr:=0; ti:=0; m:=i;
    FOR k:=i TO nos DO
      IF Abs(Yr[k,i])+Abs(Yi[k,i])>Abs(tr)+Abs(ti) THEN BEGIN
        m:=k;
        tr:=Yr[k,i];
        ti:=Yi[k,i]
      END;
    IF i<>m THEN BEGIN
      vi:=-vi; vr:=-vr;
      FOR k:=i TO nos+1 DO BEGIN
        t:=Yr[i,k];
        Yr[i,k]:=Yr[m,k];
        Yr[m,k]:=t;
        t:=Yi[i,k];
        Yi[i,k]:=Yi[m,k];
        Yi[m,k]:=t
      END
    END;
    vr:=Cmult(vr,vi,tr,ti); vi:=Imag;
    FOR j:=nos+1 DOWNTO i+1 DO BEGIN
      t:=tr*tr+ti*ti;
      qr:=(Yr[i,j]*tr+Yi[i,j]*ti)/t;
      qi:=(Yi[i,j]*tr-Yr[i,j]*ti)/t;
      Yi[i,j]:=qi;
      Yr[i,j]:=qr;
      FOR k:=1 TO nos DO
        IF i<>k THEN BEGIN
          Yr[k,j]:=Yr[k,j]-Cmult(Yr[k,i],Yi[k,i],qr,qi);
          Yi[k,j]:=Yi[k,j]-Imag
        END
    END
  END;
END; {ResolverSistema}

PROCEDURE GuardarResultados; {Armazena os valores calculados para num. e den.}
BEGIN
  Dr[ii]:=vr; Di[ii]:=vi;
  FOR i:=1 TO nos DO BEGIN
    Nr[i,ii]:=Cmult(Yr[i,nos+1],Yi[i,nos+1],vr,vi);
    Ni[i,ii]:=Imag
  END
END; {GuardarResultados}

PROCEDURE ApresentarResultados; {Denormaliza e apresenta resultados}
VAR
  maiory,nively,cnst:REAL;
  Pn,Pd:polinomio;
  Sair:BOOLEAN;
  grau:INTEGER;
LABEL
  Inicio;
BEGIN
 Inicio:
  Sair:=FALSE;
  IF numerador THEN Write(tl,#10'[Numerador] de T',nsaida,'(s)')
  ELSE BEGIN
    ClrScr; WriteLn(tl,']-----[',rede,']-----');
    Write(tl,#10'[Denominador] de T(s) ');
    npolos:=0;
  END;
  IF normalizar THEN WriteLn('normalizado') ELSE WriteLn; WriteLn;
  maiory:=0;
  FOR i:=0 TO graufft-1 DO IF Abs(AX[i])>maiory THEN maiory:=Abs(AX[i]);
  IF maiory=0 THEN
    IF numerador THEN BEGIN
      WriteLn(tl,'[Zero]: n¢ sem sinal');
      Exit
    END
    ELSE BEGIN
      WriteLn(tl,'[Erro]: m† normalizaáÑo em impedÉncia');
      WriteLn(#10'Toque uma tecla para reiniciar...');
      r:=ReadKey;
      Exit
    END;
  t:=maiory/dispersao; ok:=FALSE; j:=0;
  FOR i:=graufft-1 DOWNTO 0 DO BEGIN
    IF Abs(AX[i])>t THEN BEGIN
      IF not ok THEN BEGIN ok:=TRUE; grau:=i; nively:=AX[grau] END;
      Pn[i]:=AX[i]/nively; m:=i; {m=menor grau}
      Pd[i]:=Pn[i]*Ex(fatord,grau-i)
    END
    ELSE BEGIN Pn[i]:=0; Pd[i]:=0 END;
    IF ok THEN BEGIN
      WriteLn(tl,'a([',i,'])=',Pd[i]);
      Inc(j);
      IF j>15 THEN BEGIN
        Write('Mais...'#13);
        j:=0;
        r:=ReadKey
      END
    END
  END;
  IF numerador THEN BEGIN
    funcao[1].Num:=Pd;
    funcao[1].ngrau:=grau;
    sufixo:='.n'+Sri(nsaida);
    cnst:=nively/(Ex(fatord,grau)*mden);
    WriteLn(tl,#10'[Cte. de ganho]: ',cnst);
    funcao[1].cte:=cnst
  END
  ELSE BEGIN
    funcao[1].Den:=Pd;
    funcao[1].dgrau:=grau;
    sufixo:='.d';
    mden:=nively/Ex(fatord,grau);
    cnst:=1
  END;
  IF not numerador and (grau<>graudefault) THEN
    WriteLn(tl,#10'[*] O grau difere do esperado ([',graudefault,'])');
  funcao[1].nome:=rede+sufixo;
  WriteLn(#10'Norm. em freq.  usada = ',fatorw:10);
  IF grau>m THEN BEGIN
    Write(tl,'Norm. em freq.  [ideal] = ');
    t:=fatorw/fatord*Ex(Abs(Pd[m]),1/(grau-m));
    WriteLn(t:10)
  END;
  WriteLn('Norm. em imped. usada = ',fatorz:10);
  IF grau>m THEN nively:=nively*Ex(fatorw/t,ind-grau);
  WriteLn(tl,'Norm. em imped. [ideal] = ',Ex(Abs(nively),-1/nos)*fatorz:10);
    REPEAT
    WriteLn;
    IF numerador THEN Write(tl,'[G]rf [I]nc [E]li ');
    WriteLn(tl,'[D]en [N]um [S]al ds[P] [R]ai [M]od [F]im');
    CASE UpKey OF
      'M':BEGIN
            Window(1,1,80,25);
            ClrScr;
            WriteLn('ParÉmetros do circuito:');
            REPEAT
              WriteLn;
              FOR i:=1 TO numero DO WITH netlist[i] DO
                WITH biblioteca[tipo] DO BEGIN
                  Write(nome,': ');
                  FOR j:=1 TO nnos DO Write(no[j],' (',nmno[j],') ');
                  WriteLn;
                  FOR j:=1 TO nval DO BEGIN
                    Write(' ',nmval[j]); LerReal(val[j])
                  END
                END;
              WriteLn;
              WriteLn(tl,'[M]odificar mais [C]ontinuar');
              REPEAT r:=UpKey UNTIL r in ['M','C'];
            UNTIL r='C';
            numerador:=FALSE; Sair:=TRUE
          END;
      'G':IF numerador THEN Grafico;
      'I':IF numerador THEN
            IF nfun<mfuncoes THEN BEGIN
              Inc(nfun);
              LeFdeT(nfun);
              IF not ok THEN Dec(nfun)
              ELSE WriteLn(tl,#10'Inclu°da [',funcao[nfun].nome,'] ([',nfun,'])')
            END
          ELSE WriteLn(tl,#10'Apenas [',mfuncoes,'] funáîes permitidas');
      'E':IF numerador THEN
            IF nfun>1 THEN BEGIN
            WriteLn(tl,#10'Eliminada [',funcao[nfun].nome,'] ([',nfun,'])');
            Dec(nfun)
          END
          ELSE WriteLn(tl,#10'[NÑo h†] funáÑo a eliminar');
      'F':BEGIN
            WriteLn(tl,#10'[R]ecomeáar [C]ontinuar [F]im');
            r:=UpKey;
            CASE r OF
              'R':BEGIN recomecar:=TRUE; Sair:=TRUE END;
              'F':BEGIN Window(1,1,80,25); ClrScr; WriteLn(tl,'---[Fim]---'); Halt END;
            END;
          END;
      'P':BEGIN
            Write(#10'Nova dispersÑo'); LerReal(dispersao);
            GoTo Inicio
          END;
      'S':BEGIN
            Assign(arquivo,funcao[1].nome);
            ReWrite(arquivo);
            WriteLn(arquivo,grau);
            FOR i:=0 TO grau DO WriteLn(arquivo,Pd[i]);
            WriteLn(arquivo,cnst);
            Close(arquivo);
            WriteLn(tl,#10'Pol. salvo como [',funcao[1].nome,']')
          END;
      'R':Lib(Pn,grau,cnst);
      'N':BEGIN numerador:=TRUE;  Sair:=TRUE END;
      'D':BEGIN numerador:=FALSE; Sair:=TRUE END;
    END
  UNTIL Sair
END; {ApresentarResultados}

PROCEDURE EntrarArquivo;
BEGIN
  ok:=FALSE;
  REPEAT
    txt:=rede;
    Write(tl,#10'Arquivo com a descriáÑo do circuito (.net) ou ?: ');
    EditarLinha(txt,WhereX,WhereY,1);
    WriteLn;
    IF txt='?' THEN Diretorio
    ELSE BEGIN
      IF Pos('.',txt)=0 THEN txt:=txt+'.net';
      rede:=Copy(txt,1,Pos('.',txt)-1);
      Assign(arquivo,txt);
      {$I-} Reset(arquivo) {$I+};
      ok:=(IOresult=0);
      IF not ok THEN WriteLn(tl,#10'[*] Arquivo [',txt,'] inexistente.')
    END
  UNTIL ok;
END; {EntrarArquivo}

BEGIN {Programa Principal}
  DetectGraph(placa,modo);
  IF (placa=CGA) THEN modo:=CGAC0;
  IF paramcount=3 THEN BEGIN
    Val(ParamStr(2),placa,i);
    Val(ParamStr(3),modo,i);
  END;
  InitGraph(placa,modo,GetEnv('TPBGI'));
  IF placa>0 THEN BEGIN
    SetTextStyle(SmallFont,HorizDir,4);
    xmin:=TextWidth('-xxx.xx'); xmax:=GetMaxX; ymin:=0; ymax:=GetMaxY-TextHeight('X')-2;
    IF placa<>1 THEN BEGIN
      cor[3]:=Yellow;
      cor[2]:=Lightgray;
      cor[1]:=White;
      cor[4]:=Lightgreen
    END;
    InitSprite(cor[3],cor[2]);
  END;
  TextMode(80);
  i:=GraphResult; IF i<>GrOk THEN ErroFatal(GraphErrorMsg(i));
  DoisPi:=2*Pi; RadGraus:=180/Pi; LnDb:=10/Ln(10); amaxpt:=(xmax-xmin) div 2;
  FOR i:=1 TO mfuncoes DO WITH funcao[i] DO BEGIN
    gmin:=-60; gmax:=10
  END;
  IF ParamCount>0 THEN rede:=ParamStr(1) ELSE rede:='';
 Inicio:
  Window(1,1,80,25);
  ClrScr;
  recomecar:=FALSE;
  WriteLn(tl,'[…ÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕª]');
  WriteLn(tl,'[∫]C†lculo de Funáîes De Transferància Por [I]nterpolaáÑo por [FFT∫]');
  WriteLn(tl,'[»ÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕÕº]');
  WriteLn(tl,'Antìnio Carlos MoreirÑo de Queiroz - COPPE/UFRJ');
  WriteLn(tl,'VersÑo ',versao,' - PrecisÑo ',precisao);
  EntrarArquivo;
  LerCircuito;
  nsaida:=nosantes;
  GoTo Pulo;
 CalcDen:
  Window(1,1,80,25);
  ClrScr;
 Pulo:
  Write(#10'M†xima dispersÑo entre coeficientes de polinìmio'); LerReal(dispersao);
  Write('Fator de normalizaáÑo em freqÅància'); LerReal(fatorw);
  Write('Fator de normalizaáÑo em impedÉncia'); LerReal(fatorz);
  Write('Ordem de complexidade estimada'); LerInt(graudefault);
  graufft:=1;
  REPEAT graufft:=graufft*2 UNTIL graufft>graudefault;
  IF graufft>Gmax+1 THEN ErroFatal('A ordem m†xima Ç ['+Sri(Gmax)+']');
  Write('Apresentar resultados normalizados em freqÅància'); LerBool(normalizar);
  IF normalizar THEN fatord:=1 ELSE fatord:=fatorw;
  ordem:=Round(Ln(graufft)/Ln(2));
  WriteLn(tl,#10'Ordem para a interpolaáÑo por FFT: [',graufft,']');
  Write(tl,#10'Calculando...[');
  FOR ii:=0 TO graufft shr 1 DO BEGIN
    f:=DoisPi*ii/graufft; sr:=fatorw*Cos(f); si:=fatorw*Sin(f);
    Write(graufft shr 1-ii,' ');
    MontarSistema;
    ResolverSistema;
    GuardarResultados;
  END;
  FOR i:=0 TO graufft shr 1 DO BEGIN
    k:=(graufft-i) mod graufft;
    AX[i]:=Dr[i]; AX[k]:=Dr[i];
    BX[i]:=Di[i]; BX[k]:=-Di[i]
  END;
  FFT;
  numerador:=FALSE;
  ApresentarResultados;
  IF recomecar THEN GoTo Inicio;
  IF not numerador THEN GoTo CalcDen;
  Window(41,1,80,25); GoToXY(1,1);
 CalcNum:
  Write('N¢ de sa°da'); LerInt(nsaida);
  IF (nsaida<0) or (nsaida>nosantes) THEN BEGIN WriteLn(tl,#10'N¢ [inexistente]'#10); GoTo CalcNum END
  ELSE
    IF C[nsaida]=0 THEN BEGIN WriteLn(tl,#10'[Zero]: terra real ou virtual'#10); GoTo CalcNum END
    ELSE BEGIN
      FOR i:=0 TO graufft shr 1 DO BEGIN
        k:=(graufft-i) mod graufft;
        AX[i]:=Nr[C[nsaida],i]; AX[k]:=AX[i];
        BX[i]:=Ni[C[nsaida],i]; BX[k]:=-BX[i]
      END;
      FFT;
      numerador:=TRUE; {redundante}
      ApresentarResultados
    END;
    WriteLn;
  IF recomecar THEN GoTo Inicio;
  IF numerador THEN GoTo CalcNum ELSE GoTo CalcDen
END. {IFFT}
