PROGRAM EletSim;
{******************************************************************************
 * GeraáÑo de tabelas de filtros eletricamente simÇtricos ou antimÇtricos     *
 * Antìnio Carlos MoreirÑo de Queiroz                                         *
 * VersÑo 1.0  de 19/10/90                                                    *
 * VersÑo 1.1  de 19/11/90 Tabelas em pointers                                *
 * VersÑo 1.2  de 05/01/91 Arquivo de configuraáÑo                            *
 * VersÑo 1.3  de 15/01/91 RealizaáÑo em lattice e formas desbalanceadas      *
 * VersÑo 1.4  de 24/03/91 C†lculo do atraso de grupo e cores diferentes      *
 * VersÑo 1.4a de 01/05/91 Instr. corrigidas                                  *
 * VersÑo 1.4b de 19/07/92 Ordem dos parametros de configuracao corrigida     *
 * Versao 1.4c de 23/07/92 Correcao em latt.pas                               *
 * Versao 1.4d de 10/01/94 Salva tabela com curvas                            *
 * Versao 1.4e de 18/09/94 Extracoes no infinito permitidas no recalculo      *
 * Versao 1.4f de 27/07/95 Folga na alocacao para funcionar no Windows, instr.*
 * Versao 1.4g de 22/07/96 Corrigidos testes na impressao para evitar erro    *
 * Versao 1.4h de 23/11/05 Desnormalizacao das redes ladder                   *
 * Versao 1.4i de 14/07/06 Desnormaliza para Hz ou rad/s                      *
 * Versao 1.4j de 21/07/06 Corrigido help sobre lattice                       *
 ******************************************************************************}
{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}
USES Crt,Dos,Graph,Tela,Latt;

LABEL batch1,batch2,batch3,inicio,denovo;

FUNCTION Ex(x,y: REAL): REAL;
BEGIN Ex:=Exp(y*Ln(x)) END;

PROCEDURE Limpar(VAR x:polinomio);
  VAR
    max:REAL;
    i:INTEGER;
BEGIN
  WITH x DO BEGIN
    max:=0;
    FOR i:=0 TO grau DO IF Abs(a[i])>max THEN max:=Abs(a[i]);
    max:=max*toln;
    FOR i:=0 TO grau DO IF Abs(a[i])<max THEN a[i]:=0;
    WHILE (grau>=0) and (a[grau]=0) DO Dec(grau);
  END
END;

PROCEDURE Normalizar(VAR x:polinomio);
VAR i:INTEGER;
BEGIN
  Limpar(x);
  WITH x DO BEGIN
    IF (grau>=0) and (a[grau]<>1) THEN BEGIN
      cte:=cte*a[grau];
      FOR i:=0 TO grau DO a[i]:=a[i]/a[grau]
    END
  END
END;

PROCEDURE Inverter(VAR x:polinomio);
  VAR
    tmp:REAL;
    i:INTEGER;
BEGIN
  WITH x DO
    FOR i:=0 TO grau DIV 2 DO BEGIN
      tmp:=a[i]; a[i]:=a[grau-i]; a[grau-i]:=tmp
    END
END;

PROCEDURE Somar;
VAR i:INTEGER;
BEGIN
  FOR i:=x.grau+1 TO y.grau DO x.a[i]:=0;
  IF x.grau<y.grau THEN x.grau:=y.grau;
  FOR i:=0 TO y.grau DO x.a[i]:=x.cte*x.a[i]+y.cte*y.a[i];
  x.cte:=1;
  y:=z; z:=t
END;

PROCEDURE Negar;
BEGIN
  x.cte:=-x.cte
END;

PROCEDURE Subtrair;
BEGIN
  Negar;
  Somar;
END;

PROCEDURE Multiplicar;
  VAR
    m:coeficientes;
    i,j:INTEGER;
BEGIN
  m:=x.a;
  FOR i:=0 TO x.grau+y.grau DO x.a[i]:=0;
  FOR i:=0 TO x.grau DO
    FOR j:=0 TO y.grau DO
      x.a[i+j]:=x.a[i+j]+m[i]*y.a[j];
  x.cte:=x.cte*y.cte;
  x.grau:=x.grau+y.grau;
  y:=z; z:=t;
END;

PROCEDURE MultS;
VAR i:INTEGER;
BEGIN
  WITH x DO BEGIN
    FOR i:=grau DOWNTO 0 DO a[i+1]:=a[i];
    a[0]:=0;
    grau:=grau+1;
  END
END;

PROCEDURE MultC(c:REAL);
BEGIN
  x.cte:=x.cte*c
END;

PROCEDURE ListarRaizes(n:INTEGER; cte:REAL; VAR zr,zi:raizes);
VAR
  w:REAL;
BEGIN
  FOR i:=1 TO n DO
    WriteLn(tl,'- x([',i:2,']):',zr[i]:cm:dc,' ',zi[i]:cm:dc,'j');
  FOR i:=1 TO n DO
    IF (zi[i]>tolm) AND (Abs(zr[i])>tolm) THEN BEGIN
      w:=Sqrt(Sqr(zr[i])+Sqr(zi[i]));
      WriteLn(tl,'[w],[Q]([',i:2,']):',w:cm:dc,' ',-w/2/zr[i]:cm:dc)
    END;
  WriteLn(tl,'- [Cte]:  ',cte:cm:dc);
  Write(tl,'Salvar? ([Cr] ou nome) [');
  ReadLn(txt); Write(tl,']');
  IF txt<>'' THEN BEGIN
    Assign(arquivo,txt);
    ReWrite(arquivo);
    WriteLn(arquivo,n);
    FOR i:=1 TO n DO WriteLn(arquivo,zr[i]:cm:dc,' ',zi[i]:cm:dc);
    WriteLn(arquivo,cte:cm:dc);
    Close(arquivo)
  END;
END;

PROCEDURE ListarPolinomio(VAR x:polinomio);
BEGIN
  WITH x DO BEGIN
    FOR i:=0 TO grau DO WriteLn(tl,'[-] a([',i:2,']): ',a[i]:cm:dc);
    WriteLn(tl,'[-] Cte:   ',cte:cm:dc);
    Write(tl,'Salvar? ([Cr] ou nome) [');
    ReadLn(txt); Write(tl,']');
    IF Length(txt)>0 THEN BEGIN
      Assign(arquivo,txt);
      ReWrite(arquivo);
      WriteLn(arquivo,grau);
      FOR i:=0 TO grau DO WriteLn(arquivo,a[i]:cm:dc);
      WriteLn(arquivo,cte:cm:dc);
      Close(arquivo)
    END
  END
END;

PROCEDURE ListarRede(VAR item:filtro);
BEGIN
  IF salvarladder THEN WITH item DO BEGIN
    Write('Desnormalizar'); LerBool(desnormalizar);
    IF desnormalizar THEN BEGIN
      Write('Desnormalizar para freqÅàncias em Hz'); LerBool(emhz);
      Write('Fator de desnormalizaáÑo em impedÉncia'); LerReal(fr);
      Write('Fator de desnormalizaáÑo em freqÅància'); LerReal(ff0);
      IF emhz THEN ff:=ff0*2*pi ELSE ff:=ff0
    END
    ELSE BEGIN
      fr:=1;
      ff:=1
    END;
    WriteLn(tl,'[Rg]: ',rg*fr:cm:dc);
    WriteLn(tl,'[Rl]: ',rl*fr:cm:dc);
    FOR i:=1 TO n DO BEGIN
      IF C[i]<>0 THEN WriteLn(tl,'[C',i,']: ',C[i]/fr/ff:cm:dc);
      IF L[i]<>0 THEN WriteLn(tl,'[L',i,']: ',L[i]*fr/ff:cm:dc)
    END;
    Write(tl,'Salvar? ([Cr] ou nome) [');
    ReadLn(txt); Write(tl,']');
    IF Length(txt)>0 THEN BEGIN
      Assign(arquivo,txt);
      ReWrite(arquivo);
      WriteLn(arquivo,'RG ',rg*fr:cm:dc);
      WriteLn(arquivo,'RL ',rl*fr:cm:dc);
      FOR i:=1 TO n DO BEGIN
        IF C[i]<>0 THEN WriteLn(arquivo,'C',i,' ',C[i]/fr/ff:cm:dc);
        IF L[i]<>0 THEN WriteLn(arquivo,'L',i,' ',L[i]*fr/ff:cm:dc)
      END;
      Close(arquivo)
    END
  END
END;

PROCEDURE Enter;
BEGIN
  t:=z; z:=y; y:=x
END;

PROCEDURE Chebyshev(n:INTEGER);
  VAR k:INTEGER;
BEGIN
  x.a[0]:=1; x.grau:=0; x.cte:=1;
  IF n>0 THEN BEGIN
    Enter;
    MultS;
    k:=1;
    FOR k:=2 TO n DO BEGIN
      Enter;
      MultC(2);
      MultS;
      Enter;
      x:=t;
      Subtrair
    END
  END
END;

PROCEDURE Derivar;
VAR i:INTEGER;
BEGIN
  WITH x DO BEGIN
    IF grau=0 THEN a[0]:=0
    ELSE BEGIN
      FOR i:=1 TO grau DO a[i-1]:=a[i]*i;
      grau:=grau-1
    END;
  END
END;

PROCEDURE LerPolinomio;
BEGIN
  Write(tl,'Nome do arquivo ou [Cr]: [');
  ReadLn(txt); Write(tl,']');
  IF Length(txt)>0 THEN BEGIN
    Assign(arquivo,txt);
      {$I-} Reset(arquivo); {$I+}
    IF IOResult=0 THEN BEGIN
      ReadLn(arquivo,x.grau);
      FOR i:=0 TO x.grau DO ReadLn(arquivo,x.a[i]);
      IF SeekEof(arquivo) THEN x.cte:=1.0
      ELSE ReadLn(arquivo,x.cte)
    END
    ELSE WriteLn(tl,'[*] Arquivo inexistente')
  END
  ELSE BEGIN
    Write('Grau: '); ReadLn(x.grau);
    FOR i:=0 TO x.grau DO BEGIN
      Write(tl,'a([',i:2,']): '); ReadLn(x.a[i])
    END;
    Write('Cte: '); ReadLn(x.cte)
  END;
END;

PROCEDURE ConverterParaS(VAR x:polinomio);
BEGIN
  WITH x DO BEGIN
    FOR i:=0 TO grau DO BEGIN
      j:=i mod 4;
      IF ((j=1) OR (j=2)) THEN a[i]:=-a[i]
    END;
    IF a[grau]<0 THEN FOR i:=0 TO grau DO a[i]:=-a[i];
    cte:=Abs(cte);
  END
END;

PROCEDURE ReEscalar;
  VAR u,v,w0:REAL;
BEGIN
  t:=y;
  z:=x;
  x:=y;
  y:=z;
  Subtrair;
  WITH x DO BEGIN
    w0:=1;
    REPEAT
      u:=0; v:=0;
      FOR i:=grau DOWNTO 0 DO BEGIN
        u:=u*w0+a[i];
        IF i<>0 THEN v:=v*w0+i*a[i]
      END;
      u:=u/v;
      w0:=w0-u;
      Write('  wp:',w0:cm:dc,#13);
    UNTIL (Abs(u)<tolr) OR KeyPressed
  END;
  x:=y;
  y:=z;
  FOR i:=0 TO x.grau-1 DO x.a[i]:=x.a[i]/Ex(w0,x.grau-i);
  FOR i:=0 TO y.grau-1 DO y.a[i]:=y.a[i]/Ex(w0,y.grau-i);
  y.cte:=y.cte/Ex(w0,x.grau-y.grau);
  WriteLn(tl,#10'[-] K(jw)/Ó normalizado');
END;

PROCEDURE Grafico(tipo:INTEGER; VAR x1,x2,y1,y2:REAL; VAR log:BOOLEAN); {1=K, 2=T, 3=Tg}
  VAR
    ax,bx,ay,by,p,w,d,a1,a2,b1,b2:REAL;
    xg,yg,xa,ya:INTEGER;
    LABEL atualizar;

  FUNCTION Limx(x:REAL):INTEGER;
  BEGIN
    x:=ax*x+bx;
    IF x>xmax THEN Limx:=xmax
    ELSE IF x<xmin THEN Limx:=xmin
    ELSE Limx:=Round(x)
  END;

  FUNCTION Limy(y:REAL):INTEGER;
  BEGIN
    y:=ay*y+by;
    IF y>ymax THEN Limy:=ymax
    ELSE IF y<ymin THEN Limy:=ymin
    ELSE Limy:=Round(y)
  END;

  PROCEDURE IniciarGrafico(x1,x2,y1,y2:REAL; xlog:BOOLEAN);
  VAR
    t1,t2:REAL;
    i:INTEGER;
  BEGIN
    SetGraphMode(modo);
    SetFillStyle(emptyfill,0);
    ay:=(ymax-ymin)/(y1-y2);
    by:=ymax-ay*y1;
    IF not xlog THEN BEGIN
      ax:=(xmax-xmin)/(x2-x1);
      bx:=xmin-ax*x1;
    END
    ELSE BEGIN
      ax:=(xmax-xmin)/(Ln(x2)-Ln(x1)); bx:=xmin-ax*Ln(x1)
    END;
    IF grade THEN BEGIN
      SetLineStyle(DottedLn,0,NormWidth);
      SetColor(cor3);
      IF xlog and (x2-x1>x1) THEN t1:=x1
      ELSE t1:=x2-x1;
      t1:=Exp(Ln(10)*Round(Ln(t1)/Ln(10)-0.499999));
      t2:=Round(x1/t1+0.5)*t1;
      WHILE t2<x2 DO
        IF xlog THEN BEGIN
          IF Round(t2/t1)=10 THEN BEGIN
            t1:=10*t1;
            SetColor(cor2);
          END;
          i:=Round(ax*Ln(t2)+bx);
          Line(i,ymin,i,ymax);
          t2:=t2+t1;
          SetColor(cor3);
        END
        ELSE BEGIN
          i:=Round(ax*t2+bx);
          Line(i,ymin,i,ymax);
          t2:=t2+t1
        END;
      t1:=y2-y1;
      t1:=Exp(Ln(10)*Round(Ln(t1)/Ln(10)-0.5));
      t2:=Round(y1/t1+0.5)*t1;
      WHILE t2<y2 DO BEGIN
        i:=Round(ay*t2+by);
        Line(xmin,i,xmax,i);
        t2:=t2+t1
      END;
      SetLineStyle(SolidLn,0,NormWidth);
      SetColor(cor1)
    END;
    Rectangle(xmin,ymin,xmax,ymax);
    Str(y2:6:2,txt); OutTextXY(0,ymin,txt);
    Str(y1:6:2,txt); OutTextXY(0,ymax-8,txt);
    Str(x1:8:3,txt); OutTextXY(xmin+1,ymax+2,txt);
    Str(x2:8:3,txt); OutTextXY(xmax-64,ymax+2,txt);
    CASE tipo OF
      1:txt:='(*)';
      2:txt:='dB';
      3:txt:='seg';
    END;
    OutTextXY(0,(ymax+ymin) div 2-2,txt);
    OutTextXY((xmax+xmin) div 2-18,ymax+2,'rad/s')
  END;

BEGIN
  REPEAT
    IF (x1<=0) or (x2<=0) THEN log:=FALSE;
    IF (x1>=x2) or (y1>=y2) THEN grade:=FALSE;
    IniciarGrafico(x1,x2,y1,y2,log);
    FOR fil:=1 TO nfil DO WITH Tabela[fil]^ DO BEGIN
      SetColor(GetMaxColor-(fil-1) mod GetMaxColor);
      IF tipo=3 THEN BEGIN
        x:=eo;
        Derivar
      END;
      FOR xg:=xmin TO xmax DO BEGIN
        w:=(xg-bx)/ax;
        IF log THEN w:=Exp(w);
        CASE tipo OF
          1:BEGIN
              p:=xo.a[n];
              FOR i:=n-1 DOWNTO 0 DO p:=p*w+xo.a[i];
              d:=p*xo.cte*alfa;
              p:=yo.a[0];
              FOR i:=n-1 DOWNTO 0 DO p:=p*w+yo.a[n-i];
              d:=d/(p*yo.cte);
              p:=Abs(d);
              IF p>1 THEN p:=Ln(p)/Ln(10)+1;
              IF d<0 THEN p:=-p
            END;
          2:BEGIN
              a1:=0; a2:=0;
              FOR j:=eo.grau DOWNTO 0 DO
                BEGIN d:=a1*w; a1:=eo.a[j]-w*a2; a2:=d END;
              d:=Sqr(eo.cte)*(Sqr(a1)+Sqr(a2));
              IF d=0 THEN d:=1e-20;
              a1:=0; a2:=0;
              FOR j:=po.grau DOWNTO 0 DO
                BEGIN p:=a1*w; a1:=po.a[j]-w*a2; a2:=p END;
              d:=Sqr(po.cte)*(Sqr(a1)+Sqr(a2))/d;
              IF d=0 THEN d:=1e-20;
              p:=Ln(d)*4.342944818
            END;
          3:BEGIN
              b1:=0; b2:=0;
              FOR j:=eo.grau DOWNTO 0 DO
                BEGIN d:=b1*w; b1:=eo.a[j]-w*b2; b2:=d END;
              a1:=0; a2:=0;
              FOR j:=x.grau DOWNTO 0 DO
                BEGIN d:=a1*w; a1:=x.a[j]-w*a2; a2:=d END;
              p:=(a1*b1+a2*b2)/(Sqr(b1)+Sqr(b2));
            END
        END;
        yg:=Limy(p);
        IF salvarcurva THEN WriteLn(arquivo,w,' ',p);
        IF xg>xmin THEN
          Line(xa,ya,xg,yg);
        xa:=xg; ya:=yg;
        IF KeyPressed THEN GOTO atualizar;
      END;
      IF salvarcurva THEN WriteLn(arquivo);
    END;
    atualizar:
    IF salvarcurva THEN BEGIN
      salvarcurva:=FALSE;
      Close(arquivo);
    END;
    ch:=ReadKey;
    IF ch=#0 THEN ch:=ReadKey;
    CASE UpCase(ch) OF
      '-':y2:=y1+(y2-y1)*2;
      '+':y2:=y1+(y2-y1)/2;
      'R':IF log THEN x2:=x1*Sqr(x2/x1) ELSE x2:=x1+(x2-x1)*2;
      'A':IF log THEN x2:=x1*Sqrt(x2/x1) ELSE x2:=x1+(x2-x1)/2;
      'M':IF log THEN BEGIN d:=Sqrt(Sqrt(x2/x1)); x1:=x1*d; x2:=x2*d END
          ELSE BEGIN d:=(x2-x1)/4; x1:=x1+d; x2:=x2+d END;
      'K':IF log THEN BEGIN d:=Sqrt(Sqrt(x2/x1)); x1:=x1/d; x2:=x2/d END
          ELSE BEGIN d:=(x2-x1)/4; x1:=x1-d; x2:=x2-d END;
      'H':BEGIN d:=(y2-y1)/4; y1:=y1+d; y2:=y2+d END;
      'P':BEGIN d:=(y2-y1)/4; y1:=y1-d; y2:=y2-d END;
      'G':grade:=not grade;
      #27:;
      ELSE BEGIN
        TextMode(80);
        WriteLn(tl,'[Novos parÉmetros]:',#10);
        Write('Escala logar°tmica'); LerBool(log);
        Write('Traáar grade'); LerBool(grade);
        Write('w m°nimo'); LerReal(x1);
        Write('w m†ximo'); LerReal(x2);
        Write('y m°nimo'); LerReal(y1);
        Write('y m†ximo'); LerReal(y2);
        Write(tl,'Salvar curva? ([Cr] ou nome) [');
        ReadLn(txt); Write(tl,']');
        IF txt<>'' THEN BEGIN
          Assign(arquivo,txt);
          ReWrite(arquivo);
          salvarcurva:=TRUE
        END
      END
    END
  UNTIL ch=#27;
  TextMode(80);
END;

PROCEDURE RaizesBiv(duplas:BOOLEAN); {Ra°zes do polinomio x por Birge-Vieta}
  CONST
    imax=50;
  VAR
    a1,a2,c1,c2:coeficientes;
    Imag,told1,tolm1,t,tolr1,p1,p2,d,xr,xi,p,d1,d2,e1,e2:REAL;
    feito:BOOLEAN;
    nn,n,ordem:INTEGER;

  FUNCTION Cmult(x1,x2,y1,y2:REAL):REAL;
  BEGIN
    Cmult:=x1*y1-x2*y2;
    Imag:=x1*y2+x2*y1
  END;

BEGIN {Programa principal RaizesBiv}
  IF duplas THEN told1:=told ELSE told1:=tolm;
  tolm1:=tolm; tolr1:=tolr; n:=x.grau; a1:=x.a; ordem:=0;
  xr:=xr0; xi:=xi0; feito:=FALSE; nn:=0;
  IF n<1 THEN
    BEGIN WriteLn(tl,'[*] NÑo h† raizes a calcular'); Exit END;
  FOR i:=0 TO n DO a2[i]:=0;
  Write(tl,'  [');
  {EliminaáÑo de ra°zes na origem}
  WHILE (n>1) AND (a1[0]=0) DO BEGIN
    zr[n]:=0; zi[n]:=0;
    Write(n,' ');
    n:=n-1;
    FOR i:=0 TO n DO a1[i]:=a1[i+1]
  END;
  WHILE NOT feito DO BEGIN
    IF n>1 THEN BEGIN
      {Calculo dos valores do polinìmio (p) e de sua derivada (d)}
      d1:=a1[n]; p1:=d1;
      d2:=a2[n]; p2:=d2;
      FOR i:=n-1 DOWNTO 0 DO BEGIN
        p1:=Cmult(p1,p2,xr,xi)+a1[i];
        p2:=Imag+a2[i];
        IF i>0 THEN BEGIN
          d1:=Cmult(d1,d2,xr,xi)+p1;
          d2:=Imag+p2;
        END
      END;
      {C†lculo do erro. Esta forma dificulta overflow}
      IF (d1=0) OR (d2=0) THEN BEGIN
        d:=Sqr(d1)+Sqr(d2);
        e1:=(p1*d1+p2*d2)/d;
        e2:=(p2*d1-p1*d2)/d
      END
      ELSE BEGIN
        d:=d1/d2+d2/d1;
        e1:=(p1/d2+p2/d1)/d;
        e2:=(p2/d2-p1/d1)/d
      END;
      {Testa poss°vel ra°z m£ltipla}
      d:=Abs(d1)+Abs(d2);
      p:=Abs(p1)+Abs(p2);
      IF (d<told1) AND (p<tolm1) THEN BEGIN
        {deriva o polinìmio e continua}
        IF ordem=0 THEN BEGIN c1:=a1; c2:=a2 END;
        FOR i:=1 TO n DO BEGIN
          a1[i-1]:=a1[i]*i/n;
          a2[i-1]:=a2[i]*i/n;
        END;
        n:=n-1; ordem:=ordem+1;
        Write('+')
      END
      ELSE BEGIN
        {Atualiza ra°zes}
        xr:=xr-e1;
        xi:=xi-e2;
        {Testa convergància}
        t:=Abs(e1)+Abs(e2);
        IF t<tolr1 THEN BEGIN
          {Armazena ra°zes calculadas}
          FOR i:=n+ordem DOWNTO n DO BEGIN
            Write(i,' ');
            zr[i]:=xr; zi[i]:=xi;
          END;
          {Repîe polinìmio original, se for o caso}
          IF ordem>0 THEN BEGIN
            a1:=c1; a2:=c2; n:=n+ordem;
          END;
          {Deflaciona polinìmio}
          FOR i:=0 TO ordem DO BEGIN
            FOR j:=n-1 DOWNTO 1 DO BEGIN
              a1[j]:=Cmult(xr,xi,a1[j+1],a2[j+1])+a1[j];
              a2[j]:=Imag+a2[j];
            END;
            n:=n-1;
            FOR j:=0 TO n DO
              BEGIN a1[j]:=a1[j+1]; a2[j]:=a2[j+1] END
          END;
          {Prepara c†lculo da pr¢xima ra°z}
          IF (Abs(xi)>0.01) THEN xi:=-xi ELSE xi:=0.1;
          IF ordem>0 THEN xr:=xr-0.01; {evita derivada 0 a seguir}
          ordem:=0; nn:=0;
        END
        ELSE BEGIN
          nn:=nn+1;
          {Demorando a convergir}
          IF (nn>imax) OR KeyPressed THEN BEGIN
            WriteLn(tl,#10#13'[*] Problemas de convergància em c†lculo de ra°zes');
            IF ordem>0 THEN WriteLn(tl,'[*] Ra°z de multiplicidade ',ordem+1);
            WriteLn('  Erro atual: ',t);
            WriteLn('  Magnitude:  ',p);
            WriteLn('  Derivada:   ',d);
            Write('  TolerÉncia p/ra°zes'); LerReal(tolr1);
            Write('  TolerÉncia p/magnitudes'); LerReal(tolm1);
            Write('  TolerÉncia p/derivadas'); LerReal(told1);
            Write('  AproximaáÑo real'); LerReal(xr);
            Write('  AproximaáÑo imag'); LerReal(xi);
            Write(tl,'[');
            nn:=0;
          END
        END
      END
    END
    ELSE BEGIN
      {Ultimas ra°zes}
      d:=-(Sqr(a1[1])+Sqr(a2[1]));
      xr:=(a1[0]*a1[1]+a2[0]*a2[1])/d;
      xi:=(a2[0]*a1[1]-a1[0]*a2[1])/d;
      feito:=TRUE; nn:=0;
      FOR i:=n+ordem DOWNTO n DO BEGIN
        Write(i,' ');
        zr[i]:=xr; zi[i]:=xi;
      END
    END
  END;
  WriteLn(tl,']');
END; {RaizesBiv}

PROCEDURE RaizesLib; {Ra°zes do polinomio x por Linn-Barstow}
  CONST
    imax=150;
  VAR
    n:INTEGER;
    t,u,v,u1,v1,c1,c2,c3,d:REAL;
    ca,cb:coeficientes;

  PROCEDURE Terminar;
  BEGIN
  END;

  PROCEDURE LerParametros;
  BEGIN
    WriteLn('  Erro atual: ',t);
    Write('  TolerÉncia p/ra°zes'); LerReal(tolr1);
    Write('  Nova aproximaáÑo para u'); LerReal(u);
    Write('  Nova aproximaáÑo para v'); LerReal(v)
  END;

  PROCEDURE Resolve;
  BEGIN
    WITH x DO BEGIN
      d:=u*u-4*v;
      IF d>=0 THEN BEGIN
        zr[n]:=(-u+Sqrt(d))/2;
        zr[n-1]:=(-u-Sqrt(d))/2;
        zi[n]:=0; zi[n-1]:=0
      END
      ELSE BEGIN
        zr[n]:=-u/2; zr[n-1]:=-u/2;
        zi[n]:=Sqrt(-d)/2; zi[n-1]:=-zi[n]
      END;
      n:=n-2
    END
  END;

BEGIN
  WITH x DO BEGIN
    IF grau=0 THEN Exit;
    ca:=a;
    v:=Sqr(xr0)+Sqr(xi0); u:=-xr0-xi0;
    n:=grau;
    WHILE (ca[0]=0) AND (n>1) DO BEGIN
      zr[n]:=0; zi[n]:=0;
      n:=n-1;
      FOR j:=0 TO n DO ca[j]:=ca[j+1]
    END;
    REPEAT
      IF n=1 THEN BEGIN
        zr[1]:=-ca[0]/ca[1]; zi[1]:=0;
        Terminar; Exit
      END;
      IF n=2 THEN BEGIN
        u:=ca[1]/ca[2]; v:=ca[0]/ca[2];
        Resolve;
        Terminar; Exit
      END;
      i:=0;
      REPEAT
        IF i=imax THEN BEGIN
          WriteLn(tl,'[*] Problemas de convergància no c†lculo das freqÅàncias dos extremos');
          Write('Desistir'); LerBool(erro);
          IF erro THEN Exit;
          LerParametros;
          i:=0
        END;
        i:=i+1;
        cb[n]:=ca[n]; c2:=cb[n];
        cb[n-1]:=ca[n-1]-u*cb[n];
        c1:=cb[n-1]-u*c2;
        FOR j:=n-2 DOWNTO 1 DO BEGIN
          c3:=c2; c2:=c1;
          cb[j]:=ca[j]-u*cb[j+1]-v*cb[j+2];
          c1:=cb[j]-u*c2-v*c3
        END;
        cb[0]:=ca[0]-u*cb[1]-v*cb[2];
        IF (c3<>0) and (c2<>0) and (c1<>0) THEN BEGIN
          u1:=(cb[0]/c2-cb[1]/c3)/(c2/c3-c1/c2);
          v1:=(cb[1]/c2-cb[0]/c1)/(c2/c1-c3/c2)
        END
        ELSE BEGIN
          d:=c2*c2-c1*c3;
          u1:=(cb[0]*c3-cb[1]*c2)/d;
          v1:=(cb[1]*c1-cb[0]*c2)/d
        END;
        u:=u-u1; v:=v-v1;
        t:=Abs(u1)+Abs(v1);
      UNTIL (t<tolr1) OR (i>imax);
      Resolve;
      FOR j:=0 TO n DO ca[j]:=cb[j+2]
    UNTIL FALSE;
  END
END; {RaizesLib}

PROCEDURE OrdenarRaizes(re:BOOLEAN);
  VAR
    ordenado:BOOLEAN;
    t:REAL;
BEGIN
  WITH x DO
    IF re THEN REPEAT
      ordenado:=TRUE;
      FOR i:=1 TO grau-1 DO
        IF (zr[i+1]<zr[i]) THEN BEGIN
          t:=zr[i]; zr[i]:=zr[i+1]; zr[i+1]:=t;
          t:=zi[i]; zi[i]:=zi[i+1]; zi[i+1]:=t;
          ordenado:=FALSE
        END
    UNTIL ordenado
    ELSE REPEAT
      ordenado:=TRUE;
      FOR i:=1 TO grau-1 DO
        IF (zi[i+1]>zi[i]) THEN BEGIN
          t:=zr[i]; zr[i]:=zr[i+1]; zr[i+1]:=t;
          t:=zi[i]; zi[i]:=zi[i+1]; zi[i+1]:=t;
          ordenado:=FALSE
        END
    UNTIL ordenado
END;

PROCEDURE ResolverSistema(VAR H:matriz; n:INTEGER);
  VAR
    l,a:INTEGER;
    t,p:REAL;
BEGIN
  erro:=FALSE;
  FOR i:=1 TO n DO BEGIN
    t:=0; a:=i;
    FOR l:=i TO n DO
      IF Abs(H[l,i])>Abs(t) THEN
        BEGIN a:=l; t:=H[l,i] END;
    IF i<>a THEN
      FOR l:=1 TO n+1 DO
        BEGIN p:=H[i,l]; H[i,l]:=H[a,l]; H[a,l]:=p END;
    IF Abs(t)<tolp THEN
      BEGIN WriteLn(tl,'[*] Sistema de equaáîes singular'); erro:=TRUE; Exit END;
    FOR j:=n+1 DOWNTO i+1 DO BEGIN
      H[i,j]:=H[i,j]/t;
      p:=H[i,j];
      FOR l:=1 TO n DO
        IF l<>i THEN
          H[l,j]:=H[l,j]-H[l,i]*p
    END
  END
END;

PROCEDURE Otimizar(VAR xo,yo:polinomio; VAR f,w:valores; n,p,py:INTEGER; alfa:REAL);
  VAR
    H:matriz;
    ultimo_w:valores;
    convergiu:BOOLEAN;
    wk,d,tol:REAL;
    iter:INTEGER;
  LABEL fim;

BEGIN
  m:=(n-p) DIV 2+1;
  ultimo_w:=w;
  tol:=tolo;
  x:=xo;
  iter:=0;
  REPEAT
      {===Montar X'(w)Yr(w)-Yr'(w)X(w)===}
    y:=yo;
    Inverter(y);
    Limpar(y);
    z:=x; t:=y;
    Derivar;
    Multiplicar;
    z:=x; x:=t;
    Derivar;
    Multiplicar;
    Subtrair;
    Limpar(x);
      {===Reduzir grau do polinìmio===}
    j:=p-1; {n£mero de zeros na origem de K'(jw)}
    x.grau:=(x.grau-j) div 2;
    FOR i:=0 TO x.grau DO IF 2*i+j>=0 THEN x.a[i]:=x.a[2*i+j];
      {===Achar freqÅàncias de extremo===}
    RaizesLib;
    IF erro THEN Exit;
    OrdenarRaizes(TRUE);
    FOR i:=1 TO m-1 DO BEGIN
      IF zi[i]<>0 THEN
        WriteLn(tl,'[*] PrecisÑo insuficiente no c†lculo de ra°zes');
      IF zr[i]<0 THEN
        WriteLn(tl,'[*] SeqÅància de extremos inv†lida');
      w[i]:=Sqrt(Abs(zr[i]));
    END;
      {===Verificar convergància===}
    i:=1; convergiu:=TRUE;
    WHILE convergiu and (i<m) DO BEGIN
      d:=Abs(w[i]-ultimo_w[i]);
      Write('  Î',i,': ',d,#13);
      IF d>tol THEN BEGIN
        convergiu:=FALSE;
        convergiu_direto:=FALSE
      END;
      i:=i+1
    END;
    ultimo_w:=w;
      {===Montar sistema de equaáîes===}
    FOR i:=1 TO m-1 DO BEGIN
      wk:=y.a[y.grau];
      FOR j:=y.grau-1 DOWNTO 0 DO wk:=wk*w[i]+y.a[j];
      H[i,m+1]:=f[i]*wk/alfa;
      wk:=1;
      FOR j:=1 TO p DO wk:=wk*w[i];
      FOR j:=1 TO m DO BEGIN
        H[i,j]:=wk;
        wk:=wk*Sqr(w[i])
      END
    END;
    FOR i:=1 TO m+1 DO H[m,i]:=1;
      {===Resolver sistema de equaáîes===}
    ResolverSistema(H,m);
    IF erro THEN Exit;
      {===Copiar soluáÑo atual para x===}
    FOR i:=0 TO n DO x.a[i]:=0;
    FOR i:=1 TO m DO x.a[p+i+i-2]:=H[i,m+1];
    x.grau:=n; x.cte:=1;
    iter:=iter+1;
  UNTIL (iter=itermax) or convergiu or KeyPressed;
   {=== Terminar ===}
  fim:
  xo:=x
END;

PROCEDURE Produto(VAR t:polinomio);
  VAR
    sinal:REAL;
    i,j,l:INTEGER;
BEGIN
  x.grau:=t.grau;
  x.cte:=Sqr(t.cte);
  FOR i:=0 TO x.grau DO x.a[i]:=0;
  FOR i:=0 TO t.grau DO BEGIN
    IF Odd(i) THEN sinal:=-1 ELSE sinal:=1;
    FOR j:=0 TO t.grau DO
      IF NOT Odd(i+j) THEN BEGIN
        l:=(i+j) DIV 2;
        x.a[l]:=x.a[l]+t.a[i]*t.a[j]*sinal
      END
  END
END;

PROCEDURE Montar(ct:REAL);
  VAR
    t:REAL;
    i,j:INTEGER;
BEGIN
  x.cte:=ct;
  y.cte:=ct;
  y.grau:=x.grau;
  FOR i:=0 TO x.grau DO
    BEGIN x.a[i]:=0; y.a[i]:=0 END;
  x.a[0]:=1;
  FOR i:=1 TO x.grau DO BEGIN
    FOR j:=i DOWNTO 1 DO BEGIN
      t:=x.a[j-1]-zr[i]*x.a[j]+zi[i]*y.a[j];
      y.a[j]:=y.a[j-1]-zr[i]*y.a[j]-zi[i]*x.a[j];
      x.a[j]:=t
    END;
    t:=-zr[i]*x.a[0]+zi[i]*y.a[0];
    y.a[0]:=-zr[i]*y.a[0]-zi[i]*x.a[0];
    x.a[0]:=t
  END;
  t:=0;
  FOR i:=0 TO y.grau DO IF Abs(y.a[i])>t THEN t:=Abs(y.a[i]);
  IF t>tolm THEN
    WriteLn(tl,'[*] Poss°vel c†lculo inexato do polinìmio E(s)');
END;

FUNCTION Angle(re,im:REAL):REAL;
CONST
  pouco=1e-9;
VAR
  fase:REAL;
BEGIN
  IF Abs(re)<pouco THEN BEGIN
    IF Abs(im)<pouco THEN Angle:=0
    ELSE
      IF im>0 THEN Angle:=pi/2
      ELSE Angle:=-pi/2
  END
  ELSE BEGIN
    fase:=ArcTan(im/re);
    IF re<0 THEN
      IF im>0 THEN fase:=fase+pi ELSE fase:=fase-pi;
    Angle:=fase
  END
END;

PROCEDURE HdeK(VAR f,p,e:polinomio);
VAR
  modulo,fase:REAL;
  i:INTEGER;
BEGIN
  Produto(f);
  y:=x;
  Produto(p);
  Somar;
  RaizesBiv(FALSE);
  OrdenarRaizes(TRUE);
  FOR i:=1 TO x.grau DO BEGIN
    modulo:=Sqrt(Sqrt(Sqr(zr[i])+Sqr(zi[i])));
    fase:=Angle(zr[i],zi[i])/2;
    zr[i]:=-modulo*Cos(fase);
    zi[i]:=modulo*Sin(fase);
  END;
  WriteLn(tl,'[-] P¢los calculados');
  Montar(1);
  IF f.grau=p.grau THEN MultC(Sqrt(Sqr(f.cte)+Sqr(p.cte))) ELSE MultC(f.cte);
  e:=x;
  WriteLn(tl,'[-] E(s) calculado');
END;

PROCEDURE AproxInic(n,p:INTEGER; VAR xo:polinomio);
BEGIN
  m:=(n-p) DIV 2+1;
  IF Odd(n) THEN j:=n-p+1 ELSE j:=n-p;
  {
  WriteLn(tl,'AproximaáÑo inicial: [w^',n-j,'.C',j,'(w)]');
  }
  Chebyshev(j);
  FOR j:=1 TO n-j DO MultS;
  xo:=x;
END;

PROCEDURE FDefault(n,p:INTEGER; VAR f:valores);
BEGIN
  m:=(n-p) DIV 2+1;
  FOR i:=1 TO m-1 DO BEGIN
    IF Odd(m) xor Odd(i) THEN f[i]:=-1 ELSE f[i]:=1;
  END;
END;

PROCEDURE InicW(n,p:INTEGER; VAR w:valores);
BEGIN
  FOR i:=1 TO (n-p) div 2 DO w[i]:=1
END;

PROCEDURE LerExtremos(VAR f,w:valores; epsilon,alfa:REAL; n,p:INTEGER; funcao:STRING; bp:BOOLEAN);
VAR
  at:valores;
  indice:INTEGER;
  temp:REAL;
BEGIN
  m:=(n-p) DIV 2+1;
  indice:=1;
  IF m>1 THEN REPEAT
    WriteLn(tl,'Extremos de [',funcao,'] em 0Ûw<1:');
    FOR i:=1 TO m-1 DO BEGIN
      IF bp THEN at[i]:=10*Ln(1+Sqr(epsilon*f[i]))/Ln(10)
      ELSE IF f[i]<>0 THEN at[i]:=10*Ln(1+Sqr(epsilon*Sqr(alfa)/f[i]))/Ln(10)
        ELSE at[i]:=1000;
      Write(tl,'f([',i,']): ',f[i]:cm:dc,'   Aten([',i,']): ',at[i]:cm:dc,' dB');
      IF at[i]>=1000 THEN WriteLn(' (inf)') ELSE WriteLn;
    END;
    Write(tl,'Mudar [f], [A]tenuaáÑo ou confirmar ([Cr]): ');
    REPEAT ch:=UpKey UNTIL ch in ['F','A',#13];
    WriteLn(tl,'[',ch,']');
    IF ch<>#13 THEN BEGIN
      REPEAT
        Write('Indice'); LerInt(indice);
      UNTIL (indice>0) and (indice<m);
      CASE ch OF
        'F':BEGIN
              Write(tl,'Extremo f([',indice,'])'); LerReal(f[indice]);
              calculado:=FALSE;
            END;
        'A':BEGIN
              Write(tl,'AtenuaáÑo no extremo f([',indice,']) (dB)'); LerReal(at[indice]);
              at[indice]:=Abs(at[indice]);
              IF at[indice]<1000 THEN BEGIN
                IF bp THEN temp:=Sqrt(Ex(10,0.1*at[indice])-1)/epsilon
                ELSE temp:=epsilon*Sqr(alfa)/Sqrt(Ex(10,0.1*at[indice])-1)
              END
              ELSE temp:=0;
              IF f[indice]>0 THEN f[indice]:=temp ELSE f[indice]:=-temp;
              calculado:=FALSE;
            END
      END
    END
  UNTIL ch=#13;
END;

PROCEDURE CabPol(texto:STRING; scte:BOOLEAN);
BEGIN
  IF scte THEN j:=2 ELSE j:=1;
  WriteLn(arquivo,ct[1],Linha(ct[10],(m+j)*(cmt+1)+2),ct[3]);
  WriteLn(arquivo,ct[11],texto,Linha(' ',(m+j)*(cmt+1)+2-Length(texto)),ct[11]);
  WriteLn(arquivo,ct[4],ct[10],ct[10],Linha(ct[2]+Linha(ct[10],cmt),m+j),ct[6]);
  Write(arquivo,ct[11],' n');
  IF scte THEN Write(arquivo,ct[11],'cte':cmt);
    FOR i:=0 TO m DO BEGIN
    Str(i,txt);
    Write(arquivo,ct[11],'a'+txt:cmt)
  END;
  WriteLn(arquivo,ct[11]);
  WriteLn(arquivo,ct[4],ct[10],ct[10],Linha(ct[5]+Linha(ct[10],cmt),m+j),ct[6]);
END;

PROCEDURE SalvarPolinomio(n:INTEGER; VAR x:polinomio; scte:BOOLEAN); {Usa j de CabPol}
BEGIN
  Write(arquivo,ct[11],n:2);
  IF scte THEN Write(arquivo,ct[11],x.cte:cmt:dct);
  FOR i:=0 TO m DO
    IF (i<=x.grau) and (Abs(x.a[i])>tolm) THEN Write(arquivo,ct[11],x.a[i]:cmt:dct)
    ELSE Write(arquivo,ct[11],' ':cmt);
  WriteLn(arquivo,ct[11]);
  IF fil=nfil THEN
    WriteLn(arquivo,ct[7],ct[10],ct[10],Linha(ct[8]+Linha(ct[10],cmt),m+j),ct[9])
  {
  ELSE
    WriteLn(arquivo,ct[4],ct[10],ct[10],Linha(ct[5]+Linha(ct[10],cmt),m+j),ct[6])
  }
END;

PROCEDURE CabPolos(texto:STRING);
BEGIN
  WriteLn(arquivo,ct[1],Linha(ct[10],m*(cmt+1)+2),ct[3]);
  WriteLn(arquivo,ct[11],texto,Linha(' ',m*(cmt+1)+2-Length(texto)),ct[11]);
  WriteLn(arquivo,ct[4],ct[10],ct[10],Linha(ct[2]+Linha(ct[10],cmt),m),ct[6]);
  Write(arquivo,ct[11],' n');
    FOR i:=1 TO m DO BEGIN
    Str((i+1) div 2,txt);
    IF Odd(i) THEN Write(arquivo,ct[11],'re/im '+txt:cmt)
    ELSE Write(arquivo,ct[11],'w/Q '+txt:cmt)
  END;
  WriteLn(arquivo,ct[11]);
  WriteLn(arquivo,ct[4],ct[10],ct[10],Linha(ct[5]+Linha(ct[10],cmt),m),ct[6]);
END;

PROCEDURE SalvarPolos(n,nr:INTEGER; VAR zr,zi:raizes);
VAR
  k:INTEGER;
BEGIN
  Write(arquivo,ct[11],n:2);
  k:=0;
  FOR i:=1 TO m DO BEGIN
    IF Odd(i) THEN BEGIN
      Inc(k);
      IF (i<=nr) and (Abs(zr[k])>tolm) THEN Write(arquivo,ct[11],zr[k]:cmt:dct)
      ELSE Write(arquivo,ct[11],' ':cmt)
    END
    ELSE IF (i<=nr) THEN Write(arquivo,ct[11],Sqrt(Sqr(zr[k])+Sqr(zi[k])):cmt:dct)
      ELSE Write(arquivo,ct[11],' ':cmt)
  END;
  WriteLn(arquivo,ct[11]);
  Write(arquivo,ct[11],'  ');
  k:=0;
  FOR i:=1 TO m DO BEGIN
    IF Odd(i) THEN BEGIN
      Inc(k);
      IF (i<=nr) and (Abs(zi[k])>tolm) THEN Write(arquivo,ct[11],zi[k]:cmt:dct)
      ELSE Write(arquivo,ct[11],' ':cmt)
    END
    ELSE IF (i<=nr) THEN BEGIN
      IF Abs(zr[k])>tolm THEN Write(arquivo,ct[11],-Sqrt(Sqr(zr[k])+Sqr(zi[k]))/2/zr[k]:cmt:dct)
      ELSE Write(arquivo,ct[11],'inf':cmt)
    END
    ELSE Write(arquivo,ct[11],' ':cmt)
  END;
  WriteLn(arquivo,ct[11]);
  IF fil=nfil THEN
    WriteLn(arquivo,ct[7],ct[10],ct[10],Linha(ct[8]+Linha(ct[10],cmt),m),ct[9])
  {
  ELSE WriteLn(arquivo,ct[4],ct[10],ct[10],Linha(ct[5]+Linha(ct[10],cmt),m),ct[6])
  }
END;

PROCEDURE CabZeros(texto:STRING);
BEGIN
  WriteLn(arquivo,ct[1],Linha(ct[10],m div 2*(cmt+1)+2),ct[3]);
  WriteLn(arquivo,ct[11],texto,Linha(' ',m div 2*(cmt+1)+2-Length(texto)),ct[11]);
  WriteLn(arquivo,ct[4],ct[10],ct[10],Linha(ct[2]+Linha(ct[10],cmt),m div 2),ct[6]);
  Write(arquivo,ct[11],' n');
    FOR i:=1 TO m div 2 DO BEGIN
      Str(i,txt);
      Write(arquivo,ct[11],'w'+txt:cmt)
    END;
  WriteLn(arquivo,ct[11]);
  WriteLn(arquivo,ct[4],ct[10],ct[10],Linha(ct[5]+Linha(ct[10],cmt),m div 2),ct[6]);
END;

PROCEDURE SalvarZeros(n,nr:INTEGER; VAR zi:raizes);
BEGIN
  Write(arquivo,ct[11],n:2);
  FOR i:=1 TO m div 2 DO BEGIN
    IF (i<=nr div 2) and (Abs(zi[i])>tolm) THEN Write(arquivo,ct[11],zi[i]:cmt:dct)
    ELSE Write(arquivo,ct[11],' ':cmt)
  END;
  WriteLn(arquivo,ct[11]);
  IF fil=nfil THEN
    WriteLn(arquivo,ct[7],ct[10],ct[10],Linha(ct[8]+Linha(ct[10],cmt),m div 2),ct[9])
  {
  ELSE WriteLn(arquivo,ct[4],ct[10],ct[10],Linha(ct[5]+Linha(ct[10],cmt),m div 2),ct[6])
  }
END;

PROCEDURE SalvarLadders;
BEGIN
  IF salvarladder THEN BEGIN
    WriteLn(arquivo,ct[1],Linha(ct[10],(m+1)*(cmt+1)+2),ct[3]);
    txt:='Ladder LC d. t.';
    WriteLn(arquivo,ct[11],txt,Linha(' ',(m+1)*(cmt+1)+2-Length(txt)),ct[11]);
    WriteLn(arquivo,ct[4],ct[10],ct[10],Linha(ct[2]+Linha(ct[10],cmt),m+1),ct[6]);
    Write(arquivo,ct[11],' n',ct[11],'Rg/Rl':cmt);
      FOR i:=1 TO m DO BEGIN
      Str(i,txt);
      Write(arquivo,ct[11],'L/C '+txt:cmt)
    END;
    WriteLn(arquivo,ct[11]);
    WriteLn(arquivo,ct[4],ct[10],ct[10],Linha(ct[5]+Linha(ct[10],cmt),m+1),ct[6]);
    FOR fil:=1 TO nfil DO
      WITH Tabela[fil]^ DO BEGIN
        Write(arquivo,ct[11],n:2,ct[11],rg:cmt:dct);
        FOR i:=1 TO m DO
          IF (i<=n) and (L[i]<>0) THEN Write(arquivo,ct[11],L[i]:cmt:dct) ELSE Write(arquivo,ct[11],' ':cmt);
        WriteLn(arquivo,ct[11]);
        Write(arquivo,ct[11],'  ',ct[11],rl:cmt:dct);
        FOR i:=1 TO m DO
          IF (i<=n) and (C[i]<>0) THEN Write(arquivo,ct[11],C[i]:cmt:dct) ELSE Write(arquivo,ct[11],' ':cmt);
        WriteLn(arquivo,ct[11]);
        IF fil=nfil THEN
          WriteLn(arquivo,ct[7],ct[10],ct[10],Linha(ct[8]+Linha(ct[10],cmt),m+1),ct[9])
        ELSE WriteLn(arquivo,ct[4],ct[10],ct[10],Linha(ct[5]+Linha(ct[10],cmt),m+1),ct[6])
      END
  END
END;

PROCEDURE Ladder(VAR item:filtro);
VAR
  EmaisF,EmenosF,sr,si,xr,xi,d1,d0,k1,k0:REAL;
  ez,extraindo:BOOLEAN;
  sec,sec1,proxz,nzt:INTEGER;

  PROCEDURE Armazenar(lc,cl:REAL);
  VAR
    onde:INTEGER;
  BEGIN
    onde:=item.n+1-sec;
    IF listarz22 THEN Write(tl,'[SeáÑo no. ',onde,']: ');
    WITH item DO
      IF ez THEN BEGIN
        IF listarz22 THEN BEGIN
          WriteLn(tl,'Tanque [//] em [sÇrie]:');
          WriteLn('L=',Cpct(lc),' C=',Cpct(cl))
        END;
        C[onde]:=cl; L[onde]:=lc;
      END
      ELSE BEGIN
        IF listarz22 THEN BEGIN
          WriteLn(tl,'Tanque [sÇrie] em [//]:');
          WriteLn('C=',Cpct(lc),' L=',Cpct(cl))
        END;
        C[onde]:=lc; L[onde]:=cl;
      END
  END;

  PROCEDURE InvImitancia;
  BEGIN
    ez:=not ez;
    z:=x; x:=y; y:=z;
  END;

  PROCEDURE ExtrairPoloNoInfinito;
  BEGIN
    IF (x.grau>y.grau) THEN BEGIN
      Dec(x.grau,2);
      FOR i:=1 TO x.grau DO x.a[i]:=x.a[i]-y.a[i-1];
      Armazenar(x.cte/y.cte,0);
      Normalizar(x)
    END
    ELSE BEGIN
      erro:=TRUE;
      WriteLn(tl,'[*] NÑo h† p¢lo no infinito para extrair')
    END
  END;

  PROCEDURE Avaliar; {Avalia x/y sem ctes; Recebe sr+jzi; Retorna xr+jxi}
  VAR
    dr,di,nr,ni,t:REAL;
  BEGIN
    dr:=0; di:=0;
    FOR i:=y.grau DOWNTO 0 DO BEGIN
      t:=dr*sr-di*si+y.a[i];
      di:=dr*si+di*sr;
      dr:=t
    END;
    nr:=0; ni:=0;
    FOR i:=x.grau DOWNTO 0 DO BEGIN
      t:=nr*sr-ni*si+x.a[i];
      ni:=nr*si+ni*sr;
      nr:=t
    END;
    t:=dr*dr+di*di;
    xr:=(nr*dr+ni*di)/t;
    xi:=(ni*dr-nr*di)/t;
  END;

  PROCEDURE EliminarFator(VAR b:polinomio);
  BEGIN
    z.a[0]:=b.a[0]/d0;
    z.a[1]:=(b.a[1]-z.a[0]*d1)/d0;
    FOR i:=2 TO b.grau {-2} DO z.a[i]:=(b.a[i]-z.a[i-2]-z.a[i-1]*d1)/d0;
    IF (Abs(z.a[b.grau])>tolm) or (Abs(z.a[b.grau-1])>tolm) THEN
      WriteLn(tl,'[*] Poss°vel remoáÑo incorreta de fator');
    Dec(b.grau,2);
    b.a:=z.a;
  END;

  PROCEDURE RemoverTanque;
  VAR
    c1,g1,l2,r2:REAL;
  BEGIN
    IF si<>0 THEN BEGIN
      c1:=1/(x.cte/y.cte*k1);
      g1:=c1*(d1-k0/k1);
      l2:=1/(c1*(d0-g1/c1*k0/k1));
      r2:=l2*k0/k1;
      Armazenar(l2,c1);
      IF not ez THEN BEGIN
        IF Abs(r2)>tolm THEN WriteLn(tl,'[*] Em sÇrie com L: ',r2:cm:dc);
        IF Abs(g1)>tolm THEN WriteLn(tl,'[*] Em // com C: ',1/g1:cm:dc);
      END
      ELSE BEGIN
        IF Abs(g1)>tolm THEN WriteLn(tl,'[*] Em sÇrie com L: ',g1:cm:dc);
        IF Abs(r2)>tolm THEN WriteLn(tl,'[*] Em // com C: ',1/r2:cm:dc)
      END
    END
    ELSE BEGIN
      WriteLn(tl,'[*] NÑo implementada extraáÑo de tanque RC ou RL');
      erro:=TRUE
    END
  END;

  PROCEDURE RemoverPolos;
  BEGIN
    IF si<>0 THEN BEGIN
      d1:=-2*sr; d0:=sr*sr+si*si;
      EliminarFator(y);
      Avaliar;
      k1:=xi/si; k0:=xr-k1*sr;
      RemoverTanque;
      FOR i:=0 TO y.grau DO BEGIN
        x.a[i]:=x.a[i]-y.a[i]*k0;
        x.a[i+1]:=x.a[i+1]-y.a[i]*k1
      END;
      EliminarFator(x);
      Normalizar(x);
      Normalizar(y);
      extraindo:=FALSE;
      Inc(proxz);
    END
    ELSE BEGIN
      WriteLn(tl,'[*] NÑo implementada extraáÑo de polo real');
      erro:=TRUE
    END
  END;

  PROCEDURE DeslocarZero;
  VAR
    dr,di,t:REAL;
  BEGIN
    IF (x.grau>y.grau) THEN BEGIN
      Avaliar;
      t:=sr*sr+si*si;
      dr:=(xr*sr+xi*si)/t;
      di:=(xi*sr-xr*si)/t;
      IF (dr>=0) and (Abs(di)<tolm) and (dr<=1) THEN BEGIN
        Armazenar(x.cte/y.cte*dr,0);
        FOR i:=1 TO x.grau DO x.a[i]:=x.a[i]-y.a[i-1]*dr;
        Normalizar(x);
        extraindo:=TRUE;
      END
      ELSE BEGIN
        WriteLn(tl,'[*] Imposs°vel criar o zero em ',sr:cm:dc,' ',si:cm:dc,'j');
        erro:=TRUE
      END
    END
    ELSE BEGIN
      WriteLn(tl,'[*] NÑo h† polo no infinito para extrair parcialmente');
      erro:=TRUE
    END
  END;

BEGIN
  WITH item DO BEGIN
    EmenosF:=eo.cte*eo.a[0]-fo.cte*fo.a[0];
    EmaisF:=eo.cte*eo.a[0]+fo.cte*fo.a[0];
    rl:=1; rg:=EmaisF/EmenosF;
    k0:=Sqrt(1/(rl*rg));
    rl:=k0*rl;
    rg:=k0*rg;
    FOR j:=0 TO n DO
      IF Odd(j) THEN BEGIN
        y.a[j]:=eo.cte*eo.a[j]+fo.cte*fo.a[j];
        x.a[j]:=0
      END
      ELSE BEGIN
        x.a[j]:=eo.cte*eo.a[j]+fo.cte*fo.a[j];
        y.a[j]:=0
      END;
    x.cte:=k0; y.cte:=1; x.grau:=n; y.grau:=n;
    Normalizar(x);
    Normalizar(y);
    IF listarz22 THEN BEGIN
      WriteLn(tl,'[rg]= ',rg:cm:dc);
      WriteLn(tl,'[rl]= ',rl:cm:dc);
      WriteLn(tl,'[Numerador da impedÉncia Z22] (Ee+Fe):');
      ListarPolinomio(x);
      WriteLn(tl,'[Denominador da impedÉncia Z22] (Eo+Fo):');
      ListarPolinomio(y);
    END;
    IF eo.grau=po.grau THEN BEGIN
      erro:=TRUE;
      WriteLn(tl,'[*] RealizaáÑo duplamente terminada imposs°vel: NÑo h† zero no infinito');
      Exit
    END;
    ez:=TRUE;
    IF x.grau<y.grau THEN InvImitancia;
    extraindo:=FALSE;
    proxz:=1; nzt:=po.grau div 2;
    sec1:=(n-po.grau-1) div 2+1;
    FOR i:=1 TO nzt DO BEGIN {Ordenamento dos zeros}
      IF Odd(i) THEN j:=i div 2+1
      ELSE j:=nzt-i div 2+1;
      zr[j]:=ztr[i]; zi[j]:=zti[i];
    END;
    FOR sec:=1 TO n DO BEGIN
      IF extraindo THEN RemoverPolos
        ELSE BEGIN
          IF escolher THEN BEGIN
            WriteLn(tl,'[Zeros] de transmissÑo:');
            FOR i:=1 TO nzt DO WriteLn(tl,'z([',i,']): ',zr[i]:cm:dc,' ',zi[i]:cm:dc,'j');
            j:=proxz;
            REPEAT
              Write(tl,'Pr¢ximo zero (0=infinito)'); LerInt(j)
            UNTIL (j>=0) and (j<=nzt);
            IF j=0 THEN ExtrairPoloNoInfinito
            ELSE BEGIN
              si:=zi[j]; sr:=zr[j];
              DeslocarZero
            END
          END
          ELSE BEGIN
            IF (sec<sec1) or (proxz>nzt) or (not Odd(n) and (sec=n div 2) and not Odd(nzt)) THEN
              ExtrairPoloNoInfinito
            ELSE BEGIN
              j:=proxz;
              si:=zi[j]; sr:=zr[j];
              DeslocarZero;
            END
          END
        END;
      IF erro THEN Exit;
      IF sec<n THEN InvImitancia
    END
  END;
  WriteLn(tl,'[-] Rede ladder LC d. t. calculada')
END;

PROCEDURE CalcularTabela(VAR item:filtro);
BEGIN
  WITH item DO BEGIN
    erro:=FALSE;
    WriteLn(tl,'[Filtro no. ',fil,']');
    tolr1:=tolr;
    WriteLn(tl,'[-] Otimizando X(w) e Y(w)');
    REPEAT
      convergiu_direto:=TRUE;
      Otimizar(xo,yo,fx,wx,n,px,py,alfa);
      IF erro THEN Exit;
      Otimizar(yo,xo,fy,wy,n,py,px,alfa);
      IF erro THEN Exit;
    UNTIL convergiu_direto or Keypressed;
    WriteLn;
    WriteLn(tl,'[-] X(w) e Y(w) calculados');
    x:=xo;
    y:=yo;
    MultC(alfa);
    Inverter(y);
    Limpar(y);
    IF norm THEN ReEscalar;
    Normalizar(x);
    Normalizar(y);
    y.cte:=y.cte/x.cte/epsilon;
    x.cte:=1;
    ConverterParaS(x);
    ConverterParaS(y);
    po:=y;
    fo:=x;
    WriteLn(tl,'[-] F(s) e P(s) calculados');
    WriteLn(tl,'[-] Calculando p¢los e E(s)');
    HdeK(fo,po,eo);
    OrdenarRaizes(FALSE);
    pre:=zr; pim:=zi;
    IF po.grau>0 THEN BEGIN
      x:=po;
      WriteLn(tl,'[-] Calculando zeros');
      RaizesBiv(TRUE);
      OrdenarRaizes(FALSE);
      ztr:=zr; zti:=zi;
      WriteLn(tl,'[-] Zeros calculados')
    END;
    IF salvarladder THEN Ladder(item);
    IF erro THEN FOR i:=1 TO n DO BEGIN C[i]:=0; L[i]:=0 END;
    erro:=FALSE;
    IF salvarlattice or salvarcom or salvarsem THEN Lattice(item);
    IF erro THEN BEGIN za.n:=0; zb.n:=0; ca.n:=0; sa.n:=0 END;
    erro:=FALSE
  END
END;

PROCEDURE Menu;
BEGIN
  WriteLn(tl,'- [E]specificar tabela a gerar ou mudar especificaáîes');
  WriteLn(tl,'- Ler especificaáîes da tabela em [A]rquivo');
  WriteLn(tl,'- [C]alcular a tabela de filtros');
  WriteLn(tl,'- [L]istar/salvar °tens da tabela calculada');
  WriteLn(tl,'- [S]alvar a tabela gerada');
  IF calculado THEN BEGIN
    WriteLn(tl,'- Recalcular [U]m °tem da tabela, especificando a ordem dos zeros');
    WriteLn(tl,'- Gr†fico de ‡[X](w)/Yr(w), funáÑo caracter°stica normalizada');
    WriteLn(tl,'- Gr†fico de ≥1/[H](jw)≥, m¢dulo da funáÑo de transferància');
    WriteLn(tl,'- Gr†fico de [T]g(w), atraso de grupo');
  END;
  WriteLn(tl,'- Mudar [P]arÉmetros do programa');
  WriteLn(tl,'- [D]iret¢rio');
  WriteLn(tl,'- [Esc]: Fim');
  WriteLn(tl,'- [Cr]: Este menu');
  WriteLn(tl,'- [?]: Instruáîes');
END;

BEGIN
DetectGraph(placa,modo);
IF placa=CGA THEN modo:=CGAC0;
InitGraph(placa,modo,GetEnv('TPBGI'));
xmin:=57;
xmax:=GetMaxX;
ymin:=0;
ymax:=GetMaxY-10;
IF placa<>CGA THEN BEGIN
  cor1:=EgaWhite;
  cor2:=EgaYellow;
  cor3:=EgaLightGray
END
ELSE BEGIN
  cor1:=3;
  cor2:=1;
  cor3:=2;
END;
TextMode(80);
nfil:=0;
i:=(MaxAvail-1000) div SizeOf(filtro);
IF i<nfilmax THEN filmax:=i ELSE filmax:=nfilmax;
FOR fil:=1 TO filmax DO BEGIN
  New(Tabela[fil]);
  WITH Tabela[fil]^ DO BEGIN
    n:=0;
    px:=1;
    py:=1;
    Amax:=1;
    Amin:=40
  END
END;
nome:='';
fim:=FALSE;
ClrScr;
WriteLn(tl,'[GeraáÑo de Tabelas de Filtros Eletricamente SimÇtricos ou AntimÇtricos]');
WriteLn(tl,'[----------------------------------------------------------------------]');
WriteLn('Antìnio Carlos MoreirÑo de Queiroz - COPPE/UFRJ');
WriteLn('VersÑo ',versao,' - PrecisÑo ',precisao);
Assign(arquivo,config);
{$i-} Reset(arquivo); {$I+}
IF IOResult=0 THEN BEGIN
  ReadLn(arquivo,txt);
  IF txt=versao THEN BEGIN
    ReadLn(arquivo,ch); norm:=ch='T';
    ReadLn(arquivo,ch); salvarf:=ch='T';
    ReadLn(arquivo,ch); imzeros:=ch='T';
    ReadLn(arquivo,ch); salvarcte:=ch='T';
    ReadLn(arquivo,ch); salvarladder:=ch='T';
    ReadLn(arquivo,ch); listarz22:=ch='T';
    ReadLn(arquivo,ch); salvarlattice:=ch='T';
    ReadLn(arquivo,ch); expandirz:=ch='T';
    ReadLn(arquivo,ch); salvarcom:=ch='T';
    ReadLn(arquivo,ch); salvarsem:=ch='T';
    ReadLn(arquivo,cmt,dct,cm,dc,
                   tolr,xr0,xi0,
                   tolm,tolo,tolp,told,toln);
  END
END;
IF ParamCount>0 THEN BEGIN
  WriteLn(tl,#10'[Modo "batch"]'#10);
  batch:=TRUE;
  param:=0;
  GoTo batch1
END;
inicio:
WriteLn; Menu; WriteLn(tl,'[#]');
REPEAT
  CASE UpKey OF
    'E':BEGIN
          REPEAT
            Write(tl,'N£mero de filtros na tabela (m†x=[',filmax,'])'); LerInt(nfil);
          UNTIL nfil<=filmax;
          FOR fil:=1 TO nfil DO WITH Tabela[fil]^ DO BEGIN
            n0:=n; px0:=px; py0:=py; Amin0:=Amin; Amax0:=Amax;
           denovo:
            WriteLn(tl,#10'[Filtro no. ',fil,'] (de ',nfil,')[:]');
            Write(tl,'Ordem da aproximaáÑo (m†x=[',gmax,'])'); LerInt(n);
            Write('AtenuaáÑo m°nima na banda de rejeiáÑo (dB)'); LerReal(Amin);
            Write('AtenuaáÑo m†xima na banda passante (dB)'); LerReal(Amax);
            Write('No. de zeros de atenuaáÑo na origem'); LerInt(px);
            Write('No. de zeros de transmissÑo no infinito'); LerInt(py);
            erro:=FALSE;
            IF (n>gmax) or (Odd(n) xor Odd(px)) or (Odd(n) xor Odd(py)) or (n<px) or (n<py) or (n<=0) THEN BEGIN
              WriteLn(tl,'[*] ParÉmetros inv†lidos');
              GoTo denovo;
            END;
            epsilon:=Sqrt(Ex(10,0.1*Amax)-1);
            WriteLn(tl,'[Ó]: ',epsilon:cm:dc);
            alfa:=Sqrt(Sqrt(Ex(10,0.1*Amin)-1)/epsilon);
            WriteLn(tl,'[‡]: ',alfa:cm:dc);
            WriteLn(tl,'[X(w)]:');
            IF (n0<>n) or (px0<>px) THEN BEGIN
              AproxInic(n,px,xo);
              FDefault(n,px,fx);
            END;
            LerExtremos(fx,wx,epsilon,alfa,n,px,'‡X(w)/Yr(w)',TRUE);
            WriteLn(tl,'[Y(w)]:');
            IF (n0<>n) or (py0<>py) THEN BEGIN
              AproxInic(n,py,yo);
              FDefault(n,py,fy);
            END;
            LerExtremos(fy,wx,epsilon,alfa,n,py,'‡Y(w)/Xr(w)',FALSE);
            Write(tl,'[M]odificar algo, [R]ecomeáar ou confirmar ([Cr]):');
            ch:=UpKey;
            WriteLn;
            IF ch='R' THEN GoTo inicio;
            IF ch='M' THEN GoTo denovo;
            IF (n<>n0) or (px<>px0) or (py<>py0) or (Amin<>Amin0) or (Amax<>Amax0) THEN
              calculado:=FALSE
          END
        END;
    'A':BEGIN
          Write(tl,'Nome do arquivo com a tabela: '); EditarLinha(nome,WhereX,WhereY,1); WriteLn;
          batch1: IF batch THEN BEGIN Inc(param); nome:=ParamStr(param) END;
          Assign(arquivo,nome);
          {$I-} Reset(arquivo) {$I+};
          IF IOResult=0 THEN BEGIN
            ReadLn(arquivo,nfil);
            ReadLn(arquivo);
            FOR fil:=1 TO nfil DO WITH Tabela[fil]^ DO BEGIN
              Read(arquivo,n,Amax,px);
              FOR i:=1 TO (n-px) div 2 DO Read(arquivo,fx[i]);
              ReadLn(arquivo);
              Read(arquivo,Amin,py);
              FOR i:=1 TO (n-py) div 2 DO Read(arquivo,fy[i]);
              epsilon:=Sqrt(Ex(10,0.1*Amax)-1);
              alfa:=Sqrt(Sqrt(Ex(10,0.1*Amin)-1)/epsilon);
              AproxInic(n,px,xo);
              AproxInic(n,py,yo);
              calculado:=FALSE
            END;
            IF batch THEN GoTo batch2
          END
          ELSE BEGIN
            WriteLn(tl,'[*] Arquivo inexistente');
            batch:=FALSE
          END
        END;
    'C':BEGIN
         batch2:
          IF not calculado THEN FOR fil:=1 TO nfil DO WITH Tabela[fil]^ DO BEGIN
            InicW(n,px,wx);
            InicW(n,py,wy)
          END;
          erro:=FALSE;
          FOR fil:=1 TO nfil DO WITH Tabela[fil]^ DO IF not erro THEN BEGIN
            CalcularTabela(Tabela[fil]^);
            IF erro THEN BEGIN
              AproxInic(n,px,xo);
              AproxInic(n,py,yo)
            END
          END;
          calculado:=not erro;
          IF batch THEN GoTo batch3
        END;
    'U':IF calculado THEN BEGIN
          REPEAT
            Write(tl,'Recalcular qual °tem dos [',nfil,']'); LerInt(fil)
          UNTIL fil<=nfil;
          erro:=FALSE; escolher:=TRUE;
          CalcularTabela(Tabela[fil]^);
          escolher:=FALSE
        END;
    'X':IF calculado THEN Grafico(1,wmin,wmax,kmin,kmax,log);
    'H':IF calculado THEN Grafico(2,wmin,wmax,tmin,tmax,log);
    'T':IF calculado THEN Grafico(3,wmin,wmax,dmin,dmax,log);
    'L':BEGIN
          FOR fil:=1 TO nfil DO WITH Tabela[fil]^ DO BEGIN
            WriteLn(tl,#10'[Filtro no. ',fil,']');
            WriteLn(tl,'Ordem: [',n,']; Amin: [',Cpct(Amin),']; Amax: [',Cpct(Amax),']');
            WriteLn(tl,'px: [',px,']; py: [',py,']');
            IF calculado THEN BEGIN
              WriteLn(tl,'Polinìmio [X(w)]:');
              ListarPolinomio(xo);
              WriteLn(tl,'Polinìmio [Y(w)]:');
              ListarPolinomio(yo);
              WriteLn(tl,'Polinomio [F(s)]:');
              ListarPolinomio(fo);
              WriteLn(tl,'Polinìmio [E(s)]:');
              ListarPolinomio(eo);
              WriteLn(tl,'Polinìmio [P(s)]:');
              ListarPolinomio(po);
              WriteLn(tl,'[P¢los], ra°zes de E(s):');
              ListarRaizes(eo.grau,eo.cte,pre,pim);
              WriteLn(tl,'[Zeros], ra°zes de P(s):');
              ListarRaizes(po.grau,po.cte,ztr,zti);
              WriteLn(tl,'Rede [ladder LC d. t.]');
              ListarRede(Tabela[fil]^);
              ListarLattice(Tabela[fil]^);
            END
            ELSE WriteLn(tl,'[*] Tabela nÑo calculada');
          END
        END;
    'S':BEGIN
          Write(tl,'Arquivo onde salvar a tabela: '); EditarLinha(nome,WhereX,WhereY,1); WriteLn;
          batch3:
          Assign(arquivo,nome);
          ReWrite(arquivo);
          WriteLn(arquivo,nfil,' filtros');
          WriteLn(arquivo,' n',' ','Amax/min':15,' px/y',' fx/y');
          FOR fil:=1 TO nfil DO WITH Tabela[fil]^ DO BEGIN
            Write(arquivo,n:2,' ',Amax:15:10,px:5);
            FOR i:=1 TO (n-px) div 2 DO Write(arquivo,' ',Cpct(fx[i]):2);
            WriteLn(arquivo);
            Write(arquivo,'   ',Amin:15:10,py:5);
            FOR i:=1 TO (n-py) div 2 DO Write(arquivo,' ',Cpct(fy[i]):2);
            WriteLn(arquivo);
          END;
          IF calculado THEN BEGIN
            m:=0; FOR fil:=1 TO nfil DO IF Tabela[fil]^.n>m THEN m:=Tabela[fil]^.n;
            IF salvarf THEN BEGIN
              CabPol('Polinìmios F(s)',salvarcte);
              FOR fil:=1 TO nfil DO WITH Tabela[fil]^ DO SalvarPolinomio(n,fo,salvarcte);
            END;
            CabPol('Polinìmios E(s)',salvarcte);
            FOR fil:=1 TO nfil DO WITH Tabela[fil]^ DO SalvarPolinomio(n,eo,salvarcte);
            CabPolos('P¢los');
            FOR fil:=1 TO nfil DO WITH Tabela[fil]^ DO SalvarPolos(n,eo.grau,pre,pim);
            m:=0; FOR fil:=1 TO nfil DO IF Tabela[fil]^.po.grau>m THEN m:=Tabela[fil]^.po.grau;
            CabPol('Polinìmios P(s)',TRUE);
            FOR fil:=1 TO nfil DO WITH Tabela[fil]^ DO SalvarPolinomio(n,po,TRUE);
            IF m>0 THEN BEGIN
              IF imzeros THEN BEGIN
                CabZeros('Zeros');
                FOR fil:=1 TO nfil DO WITH Tabela[fil]^ DO SalvarZeros(n,po.grau,zti)
              END
              ELSE BEGIN
                CabPolos('Zeros de transmissÑo');
                FOR fil:=1 TO nfil DO WITH Tabela[fil]^ DO SalvarPolos(n,po.grau,ztr,zti)
              END
            END;
            m:=0; FOR fil:=1 TO nfil DO IF Tabela[fil]^.n>m THEN m:=Tabela[fil]^.n;
            SalvarLadders;
            SalvarLattices;
          END
          ELSE WriteLn(arquivo,'Tabela nÑo calculada');
          Close(arquivo);
          IF batch THEN IF param=ParamCount THEN Exit ELSE Goto batch1
        END;
    'P':BEGIN
          Write('Normalizar filtros para corte em 1 rad/s'); LerBool(norm);
          Write('Salvar F(s) nas tabelas'); LerBool(salvarf);
          Write('Salvar apenas a parte imagin†ria dos zeros'); LerBool(imzeros);
          Write('Salvar cte. multiplicativa de E(s) e F(s)'); LerBool(salvarcte);
          Write('Realizar em ladder LC dup. term.'); LerBool(salvarladder);
          Write('Listar impedÉncia Z22 e detalhes da realizaáÑo em ladder'); LerBool(listarz22);
          Write('Realizar em lattice LC dup. term.'); LerBool(salvarlattice);
          Write('Expandir a lattice com base em impedÉncias'); LerBool(expandirz);
          Write('Realizar em lattice desbal. c/acoplamentos'); LerBool(salvarcom);
          Write('Realizar em lattice desbal. s/acoplamentos'); LerBool(salvarsem);
          Write('Campo para reais nas tabelas'); LerInt(cmt);
          Write('Decimais para reais nas tabelas'); LerInt(dct);
          Write('Campo para reais normal'); LerInt(cm);
          Write('Decimais para reais normal'); LerInt(dc);
          Write('TolerÉncia p/ra°zes'); LerReal(tolr);
          Write('Aprox. inicial real'); LerReal(xr0);
          Write('Aprox. inicial imag'); LerReal(xi0);
          Write('TolerÉncia p/magnitudes'); LerReal(tolm);
          Write('TolerÉncia p/otimizaáÑo'); LerReal(tolo);
          Write('TolerÉncia p/pivot'); LerReal(tolp);
          Write('TolerÉncia p/derivadas'); LerReal(told);
          Write('DispersÑo m†xima para polinìmios'); LerReal(toln);
          {
          Write('Escolher a ordem de realizaáÑo dos zeros'); LerBool(escolher);
          Write('N£mero de iteraáîes antes da inversÑo de K (otimizaáÑo)'); LerInt(itermax);
          }
          Write('Salvar configuraáÑo ao terminar'); LerBool(salvarcfg)
        END;
    'D':Diretorio;
    #27:BEGIN
          Write('Terminar'); LerBool(fim);
          IF fim and salvarcfg THEN BEGIN
            Assign(arquivo,config);
            ReWrite(arquivo);
            WriteLn(arquivo,versao,#13#10,
               norm,#13#10,salvarf,#13#10,imzeros,#13#10,salvarcte,#13#10,
               salvarladder,#13#10,listarz22,#13#10,
               salvarlattice,#13#10,expandirz,#13#10,salvarcom,#13#10,salvarsem,#13#10,
               cmt,#13#10,dct,#13#10,cm,#13#10,dc,#13#10,
               tolr,#13#10,xr0,#13#10,xi0,#13#10,
               tolm,#13#10,tolo,#13#10,tolp,#13#10,told,#13#10,toln);
            Close(arquivo);
            WriteLn(tl,'[-] ConfiguraáÑo salva no arquivo [',config,']')
          END
        END;
    #13:Menu;
    '?':BEGIN
          WriteLn(tl,'[-] O programa [EletSim] calcula tabelas de filtros passa-baixas normalizados.');
          WriteLn(tl,'[-] Qualquer aproximaáÑo entre a de [Butterworth] e a de [Cauer] pode ser gerada.');
          WriteLn(tl,'[-] Modo [batch]: Dar nomes de arquivos de especificaáîes na linha de comando.');
          WriteLn(tl,'  O formato dos arquivos de especificaáîes Ç como o inicio de uma tabela.');
          WriteLn(tl,'[-] Gr†fico de y=[‡X(w)/Yr(w)]: [y] atÇ ≥y≥Û1 e [Ò(1+Ln(≥y≥)] para ≥y≥>1.');
          WriteLn(tl,'[-] As realizaáîes em ["ladder"] e ["lattice"] sÑo das formas:');
          WriteLn(tl,'                ⁄-[L2]ƒø');
          WriteLn(tl,'      oƒƒ[Rg]ƒƒ¬ƒƒ¥    √ƒ¬ƒƒ-   ƒƒƒ¬ƒƒo                oƒƒ[L1]ƒƒj[X1]ƒƒ¬ƒƒƒ¬ƒ- ');
          WriteLn(tl,'             [L1] ¿-[C2]ƒŸ [L3]        ≥      impedÉncias              ≥   ≥   ');
          WriteLn(tl,' "ladder"    ≥         ≥         [Rl]     da "lattice"             [C2] j[X2]  ');
          WriteLn(tl,'             [C1]        [C3]        ≥      d. t. em R=[1]             ≥   ≥   ');
          WriteLn(tl,'      oƒƒƒƒƒƒ¡ƒƒƒƒƒƒƒƒƒ¡ƒƒƒ   ƒƒƒ¡ƒƒo                oƒƒƒƒƒƒƒƒƒƒƒ¡ƒƒƒ¡ƒƒ ');
          WriteLn(tl,'[-] A formas em ["lattice" desbalanceada] sÑo das formas:');
          WriteLn(tl,'                I1->                  <-I1''');
          WriteLn(tl,'         oƒ[1]ƒ[L1]ƒ-+v-ƒ¬ƒƒ¬ƒƒ    ƒƒ¬ƒƒ¬--v+ƒƒ[L1]ƒ[1]ƒo     oƒ[1]ƒ[L1]ƒ¬-[CM2]ƒ¬-[L1]ƒ¬-o');
          WriteLn(tl,'              s[ML1]I1''≥  + +    + +  ≥ s[ML1]I1                 √ƒ   ƒ¥    ≥  ');
          WriteLn(tl,'  c/acopl.           [C2] i V2 V2'' i  [C2]            s/acopl.   [C2] ≥ [C2]    [1]  ');
          WriteLn(tl,'  n °mpar            ≥  - -    - -  ≥             n °mpar    ¿ƒƒ≈ƒƒŸ    ≥  ');
          WriteLn(tl,'         oƒƒƒƒƒƒƒƒƒƒƒ¡ƒƒ¡ƒ-    ƒƒ¡ƒƒ¡ƒƒƒƒƒƒƒƒƒƒ-o              [LM1]      ≥  ');
          WriteLn(tl,'                     s[MC2]V2''  s[MC2]V2                  oƒƒƒƒƒƒƒƒƒ¡ƒƒƒƒƒƒƒ¡-o');
          WriteLn(tl,'  c/acopl. n par, mudar: s[ML] -> j[X]; s[MC] -> -j/[X] (jX=resistor imagin†rio)');
          WriteLn(tl,'  s/acopl. n par, mudar: [L] -> [L]+j[X]; [C] -> [C]//j[X]; [CM],[LM] -> j[XM] (negativo)');
          WriteLn(tl,'  [+v-] = f. de tensÑo contr. a corrente. [+i-] = f. de corrente contr. a tensÑo.');
        END;
  END;
  WriteLn(tl,'[#]');
UNTIL fim;
END.

