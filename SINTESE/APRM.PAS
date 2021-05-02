PROGRAM Aprm;
{******************************************************************************
 * Aproximaáîes racionais multibanda                                          *
 * Antìnio Carlos MoreirÑo de Queiroz                                         *
 * VersÑo 1.0 de 31/07/1993                                                     *
 * Vers∆o 1.1 de 24/07/2003
 ******************************************************************************}

{
Reformulacao total, dividindo a parte positiva da frequencia em uma serie
de bandas que podem ser passantes ou de rejeicao.
Cada banda e definida por um polinomio par que tem suas raizes nela.
O que acontece em DC e infinito e definido por uma potencia de w que
multiplica o numerador ou o denominador.
Falta ver se e necessario restringir a cte. multiplicativa dos polinomios.
E possivel a criacao de falsos extremos nas bandas de rejeicao.
A solucao encontrada e ignora-los, forcando o ultimo extremo a ser o limite
da banda.
Nao esta funcionando (?) para filtros sem zeros em 0 ou infinito.
Implementando possibilidade de f=0 nas bandas de rejeicao.
4/7/2003 - Inclu°dos testes de validade no menu.
11/7/2003 - Funciona sem zeros em 0, com banda inicial passante, mas h† problemas com falta de zeros no infinito.
}

{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}

USES Crt,Dos,Graph,Tela;
CONST
  versao='1.1 de 24/07/2003';
  gmax=40;
  mmax=20;
  mmax1=21;
  bmax=10;
  tolr:REAL=1e-11;
  toln:REAL=1e-11;
  tolp:REAL=1e-11;
  told:REAL=1e-11;
  cm:INTEGER=26;
  dc:INTEGER=18;
  itermax:INTEGER=1;
  x1:REAL=0.01;
  x2:REAL=4;
  y1:REAL=-4;
  y2:REAL=4;
  a0:REAL=1.1;
  b0:REAL=-1.1;
  listar:BOOLEAN=TRUE;
  Amin:REAL=40;
  Amax:REAL=1;

TYPE
  coeficientes=ARRAY[0..gmax] OF REAL;
  polinomio=
  RECORD
    grau:INTEGER;
    cte:REAL;
    a:coeficientes;
  END;
  matriz=ARRAY[1..mmax,1..mmax1] OF REAL;
  valores=ARRAY[1..mmax] OF REAL;
VAR
  xo,yo,x,y,z,t:polinomio;
  banda:ARRAY[1..bmax] OF
    RECORD
      passante:BOOLEAN;
      fk:valores;
      wk:valores;
      pol:polinomio;
      limite:REAL; {Limite superior}
    END;
  zr,zi:ARRAY[1..gmax] OF REAL;
  nbandas,placa,modo,i,j,k,m,zao,zto,nt:INTEGER;
  ch:CHAR;
  arquivo:TEXT;
  txt:STRING;
  alfa,epsilon:REAL;
  raizes_calculadas,convergiu,erro,k_valido:BOOLEAN;
  tolr1:REAL;
  ok:BOOLEAN;

FUNCTION Ex(x,y: REAL): REAL;  {x^y}
BEGIN Ex:=Exp(y*Ln(x)) END;

PROCEDURE Grafico;
  CONST
    x0=100;
    xm=639;
    y0=0;
    ym=460;
  VAR
    ax,bx,ay,by,p,w,d:REAL;
    xg,yg,xa,ya,i,j,k:INTEGER;
    LABEL atualizar;

  FUNCTION Limx(x:REAL):INTEGER;
  BEGIN
    x:=ax*x+bx;
    IF x>xm THEN Limx:=xm
    ELSE IF x<x0 THEN Limx:=x0
    ELSE Limx:=Round(x)
  END;

  FUNCTION Limy(y:REAL):INTEGER;
  BEGIN
    y:=ay*y+by;
    IF y>ym THEN Limy:=ym
    ELSE IF y<y0 THEN Limy:=y0
    ELSE Limy:=Round(y)
  END;

  FUNCTION LinLog(y:REAL):REAL;
  VAR
    p:REAL;
  BEGIN
    p:=Abs(y);
    IF p>1 THEN p:=Ln(p)/Ln(10)+1;
    IF y<0 THEN p:=-p;
    LinLog:=p
  END;

BEGIN
  REPEAT
    SetGraphMode(modo);
    Rectangle(x0,y0,xm,ym);
    SetColor(LightGray);
    SetLineStyle(DottedLn,0,NormWidth);
    ay:=(y0-ym)/(y2-y1); by:=ym-ay*y1;
    ax:=(xm-x0)/(x2-x1); bx:=x0-ax*x1;
    Line(x0,Limy(0),xm,Limy(0));
    Line(Limx(0),y0,Limx(0),ym);
    SetColor(Red);
    k:=Limy(LinLog(1));
    Line(x0,k,xm,k);
    k:=Limy(LinLog(-1));
    Line(x0,k,xm,k);
    k:=Limy(LinLog(Sqr(alfa)));
    Line(x0,k,xm,k);
    k:=Limy(LinLog(-Sqr(alfa)));
    Line(x0,k,xm,k);
    FOR i:=1 TO nbandas DO WITH banda[i] DO BEGIN
      SetColor(yellow);
      Line(Limx(limite),y0,Limx(limite),ym);
      SetColor(green);
      k:=pol.grau div 2+1;
      FOR j:=1 TO k DO IF wk[k]<>0 THEN
        IF passante THEN Line(Limx(wk[j]),Limy(0),Limx(wk[j]),Limy(LinLog(fk[j])))
        ELSE Line(Limx(wk[j]),Limy(0),Limx(wk[j]),Limy(LinLog(Sqr(alfa)/fk[j])));
    END;
    SetColor(White);
    SetLineStyle(SolidLn,0,NormWidth);
    IF KeyPressed THEN GOTO atualizar;
    SetTextJustify(LeftText,TopText);
    Str(x1:7:3,txt); OutTextXY(x0,ym+2,txt);
    SetTextJustify(RightText,TopText);
    Str(x2:7:3,txt); OutTextXY(xm,ym+2,txt);
    SetTextJustify(RightText,BottomText);
    Str(y1:7:3,txt); OutTextXY(x0,ym,txt);
    OutTextXY(x0,Limy(0)+4,'K(jw)/e');
    OutTextXY(x0,Limy(LinLog(Sqr(1)))-8,'Log(K(jw)/e)');
    OutTextXY(x0,Limy(LinLog(-Sqr(1)))+16,'Log(K(jw)/e)');
    SetTextJustify(RightText,TopText);
    Str(y2:7:3,txt); OutTextXY(x0,y0,txt);
    OutTextXY((x0+xm) div 2,ym+2,'w');
    FOR xg:=x0 TO xm DO BEGIN
      w:=(xg-bx)/ax;
      p:=x.a[x.grau];
      FOR i:=x.grau-1 DOWNTO 0 DO p:=p*w+x.a[i];
      d:=p*x.cte;
      p:=y.a[y.grau];
      FOR i:=y.grau-1 DOWNTO 0 DO p:=p*w+y.a[i];
      d:=d/(p*y.cte);
      yg:=Limy(LinLog(d));
      IF xg>x0 THEN
        Line(xa,ya,xg,yg);
      xa:=xg; ya:=yg;
      IF KeyPressed THEN GOTO atualizar;
    END;
    atualizar:
    ch:=ReadKey;
    IF ch=#0 THEN ch:=ReadKey;
    CASE UpCase(ch) OF
    '-':y2:=y1+(y2-y1)*2;
    '+':y2:=y1+(y2-y1)/2;
    'R':x2:=x1+(x2-x1)*2;
    'A':x2:=x1+(x2-x1)/2;
    'M':BEGIN d:=(x2-x1)/4; x1:=x1+d; x2:=x2+d END;
    'K':BEGIN d:=(x2-x1)/4; x1:=x1-d; x2:=x2-d END;
    'H':BEGIN d:=(y2-y1)/4; y1:=y1+d; y2:=y2+d END;
    'P':BEGIN d:=(y2-y1)/4; y1:=y1-d; y2:=y2-d END;
    #27:;
    #13:;
    ELSE Goto atualizar
    END
  UNTIL (ch=#27) or (ch=#13);
  RestoreCrtMode;
END;

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
    WHILE (a[grau]=0) AND (grau>=0) DO grau:=grau-1;
  END
END; {Limpar}

PROCEDURE Normalizar(VAR x:polinomio);
VAR i:INTEGER;
BEGIN
  Limpar(x);
  WITH x DO BEGIN
    IF a[grau]<>1 THEN BEGIN
      cte:=cte*a[grau];
      FOR i:=0 TO grau DO a[i]:=a[i]/a[grau]
    END
  END
END; {Normalizar}

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

PROCEDURE ListarRaizes(grau:INTEGER);
VAR
  i:INTEGER;
BEGIN
  IF raizes_calculadas THEN
    FOR i:=1 TO grau DO
      WriteLn(tl,'[-] w([',i:2,'])=',zr[i]:cm:dc,zi[i]:cm:dc,'j')
  ELSE WriteLn(tl,'[*] NÑo h† ra°zes [*]');
  ch:=ReadKey;
END;

PROCEDURE ListarPolinomio(VAR x:polinomio);
VAR
  i:INTEGER;
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

PROCEDURE Enter;
BEGIN
  t:=z; z:=y; y:=x
END;

PROCEDURE Chebyschev(n:INTEGER);
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
VAR
  i:INTEGER;
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
    ELSE WriteLn(tl,'[*] Arquivo inexistente [*]')
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
VAR
  i:INTEGER;
BEGIN
  WITH x DO BEGIN
    FOR i:=0 TO grau DO BEGIN
      j:=i MOD 4;
      IF ((j=1) OR (j=2)) THEN a[i]:=-a[i]
    END;
    IF a[grau]<0 THEN FOR i:=0 TO grau DO a[i]:=-a[i];
    cte:=Abs(cte);
  END
END;

PROCEDURE Raizes; {Ra°zes do polinomio x por Linn-Barstow}
CONST
  imax=150;
VAR
  i,n,j:INTEGER;
  t,u,v,u1,v1,c1,c2,c3,d:REAL;
  ca,cb:coeficientes;

  PROCEDURE Terminar;
  BEGIN
    raizes_calculadas:=TRUE
  END;

  PROCEDURE LerParametros;
  BEGIN
    tolr1:=tolr1*10;
    u:=Random;
    v:=Random;
    WriteLn('Tolerancia reduzida para ',tolr1);
    {
    Write('Nova tolerÉncia'); LerReal(t);
    tolr:=1.01*t;
    Write('Nova aprox. para u'); LerReal(u);
    Write('Nova aprox. para v'); LerReal(v);
    }
  END;

  PROCEDURE Resolve; {Calcula raizes de termo de 2o. grau}
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
  END; {Resolve}

BEGIN
  tolr1:=tolr;
  raizes_calculadas:=FALSE;
  WITH x DO BEGIN
    IF grau=0 THEN Exit;
    ca:=a;
    v:=Sqr(a0)+Sqr(b0); u:=-a0-b0;
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
          WriteLn('Problemas de convergància.');
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
END; {Raizes}

PROCEDURE OrdenarRaizes;
  VAR
    ordenado:BOOLEAN;
    t:REAL;
    i:INTEGER;
BEGIN
  WITH x DO
  REPEAT
    ordenado:=TRUE;
    FOR i:=1 TO grau-1 DO BEGIN
      IF zr[i+1]<zr[i] THEN BEGIN
        t:=zr[i]; zr[i]:=zr[i+1]; zr[i+1]:=t;
        t:=zi[i]; zi[i]:=zi[i+1]; zi[i+1]:=t;
        ordenado:=FALSE
      END
    END
  UNTIL ordenado;
END;

PROCEDURE ResolverSistema(VAR H:matriz; n:INTEGER);
  VAR
    i,j,l,a:INTEGER;
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
    IF Abs(t)<told THEN
      BEGIN WriteLn(tl,'[*] Sistema de equaáîes singular [*]'); erro:=TRUE; Exit END;
    FOR j:=n+1 DOWNTO i+1 DO BEGIN
      H[i,j]:=H[i,j]/t;
      p:=H[i,j];
      FOR l:=1 TO n DO
        IF l<>i THEN
          H[l,j]:=H[l,j]-H[l,i]*p
    END
  END
END; {ResolverSistema}

PROCEDURE MontarKjw;
VAR
  i:INTEGER;
BEGIN
  xo.grau:=0; xo.cte:=1; xo.a[0]:=1;
  yo.grau:=0; yo.cte:=1; yo.a[0]:=1;
  FOR i:=1 TO nbandas DO WITH banda[i] DO BEGIN
    IF passante THEN BEGIN
      x:=xo;
      y:=pol;
      Multiplicar;
      xo:=x
    END
    ELSE BEGIN
      x:=yo;
      y:=pol;
      Multiplicar;
      yo:=x
    END
  END;
  x:=yo; FOR i:=1 TO zto DO MultS;
  yo:=x;
  x:=xo; FOR i:=1 TO zao DO MultS;
  xo:=x;
  y:=yo
END;

PROCEDURE Estimar;
VAR
  l1,l2,delta:REAL;
  i,j,k:INTEGER;
BEGIN
  FOR i:=1 TO nbandas DO WITH banda[i] DO BEGIN
    IF i=1 THEN l1:=0 ELSE l1:=banda[i-1].limite;
    l2:=limite;
    x.a[0]:=1; x.grau:=0; x.cte:=1;
    IF pol.grau>0 THEN BEGIN
      k:=pol.grau div 2;
      delta:=(l2-l1)/k;
      FOR j:=1 TO k DO zr[j]:=l1+(0.5+(j-1))*delta;
      FOR j:=1 TO k DO BEGIN
        y.a[1]:=0;
        y.a[2]:=1;
        y.a[0]:=-Sqr(zr[j]);
        y.grau:=2;
        y.cte:=1;
        Multiplicar
      END
    END;
    pol:=x
  END;
  MontarKjw
END;

FUNCTION Valor(VAR p:polinomio; w:REAL):REAL;
VAR
  v:REAL;
  i:INTEGER;
BEGIN
  v:=p.a[p.grau];
  FOR i:=p.grau-1 DOWNTO 0 DO v:=v*w+p.a[i];
  Valor:=p.cte*v
END;

PROCEDURE Otimizar(qb:INTEGER);
VAR
  H:matriz;
  ultimo_w:valores;
  pd,pn,d,tol,l1,l2,wn:REAL;
  i,j,iter,k,m:INTEGER;

BEGIN
  WITH banda[qb] DO BEGIN
    m:=pol.grau div 2; {numero de coeficientes a determinar}
    IF m=0 THEN Exit;
    ultimo_w:=wk; {vetor}
    tol:=tolp;
    iter:=0;
    x:=xo;
    y:=yo;
    REPEAT
      {===Montar X'(w)Y(w)-Y'(w)X(w)===}
      Derivar;            {x',y,?,?}
      Multiplicar;        {x'y,?,?,?}
      z:=x; y:=xo; x:=yo; {y,x,x'y,?}
      Derivar;            {y',x,x'y,?}
      Multiplicar;        {y'x,x'y,?,?}
      Subtrair;           {y'x-x'y,?,?,?}
      Limpar(x);
      IF listar THEN BEGIN
        ClrScr;
        WriteLn('Banda ',qb,': Extremos (1 lado) de polinìmio de grau ',x.grau);
      END;
      {===Reduzir grau do polinìmio===}
      j:=0;
      WHILE x.a[j]=0 DO Inc(j); {n£mero de zeros na origem de K'(jw)}
      x.grau:=(x.grau-j) div 2;
      FOR i:=0 TO x.grau DO IF 2*i+j>=0 THEN x.a[i]:=x.a[2*i+j];
      {
      IF listar THEN BEGIN
        WriteLn('Polinìmio reduzido:');
        ListarPolinomio(x);
      END;
      }
      {===Achar freqÅàncias de extremo===}
      Raizes;
      OrdenarRaizes;
      {
      IF listar THEN BEGIN
        WriteLn('Raizes do polinìmio reduzido de grau ',x.grau,':');
        ListarRaizes(x.grau)
      END;
      }
      {===Testar raizes e reconverter===}
      FOR i:=1 TO x.grau DO BEGIN
        IF zi[i]<>0 THEN BEGIN
          IF listar THEN WriteLn(tl,'Extremo ',i,' complexo (ignorado)');
          zr[i]:=0; zi[i]:=0;
        END
        ELSE IF zr[i]>0 THEN BEGIN
          zr[i]:=Sqrt(zr[i]);
          IF listar THEN WriteLn('Extremo ',i,': ',zr[i]);
        END
        ELSE BEGIN
          zi[i]:=0; zr[i]:=0;
          IF listar THEN WriteLn(tl,'Extremo ',i,' imaginario (ignorado)');
        END
      END;
      {===Escolher extremos dentro da banda===}
      IF qb=1 THEN l1:=0 ELSE l1:=banda[qb-1].limite;
      IF qb<nbandas THEN l2:=limite ELSE l2:=1e30;
      IF qb=1 THEN BEGIN
        k:=0;
        IF (zao=0) and (zto=0) THEN BEGIN k:=1; wk[1]:=0 END {K(jw) Ç constante em 0}
      END
      ELSE BEGIN k:=1; wk[1]:=l1 END; {1o. limite}
      m:=pol.grau div 2+1;
      FOR i:=1 TO x.grau DO BEGIN
        IF (zr[i]>0) and (zr[i]>l1) and (zr[i]<l2) THEN BEGIN
          Inc(k);
          wk[k]:=zr[i];
        END
      END;
      IF qb<nbandas THEN BEGIN Inc(k); wk[k]:=l2 END; {2o. limite}
      IF listar THEN BEGIN
        WriteLn('Extremos encontrados na banda ',qb,':');
        FOR i:=1 TO k DO WriteLn('w',i,': ',wk[i],'; f',i,': ',fk[i]);
      END;
      IF k>m THEN BEGIN
        WriteLn;
        WriteLn(tl,'[*] Extremos demais na banda ',qb);
        convergiu:=TRUE;
        Exit
      END;
      IF k<m THEN BEGIN
        WriteLn;
        WriteLn(tl,'[*] Extremos a menos na banda ',qb);
        convergiu:=TRUE;
        Exit
      END;
      {===Verificar convergància===}
      i:=1; convergiu:=TRUE;
      WHILE convergiu and (i<=m) DO BEGIN
        d:=Abs(wk[i]-ultimo_w[i]);
        Write('Erro na freqÅància ',i,': ',d,#13);
        IF d>tol THEN convergiu:=FALSE;
        i:=i+1
      END;
      IF listar THEN BEGIN
        WriteLn;
        WriteLn('Toque uma tecla para prosseguir, ou ESC para completar');
        ch:=ReadKey;
        IF ch=#27 THEN listar:=FALSE
      END;
      ultimo_w:=wk;
      {===Montar sistema de equaáîes===}
      IF passante THEN
        FOR i:=1 TO m DO BEGIN
          pd:=Valor(yo,wk[i]); {Supoe-se yo, denominador, montado}
          pn:=1;
          FOR j:=1 TO zao DO pn:=pn*wk[i];
          FOR j:=1 TO nbandas DO IF (banda[j].passante) and (j<>qb) THEN
            pn:=pn*Valor(banda[j].pol,wk[i]);
          H[i,m+1]:=fk[i]*pd/pn;
          wn:=1;
          FOR j:=1 TO m DO BEGIN
            H[i,j]:=wn;
            wn:=wn*Sqr(wk[i])
          END
        END
      ELSE FOR i:=1 TO m DO BEGIN
        pn:=Valor(xo,wk[i]); {Supoe-se xo, numerador, montado}
        pd:=1;
        FOR j:=1 TO zto DO pd:=pd*wk[i];
        FOR j:=1 TO nbandas DO IF (not banda[j].passante) and (j<>qb) THEN
        pd:=pd*Valor(banda[j].pol,wk[i]);
        H[i,m+1]:=pn/pd*fk[i]/Sqr(alfa);
        wn:=1;
        FOR j:=1 TO m DO BEGIN
          H[i,j]:=wn;
          wn:=wn*Sqr(wk[i])
        END
      END;
      {===Resolver sistema de equaáîes===}
      ResolverSistema(H,m);
      IF erro THEN Halt;
      {===Copiar soluáÑo atual para pol===}
      FOR i:=0 TO pol.grau DO pol.a[i]:=0;
      FOR i:=1 TO m DO pol.a[i+i-2]:=H[i,m+1];
      pol.cte:=1;
      Normalizar(pol);
      {
      IF listar THEN BEGIN
        WriteLn(tl,^M^J'Polinomio da banda [',qb,']');
        ListarPolinomio(pol);
      END;
      }
      MontarKjw;
      iter:=iter+1;
    UNTIL (iter=itermax) or convergiu or KeyPressed;
    IF listar THEN Grafico
  END
  {=== Terminar ===}
END; {Otimizar}

PROCEDURE Menu;
BEGIN
  WriteLn(tl,'- [O]timizaáÑo para K(jw)=X(w)/Y(w)');
  WriteLn(tl,'- Gerar [K](s)=F(s)/P(s)=X(s/j)/Y(s/j)');
  WriteLn(tl,'- [L]istar os fatores de X(w) e Y(w)');
  WriteLn(tl,'- [G]r†fico de K(jw)');
  WriteLn(tl,'- Mudar [T]olerÉncias e parÉmetros do programa');
  WriteLn(tl,'- [D]iret¢rio');
  WriteLn(tl,'- [^Q]: Fim');
  WriteLn(tl,'- [Cr]: Este menu');
END;

BEGIN
placa:=VGA;
modo:=VGAHI;
InitGraph(placa,modo,GetEnv('TPBGI'));
TextMode(80);
zto:=1;
zao:=0;
nbandas:=3;
FOR i:=1 TO bmax DO WITH banda[i] DO BEGIN
  limite:=i;
  pol.grau:=0;
  FOR j:=1 TO mmax DO fk[j]:=0
END;
WITH banda[1] DO BEGIN
  limite:=0.2;
  fk[1]:=196.512846456719768
END;
WITH banda[2] DO BEGIN
  pol.grau:=6;
  limite:=1;
  fk[1]:=1; fk[2]:=-1; fk[3]:=1; fk[4]:=-1
END;
WITH banda[3] DO BEGIN
  pol.grau:=4;
  fk[1]:=-1; fk[2]:=1; fk[3]:=-1
END;
k_valido:=FALSE;
ClrScr;
WriteLn(tl,'[Ap]roximaáîes [R]acionais [M]ultibanda');
WriteLn(tl,'[---------------------------------]');
WriteLn('Por Antonio Carlos M. de Queiroz - acmq@ufrj.br');
WriteLn('COPPE/UFRJ - VersÑo ',versao,' - PrecisÑo ',precisao);
WriteLn('Este programa calcula funá‰es caracter°sticas para filtros');
WriteLn('normalizados multibanda que tenham ao menos um zero de');
WriteLn('transmissÑo ou de atenuaá∆o no infinito.');
WriteLn('Polinìmios de grau atÇ ',gmax,'; AtÇ ',bmax,' bandas');
WriteLn; Menu; WriteLn(tl,'[#]');
REPEAT
  CASE UpCase(ReadKey) OF
  'G':IF k_valido THEN Grafico
      ELSE WriteLn('NÑo h† nada a plotar');
  'T':BEGIN
      Write('Ver passos da otimizaáÑo (esc interrompe)'); LerBool(listar);
      Write('Tol. p/raizes'); LerReal(tolr);
      Write('Aprox. inicial real'); LerReal(a0);
      Write('Aprox. inicial imag'); LerReal(b0);
      Write('Tol. p/normalizaáÑo'); LerReal(toln);
      Write('Tol. p/otimizaáÑo'); LerReal(tolp);
      Write('Tol. p/pivot'); LerReal(told);
      Write('N£mero de iteraáîes antes da mudanca de banda'); LerInt(itermax);
      Write('Limite inicial x no gr†fico'); LerReal(x1);
      Write('Limite final   x no gr†fico'); LerReal(x2);
      Write('Limite inicial y no gr†fico'); LerReal(y1);
      Write('Limite final   y no gr†fico'); LerReal(y2);
      Write('Campo para reais'); LerInt(cm);
      Write('Decimais para reais'); LerInt(dc);
    END;
  'O':BEGIN
        WriteLn(tl,'[OtimizaáÑo para aproximaáÑo racional]:');
        Write('AtenuaáÑo m°nima nas bandas de rejeiáÑo'); LerReal(Amin);
        Write('AtenuaáÑo m†xima nas bandas passantes'); LerReal(Amax);
        epsilon:=Sqrt(Ex(10,0.1*Amax)-1);
        WriteLn(tl,'[epsilon (e)]: ',epsilon:cm:dc);
        alfa:=Sqrt(Sqrt(Ex(10,0.1*Amin)-1)/epsilon);
        WriteLn(tl,'[alfa (a)]: ',alfa:cm:dc);
        WriteLn(tl,'[a˝] (para [limites superiores] de bandas de rejeiáÑo): ',sqr(alfa):cm:dc);
        Write('No. de zeros de atenuaáÑo na origem (0 ou mais)'); LerInt(zao);
        IF zao=0 THEN BEGIN Write('No. de zeros de transmissÑo na origem (0 ou mais)'); LerInt(zto); END
        ELSE zto:=0;
        Write('No. de bandas (2 ou mais)'); LerInt(nbandas);
        FOR i:=1 TO nbandas DO WITH banda[i] DO BEGIN
          WriteLn(tl,'[Banda ',i,':]');
          IF i<nbandas THEN BEGIN
            Write('Limite superior de freqÅància'); LerReal(limite);
          END
          ELSE limite:=banda[i-1].limite*4;
          IF i>1 THEN passante:=not banda[i-1].passante;
          Write('Banda passante'); LerBool(passante);
          IF passante THEN txt:='atenuaáÑo' ELSE txt:='transmissÑo';
          Write('No. de zeros de ',txt,' fora de 0 ou infinito na banda (1 lado)');
          k:=pol.grau div 2;
          LerInt(k);
          pol.grau:=k+k;
          IF passante THEN WriteLn(tl,'Extremos de [K(jw)/e] na banda [',i,']:')
          ELSE WriteLn(tl,'Extremos de [ea˝/K(jw)] na banda [',i,']:');
          IF i>1 THEN BEGIN
            fk[1]:=Sqr(alfa)/banda[i-1].fk[banda[i-1].pol.grau div 2+1];
            WriteLn(tl,'Extremo [1] (limite inferior): [',Cpct(fk[1]),']');
            j:=2
          END
          ELSE j:=1;
          FOR j:=j TO k+1 DO BEGIN
            IF j=k+1 THEN BEGIN
              txt:='(limite superior, nao 0)';
            END
            ELSE BEGIN
              txt:='';
            END;
            Write(tl,'Extremo [',j,'] ',txt); LerReal(fk[j])
          END;
          FOR j:=1 TO k+1 DO wk[j]:=0
        END;
        Estimar;
        WriteLn(tl,'[Aproximacao inicial]:');
        WriteLn('[F](jw):');
        ListarPolinomio(xo);
        WriteLn('[P](jw):');
        ListarPolinomio(yo);
        ok:=TRUE;
        IF (xo.grau>yo.grau) THEN BEGIN
          WriteLn(tl,'Existem ',xo.grau-yo.grau,' zeros de transmissao no infinito.');
          IF banda[nbandas].passante THEN BEGIN
            WriteLn(tl,'[*] Esta faltando uma banda de rejeicao ao final.');
            ok:=FALSE
          END
        END
        ELSE IF (xo.grau<yo.grau) THEN BEGIN
          WriteLn(tl,'Existem ',yo.grau-xo.grau,' zeros de atenuaá∆o no infinito.');
          IF not banda[nbandas].passante THEN BEGIN
            WriteLn(tl,'[*] Esta faltando uma banda passante ao final.');
            ok:=FALSE
          END
        END
        ELSE BEGIN
          WriteLn(tl,'NÑo h† zeros de transmiss∆o ou atenuaá∆o no infinito.');
          WriteLn(tl,'[*] O programa nÑo resolve este caso, presentemente.');
          {ok:=FALSE}
        END;
        Write('Iniciar otimizacao'); LerBool(ok);
        IF ok THEN BEGIN
          convergiu:=TRUE;
          REPEAT
            FOR i:=1 TO nbandas DO BEGIN
              Otimizar(i);
            END;
          UNTIL convergiu or KeyPressed;
          IF convergiu THEN BEGIN
            WriteLn(tl,#13#10'[*] OtimizaáÑo completa');
            k_valido:=TRUE
          END
          ELSE WriteLn(tl,'[*] Interrompido');
        END
      END;
  'K':IF k_valido THEN BEGIN
        x:=xo;
        y:=yo;
        MultC(epsilon);
        Normalizar(x);
        Normalizar(y);
        y.cte:=y.cte/x.cte;
        x.cte:=1;
        ConverterParaS(x);
        ConverterParaS(y);
        WriteLn(tl,'Polinìmio [P(s)]:');
        ListarPolinomio(y);
        WriteLn(tl,'Polinìmio [F(s)]:');
        ListarPolinomio(x);
      END
      ELSE WriteLn('NÑo h† dados para gerar K.');
  'L':IF k_valido THEN BEGIN
        WriteLn(tl,'[Fatores do numerador de K(jw)/e]:');
        FOR i:=1 TO nbandas DO
          WITH banda[i] DO
            IF passante THEN BEGIN
              WriteLn(tl,'Banda [',i,']:');
              ListarPolinomio(banda[i].pol)
            END;
        WriteLn(tl,'[Fatores do denominador de K(jw)/e]:');
        FOR i:=1 TO nbandas DO
          WITH banda[i] DO
            IF not passante THEN BEGIN
              WriteLn(tl,'Banda [',i,']:');
              ListarPolinomio(banda[i].pol)
            END;
        WriteLn(tl,'Zeros de [atenuaáÑo] na origem: ',zao);
        WriteLn(tl,'Zeros de [transmissÑo] na origem: ',zto);
      END
      ELSE WriteLn('NÑo h† K calculado.');
  'D':Diretorio;
  ^Q:Halt;
  #13:Menu;
  END;
  WriteLn(tl,'[#]');
UNTIL FALSE;
END.
