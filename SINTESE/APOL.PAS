PROGRAM APol;
{******************************************************************************
 * Aproxima‡”es polinomiais para K(jw)                                        *
 * Ant“nio Carlos Moreir„o de Queiroz                                         *
 * Vers„o 2.0 de 07/10/87                                                     *
 * Vers„o 2.0a de 15/08/88 Atualizado                                         *
 * Vers„o 2.1 de 12/02/89 Turbo 5.0                                           *
 * Vers„o 2.2 de 03/08/89 Revis„o geral                                       *
 * Vers„o 2.2a de 12/09/89 Corre‡„o na leitura dos f                          *
 * Vers„o 2.2b de 28/11/89 Precis„o extendida                                 *
 * Vers„o 2.2c de 25/10/90 Atualizado                                         *
 * Vers„o 2.2d de 29/03/91 Transforma‡„o de Moebius simplificada              *
 * Vers„o 2.2e de 30/07/93 TPBGI                                              *
 * Vers„o 2.3  de 03/04/97 Salva valores em arquivo para Word
 ******************************************************************************}
{$IFDEF DOUBLE}
 {$N+,E+}
{$ENDIF}
USES Graph,Crt,Dos,Tela;

CONST gmax=60;
  mmax=20;
  mmax1=21;
  versao='2.3 de 03/04/97';
  cm:INTEGER=26;
  dc:INTEGER=18;
TYPE coeficientes=ARRAY[0..gmax] OF REAL;
  polinomio=
  RECORD
    a:coeficientes;
    grau:INTEGER;
    cte:REAL;
  END;
  matriz=ARRAY[1..mmax,1..mmax1] OF REAL;
VAR x,y,z,t:polinomio;
  zr,zi:ARRAY[1..gmax] OF REAL;
  placa,modo,i,j,k,p,n:INTEGER;
  r:CHAR;
  arquivo:TEXT;
  txt:STRING;
  xx,yy,epsilon,Amax,tolr,toln,tolp,told,a0,b0:REAL;
  raizes_calculadas,erro,escrever:BOOLEAN;

PROCEDURE Grafico;
  CONST x0=259;
    xm=639;
    y0=0;
    ym=199;
    margem=1;
  VAR x1,y1,x2,y2,ax,bx,ay,by,p,w,d:REAL;
    xg,yg,xa,ya:INTEGER;
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

BEGIN
  x1:=-xx;
  x2:=xx;
  y1:=-yy;
  y2:=yy;
  WITH x DO
  REPEAT
    SetGraphMode(modo);
    RecTangle(x0,y0,xm,ym);
    ay:=(y0-ym)/(y2-y1); by:=ym-ay*y1;
    ax:=(xm-x0)/(x2-x1); bx:=x0-ax*x1;
    Line(x0,Limy(0),xm,Limy(0));
    Line(Limx(0),y0,Limx(0),ym);
    SetLineStyle(DottedLn,0,NormWidth);
    Rectangle(Limx(-1)-margem,Limy(1)-margem,Limx(1)+margem,Limy(-1)+margem);
    SetLineStyle(SolidLn,0,NormWidth);
    IF KeyPressed THEN GOTO atualizar;
    Str(x1:7:3,txt); OutTextXY(0,0, 'x: w min:   '+txt);
    Str(x2:7:3,txt); OutTextXY(0,8, '   w max:   '+txt);
    Str(y1:7:3,txt); OutTextXY(0,16,'y: M(w) min:'+txt);
    Str(y2:7:3,txt); OutTextXY(0,24,'   M(w) max:'+txt);
    FOR xg:=x0 TO xm DO
    BEGIN
      w:=(xg-bx)/ax;
      p:=a[grau];
      FOR i:=grau-1 DOWNTO 0 DO p:=p*w+a[i];
      yg:=Limy(p*cte);
      IF xg>x0 THEN
        Line(xa,ya,xg,yg);
      xa:=xg; ya:=yg;
      IF escrever THEN
        WriteLn(arquivo,w,',',p*cte);
      IF KeyPressed THEN GOTO atualizar;
    END;
    OutTextXY(0,40,'+ amplia y');
    OutTextXY(0,48,'- reduz  y');
    OutTextXY(0,56,'A amplia x');
    OutTextXY(0,64,'R reduz  x');
    OutTextXY(0,72,'Cursor move');
    OutTextXY(0,80,'E escreve');
    OutTextXY(0,88,'Esc retorna');
    atualizar:
    r:=ReadKey;
    IF r=#0 THEN r:=ReadKey;
    IF escrever THEN BEGIN
      close(arquivo);
      escrever:=FALSE
    END;
    CASE UpCase(r) OF
    '-':y2:=y1+(y2-y1)*2;
    '+':y2:=y1+(y2-y1)/2;
    'R':x2:=x1+(x2-x1)*2;
    'A':x2:=x1+(x2-x1)/2;
    'M':BEGIN d:=(x2-x1)/4; x1:=x1+d; x2:=x2+d END;
    'K':BEGIN d:=(x2-x1)/4; x1:=x1-d; x2:=x2-d END;
    'H':BEGIN d:=(y2-y1)/4; y1:=y1+d; y2:=y2+d END;
    'P':BEGIN d:=(y2-y1)/4; y1:=y1-d; y2:=y2-d END;
    'E':BEGIN
      TextMode(80);
      Write(tl,'Arquivo onde salvar os valores ou [cr]: [');
      ReadLn(txt);
      IF Length(txt)>0 THEN BEGIN
        escrever:=TRUE;
        Assign(arquivo,txt);
        ReWrite(arquivo);
        WriteLn(arquivo,'x,y');
      END;
    END;
    END
  UNTIL r=#27;
  TextMode(80);
END;

PROCEDURE Limpar;
  VAR max:REAL;
BEGIN
  WITH x DO
  BEGIN
    max:=0;
    FOR i:=0 TO grau DO IF Abs(a[i])>max THEN max:=Abs(a[i]);
    max:=max*toln;
    FOR i:=0 TO grau DO IF Abs(a[i])<max THEN a[i]:=0;
    WHILE (a[grau]=0) AND (grau>=0) DO grau:=grau-1
  END
END;

PROCEDURE Normalizar;
BEGIN
  Limpar;
  WITH x DO
  BEGIN
    IF a[grau]<>1 THEN
    BEGIN
      cte:=cte*a[grau];
      FOR i:=0 TO grau DO a[i]:=a[i]/a[grau]
    END
  END
END; {Normalizar}

PROCEDURE ConverterParaS;
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

PROCEDURE Raizes; {Raizes de polinomio por Linn-Barstow}
  CONST imax=150;
  VAR n:INTEGER;
    t,tol,u,v,u1,v1,c1,c2,c3,d:REAL;
    ca,cb:coeficientes;

  PROCEDURE Terminar;
  BEGIN
    raizes_calculadas:=TRUE
  END;

  PROCEDURE Resolve; {Calcula raizes de termo de 2o. grau}
  BEGIN
    WITH x DO
    BEGIN
      d:=u*u-4*v;
      IF d>=0 THEN
      BEGIN
        zr[n]:=(-u+Sqrt(d))/2;
        zr[n-1]:=(-u-Sqrt(d))/2;
        zi[n]:=0; zi[n-1]:=0
      END
      ELSE
      BEGIN
        zr[n]:=-u/2; zr[n-1]:=-u/2;
        zi[n]:=Sqrt(-d)/2; zi[n-1]:=-zi[n]
      END;
      n:=n-2
    END
  END; {Resolve}

BEGIN
  WITH x DO
  BEGIN
    ca:=a;
    v:=Sqr(a0)+Sqr(b0); u:=-a0-b0; tol:=tolr;
    IF grau=0 THEN BEGIN WriteLn(tl,'[*] N„o h  ra¡zes a calcular [*]'); Exit END;
    n:=grau;
    WHILE (ca[0]=0) AND (n>1) DO
    BEGIN
      zr[n]:=0; zi[n]:=0;
      n:=n-1;
      FOR j:=0 TO n DO ca[j]:=ca[j+1]
    END;
    REPEAT
      IF n=1 THEN
      BEGIN
        zr[1]:=-ca[0]/ca[1]; zi[1]:=0;
        Terminar; Exit
      END;
      IF n=2 THEN
      BEGIN
        u:=ca[1]/ca[2]; v:=ca[0]/ca[2];
        Resolve;
        Terminar; Exit
      END;
      i:=0;
      REPEAT
        IF i=imax THEN
        BEGIN
          WriteLn('Tolerƒncia reduzida para ',t:12);
          tol:=t
        END;
        i:=i+1;
        cb[n]:=ca[n]; c2:=cb[n];
        cb[n-1]:=ca[n-1]-u*cb[n];
        c1:=cb[n-1]-u*c2;
        FOR j:=n-2 DOWNTO 1 DO
        BEGIN
          c3:=c2; c2:=c1;
          cb[j]:=ca[j]-u*cb[j+1]-v*cb[j+2];
          c1:=cb[j]-u*c2-v*c3
        END;
        cb[0]:=ca[0]-u*cb[1]-v*cb[2];
        IF (c3<>0) AND (c2<>0) AND (c1<>0) THEN BEGIN
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
      UNTIL (t<tol) OR (i>imax);
      Resolve;
      FOR j:=0 TO n DO ca[j]:=cb[j+2]
    UNTIL FALSE;
  END
END; {Raizes}

PROCEDURE Somar;
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
  Somar
END;

PROCEDURE Multiplicar;
  VAR m:coeficientes;
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
BEGIN
  WITH x DO
  BEGIN
    FOR i:=grau DOWNTO 0 DO a[i+1]:=a[i];
    a[0]:=0;
    grau:=grau+1;
  END
END;

PROCEDURE MultC(c:REAL);
BEGIN
  x.cte:=x.cte*c
END;
  
PROCEDURE ListarPolinomio;
BEGIN
  WITH x DO
  BEGIN
    FOR i:=0 TO grau DO WriteLn(tl,'[-] a([',i:2,']): ',a[i]:cm:dc);
    WriteLn(tl,'[-] Cte:   ',cte:cm:dc);
    Write(tl,'Salvar? ([Cr] ou nome) ');
    ReadLn(txt);
    IF Length(txt)>0 THEN
    BEGIN
      Assign(arquivo,txt);
      ReWrite(arquivo);
      WriteLn(arquivo,grau);
      FOR i:=0 TO grau DO WriteLn(arquivo,a[i]:cm:dc);
      WriteLn(arquivo,cte:cm:dc);
      Close(arquivo)
    END
  END
END;
  
PROCEDURE Entrar;
BEGIN
  t:=z; z:=y; y:=x
END;
  
PROCEDURE Chebyshev(n:INTEGER);
  VAR k:INTEGER;
BEGIN
  x.a[0]:=1; x.grau:=0; x.cte:=1;
  IF n>0 THEN
  BEGIN
    Entrar;
    MultS;
    k:=1;
    FOR k:=2 TO n DO
    BEGIN
      Entrar;
      MultC(2);
      MultS;
      Entrar;
      x:=t;
      Subtrair
    END
  END
END;
  
PROCEDURE Moebius(n:INTEGER);
  VAR k:INTEGER;
    w:REAL;
BEGIN
  IF Odd(n) THEN
  BEGIN
    WriteLn(tl,'[*] O grau deve ser par [*]');
    Exit
  END;
  Chebyshev(n);
  w:=Cos((n-1)*Pi/(2*n));
  y.a[0]:=Sqr(w); y.a[1]:=0; y.a[2]:=(1-Sqr(w)); y.cte:=1; y.grau:=2;
  Entrar;
  x.a[0]:=y.a[n]; x.cte:=1; x.grau:=0;
  FOR k:=n-2 DOWNTO 0 DO IF NOT Odd(k) THEN
    BEGIN
      Entrar;
      x:=t;
      Multiplicar;
      x.a[0]:=x.a[0]+y.a[k];
    END;
  Limpar;
END; {Moebius}

PROCEDURE ListarRaizes;
BEGIN
  WITH x DO
    IF raizes_calculadas THEN
    BEGIN
      FOR i:=1 TO grau DO
        WriteLn(tl,'[-] x([',i:2,'])=',zr[i]:cm:dc,zi[i]:cm:dc,'j');
    END
    ELSE WriteLn(tl,'[*] N„o h  ra¡zes calculadas [*]');
END;
  
PROCEDURE Derivar;
BEGIN
  WITH x DO
  BEGIN
    FOR i:=1 TO grau DO a[i-1]:=a[i]*i;
    IF grau>0 THEN grau:=grau-1;
  END
END;
  
PROCEDURE Integrar;
BEGIN
  WITH x DO
  BEGIN
    FOR i:=grau+1 DOWNTO 1 DO a[i]:=a[i-1]/i;
    a[0]:=0; grau:=grau+1;
  END
END;
  
PROCEDURE Escalar;
  VAR p:REAL;
BEGIN
  WITH x DO
  BEGIN
    p:=a[grau];
    FOR i:=grau-1 DOWNTO 0 DO p:=p+a[i];
    cte:=1/p
  END
END;
  
PROCEDURE OrdenarRaizes;
  VAR ordenado:BOOLEAN;
    t:REAL;
BEGIN
  WITH x DO
  REPEAT
    ordenado:=TRUE;
    FOR i:=1 TO grau-1 DO
    BEGIN
      IF zr[i+1]<zr[i] THEN
      BEGIN
        t:=zr[i]; zr[i]:=zr[i+1]; zr[i+1]:=t;
        t:=zi[i]; zi[i]:=zi[i+1]; zi[i+1]:=t;
        ordenado:=FALSE
      END
    END
  UNTIL ordenado;
END;

PROCEDURE ResolverSistema(VAR H:matriz; n:INTEGER);
  VAR i,j,l,a:INTEGER;
    t,p:REAL;
BEGIN
  FOR i:=1 TO n DO
  BEGIN
    t:=0; a:=i;
    FOR l:=i TO n DO
      IF Abs(H[l,i])>Abs(t) THEN
        BEGIN a:=l; t:=H[l,i] END;
    IF i<>a THEN
      FOR l:=1 TO n+1 DO
        BEGIN p:=H[i,l]; H[i,l]:=H[a,l]; H[a,l]:=p END;
    IF Abs(t)<told THEN
      BEGIN WriteLn(tl,'[*] Sistema insol£vel [*]'); erro:=TRUE; Exit END;
    FOR j:=n+1 DOWNTO i+1 DO
    BEGIN
      H[i,j]:=H[i,j]/t;
      p:=H[i,j];
      FOR l:=1 TO n DO
        IF l<>i THEN
          H[l,j]:=H[l,j]-H[l,i]*p
    END
  END
END; {ResolverSistema}

PROCEDURE Otimizar(n,p:INTEGER);
  VAR m:INTEGER;
    H:matriz;
    f,w:ARRAY[1..mmax] OF REAL;
    d,wk:REAL;
    convergiu:BOOLEAN;

BEGIN
  m:=(n-p) DIV 2+1;
  IF (Odd(n) XOR Odd(p)) OR (n<p) OR (m>mmax) THEN
  BEGIN
    WriteLn(tl,'[*] Parƒmetros inv lidos [*]');
    Exit
  END;
  IF p=0 THEN i:=n
  ELSE IF Odd(n) THEN i:=n-p+1 ELSE i:=n-p;
  WriteLn(tl,'Aproxima‡„o inicial: [M(w)=w^',n-i,'.C',i,'(w)]');
  Chebyshev(i);
  FOR j:=1 TO n-i DO MultS;
  WriteLn(tl,'Extremos de [M',n,'(w)] p/ 0ówó=1: (1..',m,')');
  FOR i:=1 TO m DO
  BEGIN
    IF Odd(m) XOR Odd(i) THEN f[i]:=-1 ELSE f[i]:=1;
    Write(tl,'f([',i,'])'); LerReal(f[i])
  END;
  REPEAT
      {===Encontrar frequencias de extremo===}
    Entrar;
    Derivar;
    IF p>0 THEN x.a[0]:=x.a[p-1];
    FOR i:=1 TO m-1 DO
      x.a[i]:=x.a[p-1+i+i];
    x.grau:=m-1;
    Raizes;
    OrdenarRaizes;
    w[m]:=1.0;
    FOR i:=1 TO m-1 DO w[i]:=Sqrt(zr[i]);
      {===Montar Sistema===}
    FOR i:=1 TO m DO
    BEGIN
      H[i,m+1]:=f[i];
      wk:=1;
      FOR j:=1 TO p DO wk:=wk*w[i];
      FOR j:=1 TO m DO
      BEGIN
        H[i,j]:=wk;
        wk:=wk*Sqr(w[i])
      END
    END;
      {===Resolver===}
    erro:=FALSE;
    ResolverSistema(H,m);
    IF erro OR KeyPressed THEN
      BEGIN x:=y; WriteLn(tl,'[*] C lculo interrompido [*]'); Exit END;
      {===Atualizar===}
    x.grau:=n;
    FOR i:=0 TO n DO x.a[i]:=0;
    FOR i:=1 TO m DO x.a[i+i+p-2]:=H[i,m+1];
      {===Verificar convergˆncia===}
    i:=1;
    REPEAT
      j:=i+i+p-2;
      d:=Abs(x.a[j]-y.a[j]);
      IF x.a[j]<>0 THEN d:=d/Abs(x.a[j]);
      convergiu:=(d<tolp);
      WriteLn('ë',j,': ',d);
      i:=Succ(i)
    UNTIL (NOT convergiu) OR (i>m)
  UNTIL convergiu;
END; {Otimizar}

PROCEDURE LerPolinomio;
BEGIN
  Write(tl,'Nome do arquivo ou [Cr]: [');
  ReadLn(txt); Write(tl,']');
  IF Length(txt)>0 THEN
  BEGIN
    Assign(arquivo,txt);
      {$I-} Reset(arquivo); {$I+}
    IF IOResult=0 THEN
    BEGIN
      ReadLn(arquivo,x.grau);
      FOR i:=0 TO x.grau DO ReadLn(arquivo,x.a[i]);
      IF SeekEof(arquivo) THEN x.cte:=1.0
      ELSE ReadLn(arquivo,x.cte)
    END
    ELSE WriteLn(tl,'[*] Arquivo inexistente [*]')
  END
  ELSE
  BEGIN
    Write('Grau: '); ReadLn(x.grau);
    FOR i:=0 TO x.grau DO
    BEGIN
      Write(tl,'a([',i:2,']): '); ReadLn(x.a[i])
    END;
    Write('Cte: '); ReadLn(x.cte)
  END;
END;

PROCEDURE Menu;
BEGIN
  WriteLn(tl,'- M(w)=[C]hebyshev');
  WriteLn(tl,'- M(w)=Chebyshev [M]odificado');
  WriteLn(tl,'- [O]timiza‡„o para M(w)');
  WriteLn(tl,'- Gerar [K](s)=F(s)=î.M(s/j)');
  WriteLn(tl,'- [L]istar/salvar M(w)');
  WriteLn(tl,'- Ler [P]olin“mio M(w)');
  WriteLn(tl,'- Calcular [R]a¡zes de M(w)');
  WriteLn(tl,'- Elevar ao M(w) ao [Q]uadrado');
  WriteLn(tl,'- [D]erivar M(w)');
  WriteLn(tl,'- [I]ntegrar M(w)');
  WriteLn(tl,'- [E]scalar M(w) para M(1)=1');;
  WriteLn(tl,'- Mudar [T]olerƒncias e parƒmetros do programa');
  WriteLn(tl,'- [G]r fico de M(w)');
  WriteLn(tl,'- [Esc]: Fim');
  WriteLn(tl,'- [Cr]: Este menu');
END;

BEGIN
escrever:=FALSE;
{$IFDEF DOUBLE}
tolr:=1e-15; toln:=1e-12; tolp:=1e-10; told:=1e-10;
{$ELSE}
tolr:=1e-8; toln:=1e-7; tolp:=1e-7; told:=1e-7;
{$ENDIF}
n:=5; p:=1; Amax:=1; xx:=2; yy:=2;
a0:=-1.1; b0:=1.1; x.a[0]:=0; x.grau:=0; x.cte:=1; raizes_calculadas:=FALSE;
placa:=CGA; modo:=CGAHI;
InitGraph(placa,modo,GetEnv('TPBGI'));
TextMode(80);
ClrScr;
WriteLn(tl,'[A]proxima‡”es [Pol]inomiais');
WriteLn(tl,'[------------------------]');
WriteLn('ACMQ - COPPE/UFRJ - Vers„o ',versao,' - Precis„o ',precisao);
WriteLn('Polin“mios de grau at‚ ',gmax);
WriteLn; Menu; WriteLn(tl,'[#]');
REPEAT
  CASE UpCase(ReadKey) OF
  'P':LerPolinomio;
  'D':BEGIN Derivar; WriteLn('M(w) derivado.') END;
  'I':BEGIN Integrar; WriteLn('M(w) integrado.') END;
  'E':BEGIN Escalar; WriteLn('M(w) escalado para M(1)=1.') END;
  'G':Grafico;
  'T':BEGIN
      Write('Tol. p/raizes'); LerReal(tolr);
      Write('Tol. p/normaliza‡„o'); LerReal(toln);
      Write('Tol. p/otimiza‡„o'); LerReal(tolp);
      Write('Tol. p/pivot'); LerReal(told);
      Write('Raiz real inicial'); LerReal(a0);
      Write('Raiz imag inicial'); LerReal(b0);
      Write('Limites iniciais x no gr fico'); LerReal(xx);
      Write('Limites iniciais y no gr fico'); LerReal(yy);
      Write('Campo para reais'); LerInt(cm);
      Write('Decimais para reais'); LerInt(dc)
    END;
  'O':BEGIN
      WriteLn(tl,'[Polin“mio otimizado]:');
      Write('Grau do polin“mio a obter: '); LerInt(n);
      Write('N£mero de zeros na origem: '); LerInt(p);
      Otimizar(n,p);
    END;
  'Q':BEGIN
      Entrar;
      Multiplicar;
      WriteLn('M(w) elevado ao quadrado.')
    END;
  'R':BEGIN
      WriteLn(tl,'[Ra¡zes de M(w)]:');
      Raizes;
      OrdenarRaizes;
      ListarRaizes;
    END;
  'C':BEGIN
      Write(tl,'[M(w)=Chebyshev]: Grau? '); LerInt(n);
      Chebyshev(n);
    END;
  'M':BEGIN
      Write(tl,'[M(w)=Chebyshev modificado]: Grau? '); LerInt(n);
      Moebius(n);
    END;
  'K':BEGIN
      Write('Atenua‡„o m xima na banda passante'); LerReal(Amax);
      epsilon:=Sqrt(Exp(0.1*Amax*Ln(10))-1);
      WriteLn(tl,'[î]: ',epsilon:cm:dc);
      t:=x;
      MultC(epsilon);
      ConverterParaS;
      Normalizar;
      WriteLn(tl,'Polin“mio [K(s)]:');
      ListarPolinomio;
      x:=t
    END;
  'L':BEGIN
      WriteLn(tl,'Polin“mio [M(w)]:');
      ListarPolinomio
    END;
  #27:Halt;
  #13:Menu;
  END;
  WriteLn(tl,'[#]');
UNTIL FALSE;
END.
