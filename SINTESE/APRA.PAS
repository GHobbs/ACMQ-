PROGRAM Apra;
{******************************************************************************
 * Aproximaáîes racionais assimÇtricas                                        *
 * Antìnio Carlos MoreirÑo de Queiroz                                         *
 * VersÑo 1.0  de 03/08/89                                                    *
 * VersÑo 1.0a de 03/09/89 Nome da funáÑo na estimaáÑo                        *
 * VersÑo 1.0b de 12/09/89 CorreáÑo na leitura dos f                          *
 * VersÑo 1.0c de 17/09/89 Aviso de precisÑo insuficiente                     *
 * VersÑo 1.0d de 28/11/89 PrecisÑo extendida                                 *
 * VersÑo 1.1  de 05/01/90 Poss°vel especificaáÑo direta de atenuaáîes        *
 * VersÑo 1.1a de 30/07/93 TPBGI                                              *
 ******************************************************************************}
{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}
USES Crt,Dos,Graph,Tela;
CONST
  versao='1.1a de 30/07/93';
  gmax=40;
  mmax=20;
  mmax1=21;
  Amax:REAL=1; {3.01029995663981}
  Amin:REAL=40;
  {$IFDEF DOUBLE}
  tolr:REAL=1e-13;
  toln:REAL=1e-13;
  tolp:REAL=1e-12;
  told:REAL=1e-10;
  cm:INTEGER=26;
  dc:INTEGER=18;
  {$ELSE}
  tolr:REAL=1e-8;
  toln:REAL=1e-8;
  tolp:REAL=1e-7;
  told:REAL=1e-6;
  cm:INTEGER=19;
  dc:INTEGER=11;
  {$ENDIF}
  a0:REAL=-1.1;
  b0:REAL=1.1;
  n:INTEGER=3;
  px:INTEGER=1;
  py:INTEGER=1;
  itermax:INTEGER=1;
  xx:REAL=4;
  yy:REAL=4;

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
  fx,fy,wx,wy:valores;
  zr,zi:ARRAY[1..gmax] OF REAL;
  placa,modo,i,j,m:INTEGER;
  ch:CHAR;
  arquivo:TEXT;
  txt:STRING;
  alfa,epsilon:REAL;
  raizes_calculadas,convergiu_direto,erro:BOOLEAN;

FUNCTION Ex(x,y: REAL): REAL;  {x^y}
BEGIN Ex:=Exp(y*Ln(x)) END;

PROCEDURE Grafico;
  CONST
    x0=259;
    xm=639;
    y0=0;
    ym=199;
  VAR
    x1,y1,x2,y2,ax,bx,ay,by,p,w,d:REAL;
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
  x1:=0;
  x2:=xx;
  y1:=-yy;
  y2:=yy;
  REPEAT
    SetGraphMode(modo);
    Rectangle(x0,y0,xm,ym);
    SetLineStyle(DottedLn,0,NormWidth);
    ay:=(y0-ym)/(y2-y1); by:=ym-ay*y1;
    ax:=(xm-x0)/(x2-x1); bx:=x0-ax*x1;
    Line(x0,Limy(0),xm,Limy(0));
    Line(Limx(0),y0,Limx(0),ym);
    Rectangle(Limx(-1),Limy(1),Limx(1),Limy(-1));
    d:=Sqr(alfa);
    IF d>1 THEN d:=1+Ln(d)/Ln(10);
    Line(x0,Limy(d),xm,Limy(d));
    Line(x0,Limy(-d),xm,Limy(-d));
    SetLineStyle(SolidLn,0,NormWidth);
    IF KeyPressed THEN GOTO atualizar;
    Str(x1:7:3,txt); OutTextXY(0,0, 'x: w min:      '+txt);
    Str(x2:7:3,txt); OutTextXY(0,8, '   w max:      '+txt);
    Str(y1:7:3,txt); OutTextXY(0,16,'y: K(jw)/e min:'+txt);
    Str(y2:7:3,txt); OutTextXY(0,24,'   K(jw)/e max:'+txt);
    FOR xg:=x0 TO xm DO BEGIN
      w:=(xg-bx)/ax;
      p:=x.a[x.grau];
      FOR i:=x.grau-1 DOWNTO 0 DO p:=p*w+x.a[i];
      d:=p*x.cte;
      p:=y.a[y.grau];
      FOR i:=y.grau-1 DOWNTO 0 DO p:=p*w+y.a[i];
      d:=d/(p*y.cte);
      p:=Abs(d);
      IF p>1 THEN p:=Ln(p)/Ln(10)+1;
      IF d<0 THEN p:=-p;
      yg:=Limy(p);
      IF xg>x0 THEN
        Line(xa,ya,xg,yg);
      xa:=xg; ya:=yg;
      IF KeyPressed THEN GOTO atualizar;
    END;
    OutTextXY(0,40,'+ amplia y');
    OutTextXY(0,48,'- reduz  y');
    OutTextXY(0,56,'A amplia x');
    OutTextXY(0,64,'R reduz  x');
    OutTextXY(0,72,'Cursor move');
    OutTextXY(0,80,'Esc retorna');
    OutTextXY(0,96,'Escala para -1<y<1: Linear');
    OutTextXY(0,104,'Escala para -1>y>1: log(y)+1');
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
    'P':BEGIN d:=(y2-y1)/4; y1:=y1-d; y2:=y2-d END
    END
  UNTIL ch=#27;
  TextMode(80);
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

PROCEDURE ListarRaizes;
BEGIN
  IF raizes_calculadas THEN
    WITH x DO
      FOR i:=1 TO grau DO
        WriteLn(tl,'[-] w([',i:2,'])=',zr[i]:cm:dc,zi[i]:cm:dc,'j')
  ELSE WriteLn(tl,'[*] NÑo h† ra°zes [*]');
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
      Write('wp=',w0:cm:dc,#13);
    UNTIL (Abs(u)<tolr) OR KeyPressed
  END;
  x:=y;
  y:=z;
  FOR i:=0 TO x.grau-1 DO x.a[i]:=x.a[i]/Ex(w0,x.grau-i);
  FOR i:=0 TO y.grau-1 DO y.a[i]:=y.a[i]/Ex(w0,y.grau-i);
  y.cte:=y.cte/Ex(w0,x.grau-y.grau);
  WriteLn(tl,#10'[*] K(jw)/Ó escalado [*]');
END;

PROCEDURE Raizes; {Ra°zes do polinomio x por Linn-Barstow}
  CONST
    imax=150;
  VAR
    n:INTEGER;
    t,u,v,u1,v1,c1,c2,c3,d:REAL;
    ca,cb:coeficientes;

  PROCEDURE Terminar;
  BEGIN
    raizes_calculadas:=TRUE
  END;

  PROCEDURE LerParametros;
  BEGIN
    Write('Nova tolerÉncia'); LerReal(t);
    tolr:=1.01*t;
    Write('Nova aprox. para u'); LerReal(u);
    Write('Nova aprox. para v'); LerReal(v)
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
      UNTIL (t<tolr) OR (i>imax);
      Resolve;
      FOR j:=0 TO n DO ca[j]:=cb[j+2]
    UNTIL FALSE;
  END
END; {Raizes}

PROCEDURE OrdenarRaizes;
  VAR
    ordenado:BOOLEAN;
    t:REAL;
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

PROCEDURE Estimar(VAR xo:polinomio; VAR f,w:valores; n,p:INTEGER; funcao:STRING; bp:BOOLEAN);
VAR
  at:valores;
  indice:INTEGER;
  temp:REAL;
BEGIN
  m:=(n-p) DIV 2+1;
  IF (Odd(n) XOR Odd(p)) OR (n<p) OR (m>mmax) THEN BEGIN
    WriteLn(tl,'[*] ParÉmetros inv†lidos [*]');
    erro:=TRUE;
    Exit
  END
  ELSE erro:=FALSE;
  IF Odd(n) THEN j:=n-p+1 ELSE j:=n-p;
  WriteLn(tl,'AproximaáÑo inicial: [w^',n-j,'.C',j,'(w)]');
  Chebyschev(j);
  FOR j:=1 TO n-j DO MultS;
  xo:=x;
  FOR i:=1 TO m-1 DO BEGIN
    IF Odd(m) xor Odd(i) THEN f[i]:=-1 ELSE f[i]:=1;
    w[i]:=1
  END;
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
    Write(tl,'Mudar [f], [A]tenuaáÑo, [S]inal de f ou [C]ontinuar: ');
    REPEAT ch:=UpKey UNTIL ch in ['F','A','S','C'];
    WriteLn(tl,'[',ch,']');
    IF ch<>'C' THEN BEGIN
      REPEAT
        Write('Indice'); LerInt(indice);
      UNTIL (indice>0) and (indice<m);
      CASE ch OF
        'F':BEGIN
              Write(tl,'Extremo f([',indice,'])'); LerReal(f[indice]);
            END;
        'A':BEGIN
              Write(tl,'AtenuaáÑo no extremo f([',indice,'])'); LerReal(at[indice]);
              at[indice]:=Abs(at[indice]);
              IF at[indice]<1000 THEN BEGIN
                IF bp THEN temp:=Sqrt(Ex(10,0.1*at[indice])-1)/epsilon
                ELSE temp:=epsilon*Sqr(alfa)/Sqrt(Ex(10,0.1*at[indice])-1)
              END
              ELSE temp:=0;
              IF f[indice]>0 THEN f[indice]:=temp ELSE f[indice]:=-temp
            END;
        'S':f[indice]:=-f[indice];
      END;
    END
  UNTIL ch='C';
END;

PROCEDURE Otimizar(VAR xo,yo:polinomio; VAR f,w:valores; n,p,py:INTEGER);
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
  tol:=tolp;
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
    Raizes;
    OrdenarRaizes;
    FOR i:=1 TO m-1 DO BEGIN
      IF zi[i]<>0 THEN
        WriteLn(tl,'[*] PrecisÑo insuficiente no c†lculo de ra°zes [*]');
      IF zr[i]<0 THEN
        WriteLn(tl,'[*] SeqÅància de extremos inv†lida [*]');
      w[i]:=Sqrt(Abs(zr[i]));
    END;
      {===Verificar convergància===}
    i:=1; convergiu:=TRUE;
    WHILE convergiu and (i<m) DO BEGIN
      d:=Abs(w[i]-ultimo_w[i]);
      Write('Î',i,': ',d,#13);
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
    IF erro THEN BEGIN x:=xo; GOTO fim END;
      {===Copiar soluáÑo atual para x===}
    FOR i:=0 TO n DO x.a[i]:=0;
    FOR i:=1 TO m DO x.a[p+i+i-2]:=H[i,m+1];
    x.grau:=n; x.cte:=1;
    iter:=iter+1;
  UNTIL (iter=itermax) or convergiu or KeyPressed;
   {=== Terminar ===}
  fim:
  xo:=x;
END; {Otimizar}

PROCEDURE Menu;
BEGIN
  WriteLn(tl,'- [O]timizaáÑo para ‡.X(w)/Yr(w)');
  WriteLn(tl,'- Ler [P]olinìmios ‡.X(w) e Y(w), gerando ‡.X(w)/Yr(w)');
  WriteLn(tl,'- Gerar [K](s)=F(s)/P(s)=Ó‡.X(s)/Yr(s)');
  WriteLn(tl,'- [L]istar/salvar ‡.X(w)/Yr(w)');
  WriteLn(tl,'- [G]r†fico de K(jw)/Ó');
  WriteLn(tl,'- [E]scalar ‡.X(w)/Yr(w) para corte em 1 rad/s');
  WriteLn(tl,'- Ra°zes do polinìmio [X](w)');
  WriteLn(tl,'- Ra°zes do polinìmio [Y]r(w)');
  WriteLn(tl,'- Mudar [T]olerÉncias e parÉmetros do programa');
  WriteLn(tl,'- [D]iret¢rio');
  WriteLn(tl,'- [Esc]: Fim');
  WriteLn(tl,'- [Cr]: Este menu');
END;

BEGIN
placa:=CGA;
modo:=CGAHI;
InitGraph(placa,modo,GetEnv('TPBGI'));
TextMode(80);
x.a[0]:=1; x.grau:=0; x.cte:=1;
Enter;
ClrScr;
WriteLn(tl,'[Ap]roximaáîes [R]acionais [A]ssimÇtricas');
WriteLn(tl,'[-----------------------------------]');
WriteLn('ACMQ - COPPE/UFRJ - VersÑo ',versao,' - PrecisÑo ',precisao);
WriteLn('Polinìmios de grau atÇ ',gmax);
WriteLn; Menu; WriteLn(tl,'[#]');
REPEAT
  CASE UpCase(ReadKey) OF
  'G':Grafico;
  'T':BEGIN
      Write('Tol. p/raizes'); LerReal(tolr);
      Write('Aprox. inicial real'); LerReal(a0);
      Write('Aprox. inicial imag'); LerReal(b0);
      Write('Tol. p/normalizaáÑo'); LerReal(toln);
      Write('Tol. p/otimizaáÑo'); LerReal(tolp);
      Write('Tol. p/pivot'); LerReal(told);
      Write('N£mero de iteraáîes antes da inversÑo de K'); LerInt(itermax);
      Write('Limites iniciais x no gr†fico'); LerReal(xx);
      Write('Limites iniciais y no gr†fico'); LerReal(yy);
      Write('Campo para reais'); LerInt(cm);
      Write('Decimais para reais'); LerInt(dc);
    END;
  'O':BEGIN
      WriteLn(tl,'[OtimizaáÑo para aproximaáÑo racional]:');
      Write('Grau da aproximaáÑo a obter'); LerInt(n);
      Write('No. de zeros de atenuaáÑo na origem'); LerInt(px);
      Write('No. de zeros de transmissÑo no infinito'); LerInt(py);
      Write('AtenuaáÑo m°nima na banda de rejeiáÑo'); LerReal(Amin);
      Write('AtenuaáÑo m†xima na banda passante'); LerReal(Amax);
      epsilon:=Sqrt(Ex(10,0.1*Amax)-1);
      WriteLn(tl,#10'[Ó]: ',epsilon:cm:dc);
      alfa:=Sqrt(Sqrt(Ex(10,0.1*Amin)-1)/epsilon);
      WriteLn(tl,'[‡]: ',alfa:cm:dc);
      WriteLn(tl,#10'[AproximaáÑo para X(w)]:');
      Estimar(xo,fx,wx,n,px,'‡X(w)/Yr(w)',TRUE);
      IF not erro THEN BEGIN
        WriteLn(tl,#10'[AproximaáÑo para Y(w)]:');
        Estimar(yo,fy,wy,n,py,'‡Y(w)/Xr(w)',FALSE);
        IF not erro THEN BEGIN
        WriteLn;
          REPEAT
            convergiu_direto:=TRUE;
            Otimizar(xo,yo,fx,wx,n,px,py);
            Otimizar(yo,xo,fy,wy,n,py,px);
          UNTIL convergiu_direto or KeyPressed;
          x:=xo;
          MultC(alfa);
          y:=yo;
          Inverter(y);
          Limpar(y);
          WriteLn(tl,#10#10'[*] OtimizaáÑo completa [*]')
        END
      END
    END;
  'K':BEGIN
      z:=x;
      t:=y;
      Normalizar(x);
      Normalizar(y);
      y.cte:=y.cte/x.cte/epsilon;
      x.cte:=1;
      ConverterParaS(x);
      ConverterParaS(y);
      WriteLn(tl,'Polinìmio [P(s)]:');
      ListarPolinomio(y);
      WriteLn(tl,'Polinìmio [F(s)]:');
      ListarPolinomio(x);
      x:=z;
      y:=t
    END;
  'L':BEGIN
      WriteLn(tl,'[Numerador de ‡.X(w)/Yr(w)]:');
      ListarPolinomio(x);
      WriteLn(tl,'[Denominador de ‡.X(w)/Yr(w)]:');
      ListarPolinomio(y)
    END;
  'P':BEGIN
        WriteLn('Polinìmio Y(w):');
        LerPolinomio;
        y:=x;
        Inverter(y);
        Limpar(y);
        WriteLn('Polinìmio ‡.X(w) (‡ Ç a cte.):');
        LerPolinomio;
        alfa:=x.cte;
        WriteLn('‡.X(w)/Yr(w) gerado.');
      END;
  'D':Diretorio;
  'X':BEGIN
        WriteLn(tl,'Ra°zes do polinìmio X(w), freqÅàncias dos [zeros de atenuaáÑo]:');
        Raizes;
        ListarRaizes
      END;
  'Y':BEGIN
        WriteLn(tl,'Ra°zes do polinìmio Yr(w), freqÅàncias dos [zeros de transmissÑo]:');
        t:=x;
        x:=y;
        Raizes;
        ListarRaizes;
        x:=t
      END;
  'E':ReEscalar;
  #27:Halt;
  #13:Menu;
  END;
  WriteLn(tl,'[#]');
UNTIL FALSE;
END.
