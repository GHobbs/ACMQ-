UNIT Latt;

{******************************************************************************
 * Defini‡”es do programa EletSim e rotinas para realiza‡„o nas formas        *
 * derivadas da lattice                                                       *
 * V. 1.3 de 15/01/91                                                         *
 * Vers„o 1.4  de 24/03/91 Inclu¡dos limites de Tg                            *
 * Vers„o 1.4a de 01/05/91 Nada neste arquivo                                 *
 * Versao 1.4b de 19/07/92 Nada neste arquivo                                 *
 * Versao 1.4c de 23/07/92 Mudada ordem de testes na geracao da lattice para  *
 *                         evitar erro em Abs de valor nao definido           *
 * Versao 1.4d de 10/01/94 Salva tabela com curvas                            *
 * Versao 1.4e de 18/09/94 Extracoes no infinito permitidas no recalculo      *
 * Versao 1.4f de 27/07/95 Nada neste arquivo                                 *
 * Versao 1.4g de 22/07/96 Nada neste arquivo                                 *
 * Versao 1.4h de 23/11/05 Fatores de desnormaliza‡„o                         *
 * Versao 1.4i de 14/07/06 Desnormaliza para Hz ou rad/s                      *
 * Versao 1.4j de 21/07/06 Nada nesse arquivo                                 *
 ******************************************************************************}

INTERFACE

{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}

USES Tela;

CONST
  {Configura‡„o}
  versao='1.4j de 21/07/06';
  {$IFDEF DOUBLE}
  config='eletsim2.cfg';
  tolr:REAL=1e-13;
  tolm:REAL=1e-12;
  toln:REAL=1e-13;
  tolo:REAL=1e-11;
  tolp:REAL=1e-10;
  told:REAL=1e-7;
  cm:INTEGER=26;
  dc:INTEGER=18;
  {$ELSE}
  config='eletsim1.cfg';
  tolr:REAL=1e-8;
  tolm:REAL=1e-8;
  toln:REAL=1e-8;
  tolo:REAL=1e-7;
  tolp:REAL=1e-6;
  told:REAL=1e-4;
  cm:INTEGER=19;
  dc:INTEGER=11;
  {$ENDIF}
  xr0:REAL=-1.1;
  xi0:REAL=1.1;
  salvarf:BOOLEAN=FALSE;
  imzeros:BOOLEAN=TRUE;
  salvarcte:BOOLEAN=FALSE;
  salvarladder:BOOLEAN=TRUE;
  listarz22:BOOLEAN=FALSE;
  salvarlattice:BOOLEAN=FALSE;
  expandirz:BOOLEAN=TRUE;
  salvarcom:BOOLEAN=FALSE;
  salvarsem:BOOLEAN=TRUE;
  {--//--}
  gmax=40;
  mmax=20;
  nfilmax=100;
  itermax:INTEGER=1;
  norm:BOOLEAN=TRUE;
  escolher:BOOLEAN=FALSE;
  calculado:BOOLEAN=FALSE;
  batch:BOOLEAN=FALSE;
  salvarcfg:BOOLEAN=FALSE;
  dct:INTEGER=5;
  cmt:INTEGER=8;
  wmin:REAL=0.1;
  wmax:REAL=10;
  kmin:REAL=-4;
  kmax:REAL=4;
  tmin:REAL=-60;
  tmax:REAL=10;
  dmin:REAL=0;
  dmax:REAL=20;
  log:BOOLEAN=TRUE;
  ct:STRING[11]='ÚÂ¿ÃÅ´ÀÁÙÄ³';
  grade:BOOLEAN=TRUE;
  salvarcurva:BOOLEAN=FALSE;
  fr:REAL=1;
  ff0:REAL=1;
  desnormalizar:BOOLEAN=FALSE;
  emhz:BOOLEAN=FALSE;

TYPE
   nomes=(ia,ib);
   complex=RECORD
             re,im:REAL
           END;
  lista=
  RECORD
    n:INTEGER;
    el:ARRAY[1..gmax*3 div 2+1] OF
    RECORD
      nme:STRING[4];
      valor:complex
    END
  END;
  coeficientes=ARRAY[0..gmax] OF REAL;
  polinomio=
  RECORD
    grau:INTEGER;
    cte:REAL;
    a:coeficientes;
  END;
  matriz=ARRAY[1..mmax,1..mmax+1] OF REAL;
  valores=ARRAY[1..mmax] OF REAL;
  raizes=ARRAY[1..gmax] OF REAL;
  filtro=
    RECORD
      n,px,py:INTEGER;
      Amax,Amin,epsilon,alfa,rg,rl:REAL;
      fx,fy,wx,wy:valores;
      xo,yo,po,fo,eo:polinomio;
      pre,pim,ztr,zti,C,L:raizes;
      za,zb,ca,sa:lista;
    END;
VAR
  tabela:ARRAY [1..nfilmax] OF ^filtro;
  x,y,z,t:polinomio;
  zr,zi:raizes;
  param,cor1,cor2,cor3,xmin,ymin,xmax,ymax,n0,px0,py0,nfil,placa,modo,i,j,m,fil,filmax:INTEGER;
  ch:CHAR;
  arquivo:TEXT;
  txt,nome:STRING;
  fim,convergiu_direto,erro:BOOLEAN;
  Amin0,Amax0,tolr1,ff:REAL;

FUNCTION Linha(c:STRING; n:INTEGER):STRING;
FUNCTION Nm(ix:nomes):STRING;
PROCEDURE Lattice(VAR item:filtro);
PROCEDURE ListarLattice(VAR item:filtro);
PROCEDURE SalvarLattices;

IMPLEMENTATION

FUNCTION Linha(c:STRING; n:INTEGER):STRING;
VAR
  i:INTEGER;
  txt:STRING;
BEGIN
  txt:='';
  FOR i:=1 TO n DO txt:=txt+c;
  Linha:=txt
END;

FUNCTION Nm(ix:nomes):STRING;
  BEGIN
    IF ExpandirZ THEN BEGIN
      IF ix=ia THEN Nm:='Za' ELSE Nm:='Zb'
    END
    ELSE BEGIN
      IF ix=ia THEN Nm:='Yb' ELSE Nm:='Ya'
    END
  END;

PROCEDURE Lattice(VAR item:filtro);

TYPE
  polinc=
  RECORD
    n:INTEGER;
    a:ARRAY[0..gmax] OF complex
  END;
  raizesc=
  RECORD
    n:INTEGER;
    z:ARRAY[1..gmax] OF complex
  END;

VAR
  rede:STRING;
  res,polo,zza,zzb,kza,kzb:raizesc;
  num,tmp,nza,dza,nzb,dzb:polinc;
  marcado:ARRAY[1..gmax] OF BOOLEAN;
  c:CHAR;
  t,temp:complex;
  ordenado:BOOLEAN;
  sx,sy,sz,st:complex;

  PROCEDURE Enter(VAR a:complex);
  BEGIN
    st:=sz;
    sz:=sy;
    sy:=sx;
    sx:=a
  END;

  PROCEDURE Somar;
  BEGIN
    sx.re:=sx.re+sy.re;
    sx.im:=sx.im+sy.im;
    sy:=sz;
    sz:=st
  END;

  PROCEDURE Subtrair;
  BEGIN
    sx.re:=-sx.re;
    sx.im:=-sx.im;
    Somar
  END;

  PROCEDURE Multiplicar;
  VAR k:REAL;
  BEGIN
    k:=sx.re*sy.re-sx.im*sy.im;
    sx.im:=sx.re*sy.im+sx.im*sy.re;
    sx.re:=k;
    sy:=sz;
    sz:=st
  END;

  PROCEDURE Dividir;
  VAR k,d:REAL;
  BEGIN
    d:=Sqr(sx.re)+Sqr(sx.im);
    k:=sx.re*sy.re+sx.im*sy.im;
    sx.im:=(sx.re*sy.im-sx.im*sy.re)/d;
    sx.re:=k/d;
    sy:=sz;
    sz:=st
  END;

  PROCEDURE Atribuir(VAR x:complex; r,i:REAL);
  BEGIN
    x.re:=r; x.im:=i
  END;

  PROCEDURE DivFator(VAR p:polinc; VAR fator:complex);
  BEGIN
    WITH p DO
      FOR i:=0 TO n DO BEGIN
        sy:=a[i];
        sx:=fator;
        Dividir;
        a[i]:=sx
      END
  END;

  PROCEDURE Expandir(nzz,dzz:polinc; VAR circuito:lista);
    VAR
      X:complex;
      Z:BOOLEAN;
      e:INTEGER;
      tmp:polinc;

    PROCEDURE Inverter;
    BEGIN
      tmp:=nzz; nzz:=dzz; dzz:=tmp; Z:=NOT Z
    END;

    PROCEDURE Remover(grau:INTEGER);
    VAR
      nome:STRING[3];
    BEGIN
      Enter(nzz.a[dzz.n+grau]);
      Enter(dzz.a[dzz.n]);
      IF (Abs(sx.re)<tolm) AND (Abs(sx.im)<tolm) OR (nzz.n-dzz.n<>grau) THEN   BEGIN
        WriteLn(tl,'[*] Nada a extrair');
        Exit
      END;
      Dividir;
      X:=sx;
      FOR i:=grau TO dzz.n+grau DO BEGIN
        Enter(nzz.a[i]);
        Enter(dzz.a[i-grau]);
        Enter(X);
        Multiplicar;
        Subtrair;
        nzz.a[i]:=sx
      END;
      nzz.n:=nzz.n-1;
      IF grau=0 THEN
        IF Z THEN c:='R'
        ELSE c:='G'
      ELSE BEGIN
        e:=e+1;
        IF Z THEN c:='L'
        ELSE c:='C';
      END;
      Str(e,nome); nome:=c+nome;
      WITH circuito DO BEGIN
        n:=n+1;
        el[n].nme:=nome;
        el[n].valor:=X;
      END
    END;

  BEGIN
    IF Abs(nzz.n-dzz.n)>1 THEN
      BEGIN WriteLn(tl,'[*] Imitƒncia inv lida'); Exit END;
    Z:=ExpandirZ;
    e:=0; circuito.n:=0;
    IF nzz.n<dzz.n THEN Inverter;
    REPEAT
      Remover(1);
      Remover(0);
      Inverter
    UNTIL dzz.n<0;
  END;

  PROCEDURE ProdutoLimitado(VAR f:raizesc; l:INTEGER);
  VAR
    i,j:INTEGER;
  BEGIN
    WITH tmp DO BEGIN
      Atribuir(a[0],1,0); n:=0;
      FOR i:=1 TO f.n DO
        IF i<>l THEN BEGIN
          n:=n+1;
          FOR j:=n DOWNTO 1 DO
            a[j]:=a[j-1];
          Atribuir(a[0],0,0);
          FOR j:=0 TO n-1 DO BEGIN
            Enter(a[j]);
            Enter(a[j+1]);
            Enter(f.z[i]);
            Multiplicar;
            Subtrair;
            a[j]:=sx
          END
        END
    END
  END;

  PROCEDURE CalcularResiduos;
  VAR
    d:complex;
    l:INTEGER;
  BEGIN
    res.n:=polo.n;
    FOR l:=1 TO polo.n DO BEGIN
      Atribuir(sx,1,0);
      FOR i:=1 TO polo.n DO
        IF i<>l THEN BEGIN
          Enter(polo.z[l]);
          Enter(polo.z[i]);
          Subtrair;
          Multiplicar;
        END;
      d:=sx;
      sx:=num.a[num.n];
      FOR i:=num.n-1 DOWNTO 0 DO BEGIN
        Enter(polo.z[l]);
        Multiplicar;
        Enter(num.a[i]);
        Somar
      END;
      Enter(d);
      Dividir;
      res.z[l]:=sx;
    END
  END;

  PROCEDURE SepararPolos;
  BEGIN
    zza.n:=0; zzb.n:=0;
    kza.n:=0; kzb.n:=0;
    FOR i:=1 TO polo.n DO
      IF marcado[i] THEN BEGIN
        WITH zza DO BEGIN
          n:=n+1;
          z[n]:=polo.z[i]
        END;
        WITH kza DO BEGIN
          n:=n+1;
          z[n]:=res.z[i]
        END;
      END
      ELSE BEGIN
        WITH zzb DO BEGIN
          n:=n+1;
          z[n]:=polo.z[i]
        END;
        WITH kzb DO BEGIN
          n:=n+1;
          z[n]:=res.z[i]
        END
      END
  END;

  PROCEDURE MontarImpedancias;
  BEGIN
     { Montar numerador de Za ou Yb }
    ProdutoLimitado(zza,0); nza:=tmp;
     { Montar numerador de Zb ou Ya }
    ProdutoLimitado(zzb,0); nzb:=tmp;
     { Montar denominador de Za ou Yb }
    WITH dza DO BEGIN
      n:=zza.n-1;
      FOR i:=0 TO n DO Atribuir(a[i],0,0);
      FOR i:=1 TO zza.n DO BEGIN
        ProdutoLimitado(zza,i);
        FOR j:=0 TO n DO BEGIN
          Enter(a[j]);
          Enter(tmp.a[j]);
          Enter(kza.z[i]);
          Multiplicar;
          Somar;
          a[j]:=sx;
        END
      END
    END;
     { Montar denominador de Zb ou Ya }
    WITH dzb DO BEGIN
      n:=zzb.n-1;
      FOR i:=0 TO n DO Atribuir(a[i],0,0);
      FOR i:=1 TO zzb.n DO BEGIN
        ProdutoLimitado(zzb,i);
        FOR j:=0 TO n DO BEGIN
          Enter(a[j]);
          Enter(tmp.a[j]);
          Enter(kzb.z[i]);
          Multiplicar;
          Somar;
          a[j]:=sx
        END;
      END
    END;
     {Trocar o sinal de Zb ou Ya }
    WITH nzb DO
      FOR i:=0 TO n DO BEGIN
        a[i].re:=-a[i].re;
        a[i].im:=-a[i].im
      END
  END;

  PROCEDURE Desbalancear(x:CHAR; VAR zt:lista);
  BEGIN
    WITH zt DO BEGIN
      IF x='C' THEN BEGIN
        i:=0; n:=0;
        REPEAT
          i:=i+1; n:=n+1;
          IF item.za.el[i].nme[1]<>item.zb.el[i].nme[1] THEN BEGIN
            WriteLn(tl,'[*] As duas imitƒncias n„o s„o da mesma forma (?!)');
            erro:=TRUE;
            Exit
          END;
          Enter(item.zb.el[i].valor);
          Enter(item.za.el[i].valor);
          Somar;
          Atribuir(sy,0.5,0);
          Multiplicar;
          el[n].valor:=sx;
          el[n].nme:=item.za.el[i].nme;
          Enter(item.zb.el[i].valor);
          Enter(item.za.el[i].valor);
          Subtrair;
          IF ExpandirZ THEN Atribuir(sy,0.5,0) ELSE Atribuir(sy,-0.5,0);
              {-0.5 para compensar a troca de ordem entre Ya e Yb}
          Multiplicar;
          el[n+1].valor:=sx;
          el[n+1].nme:='M'+item.za.el[i].nme;
          n:=n+1
        UNTIL (i=item.za.n) OR (i=item.zb.n)
      END
      ELSE BEGIN
        i:=0; n:=0;
        REPEAT
          i:=i+1; n:=n+1;
          c:=item.za.el[i].nme[1];
          IF c<>item.zb.el[i].nme[1] THEN BEGIN
            WriteLn(tl,'[*] As duas imitƒncias n„o s„o da mesma forma (?!)');
            erro:=TRUE;
            Exit
          END;
          IF c IN ['R','L'] THEN BEGIN
            Enter(item.zb.el[i].valor);
            Enter(item.za.el[i].valor);
          END
          ELSE BEGIN
            Enter(item.za.el[i].valor);
            Enter(item.zb.el[i].valor);
          END;
          IF NOT ExpandirZ THEN BEGIN {Trocar Ya e Yb}
            sz:=sx; sx:=sy; sy:=sz
          END;
          el[n].valor:=sx;
          el[n].nme:=item.za.el[i].nme;
          Subtrair;
          Atribuir(sy,0.5,0);
          Multiplicar;
          el[n+1].valor:=sx;
          el[n+1].nme:=item.za.el[i].nme[1]+'M'+Copy(item.za.el[i].nme,2,10);
          n:=n+1
        UNTIL (i=item.za.n) OR (i=item.zb.n)
      END;
        {Elemento central}
      IF item.za.n>item.zb.n THEN
        FOR j:=item.zb.n+1 TO item.za.n DO BEGIN
          n:=n+1;
          Enter(item.za.el[j].valor);
          Atribuir(sy,2,0);
          Multiplicar;
          el[n].valor:=sx;
          el[n].nme:=item.za.el[j].nme
        END
      ELSE
        FOR j:=item.za.n+1 TO item.zb.n DO BEGIN
          n:=n+1;
          Enter(item.zb.el[j].valor);
          Atribuir(sy,2,0);
          Multiplicar;
          el[n].valor:=sx;
          el[n].nme:=item.zb.el[j].nme
        END;
    END
  END;

  BEGIN
    {Convers„o de formatos}
    WITH item DO BEGIN
      IF eo.grau=po.grau THEN BEGIN
        erro:=TRUE;
        WriteLn(tl,'[*] Realiza‡„o duplamente terminada imposs¡vel: N„o h  zero no infinito');
        Exit
      END;
      FOR i:=1 TO n DO BEGIN
        polo.z[i].re:=pre[i];
        polo.z[i].im:=pim[i]
      END;
      polo.n:=n;
      FOR i:=0 TO po.grau DO BEGIN
        num.a[i].re:=po.a[i]*po.cte; num.a[i].im:=0
      END;
      num.n:=po.grau;
    END;
    {Ordena‡„o dos p¢los}
    WITH polo DO BEGIN
      REPEAT
        ordenado:=TRUE;
        FOR i:=1 TO n-1 DO BEGIN
          IF ArcTan(z[i+1].im/z[i+1].re)<ArcTan(z[i].im/z[i].re) THEN BEGIN
            t:=z[i]; z[i]:=z[i+1]; z[i+1]:=t;
            ordenado:=FALSE
          END
        END
      UNTIL ordenado;
      {Divis„o dos p¢los}
      FOR i:=1 TO n DO marcado[i]:=Odd(i) xor Odd(n div 2);
    END;
    CalcularResiduos;
    SepararPolos;
    MontarImpedancias;
    IF Odd(polo.n) THEN BEGIN
      temp.re:=1;
      temp.im:=0;
    END
    ELSE BEGIN
      temp.im:=-1;
      temp.re:=0;
    END;
    DivFator(nza,temp);
    Expandir(nza,dza,item.za);
    DivFator(nzb,temp);
    Expandir(nzb,dzb,item.zb);
    Desbalancear('C',item.ca);
    Desbalancear('S',item.sa);
    WriteLn(tl,'[-] Rede lattice e derivadas calculadas');
  END;

PROCEDURE ListarLattice(VAR item:filtro);

  PROCEDURE ListarRede(VAR circuito:lista);
  VAR
    t:REAL;
  BEGIN
    WITH circuito DO BEGIN
      FOR i:=1 TO n DO
        WITH el[i] DO BEGIN
          IF Abs(valor.re)>tolm THEN BEGIN
            CASE nme[1] OF
              'G':BEGIN
                    t:=1/valor.re;
                    txt:='R'+Copy(nme,2,4);
                  END;
              'R':BEGIN
                    t:=valor.re;
                    txt:='R'+Copy(nme,2,4)
                  END
              ELSE
                t:=valor.re;
                txt:=nme
            END;
            WriteLn(tl,'[',txt:4,']: ',t:cm:dc)
          END;
          IF Abs(valor.im)>tolm THEN BEGIN
            CASE nme[1] OF
              'G':BEGIN
                    t:=-1/valor.im;
                    txt:='X'+Copy(nme,2,4)
                  END;
              'R':BEGIN
                    t:=valor.im;
                    txt:='X'+Copy(nme,2,4)
                  END
              ELSE
                t:=valor.im;
                txt:=nme+'J'
            END;
            WriteLn(tl,'[',txt:4,']: ',t:cm:dc)
          END
        END;
      Write(tl,'Salvar? ([Cr] ou nome) [');
      ReadLn(txt); Write(tl,']');
      IF txt='' THEN Exit;
      Assign(arquivo,txt);
      ReWrite(arquivo);
      FOR i:=1 TO n DO
        WITH el[i] DO BEGIN
          IF Abs(valor.re)>tolm THEN BEGIN
            CASE nme[1] OF
              'G':BEGIN
                    t:=1/valor.re;
                    txt:='R'+Copy(nme,2,4)
                  END;
              'R':BEGIN
                    t:=valor.re;
                    txt:='R'+Copy(nme,2,4)
                  END
              ELSE
                t:=valor.re;
                txt:=nme
            END;
            WriteLn(arquivo,txt,' ',t:cm:dc);
          END;
          IF Abs(valor.im)>tolm THEN BEGIN
            CASE nme[1] OF
              'G':BEGIN
                    t:=-1/valor.im;
                    txt:='X'+Copy(nme,2,4)
                  END;
              'R':BEGIN
                    t:=valor.im;
                    txt:='X'+Copy(nme,2,4)
                  END
              ELSE
                t:=valor.im;
                txt:=nme+'J'
            END;
            WriteLn(arquivo,txt,' ',t:cm:dc);
          END
        END;
      Close(arquivo)
    END
  END;

BEGIN
  IF salvarlattice THEN BEGIN
    WriteLn(tl,'[Realiza‡„o de '+Nm(ia)+' da lattice]:');
    ListarRede(item.za);
    WriteLn(tl,'[Realiza‡„o de '+Nm(ib)+' da lattice]:');
    ListarRede(item.zb)
  END;
  IF salvarcom THEN BEGIN
    WriteLn(tl,'[Realiza‡„o em lattice desb. com acoplamentos]:');
    ListarRede(item.ca)
  END;
  IF salvarsem THEN BEGIN
    WriteLn(tl,'[Realiza‡„o em lattice desb. sem acoplamentos]:');
    ListarRede(item.sa)
  END
END;

PROCEDURE SalvarLattices;
VAR
  m,j:INTEGER;
  t:REAL;

BEGIN
  m:=0;
  FOR fil:=1 TO nfil DO IF tabela[fil]^.n>m THEN m:=tabela[fil]^.n;
  m:=(m+1) div 2;
  IF salvarlattice THEN BEGIN
    WriteLn(arquivo,ct[1],Linha(ct[10],(m)*(cmt+1)+6),ct[3]);
    txt:='Lattice d. t.';
    WriteLn(arquivo,ct[11],txt,Linha(' ',(m)*(cmt+1)+6-Length(txt)),ct[11]);
    WriteLn(arquivo,ct[4],ct[10],ct[10],ct[2],ct[10],ct[10],ct[10],Linha(ct[2]+Linha(ct[10],cmt),m),ct[6]);
    Write(arquivo,ct[11],' n',ct[11],'a/b');
    FOR i:=1 TO m DO BEGIN
      Str(i,txt);
      IF Odd(i) xor expandirz THEN Write(arquivo,ct[11],'C/X '+txt:cmt)
      ELSE Write(arquivo,ct[11],'L/X '+txt:cmt)
    END;
    WriteLn(arquivo,ct[11]);
    WriteLn(arquivo,ct[4],ct[10],ct[10],ct[5],ct[10],ct[10],ct[10],Linha(ct[5]+Linha(ct[10],cmt),m),ct[6]);
    FOR fil:=1 TO nfil DO WITH tabela[fil]^ DO BEGIN
      Write(arquivo,ct[11],n:2,ct[11],Nm(ia):3);
      FOR i:=1 TO m DO BEGIN
        j:=i*2-1;
        IF (j<=za.n) THEN Write(arquivo,ct[11],za.el[j].valor.re:cmt:dct) ELSE Write(arquivo,ct[11],' ':cmt);
      END;
      WriteLn(arquivo,ct[11]);
      Write(arquivo,ct[11],'  ',ct[11],'   ');
      FOR i:=1 TO m DO BEGIN
        j:=i*2;
        t:=za.el[j].valor.im; IF (za.el[j].nme[1]='G') and (Abs(t)>tolm) THEN t:=-1/t;
        IF (j<=za.n) and (Abs(t)>tolm) THEN Write(arquivo,ct[11],t:cmt:dct) ELSE Write(arquivo,ct[11],' ':cmt);
      END;
      WriteLn(arquivo,ct[11]);
      Write(arquivo,ct[11],'  ',ct[11],Nm(ib):3);
      FOR i:=1 TO m DO BEGIN
        j:=i*2-1;
        IF (j<=zb.n) THEN Write(arquivo,ct[11],zb.el[j].valor.re:cmt:dct) ELSE Write(arquivo,ct[11],' ':cmt);
      END;
      WriteLn(arquivo,ct[11]);
      Write(arquivo,ct[11],'  ',ct[11],'   ');
      FOR i:=1 TO m DO BEGIN
        j:=i*2;
        t:=zb.el[j].valor.im; IF (zb.el[j].nme[1]='G') and (Abs(t)>tolm) THEN t:=-1/t;
        IF (j<=zb.n) and (Abs(t)>tolm) THEN Write(arquivo,ct[11],t:cmt:dct) ELSE Write(arquivo,ct[11],' ':cmt);
      END;
      WriteLn(arquivo,ct[11]);
      IF fil=nfil THEN
        WriteLn(arquivo,ct[7],ct[10],ct[10],ct[8],ct[10],ct[10],ct[10],Linha(ct[8]+Linha(ct[10],cmt),m),ct[9])
      ELSE
      WriteLn(arquivo,ct[4],ct[10],ct[10],ct[5],ct[10],ct[10],ct[10],Linha(ct[5]+Linha(ct[10],cmt),m),ct[6])
    END
  END;
  IF salvarcom THEN BEGIN
    WriteLn(arquivo,ct[1],Linha(ct[10],(m)*(cmt+1)+2),ct[3]);
    txt:='Lattice d. t. desb. c/acopl.';
    WriteLn(arquivo,ct[11],txt,Linha(' ',(m)*(cmt+1)+2-Length(txt)),ct[11]);
    WriteLn(arquivo,ct[4],ct[10],ct[10],Linha(ct[2]+Linha(ct[10],cmt),m),ct[6]);
    Write(arquivo,ct[11],' n');
    FOR i:=1 TO m DO BEGIN
      Str(i,txt);
      IF Odd(i) xor expandirz THEN Write(arquivo,ct[11],'C/MC,X '+txt:cmt)
      ELSE Write(arquivo,ct[11],'L/ML,X '+txt:cmt)
    END;
    WriteLn(arquivo,ct[11]);
    WriteLn(arquivo,ct[4],ct[10],ct[10],Linha(ct[5]+Linha(ct[10],cmt),m),ct[6]);
    FOR fil:=1 TO nfil DO WITH tabela[fil]^ DO BEGIN
      Write(arquivo,ct[11],n:2);
      FOR i:=1 TO m DO BEGIN
        j:=i*4-3;
        IF (j<=ca.n) THEN Write(arquivo,ct[11],ca.el[j].valor.re:cmt:dct) ELSE Write(arquivo,ct[11],' ':cmt);
      END;
      WriteLn(arquivo,ct[11]);
      Write(arquivo,ct[11],'  ');
      FOR i:=1 TO m DO BEGIN
        IF Odd(n) THEN BEGIN
          j:=i*4-2;
          t:=ca.el[j].valor.re
        END
        ELSE BEGIN
          j:=i*4;
          t:=ca.el[j].valor.im;
          IF (ca.el[j].nme[2]='G') and (Abs(t)>tolm) THEN t:=-1/t
        END;
        IF (j<=ca.n) and (Abs(t)>tolm) THEN Write(arquivo,ct[11],t:cmt:dct) ELSE Write(arquivo,ct[11],' ':cmt);
      END;
      WriteLn(arquivo,ct[11]);
      IF fil=nfil THEN
        WriteLn(arquivo,ct[7],ct[10],ct[10],Linha(ct[8]+Linha(ct[10],cmt),m),ct[9])
      ELSE
        WriteLn(arquivo,ct[4],ct[10],ct[10],Linha(ct[5]+Linha(ct[10],cmt),m),ct[6])
    END
  END;
  IF salvarsem THEN BEGIN
    WriteLn(arquivo,ct[1],Linha(ct[10],(m)*(cmt+1)+2),ct[3]);
    txt:='Lattice d. t. desb. s/acopl.';
    WriteLn(arquivo,ct[11],txt,Linha(' ',(m)*(cmt+1)+2-Length(txt)),ct[11]);
    WriteLn(arquivo,ct[4],ct[10],ct[10],Linha(ct[2]+Linha(ct[10],cmt),m),ct[6]);
    Write(arquivo,ct[11],' n');
    FOR i:=1 TO m DO BEGIN
      Str(i,txt);
      IF Odd(i) xor expandirz THEN Write(arquivo,ct[11],'C/CM,X '+txt:cmt)
      ELSE Write(arquivo,ct[11],'L/LM,X '+txt:cmt)
    END;
    WriteLn(arquivo,ct[11]);
    WriteLn(arquivo,ct[4],ct[10],ct[10],Linha(ct[5]+Linha(ct[10],cmt),m),ct[6]);
    FOR fil:=1 TO nfil DO WITH tabela[fil]^ DO BEGIN
      Write(arquivo,ct[11],n:2);
      FOR i:=1 TO m DO BEGIN
        j:=i*4-3;
        IF (j<=sa.n) THEN Write(arquivo,ct[11],sa.el[j].valor.re:cmt:dct) ELSE Write(arquivo,ct[11],' ':cmt);
      END;
      WriteLn(arquivo,ct[11]);
      Write(arquivo,ct[11],'  ');
      FOR i:=1 TO m DO BEGIN
        IF Odd(n) THEN BEGIN
          j:=i*4-2;
          t:=sa.el[j].valor.re
        END
        ELSE BEGIN
          j:=i*4-1;
          t:=sa.el[j].valor.im;
          IF (sa.el[j].nme[1]='G') and (Abs(t)>tolm) THEN t:=-1/t
        END;
        IF (j<=sa.n) and (Abs(t)>tolm) THEN Write(arquivo,ct[11],t:cmt:dct) ELSE Write(arquivo,ct[11],' ':cmt);
      END;
      WriteLn(arquivo,ct[11]);
      IF fil=nfil THEN
        WriteLn(arquivo,ct[7],ct[10],ct[10],Linha(ct[8]+Linha(ct[10],cmt),m),ct[9])
      ELSE
        WriteLn(arquivo,ct[4],ct[10],ct[10],Linha(ct[5]+Linha(ct[10],cmt),m),ct[6])
    END
  END
END;

END.