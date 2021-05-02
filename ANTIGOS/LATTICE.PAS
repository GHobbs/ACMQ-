PROGRAM Lattice;
{******************************************************************************
 * Decomposi‡„o T=(R/2)(1/Za-1/Zb) ou T=(G/2)(1/Yb-1/Ya)                      *
 * para realiza‡„o em lattice, com expans„o das imitƒncias resultantes.       *
 * Ant“nio Carlos Moreir„o de Queiroz - COPPE/UFRJ                            *
 * Vers„o 1.4 de 17/09/87                                                     *
 * Vers„o 1.5 de 17/01/88                                                     *
 * Vers„o 1.6 de 21/02/88                                                     *
 * Vers„o 1.7 de 09/03/88                                                     *
 * Vers„o 1.8 de 10/03/89 Turbo 5.0                                           *
 * Vers„o 1.9 de 12/08/89 Melhor Menu                                         *
 * Vers„o 2.0 de 27/08/89 Duas formas de expans„o, etc.                       *
 * Vers„o 2.0a de 10/09/89 Corrigida forma sem acoplamentos para expans„o Y   *
 * Vers„o 2.0b de 12/09/89 Mudada nomenclatura dos acoplamentos               *
 * Vers„o 2.0c de 17/01/90 Precis„o extendida, varias modifica‡”es            *
 * Vers„o 2.0d de 19/02/90 Multiplica‡„o por fator, corrigido fator normal    *
 * Vers„o 2.0e de 25/02/90 Nomes de arquivo corrigidos                        *
 * Vers„o 2.0f de 10/11/90 Fatores de divis„o corrigidos                      *
 ******************************************************************************}

{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}

USES Crt,Graph3,Tela;

{$I cmplx.p}
{$I sprites.p}

CONST
  versao='2.0f de 10/11/90';
  mg=40;
  mg2=80;
  pouco=1e-7;
  SimNao:SET OF CHAR=['S','N'];
  fim:BOOLEAN=FALSE;
  ExpandirZ:BOOLEAN=TRUE;

TYPE
  polinomio=
  RECORD
    n:INTEGER;
    a:ARRAY[0..mg] OF complex
  END;
  raizes=
  RECORD
    n:INTEGER;
    z:ARRAY[1..mg] OF complex
  END;
  lista=
  RECORD
    n:INTEGER;
    el:ARRAY[1..mg2] OF
    RECORD
      nme:STRING[4];
      valor:complex
    END
  END;
  filename=STRING;
  teclas=SET OF CHAR;
  nomes=(ia,ib);

VAR
  rede,nome:filename;
  res,polo,zero,zza,zzb,kza,kzb:raizes;
  num,tmp,nza,dza,nzb,dzb:polinomio;
  marcado:ARRAY[1..mg] OF BOOLEAN;
  za,zb,zt:lista;
  i,j,l:INTEGER;
  arquivo:TEXT;
  ok:BOOLEAN;
  sufixo:STRING[4];
  c:CHAR;
  temp:complex;

FUNCTION Nm(ix:nomes):STRING;
BEGIN
  IF ExpandirZ THEN BEGIN
    IF ix=ia THEN Nm:='Za' ELSE Nm:='Zb'
  END
  ELSE BEGIN
    IF ix=ia THEN Nm:='Yb' ELSE Nm:='Ya'
  END
END;
  
FUNCTION Sim:BOOLEAN;
BEGIN
  Write(tl,' [s/n] ');
  REPEAT
    c:=UpCase(ReadKey)
  UNTIL c IN ['S','N'];
  WriteLn(c);
  Sim:=c='S'
END;

PROCEDURE ListarRede(VAR circuito:lista; onde:filename);
   VAR t:REAL;
   BEGIN
   WITH circuito DO
      BEGIN
      FOR i:=1 TO n DO
        IF (Abs(el[i].valor.re)>pouco) or (Abs(el[i].valor.im)>pouco) THEN
           WriteLn(tl,'[',el[i].nme:4,']: ',StrCmplx(el[i].valor));
      Write('Salvar?');
      IF not Sim THEN Exit;
      Assign(arquivo,onde);
      ReWrite(arquivo);
      FOR i:=1 TO n DO
         WITH el[i] DO
            BEGIN
            IF Abs(valor.re)>pouco THEN
               BEGIN
               CASE nme[1] OF
                  'G':BEGIN
                      t:=1/valor.re;
                      nome:='R'+Copy(nme,2,4)
                      END;
                  'R':BEGIN
                      t:=valor.re;
                      nome:='R'+Copy(nme,2,4)
                      END
                  ELSE
                     t:=valor.re;
                     nome:=nme
                  END;
               WriteLn(arquivo,nome,' ',t:cm:dc);
               WriteLn(tl,'[',nome:4,']: ',t:cm:dc)
               END;
            IF Abs(valor.im)>pouco THEN
               BEGIN
               CASE nme[1] OF
                  'G':BEGIN
                      t:=-1/valor.im;
                      nome:='X'+Copy(nme,2,4)
                      END;
                  'R':BEGIN
                      t:=valor.im;
                      nome:='X'+Copy(nme,2,4)
                      END
                  ELSE
                     t:=valor.im;
                     nome:=nme+'J'
                  END;
               WriteLn(arquivo,nome,' ',t:cm:dc);
               WriteLn(tl,'[',nome:4,']: ',t:cm:dc)
               END
            END;
      Close(arquivo);
      WriteLn(tl,'[*] Circuito salvo como [',onde,']')
      END
   END;

PROCEDURE ListarPolinomio(VAR x:polinomio; nome:filename);
  VAR
    i:INTEGER;
BEGIN
  WITH x DO BEGIN
    FOR i:=0 TO n DO WriteLn(tl,'a([',i:2,']):',StrCmplx(a[i]));
    IF nome='' THEN Exit;
    Write('Salvar?');
    IF Sim THEN BEGIN
      Assign(arquivo,nome);
      Rewrite(arquivo);
      WriteLn(arquivo,n);
      FOR i:=0 TO n DO WriteLn(arquivo,a[i].re:cm:dc,' ',a[i].im:cm:dc);
      Close(arquivo);
      WriteLn(tl,'[*] Polin“mio salvo como [',nome,']');
    END
  END
END;
  
PROCEDURE ListarRaizes(VAR x:raizes; nome:filename);
  VAR
    i:INTEGER;
BEGIN
  WITH x DO BEGIN
    FOR i:=1 TO n DO WriteLn(tl,'x([',i:2,']):',StrCmplx(z[i]));
    Write('Salvar?');
    IF Sim THEN BEGIN
      Assign(arquivo,nome);
      Rewrite(arquivo);
      WriteLn(arquivo,n);
      FOR i:=1 TO n DO WriteLn(arquivo,StrCmplx(z[i]));
      Close(arquivo);
      WriteLn(tl,'[*] Ra¡zes salvas como [',nome,']')
    END
  END
END;

PROCEDURE DivFator(VAR p:polinomio; VAR fator:complex);
BEGIN
  WITH p DO
    FOR i:=0 TO n DO BEGIN
      sy:=a[i];
      sx:=fator;
      Dividir;
      a[i]:=sx
    END;
  WriteLn('Dividido por:',StrCmplx(fator));
END;

PROCEDURE Expandir(nzz,dzz:polinomio; VAR circuito:lista; onde:filename; direto:BOOLEAN);
  VAR
    X:complex;
    Z,so_imag,so_real,parcial:BOOLEAN;
    e:INTEGER;
    tmp:polinomio;

  PROCEDURE Inverter;
  BEGIN
    tmp:=nzz; nzz:=dzz; dzz:=tmp; Z:=NOT Z
  END;

  PROCEDURE Remover(grau:INTEGER);
    VAR
      nome:STRING[3];
  BEGIN
    so_imag:=grau=-1;
    so_real:=grau=-2;
    parcial:=grau=-3;
    IF grau<0 THEN grau:=0;
    Enter(nzz.a[dzz.n+grau]);
    Enter(dzz.a[dzz.n]);
    IF (Abs(sx.re)<pouco) AND (Abs(sx.im)<pouco) OR ((nzz.n-dzz.n<>grau) AND NOT parcial) THEN   BEGIN
      WriteLn(tl,'[*] Nada a extrair');
      Exit
    END;
    Dividir;
    X:=sx;
    IF so_imag THEN X.re:=0;
    IF so_real THEN X.im:=0;
    IF parcial THEN BEGIN
      Write('Cte:');
      LerComplexo(X)
    END;
    FOR i:=grau TO dzz.n+grau DO BEGIN
      Enter(nzz.a[i]);
      Enter(dzz.a[i-grau]);
      Enter(X);
      Multiplicar;
      Subtrair;
      nzz.a[i]:=sx
    END;
    IF NOT (so_imag OR so_real OR parcial) THEN nzz.n:=nzz.n-1;
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
      IF NOT direto THEN
        WriteLn(nome,StrCmplx(X))
    END
  END;

BEGIN
  IF Abs(nzz.n-dzz.n)>1 THEN
    BEGIN WriteLn(tl,'[*] Imitƒncia inv lida'); Exit END;
  Z:=ExpandirZ;
  e:=0; circuito.n:=0;
  IF direto THEN BEGIN
    IF nzz.n<dzz.n THEN Inverter;
    REPEAT
      Remover(1);
      Remover(0);
      Inverter
    UNTIL dzz.n<0
  END
  ELSE BEGIN
    WriteLn(tl,'[Comandos]:');
    WriteLn(tl,'Extrair: [C]te no infinito');
    WriteLn(tl,'         Cte R[E]al no infinito');
    WriteLn(tl,'         Cte I[M]ag no infinito');
    WriteLn(tl,'         Cte [A]rbitrada');
    WriteLn(tl,'         [P]olo no infinito');
    WriteLn(tl,'[I]nverter imitƒncia');
    WriteLn(tl,'[L]istar imitƒncia');
    WriteLn(tl,'[ESC] interrompe');
    REPEAT
      IF Z THEN WriteLn(tl,'[Z(s)]:') ELSE WriteLn(tl,'[Y(s)]:');
      c:=ReadKey;
      CASE UpCase(c) OF
      'C':Remover(0);
      'P':Remover(1);
      'M':Remover(-1);
      'E':Remover(-2);
      'A':Remover(-3);
      'I':Inverter;
      'L':BEGIN
          WriteLn(tl,'[Numerador]:');
          ListarPolinomio(nzz,'');
          WriteLn(tl,'[Denominador]:');
          ListarPolinomio(dzz,'')
        END;
      #27:Exit
      END
    UNTIL nzz.n<0
  END;
  IF NOT direto THEN WriteLn(tl,'[Realiza‡„o final]:');
  ListarRede(circuito,onde);
END;

PROCEDURE ProdutoLimitado(VAR f:raizes; l:INTEGER);
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
  
PROCEDURE LerRaizes(VAR x:raizes; onde:filename);
BEGIN
  Assign(arquivo,onde);
   {$I-} Reset(arquivo); {$I+}
  ok:=IOResult=0;
  IF NOT ok THEN BEGIN
    WriteLn(tl,'[*] Arquivo [',onde,'] n„o encontrado');
    Exit
  END;
  WITH x DO BEGIN
    ReadLn(arquivo,n);
    WriteLn(n,' raizes:');
    FOR i:=1 TO n DO BEGIN
      ReadLn(arquivo,z[i].re,z[i].im);
      WriteLn(tl,'x([',i:2,']):',StrCmplx(z[i]));
    END;
    Close(arquivo)
  END;
END;

PROCEDURE LerPolinomio(VAR x:polinomio; onde:filename);
  VAR
    cte:REAL;
BEGIN
  Assign(arquivo,onde);
   {$I-} Reset(arquivo); {$I+}
  ok:=IOResult=0;
  IF NOT ok THEN BEGIN
    WriteLn(tl,'[*] Arquivo [',onde,'] n„o encontrado');
    Exit
  END;
  WITH x DO BEGIN
    ReadLn(arquivo,n);
    WriteLn('Grau ',n,':');
    FOR i:=0 TO n DO BEGIN
      ReadLn(arquivo,a[i].re); a[i].im:=0;
      WriteLn(tl,'a([',i:2,']):',StrCmplx(a[i]));
    END;
    ReadLn(arquivo,cte);
    WriteLn('Cte:  ',cte:cm:dc);
    FOR i:=0 TO n DO
      a[i].re:=a[i].re*cte;
    Close(arquivo)
  END;
END;

PROCEDURE LerParametros;
  VAR
    ordenado:BOOLEAN;
    t:complex;
BEGIN
  Write(tl,'Nome da rede: ['); ReadLn(nome); Write(tl,']');
  rede:=nome;
  Write(tl,'[P¢los]: ');
  LerRaizes(polo,nome+'.r');
  IF NOT ok THEN Exit;
  Write(tl,'[Numerador]: ');
  LerPolinomio(num,nome+'.p');
  IF NOT ok THEN BEGIN
    Write(tl,'[Zeros]: ');
    LerRaizes(zero,nome+'.z');
    IF not ok THEN Exit;
    ProdutoLimitado(zero,0); num:=tmp
  END;
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
      FOR i:=1 TO n DO marcado[i]:=Odd(i) xor Odd(n div 2);
    END
END;
  
PROCEDURE CalcularResiduos;
  VAR
    d:complex;
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

PROCEDURE ListarParametros;
BEGIN
  WriteLn(tl,'[Zeros de '+Nm(ia)+']:');
  ListarRaizes(zza,rede+'.z'+Nm(ia));
  WriteLn(tl,'[Zeros de '+Nm(ib)+']:');
  ListarRaizes(zzb,rede+'.z'+Nm(ib));
  WriteLn(tl,'[Numerador de '+Nm(ia)+']:');
  ListarPolinomio(nza,rede+'.n'+Nm(ia));
  WriteLn(tl,'[Denominador de '+Nm(ia)+']:');
  ListarPolinomio(dza,rede+'.d'+Nm(ia));
  WriteLn(tl,'[Numerador de '+Nm(ib)+']:');
  ListarPolinomio(nzb,rede+'.n'+Nm(ib));
  WriteLn(tl,'[Denominador de '+Nm(ib)+']:');
  ListarPolinomio(dzb,rede+'.d'+Nm(ib))
END;

PROCEDURE EscolherPolos;
  CONST
    max=199;
    base=27;
  VAR
    xmin,ymin,delta,ay,by,ax,bx:REAL;
    x,y,csr:INTEGER;
  
  FUNCTION Limx(x:REAL):INTEGER;
  BEGIN
    IF x>=xmin+delta THEN Limx:=max
    ELSE IF x<=xmin THEN Limx:=0
    ELSE Limx:=Round(ax*x+bx)
  END;
  
  FUNCTION Limy(y:REAL):INTEGER;
  BEGIN
    IF y>=ymin+delta THEN Limy:=0
    ELSE IF y<=ymin THEN Limy:=max
    ELSE Limy:=Round(ay*y+by)
  END;
  
  PROCEDURE Marcar; {recebe i,x e y}
  BEGIN
    IF marcado[i] THEN j:=2 ELSE j:=0;
    Square(x-4,y-4,x+4,y+4,j)
  END;
  
BEGIN
  xmin:=-3; ymin:=-2; delta:=4; csr:=1;
  REPEAT
    ay:=-max/delta; by:=max-ay*ymin;
    ax:=max/delta; bx:=-ax*xmin;
    GraphColorMode; Palette(3); ColorTable(3,2,1,0);
    SpriteMode;
    Sprite(0,#$FF#$FE#$FC#$FE#$FF#$FE#$DC#$88);
    Square(0,0,max,max,3);
    i:=Limx(0);
    Draw(i,0,i,max,1);
    i:=Limy(0);
    Draw(0,i,max,i,1);
    GoToXY(base,1); Write('X1:',xmin:7:4);
    GoToXY(base,2); Write('X2:',xmin+delta:7:4);
    GoToXY(base,3); Write('Y1:',ymin:7:4);
    GoToXY(base,4); Write('Y2:',ymin+delta:7:4);
    GoToXY(base,9); Write('Escolha os');
    GoToXY(base,10); Write('zeros p/'+Nm(ia));
    GOTOXY(base,22); Write('Comandos:');
    GoToXY(base,23); Write('cursor,+,-');
    GoToXY(base,24); Write('espa‡o');
    GoToXY(base,25); Write('RET,ESC');
    WITH polo DO BEGIN
      FOR i:=1 TO n DO BEGIN
        x:=Limx(z[i].re);
        y:=Limy(z[i].im);
        Draw(x-2,y-2,x+2,y+2,3);
        Draw(x-2,y+2,x+2,y-2,3);
        Marcar;
      END;
      REPEAT
        x:=Limx(z[csr].re);
        y:=Limy(z[csr].im);
        PutsPrite(0,x,y);
        GoToXY(base,6); Write('Re:',Z[csr].re:7:4);
        GoToXY(base,7); Write('Im:',Z[csr].im:7:4);
        c:=ReadKey;
        CASE c OF
        #0:BEGIN
            c:=ReadKey;
            CASE c OF
            'M':xmin:=xmin+delta/4;
            'K':xmin:=xmin-delta/4;
            'H':ymin:=ymin+delta/4;
            'P':ymin:=ymin-delta/4
            END
          END;
        #13:IF csr<n THEN csr:=csr+1 ELSE csr:=1;
        '-':BEGIN
            xmin:=xmin-delta/2;
            ymin:=ymin-delta/2;
            delta:=delta*2
          END;
        '+':BEGIN
            xmin:=xmin+delta/4;
            ymin:=ymin+delta/4;
            delta:=delta/2;
          END;
        ' ':BEGIN
            marcado[csr]:=NOT marcado[csr];
            i:=csr;
            PutSprite(0,-10,-10);
            Marcar
          END
        END
      UNTIL c IN [#27,'M','K','H','P','+','-'];
    END;
  UNTIL c=#27;
  TextMode(C80);
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

PROCEDURE Desbalancear(x:CHAR; saida:filename);
BEGIN
  WITH zt DO BEGIN
    IF x='C' THEN BEGIN
      WriteLn(tl,'[Realiza‡„o com acoplamentos]:');
      i:=0; n:=0;
      REPEAT
        i:=i+1; n:=n+1;
        IF za.el[i].nme[1]<>zb.el[i].nme[1] THEN BEGIN
          WriteLn(tl,'[*] As duas imitƒncias n„o s„o da mesma forma (?!)');
          Exit
        END;
        Enter(zb.el[i].valor);
        Enter(za.el[i].valor);
        Somar;
        Atribuir(sy,0.5,0);
        Multiplicar;
        el[n].valor:=sx;
        el[n].nme:=za.el[i].nme;  
        Enter(zb.el[i].valor);
        Enter(za.el[i].valor);
        Subtrair;
        IF ExpandirZ THEN Atribuir(sy,0.5,0) ELSE Atribuir(sy,-0.5,0);
            {-0.5 para compensar a troca de ordem entre Ya e Yb}
        Multiplicar;
        el[n+1].valor:=sx;
        el[n+1].nme:='M'+za.el[i].nme;
        n:=n+1
      UNTIL (i=za.n) OR (i=zb.n)
    END
    ELSE BEGIN
      WriteLn(tl,'[Realiza‡„o sem acoplamentos]:');
      i:=0; n:=0;
      REPEAT
        i:=i+1; n:=n+1;
        c:=za.el[i].nme[1];
        IF c<>zb.el[i].nme[1] THEN BEGIN
          WriteLn(tl,'[*] As duas imitƒncias n„o s„o da mesma forma (?!)');
          Exit
        END;
        IF c IN ['R','L'] THEN BEGIN
          Enter(zb.el[i].valor);
          Enter(za.el[i].valor);
        END
        ELSE BEGIN
          Enter(za.el[i].valor);
          Enter(zb.el[i].valor);
        END;
        IF NOT ExpandirZ THEN BEGIN {Trocar Ya e Yb}
          sz:=sx; sx:=sy; sy:=sz
        END;
        el[n].valor:=sx;
        el[n].nme:=za.el[i].nme;  
        Subtrair;
        Atribuir(sy,0.5,0);
        Multiplicar;
        el[n+1].valor:=sx;
        el[n+1].nme:=za.el[i].nme[1]+'M'+Copy(za.el[i].nme,2,10);
        n:=n+1
      UNTIL (i=za.n) OR (i=zb.n)
    END;
      {Elemento central}
    IF za.n>zb.n THEN
      FOR j:=zb.n+1 TO za.n DO BEGIN
        n:=n+1;
        Enter(za.el[j].valor);
        Atribuir(sy,2,0);
        Multiplicar;
        el[n].valor:=sx;
        el[n].nme:=za.el[j].nme  
      END
    ELSE
      FOR j:=za.n+1 TO zb.n DO BEGIN
        n:=n+1;
        Enter(zb.el[j].valor);
        Atribuir(sy,2,0);
        Multiplicar;
        el[n].valor:=sx;
        el[n].nme:=zb.el[j].nme
      END;
    ListarRede(zt,saida)
  END
END;

PROCEDURE Menu;
BEGIN
  WriteLn(tl,'-Determinar expans„o a [U]sar');
  WriteLn(tl,'-[A]utomaticamente fazer tudo');
  WriteLn(tl,'-[L]er parƒmetros para T(s) e calcular res¡duos dos p¢los');
  WriteLn(tl,'-Listar P¢los e res¡duos de [T](s)');
  WriteLn(tl,'-S[E]parar p¢los de T(s) e montar '+Nm(ia)+'(s) e '+Nm(ib)+'(s)');
  WriteLn(tl,'-Di[V]idir '+Nm(ia)+'(s) e '+Nm(ib)+'(s) por fator');
  WriteLn(tl,'-[M]ultiplicar '+Nm(ia)+'(s) e '+Nm(ib)+'(s) por fator');
  WriteLn(tl,'-Listar [P]arƒmetros de '+Nm(ia)+'(s) e '+Nm(ib)+'(s)');
  WriteLn(tl,'-E[X]pandir '+Nm(ia)+'(s) e '+Nm(ib)+'(s) passo a passo');
  WriteLn(tl,'-Expandir '+Nm(ia)+'(s) e '+Nm(ib)+'(s) na forma [N]ormal');
  WriteLn(tl,'-Desbalancear lattice [C]/ acoplamentos');
  WriteLn(tl,'-Desbalancear lattice [S]/ acoplamentos');
  WriteLn(tl,'-[D]iret¢rio');
  WriteLn(tl,'-[Esc]: Fim');
  WriteLn(tl,'-[CR]: Menu');
END;

BEGIN
ClrScr;
zza.n:=0; zzb.n:=0; kza.n:=0; kzb.n:=0;
nza.n:=0; dza.n:=0; nzb.n:=0; dzb.n:=0;
temp.re:=1; temp.im:=0;
WriteLn(tl,'[Realiza‡„o em Lattice RLCX');
WriteLn(tl,'--------------------------]');
WriteLn('ACMQ - Vers„o ',versao,' - Precis„o ',precisao);
WriteLn(tl,'[');
WriteLn('Este programa obt‚m a realiza‡„o em "lattice" RLCX sim‚trica para uma');
WriteLn('fun‡„o de transferˆncia cujos p¢los e zeros (ou numerador) sejam dados.');
WriteLn('Realiza‡”es desbalanceadas podem ser obtidas a partir da "lattice".');
WriteLn(tl,']');
Menu;
WriteLn(tl,'[#]');
REPEAT
  c:=ReadKey; c:=UpCase(c);
  CASE c OF
  'U':BEGIN
      WriteLn('Forma da expans„o a usar:');
      WriteLn(tl,'T = (R/2) (1/[Z]a-1/Zb)');
      WriteLn(tl,'T = (G/2) (1/[Y]b-1/Ya)');
      REPEAT c:=UpKey UNTIL c IN ['Z','Y'];
      ExpandirZ:=c='Z'
    END;
  'A':BEGIN
      LerParametros;
      IF ok THEN BEGIN
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
        WriteLn(tl,'[Realiza‡„o de '+Nm(ia)+']:');
        DivFator(nza,temp);
        Expandir(nza,dza,za,rede+'.'+Nm(ia),TRUE);
        WriteLn(tl,'[Realiza‡„o de '+Nm(ib)+']:');
        DivFator(nzb,temp);
        Expandir(nzb,dzb,zb,rede+'.'+Nm(ib),TRUE);
        Desbalancear('C',rede+'.vlc');
        Desbalancear('S',rede+'.vls');
      END
    END;
  'M','V':BEGIN
      IF c='V' THEN BEGIN
        WriteLn('Dividir ',Nm(ia),'(s) e ',Nm(ib),'(s) por:');
        LerComplexo(temp);
      END
      ELSE BEGIN
        WriteLn('Multiplicar ',Nm(ia),'(s) e ',Nm(ib),'(s) por:');
        LerComplexo(temp);
        Atribuir(sy,1,0);
        sx:=temp;
        Dividir;
        temp:=sx
      END;
      Write(Nm(ia),'(s): ');
      DivFator(nza,temp);
      Write(Nm(ib),'(s): ');
      DivFator(nzb,temp)
    END;
  'L':BEGIN
      LerParametros;
      IF ok THEN CalcularResiduos;
    END;
  'E':BEGIN
      EscolherPolos;
      SepararPolos;
      MontarImpedancias;
    END;
  'X':BEGIN
      WriteLn(tl,'[Realiza‡„o de '+Nm(ia)+']:');
      Expandir(nza,dza,za,rede+'.'+Nm(ia),FALSE);
      WriteLn(tl,'[Realiza‡„o de '+Nm(ib)+']:');
      Expandir(nzb,dzb,zb,rede+'.'+Nm(ib),FALSE);
    END;
  'N':BEGIN
      WriteLn(tl,'[Realiza‡„o de '+Nm(ia)+']:');
      Expandir(nza,dza,za,rede+'.'+Nm(ia),TRUE);
      WriteLn(tl,'[Realiza‡„o de '+Nm(ib)+']:');
      Expandir(nzb,dzb,zb,rede+'.'+Nm(ib),TRUE);
    END;
  'P':ListarParametros;
  'C':Desbalancear('C',rede+'.vlc');
  'S':Desbalancear('S',rede+'.vls');
  'T':BEGIN
      WriteLn(tl,'[P¢los de T(s)]:');
      ListarRaizes(polo,rede+'.r');
      WriteLn(tl,'[Res¡duos dos p¢los]:');
      ListarRaizes(res,rede+'.k');
    END;
  'D':Diretorio;
  #13:Menu;
  #27:fim:=TRUE;
  END;
  WriteLn(tl,'[#]')
UNTIL fim
END.
