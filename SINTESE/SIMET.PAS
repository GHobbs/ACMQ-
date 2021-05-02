PROGRAM Simet;
{******************************************************************************
 * Realiza‡„o de filtros "s¢ polos" por redes RLC sim‚tricas                  *
 * Ant“nio Carlos Moreir„o de Queiroz - COPPE/UFRJ                            *
 * Vers„o 1.0 de 09/03/88                                                     *
 * Vers„o 1.1 de 07/05/88 Melhor gr fico, arquivo .VAL normal                 *
 * Vers„o 1.2 de 13/05/88 Arquivo .VAL sem condutƒncias                       *
 * Vers„o 1.3 de 12/08/89 Turbo 5.0                                           *
 * Vers„o 1.4 de 27/08/89 Cores, nomes, etc.                                  *
 * Vers„o 1.4a de 17/01/90 Pequenas compatibiliza‡”es com o prog. Lattice     *
 * Vers„o 1.5 de 19/02/90 Melhorias na escolha do fator de divis„o            *
 ******************************************************************************}
{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}
  
USES Graph3,Crt,Tela;
  
{$I cmplx.p}
{$I sprites.p}
  
CONST
  versao='1.5 de 19/02/90';
  mg=40;
  mg2=80;
  pouco=1e-7;
  
TYPE
  polinomio=
  RECORD
    n:INTEGER;
    a:ARRAY[0..mg] OF complex;
  END;
  raizes=
  RECORD
    n:INTEGER;
    z:ARRAY[1..mg] OF complex;
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
  teclas=SET OF CHAR;
  filename=STRING;
  
VAR
  c:CHAR;
  fim:BOOLEAN;
  i,j:INTEGER;
  arquivo:TEXT;
  nome,rede:filename;
  polos,zz,pz:raizes;
  nz,dz,dt:polinomio;
  circuito:lista;
  marcado:ARRAY[1..mg] OF BOOLEAN;
  temp:complex;
  
FUNCTION Sim:BOOLEAN;
BEGIN
  Write(tl,' [s/n] ');
  REPEAT
    c:=UpCase(ReadKey)
  UNTIL c IN ['S','N'];
  WriteLn(c);
  Sim:=c='S'
END;
  
PROCEDURE ListarRede;
  VAR t:REAL;
BEGIN
  WITH circuito DO BEGIN
    FOR i:=1 TO n DO
      IF (Abs(el[i].valor.re)>pouco) OR (Abs(el[i].valor.im)>pouco) THEN
        WriteLn(tl,'[',el[i].nme:4,']: ',StrCmplx(el[i].valor));
    Write('Salvar?');
    IF NOT Sim THEN Exit;
    Assign(arquivo,rede+'.val');
    ReWrite(arquivo);
    FOR i:=1 TO n DO
      WITH el[i] DO BEGIN
        IF Abs(valor.re)>pouco THEN BEGIN
          CASE nme[1] OF
          'G':BEGIN
              t:=1/valor.re;
              nome:='RP'+Copy(nme,2,4)
            END;
          'R':BEGIN
              t:=valor.re;
              nome:='RS'+Copy(nme,2,4)
            END
          ELSE
              t:=valor.re;
            nome:=nme
          END;
          WriteLn(arquivo,nome,' ',t:cm:dc);
          WriteLn(tl,'[',nome:4,']: ',t:cm:dc)
        END;
        IF Abs(valor.im)>pouco THEN BEGIN
          CASE nme[1] OF
          'G':BEGIN
              t:=-1/valor.im;
              nome:='XP'+Copy(nme,2,4)
            END;
          'R':BEGIN
              t:=valor.im;
              nome:='XS'+Copy(nme,2,4)
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
    WriteLn(tl,'[*] Circuito salvo como [',rede+'.val]')
  END
END;
  
PROCEDURE ListarPolinomio(VAR x:polinomio; nome:filename);
  VAR i:INTEGER;
BEGIN
  WITH x DO BEGIN
    FOR i:=0 TO n DO WriteLn(tl,'a([',i:2,']):',StrCmplx(a[i]));
    IF nome='' THEN Exit;
    Write('Salvar?');
    IF Sim THEN BEGIN
      Assign(arquivo,nome);
      Rewrite(arquivo);
      WriteLn(arquivo,n);
      FOR i:=0 TO n DO WriteLn(arquivo,a[i].re,' ',a[i].im);
      Close(arquivo);
      WriteLn(tl,'[*] Polin“mio salvo como [',nome,']');
    END
  END
END;
  
PROCEDURE ListarRaizes(VAR x:raizes; nome:filename);
  VAR i:INTEGER;
BEGIN
  WITH x DO BEGIN
    FOR i:=1 TO n DO WriteLn(tl,'x([',i:2,']):',StrCmplx(z[i]));
    Write('Salvar?');
    IF Sim THEN BEGIN
      Assign(arquivo,nome);
      Rewrite(arquivo);
      WriteLn(arquivo,n);
      FOR i:=1 TO n DO WriteLn(arquivo,z[i].re,' ',z[i].im);
      Close(arquivo);
      WriteLn(tl,'[*] Ra¡zes salvas como [',nome,']')
    END
  END
END;
  
PROCEDURE LerPolos;
  VAR ordenado:BOOLEAN;
    t:complex;
    LABEL Inicio;
BEGIN
  Inicio:
  Write(tl,'Nome do arquivo (.r) ou [CR]: [');
  ReadLn(nome); Write(tl,']');
  IF Length(nome)=0 THEN
    WITH polos DO BEGIN
      Write('No. de polos: '); ReadLn(n);
      FOR i:=1 TO n DO BEGIN
        Write('p(',i:2,') (<re> <im>): ');
        ReadLn(z[i].re,z[i].im)
      END;
    END
  ELSE BEGIN
    IF Pos('.',nome)=0 THEN nome:=nome+'.r';
    Assign(arquivo,nome);
      {$I-} Reset(arquivo); {$I+}
    IF IOResult<>0 THEN BEGIN
      WriteLn(tl,'[*] Arquivo [',nome,'] n„o encontrado');
      GOTO Inicio
    END;
    rede:=Copy(nome,1,Pos('.',nome)-1);
    WITH polos DO BEGIN
      ReadLn(arquivo,n);
      WriteLn(n,' polos:');
      FOR i:=1 TO n DO BEGIN
        ReadLn(arquivo,z[i].re,z[i].im);
        WriteLn(tl,'p([',i:2,']):',StrCmplx(z[i]));
      END;
      Close(arquivo)
    END
  END;
  WITH polos DO
  REPEAT
    ordenado:=TRUE;
    FOR i:=1 TO n-1 DO BEGIN
      IF ArcTan(z[i+1].im/z[i+1].re)<ArcTan(z[i].im/z[i].re) THEN BEGIN
        t:=z[i]; z[i]:=z[i+1]; z[i+1]:=t;
        ordenado:=FALSE
      END
    END
  UNTIL ordenado;
  FOR i:=1 TO polos.n DO marcado[i]:=NOT Odd(i);
END;
  
PROCEDURE Expandir(direto:BOOLEAN);
  VAR X:complex;
    Z,so_imag,so_real,parcial:BOOLEAN;
    e:INTEGER;
    tmp,nzz,dzz:polinomio;
  
  PROCEDURE Inverter;
  BEGIN
    tmp:=nzz; nzz:=dzz; dzz:=tmp; Z:=NOT Z
  END;

  PROCEDURE Remover(grau:INTEGER);
    VAR nome:STRING[3];
  BEGIN
    so_imag:=grau=-1;
    so_real:=grau=-2;
    parcial:=grau=-3;
    IF grau<0 THEN grau:=0;
    Enter(nzz.a[dzz.n+grau]);
    Enter(dzz.a[dzz.n]);
    IF (Abs(sx.re)<pouco) AND (Abs(sx.im)<pouco) OR
    ((nzz.n-dzz.n<>grau) AND NOT parcial) THEN BEGIN
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
  nzz:=nz;
  dzz:=dz;
  IF Abs(nzz.n-dzz.n)>1 THEN BEGIN WriteLn(tl,'[*] Zm n„o ‚ imitƒncia v lida'); Exit END;
  Z:=TRUE;
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
      IF Z THEN WriteLn(tl,'[Zm(s)]:') ELSE WriteLn(tl,'[Ym(s)]:');
      CASE UpCase(ReadKey) OF
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
      #27:BEGIN WriteLn(tl,'[*] S¡ntese interrompida'); Exit END
      END
    UNTIL nzz.n<0
  END;
  WriteLn(tl,'[Realiza‡„o de Zm(s)]:');
  ListarRede
END;
  
PROCEDURE SepararPolos;
BEGIN
  zz.n:=0; pz.n:=0;
  FOR i:=1 TO polos.n DO
    IF marcado[i] THEN BEGIN
      pz.n:=pz.n+1;
      pz.z[pz.n]:=polos.z[i]
    END
    ELSE BEGIN
      zz.n:=zz.n+1;
      zz.z[zz.n]:=polos.z[i]
    END
END;
  
PROCEDURE EscolherPolos;
  CONST max=199;
    base=27;
  VAR xmin,ymin,delta,ay,by,ax,bx:REAL;
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
    IF marcado[i] THEN j:=1 ELSE j:=0;
    Square(x-4,y-4,x+4,y+4,j)
  END;
  
BEGIN
  xmin:=-3;
  ymin:=-2;
  delta:=4;
  csr:=1;
  REPEAT
    ay:=-max/delta; by:=max-ay*ymin;
    ax:=max/delta; bx:=-ax*xmin;
    GraphColorMode; Palette(3); ColorTable(3,2,1,0);
    SpriteMode;
    Sprite(0,#$FF#$FE#$FC#$FE#$FF#$FE#$DC#$88);
    Square(0,0,max,max,3);
    i:=Limx(0);
    Draw(i,0,i,max,2);
    i:=Limy(0);
    Draw(0,i,max,i,2);
    GoToXY(base,1); Write('X1:',xmin:7:4);
    GoToXY(base,2); Write('X2:',xmin+delta:7:4);
    GoToXY(base,3); Write('Y1:',ymin:7:4);
    GoToXY(base,4); Write('Y2:',ymin+delta:7:4);
    GoToXY(base,9); Write('Escolha os');
    GoToXY(base,10); Write('polos p/Zm');
    GOTOXY(base,22); Write('Comandos:');
    GoToXY(base,23); Write('cursor,+,-');
    GoToXY(base,24); Write('espaco');
    GoToXY(base,25); Write('RET,BS,ESC');
    WITH polos DO BEGIN
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
        #13:IF csr<n THEN csr:=csr+1 ELSE csr:=1;
        #8:IF csr>1 THEN csr:=csr-1 ELSE csr:=n;
        #0:BEGIN
            c:=ReadKey;
            CASE c OF
            'M':xmin:=xmin+delta/4;
            'K':xmin:=xmin-delta/4;
            'H':ymin:=ymin+delta/4;
            'P':ymin:=ymin-delta/4
            END
          END;
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
  TextMode(80);
  Write(tl,'Nome a dar ao circuito: ([',rede,']) [');
  ReadLn(nome); Write(tl,']');
  IF nome<>'' THEN rede:=nome
END;
  
PROCEDURE Montar(VAR r:raizes; VAR p:polinomio);
BEGIN
  WITH p DO BEGIN
    Atribuir(a[0],1,0); n:=0;
    FOR i:=1 TO r.n DO BEGIN
      n:=n+1;
      FOR j:=n DOWNTO 1 DO
        a[j]:=a[j-1];
      Atribuir(a[0],0,0);
      FOR j:=0 TO n-1 DO BEGIN
        Enter(a[j]);
        Enter(a[j+1]);
        Enter(r.z[i]);
        Multiplicar;
        Subtrair;
        a[j]:=sx
      END
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
  WriteLn('Zm(s) dividido por:',StrCmplx(fator));
END;
  
PROCEDURE Menu;
BEGIN
  WriteLn(tl,'-[A]utomaticamente fazer tudo');
  WriteLn(tl,'-[L]er Novos polos de T(s)');
  WriteLn(tl,'-Listar [T](s)');
  WriteLn(tl,'-S[E]parar polos de T(s) e montar Zm(s)');
  WriteLn(tl,'-[M]ultiplicar Zm(s) por fator');
  WriteLn(tl,'-Di[V]idir Zm(s) por fator');
  WriteLn(tl,'-Listar [Z]m(s)');
  WriteLn(tl,'-Expandir Zm(s) na forma [N]ormal');
  WriteLn(tl,'-Expandir Zm(s) [P]asso a passo');
  WriteLn(tl,'-[Esc]: Fim');
  WriteLn(tl,'-[CR]: Menu');
END;

BEGIN
fim:=FALSE;
polos.n:=0; dt.n:=0; temp.re:=1; temp.im:=0;
zz.n:=0; pz.n:=0; nz.n:=0; dz.n:=0;
rede:='xxx';
ClrScr;
WriteLn(tl,'[Realiza‡„o em Ladder sim‚trica RLC');
WriteLn(tl,'----------------------------------]');
WriteLn('ACMQ - Vers„o ',versao,' - Precis„o ',precisao);
WriteLn(tl,'[');
WriteLn('Este programa monta e realiza a impedƒncia vista pelo centro de uma');
WriteLn('rede "ladder" RLCX sim‚trica que possui a fun‡„o de transferˆncia');
WriteLn('"s¢ polos" com os polos dados.');
WriteLn(tl,']');
Menu;
WriteLn(tl,'[#]');
REPEAT
  c:=UpKey;
  CASE c OF
  'A':BEGIN
      LerPolos;
      Montar(polos,dt);
      SepararPolos;
      Montar(zz,nz);
      Montar(pz,dz);
      IF Odd(polos.n) THEN BEGIN
        Enter(nz.a[0]);
        Enter(dz.a[0]);
        IF (Abs(sx.re)<pouco) AND (Abs(sx.im)<pouco) THEN Atribuir(temp,1,0)
        ELSE BEGIN
          Dividir;
          temp:=sx
        END
      END
      ELSE Atribuir(temp,0,-2);
      DivFator(nz,temp);
      Expandir(TRUE)
    END;
  'L':BEGIN
      LerPolos;
      Montar(polos,dt);
    END;
  'E':BEGIN
      EscolherPolos;
      SepararPolos;
      Montar(zz,nz);
      Montar(pz,dz);
    END;
  'M','V':BEGIN
      IF c='V' THEN BEGIN
        WriteLn('Dividir Zm(s) por:');
        LerComplexo(temp);
      END
      ELSE BEGIN
        WriteLn('Multiplicar Zm(s) por:');
        LerComplexo(temp);
        Atribuir(sy,1,0);
        sx:=temp;
        Dividir;
        temp:=sx
      END;
      DivFator(nz,temp);
    END;
  'N':Expandir(TRUE);
  'P':Expandir(FALSE);
  'T':BEGIN
      WriteLn(tl,'[Polos de T(s)]:');
      ListarRaizes(polos,rede+'.r');
      WriteLn(tl,'[Denominador de T(s)]:');
      ListarPolinomio(dt,rede+'.e')
    END;
  'Z':BEGIN
      WriteLn(tl,'[Zeros de Zm(s)]:');
      ListarRaizes(zz,rede+'.zz');
      WriteLn(tl,'[Polos de Zm(s)]:');
      ListarRaizes(pz,rede+'.pz');
      WriteLn(tl,'[Numerador de Zm(s)]:');
      ListarPolinomio(nz,rede+'.nz');
      WriteLn(tl,'[Denominador de Zm(s)]:');
      ListarPolinomio(dz,rede+'.dz')
    END;
  #27:fim:=TRUE;
  #13:Menu
  END;
  WriteLn(tl,'[#]')
UNTIL fim
END.
