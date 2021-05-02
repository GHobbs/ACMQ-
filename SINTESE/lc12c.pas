PROGRAM LC;
{******************************************************************************
 * S¡ntese de redes LC                                                        *
 * Ant“nio Carlos Moreir„o de Queiroz - COPPE/UFRJ                            *
 * Vers„o 1.0  de 11/01/88                                                    *
 * Vers„o 1.1  de 12/04/89                                                    *
 * Vers„o 1.2  de 09/06/90 Entrada com arquivos de p¢los e zeros normais      *
 * Vers„o 1.2a de 14/04/91 Erro no mapa corrigido, mapa se move               *
 * Vers„o 1.2b de 19/04/92 TPBGI
 * Vers„o 1.2c de 30/08/1999 Aumentado o tamanho do mapa                                          *
 ******************************************************************************}

{$IFDEF DOUBLE}
  {$N+,E+}
{$ENDIF}

USES Dos,Crt,Graph,Tela;

CONST
  versao='1.2c de 30/08/1999';
  maxgrau=20;
  maxel=30;
  maxmapa=40;
  tol=1e-7;
  SN:SET of CHAR=['S','N'];

  driver:INTEGER=0;
  modo:INTEGER=0;

TYPE
  valores=ARRAY[1..maxgrau] of REAL;
  possibilidades=SET of 'A'..'Z';

VAR
  wp,wz,k: valores;
  cte,ko,koo,w0,x,x1,k1:REAL;
  erro,e_impedancia,polo_na_origem,polo_no_infinito:BOOLEAN;
  imitancia_lida,residuos_validos,ok,interrompido:BOOLEAN;
  nz,mp,i,j,polo,secoes,nlista,nmapa:INTEGER;
  r:CHAR;
  nome:STRING;
  arquivo:TEXT;
  lista:ARRAY[1..maxel] of
    RECORD
      tpo:CHAR;
      nmr:INTEGER;
      vlr:REAL
    END;
  mapa:ARRAY[0..maxmapa] of
    RECORD
      nup,nuz:INTEGER;
      p,z:valores;
      po,poo,zy:BOOLEAN;
      el:STRING[6];
    END;

PROCEDURE Mapear;
CONST
  xmin=20;
  xmax=510;
VAR
  x,y:INTEGER;
  ax,bx,wmin,wmax,dw:REAL;

  PROCEDURE PlotarPolo(w:REAL; y:INTEGER; inf:BOOLEAN);
  BEGIN
    IF inf THEN x:=xmax+20
    ELSE BEGIN
      w:=ax*w+bx;
      IF w>xmax THEN w:=xmax+5
      ELSE IF w<xmin THEN w:=xmin-5;
      x:=Round(w)
    END;
    Line(x-2,y-2,x+2,y+2);
    Line(x-2,y+2,x+2,y-2);
  END; {PlotarPolo}

  PROCEDURE PlotarZero(w:REAL; y:INTEGER; inf:BOOLEAN);
  BEGIN
    IF inf THEN x:=xmax+20
    ELSE BEGIN
      w:=ax*w+bx;
      IF w>xmax THEN w:=xmax+5
      ELSE IF w<xmin THEN w:=xmin-5;
      x:=Round(w)
    END;
    Rectangle(x-2,y-2,x+2,y+2)
  END; {PlotarZero}

BEGIN
  wmin:=0; wmax:=20;
  REPEAT
    ax:=(xmax-xmin)/(wmax-wmin);
    bx:=xmin-ax*wmin;
    SetGraphMode(modo);
    Str(wmin:7:3,nome); OutTextXY(0,0,nome);
    Str(wmax:7:3,nome); OutTextXY(xmax-56,0,nome);
    FOR i:=1 TO nmapa DO
      WITH mapa[i] DO BEGIN
        y:=i*8+4;
        MoveTo(1,y-4);
        IF zy THEN OutText('Z') ELSE OutText('Y');
        MoveTo(xmax+30,y-7); OutText(el);
        Line(xmin,y,xmax,y);
        FOR j:=1 TO nuz DO
          PlotarZero(z[j],y,FALSE);
        FOR j:=1 TO nup DO
          PlotarPolo(p[j],y,FALSE);
        IF po THEN PlotarPolo(0,y,FALSE) ELSE IF (nup>0) or poo THEN PlotarZero(0,y,FALSE);
        IF poo THEN PlotarPolo(0,y,TRUE) ELSE IF (nup>0) or po THEN PlotarZero(0,y,TRUE);
      END;
    r:=UpKey;
    CASE r OF
      'R':wmax:=wmax+(wmax-wmin);
      'A':wmax:=wmax-(wmax-wmin)/2;
      #0:CASE ReadKey OF
           #77:BEGIN dw:=(wmax-wmin)/4; wmax:=wmax+dw; wmin:=wmin+dw END;
           #75:BEGIN dw:=(wmax-wmin)/4; wmax:=wmax-dw; wmin:=wmin-dw END;
         END;
      #27:;
    END;
  UNTIL r=#27;
  RestoreCrtMode
END; {Mapear}

PROCEDURE AumentarMapa(feita_extracao,paralelo:BOOLEAN);
BEGIN
  nmapa:=nmapa+1;
  WITH mapa[nmapa] DO BEGIN
    nup:=mp;
    nuz:=nz;
    p:=wp;
    z:=wz;
    po:=polo_na_origem;
    poo:=polo_no_infinito;
    zy:=e_impedancia;
    IF feita_extracao THEN BEGIN
      el:=lista[nlista].tpo;
      IF nlista>1 THEN
        IF lista[nlista-1].nmr=secoes THEN el:='LC';
      Str(secoes,nome);
      el:=el+nome;
      IF paralelo THEN el:=el+'//' ELSE el:=el+'--';
    END
    ELSE el:=''
  END;
END; {AumentarMapa}

FUNCTION Resposta(x:possibilidades):CHAR;
BEGIN
  REPEAT r:=UpCase(ReadKey) UNTIL r in x;
  WriteLn(r);
  Resposta:=r
END; {Resposta}

PROCEDURE Guardar(tipo:INTEGER; valor:REAL);
BEGIN
  IF tipo<4 THEN
    secoes:=secoes+1;
  nlista:=nlista+1;
  WITH lista[nlista] DO BEGIN
    IF e_impedancia xor Odd(tipo) THEN tpo:='L' ELSE tpo:='C';
    nmr:=secoes;
    vlr:=valor;
    WriteLn(tpo,nmr,': ',vlr:11:8);
  END;
END; {Guardar}

PROCEDURE LerImitancia;
VAR
  lerarquivos:BOOLEAN;
  ctez,ctep:REAL;

  PROCEDURE LerArquivo(pz:STRING; VAR n:INTEGER; VAR w:valores; VAR cte:REAL);
  VAR
    i,j:INTEGER;
    tr,ti:REAL;
  BEGIN
    Write('Arquivo com os ',pz,': '); ReadLn(nome);
    Assign(arquivo,nome);
    {$I-} Reset(arquivo); {$I+}
    erro:=IOResult<>0;
    IF erro THEN BEGIN
      WriteLn(tl,'[*] Arquivo n„o encontrado');
      Exit
    END;
    ReadLn(arquivo,n);
    i:=0;
    FOR j:=1 TO n DO BEGIN
      ReadLn(arquivo,tr,ti);
      Write(tl,'s([',j,']): ',tr,ti,'j');
      IF Abs(tr)>tol THEN BEGIN
        WriteLn;
        WriteLn(tl,'[*] Imitƒncia LC s¢ pode possu¡r ',pz,' no eixo jw');
        erro:=TRUE;
        Close(arquivo);
        Exit
      END;
      IF (Abs(ti)>tol) and (ti>0) THEN BEGIN
        Inc(i); w[i]:=ti; WriteLn(tl,' ([w',pz[1],'(',i,')])')
      END
      ELSE WriteLn;
    END;
    IF not SeekEof(arquivo) THEN ReadLn(arquivo,cte) ELSE cte:=1;
    WriteLn(tl,'[Cte]:  ',cte);
    Close(arquivo)
  END;

  PROCEDURE Ordenar(n:INTEGER; VAR w:valores);
  VAR
    ordenado:BOOLEAN;
    t:REAL;
    i:INTEGER;
  BEGIN
    REPEAT
      ordenado:=TRUE;
      FOR i:=1 TO n-1 DO
      BEGIN
        IF w[i+1]<w[i] THEN
        BEGIN
          t:=w[i]; w[i]:=w[i+1]; w[i+1]:=t;
          ordenado:=FALSE
        END
      END
    UNTIL ordenado;
  END;

BEGIN
  Write(tl,'Imitƒncia de entrada em arquivos? ([s/n]) ');
  lerarquivos:=Resposta(SN)='S';
  Write(tl,'[I]mpedƒncia ou [A]dmitƒncia? ');
  e_impedancia:=(Resposta(['A','I'])='I');
  IF lerarquivos THEN BEGIN
    LerArquivo('zeros',nz,wz,ctez);
    IF erro THEN Exit;
    LerArquivo('p¢los',mp,wp,ctep);
    IF erro THEN Exit;
    cte:=ctez/ctep
  END
  ELSE BEGIN
    Write('Grau do numerador: '); ReadLn(nz);
    Write('Grau do denominador: '); ReadLn(mp);
    WriteLn('Freqˆncias dos zeros finitos:');
    FOR i:=1 TO nz shr 1 DO BEGIN
      Write(tl,'wz([',i,']): '); ReadLn(wz[i])
    END;
    WriteLn('Freqˆncias dos p¢los finitos:');
    FOR i:=1 TO mp shr 1 DO BEGIN
      Write(tl,'wp([',i,']): '); ReadLn(wp[i])
    END;
    Write(tl,'[Cte]. multiplicativa: ');
    ReadLn(cte)
  END;
  erro:=FALSE;
  IF not ((mp=nz+1) or (mp=nz-1)) THEN BEGIN
    WriteLn(tl,'[*] Os graus devem diferir de 1');
    erro:=TRUE;
    Exit
  END;
  polo_na_origem:=Odd(mp);
  polo_no_infinito:=(nz>mp);
  Write(#10'H  um ');
  IF polo_na_origem THEN Write('p¢lo')
  ELSE Write('zero');
  WriteLn(' na origem.');
  Write('H  um ');
  IF polo_no_infinito THEN Write('p¢lo')
  ELSE Write('zero');
  WriteLn(' no infinito.');
  mp:=mp shr 1; nz:=nz shr 1;
  WriteLn('H  ',nz,' pares de zeros em jw');
  WriteLn('H  ',mp,' pares de p¢los em jw');
  Ordenar(nz,wz);
  Ordenar(mp,wp);
  WriteLn('Ver no mapa se os p¢los e zeros se alternam antes de prosseguir');
END; {LerImitancia}

FUNCTION Prod(n:INTEGER; x:valores; w:REAL; pula:INTEGER):REAL;
VAR
  i:INTEGER;
  p:REAL;
BEGIN
  p:=1; w:=Sqr(w);
  FOR i:=1 TO n DO
     IF i<>pula THEN p:=p*(Sqr(x[i])-w);
  Prod:=p
END; {Prod}

PROCEDURE FracoesParciais;
BEGIN
  IF polo_na_origem THEN BEGIN
    ko:=cte;
    FOR i:=1 TO nz DO ko:=ko*Sqr(wz[i]);
    FOR i:=1 TO mp DO ko:=ko/Sqr(wp[i]);
  END
  ELSE ko:=0;
  IF polo_no_infinito THEN koo:=cte ELSE koo:=0;
  FOR i:=1 TO mp DO BEGIN
    k[i]:=cte*Prod(nz,wz,wp[i],0)/Prod(mp,wp,wp[i],i);
    IF polo_na_origem THEN k[i]:=-k[i]/Sqr(wp[i])
  END;
  residuos_validos:=TRUE
END; {FracoesParciais}

PROCEDURE AvaliarExpansao(w:REAL);
VAR
  w2,d:REAL;
BEGIN
  w2:=Sqr(w);
  x:=-ko/w+koo*w;
  x1:=ko/w2+koo;
  FOR j:=1 TO mp DO BEGIN
    d:=Sqr(wp[j])-w2;
    x:=x+k[j]*w/d;
    x1:=x1+k[j]*(Sqr(wp[j])+w2)/Sqr(d)
  END;
END; {AvaliarExpansao}

PROCEDURE Confirmar;
BEGIN
  Write(tl,'[*] Elemento<=0. Continuar? ([s/n]) ');
  ok:=Resposta(SN)='S'
END; {Confirmar}

PROCEDURE TotalOrigem;
BEGIN
  ok:=polo_na_origem;
  IF ok THEN BEGIN
    IF e_impedancia THEN WriteLn('Em s‚rie:')
    ELSE WriteLn('Em //:');
    Guardar(1,1/ko);
    ko:=0;
    polo_na_origem:=FALSE;
    nz:=nz-1;
    FOR i:=1 TO nz DO wz[i]:=wz[i+1]
  END
  ELSE
    WriteLn(tl,'[*] N„o h  p¢lo na origem');
END; {TotalOrigem}

PROCEDURE ParcialOrigem;
BEGIN
  ok:=polo_na_origem;
  IF ok THEN BEGIN
    AvaliarExpansao(w0);
    k1:=-w0*x;
    ok:=(ko>k1) and (k1>0);
    IF not ok THEN Confirmar;
    IF ok THEN BEGIN
      IF e_impedancia THEN WriteLn('Em s‚rie:')
      ELSE WriteLn('Em //:');
      Guardar(1,1/k1);
      ko:=ko-k1
    END
  END
  ELSE
    WriteLn(tl,'[*] N„o h  p¢lo na origem');
END; {ParcialOrigem}

PROCEDURE TotalInfinito;
BEGIN
  ok:=polo_no_infinito;
  IF ok THEN BEGIN
    IF e_impedancia THEN WriteLn('Em s‚rie:')
    ELSE WriteLn('Em //:');
    Guardar(2,koo);
    koo:=0;
    polo_no_infinito:=FALSE;
    nz:=nz-1;
  END
  ELSE
    WriteLn(tl,'[*] N„o h  p¢lo no infinito');
END; {TotalInfinito}

PROCEDURE ParcialInfinito;
BEGIN
  ok:=polo_no_infinito;
  IF ok THEN BEGIN
    AvaliarExpansao(w0);
    k1:=x/w0;
    ok:=(koo>k1) and (k1>0);
    IF not ok THEN Confirmar;
    IF ok THEN BEGIN
      IF e_impedancia THEN WriteLn('Em s‚rie:')
      ELSE WriteLn('Em //:');
      Guardar(2,k1);
      koo:=koo-k1
    END
  END
  ELSE
    WriteLn(tl,'[*] N„o h  p¢lo no infinito');
END; {ParcialInfinito}

PROCEDURE TotalFinito;
BEGIN
  ok:=(polo>0) and (polo<=mp);
  IF ok THEN BEGIN
    IF e_impedancia THEN WriteLn('Tanque // em s‚rie:')
    ELSE WriteLn('Tanque s‚rie em //');
    Guardar(3,1/k[polo]);
    Guardar(4,k[polo]/Sqr(wp[polo]));
    FOR i:=polo TO mp-1 DO BEGIN
      wp[i]:=wp[i+1];
      k[i]:=k[i+1]
    END;
    FOR i:=polo TO nz-1 DO wz[i]:=wz[i+1];
    mp:=mp-1;
    nz:=nz-1
  END
  ELSE
    WriteLn(tl,'[*] N„o existe o p¢lo no. ',polo);
END; {TotalFinito}

PROCEDURE ParcialFinito;
BEGIN
  ok:=(polo>0) and (polo<=mp);
  IF ok THEN BEGIN
    AvaliarExpansao(w0);
    k1:=x*(Sqr(wp[polo])-Sqr(w0))/w0;
    ok:=(k[polo]>k1) and (k1>0);
    IF not ok THEN Confirmar;
    IF ok THEN BEGIN
      IF e_impedancia THEN WriteLn('Tanque // em s‚rie:')
      ELSE WriteLn('Tanque s‚rie em //');
      Guardar(3,1/k1);
      Guardar(4,k1/Sqr(wp[polo]));
      k[polo]:=k[polo]-k1
    END
  END
  ELSE
    WriteLn(tl,'[*] N„o existe o p¢lo no. ',polo);
END; {ParcialFinito}

PROCEDURE NovosZeros;
VAR
  dz,wmin,wmax,w:REAL;
BEGIN
  FOR i:=1 TO nz DO BEGIN
    IF polo_na_origem THEN BEGIN
      IF i=1 THEN wmin:=0
      ELSE wmin:=wp[i-1];
      IF (i=nz) and polo_no_infinito THEN wmax:=1e30
      ELSE wmax:=wp[i]
    END
    ELSE BEGIN
      wmin:=wp[i];
      IF (i=nz) and polo_no_infinito THEN wmax:=1e30
      ELSE wmax:=wp[i+1]
    END;
    w:=wz[i];
    REPEAT
      AvaliarExpansao(w);
      dz:=x/x1;
      REPEAT
        x:=w-dz;
        ok:=(x>wmin) and (x<wmax);
        IF not ok THEN dz:=dz/2
      UNTIL ok;
      w:=x;
      Write('wz(',i,'): ',w:11:8,#13);
    UNTIL (Abs(dz)<tol) or KeyPressed;
    wz[i]:=w;
    WriteLn;
  END;
  IF polo_no_infinito THEN cte:=koo
  ELSE BEGIN
    cte:=ko;
    FOR i:=1 TO mp DO cte:=cte+k[i]
  END;
END; {NovosZeros}

PROCEDURE Inverter;
VAR
  w:REAL;
BEGIN
  e_impedancia:=not e_impedancia;
  polo_na_origem:=not polo_na_origem;
  polo_no_infinito:=not polo_no_infinito;
  i:=nz; nz:=mp; mp:=i;
  IF nz>mp THEN j:=nz ELSE j:=mp;
  FOR i:=1 TO j DO BEGIN
    w:=wp[i]; wp[i]:=wz[i]; wz[i]:=w
  END;
  cte:=1/cte;
END; {Inverter}

PROCEDURE Salvar;
BEGIN
  Write('Arquivo de sa¡da (.val): ');
  ReadLn(nome);
  IF Length(nome)=0 THEN Exit;
  i:=Pos('.',nome);
  IF i=0 THEN nome:=nome+'.val';
  Assign(arquivo,nome);
  ReWrite(arquivo);
  FOR i:=1 TO nlista DO
    WITH lista[i] DO
      WriteLn(arquivo,tpo,nmr,' ',vlr);
  Close(arquivo)
END; {Salvar}

PROCEDURE ListarImitancia;
BEGIN
  Write('Polos e zeros de ');
  IF e_impedancia THEN WriteLn(tl,'[Z(s):]')
  ELSE WriteLn(tl,'[Y(s)]:');
  IF polo_na_origem THEN Write('- P¢lo') ELSE Write('- Zero');
  WriteLn(' na origem');
  IF polo_no_infinito THEN Write('- P¢lo') ELSE Write('- Zero');
  WriteLn(' no infinito');
  WriteLn('- ',mp,' pares de polos finitos:');
  FOR i:=1 TO mp DO WriteLn(tl,'  wp([',i,']):',wp[i]:11:8);
  WriteLn('- ',nz,' pares de zeros finitos:');
  FOR i:=1 TO nz DO
     WriteLn(tl,'  wz([',i,']):',wz[i]:11:8);
  WriteLn(tl,'- [Cte]:',cte:11:8)
END; {ListarImitancia}

PROCEDURE ListarFracoes;
BEGIN
  Write(#10'Expans„o em fra‡”es parciais de ');
  IF e_impedancia THEN WriteLn(tl,'[Z(s)]')
  ELSE WriteLn(tl,'[Y(s)]');
  WriteLn(tl,ko:11:8,'/[s]');
  WriteLn(tl,koo:11:8,'[s]');
  FOR i:=1 TO mp DO
    WriteLn(tl,k[i]:11:8,'[s]/([s^2]+',Sqr(wp[i]):11:8,')');
END; {ListarFracoes}

PROCEDURE Inicializar;
BEGIN
  secoes:=0; nlista:=0; nmapa:=0;
  interrompido:=FALSE;
  imitancia_lida:=FALSE;
  residuos_validos:=FALSE;
END; {Inicializar}

PROCEDURE Menu;
BEGIN
  WriteLn(tl,'- [Esc]: Fim.');
  WriteLn(tl,'- [Ret]: Menu.');
  WriteLn(tl,'- [R]: Ler imitƒncia.');
  WriteLn(tl,'- [L]: Listar imitƒncia.');
  WriteLn(tl,'- [X]: Listar expans„o em f. parciais.');
  WriteLn(tl,'- [P]: Extrair totalmente polo.');
  WriteLn(tl,'- [Z]: Criar zero de transmiss„o.');
  WriteLn(tl,'- [I]: Inverter imitƒncia.');
  WriteLn(tl,'- [M]: Desenhar mapa.');
END; {Menu}

BEGIN
  InitGraph(driver,modo,GetEnv('TPBGI'));
  REPEAT
    RestoreCrtMode;
    ClrScr;
    WriteLn(tl,'[Expans„o "ladder" LC]');
    WriteLn(tl,'[--------------------]');
    WriteLn('Ant“nio Carlos M. de Queiroz - COPPE/UFRJ');
    WriteLn('Vers„o ',versao,' - Precis„o ',precisao);
    WriteLn;
    Inicializar;
    Menu;
    WriteLn(tl,'[#]');
    REPEAT
      r:=ReadKey;
      CASE UpCase(r) OF
        #27:interrompido:=TRUE;
        #13:Menu;
        'R':BEGIN
              Inicializar;
              LerImitancia;
              IF not erro THEN BEGIN
                imitancia_lida:=TRUE;
                AumentarMapa(FALSE,e_impedancia)
              END
            END;
        'L':IF imitancia_lida THEN ListarImitancia;
        'X':IF imitancia_lida THEN BEGIN
              IF not residuos_validos THEN FracoesParciais;
              ListarFracoes
            END;
        'P':IF imitancia_lida THEN BEGIN
              IF not residuos_validos THEN FracoesParciais;
              Write(tl,'P¢lo a extrair: [I]nfinito, [O]rigem, [F]inito: ');
              CASE Resposta(['I','O','F']) OF
                'I':TotalInfinito;
                'O':ToTalOrigem;
                'F':BEGIN
                      Write('No. do polo a extrair: ');
                      ReadLn(polo);
                      TotalFinito;
                    END
                END;
              IF ok THEN BEGIN
                NovosZeros;
                AumentarMapa(TRUE,not e_impedancia)
              END
            END;
        'Z':IF imitancia_lida THEN
              IF nz=0 THEN WriteLn(tl,'[*] N„o h  zeros para deslocar')
              ELSE BEGIN
                IF not residuos_validos THEN FracoesParciais;
                Write('Freqˆncia dos zeros a criar: ');
                ReadLn(w0);
                Write(tl,'P¢lo a extrair: [I]nfinito, [O]rigem, [F]inito: ');
                CASE Resposta(['I','O','F']) OF
                  'I':ParcialInfinito;
                  'O':ParcialOrigem;
                  'F':BEGIN
                        Write('No. do p¢lo a extrair: ');
                        ReadLn(polo);
                        ParcialFinito;
                      END
                  END;
                IF ok THEN BEGIN
                  NovosZeros;
                  Inverter;
                  AumentarMapa(TRUE,e_impedancia);
                  FracoesParciais;
                  polo:=0;
                  REPEAT polo:=polo+1 UNTIL (polo>mp) or (Abs(wp[polo]-w0)<tol);
                  IF polo>mp THEN BEGIN
                    Write(tl,'[*] ???!!!');
                    Halt
                  END;
                  TotalFinito;
                  NovosZeros;
                  IF cte<>0 THEN BEGIN
                    Inverter;
                    AumentarMapa(TRUE,e_impedancia)
                  END;
                  residuos_validos:=FALSE
                END
              END;
        'I':IF imitancia_lida THEN BEGIN
              Inverter;
              IF e_impedancia THEN WriteLn(tl,'[Impedƒncia]')
              ELSE WriteLn(tl,'[Admitƒncia]');
              residuos_validos:=FALSE;
              AumentarMapa(FALSE,e_impedancia)
            END;
        'M':IF nmapa>0 THEN Mapear
        END;
      WriteLn(tl,'[#]');
    UNTIL (imitancia_lida and (mp=0) and not polo_no_infinito and not polo_na_origem) or interrompido;
    IF not interrompido THEN BEGIN
      WriteLn(tl,'[S¡ntese completa]');
      Write(tl,#10'Ver mapa? ([s/n]) ');
      IF Resposta(SN)='S' THEN Mapear;
      Write(tl,#10'Salvar rede? ([s/n]) ');
      IF Resposta(SN)='S' THEN Salvar;
    END;
    Write(tl,#10'Recome‡ar? ([s/n]) ');
  UNTIL Resposta(SN)='N'
END.
