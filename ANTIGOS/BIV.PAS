{******************************************************************************
 * Calculo de raizes de um polinomio pelo metodo de Birge-Vieta.              *
 * Antonio Carlos Moreirao de Queiroz COPPE/UFRJ 1985                         *
 * Versao 1.2  6/26/1985 - Insercao de espaco entre parte real e              *
 * imag. no arq. de raizes, apagar tela no inicio, nao interromper quando     *
 * exceder 300 it.                                                            *
 * Versao 1.3  2/7/1985 - Acrescimo da rotina de remontagem, modificacao no   *
 * formato de impressao das raizes.                                           *
 * Versao 1.4 15/8/1985 - Versao para Turbo Pascal.                           *
 * Versao 1.5 11/12/85 - Incluida verificacao de existencia de arquivo.       *
 * Versao 1.6 17/04/86 - Verificacao de max. grau, grau maior e aprox. inic.  *
 * Versao 1.7 10/06/89 - Versao para Turbo 5.0                                *
 ******************************************************************************}
{$N+,E+}

USES Crt;

CONST MG=200;
TYPE polinomio=ARRAY[0..MG] OF EXTENDED;
     LETRAS=STRING[100];
VAR grau,i : INTEGER;
    tol,x10,x20 : EXTENDED;
    fim,OK : BOOLEAN;
    A,B : polinomio;
    nome : STRING;
    r : CHAR;
    arquivo : TEXT;

PROCEDURE REMONTA(VAR A1,A2 : polinomio; n : INTEGER);
   VAR B1,B2 : polinomio;
       i,j : INTEGER;
       r : EXTENDED;
   BEGIN
   FOR i:=0 TO n DO
      BEGIN B1[i]:=0; B2[i]:=0 END;
   B1[0]:=1;
   FOR i:=1 TO n DO
      BEGIN
      FOR j:=i DOWNTO 1 DO
         BEGIN
         r:=B1[j-1]-A1[i]*B1[j]+A2[i]*B2[j];
         B2[j]:=B2[j-1]-A1[i]*B2[j]-A2[i]*B1[j];
         B1[j]:=r
         END;
      r:=-A1[i]*B1[0]+A2[i]*B2[0];
      B2[0]:=-A1[i]*B2[0]-A2[i]*B1[0];
      B1[0]:=r
      END;
   WriteLn; WriteLn('Polinomio montado a partir das raizes:'); WriteLn;
   FOR i:=0 TO n DO WriteLn('a(',i:2,')=',B1[i],B2[i],'j');
   WriteLn;
   END; {REMONTA}

PROCEDURE BIV(VAR A1,A2 : polinomio; n : INTEGER);
   VAR B1,B2 : polinomio;
       p1,p2,d,x1,x2,p,d1,d2,e1,e2 : EXTENDED;
       feito : BOOLEAN;
       nn,i : INTEGER;
   BEGIN
   x1:=x10; x2:=x20; feito:=FALSE; nn:=0;
   IF n<1 THEN
      BEGIN feito:=TRUE; WriteLn('Nao ha raizes') END;
   WHILE not feito DO
      BEGIN {ITERACAO}
      IF n>1 THEN
         BEGIN  {RAIZ QUALQUER}
         B1[n]:=A1[n]; d1:=B1[n]; p1:=d1;
         B2[n]:=A2[n]; d2:=B2[n]; p2:=d2;
         FOR i:=n-1 DOWNTO 0 DO
            BEGIN
            B1[i]:=p1*x1-p2*x2+A1[i]; p:=B1[i];
            B2[i]:=p2*x1+p1*x2+A2[i]; p2:=B2[i];
            p1:=p;
            IF i>0 THEN
               BEGIN
               d:=d1*x1-d2*x2+p1;
               d2:=d2*x1+d1*x2+p2;
               d1:=d;
               END
            END;
         d:=d1*d1+d2*d2;
         e1:=(p1*d1+p2*d2)/d;
         e2:=(p2*d1-p1*d2)/d;
         x1:=x1-e1;
         x2:=x2-e2;
         IF e1*e1+e2*e2 < tol THEN
            BEGIN {RAIZ ENCONTRADA}
            WriteLn('r(',n:2,')=',x1,x2,'j   (',nn:3,' iteracoes)');
            A1[n]:=x1; A2[n]:=x2;
            n:=n-1; nn:=0;
            FOR i:=0 TO n DO
               BEGIN A1[i]:=B1[i+1]; A2[i]:=B2[i+1] END;
            IF (ABS(x1)<1E-5) AND (ABS(x2)<1E-5) THEN BEGIN x1:=x10; x2:=x10 END
            ELSE IF ABS(x2)>1E-3 THEN x2:=-x2 ELSE x2:=0.1;
            END
         ELSE
            BEGIN
            nn:=nn+1;
            IF nn>299 THEN
               BEGIN {NAO CONVERGIU}
               WriteLn('Raiz nao encontrada em 300 iteracoes');
               WriteLn('Ultimo valor: ',x1,x2,'j');
               WriteLn('Ultimo P(S):  ',p1,p2,'j');
               WriteLn('Ultimo DP/DS: ',d1,d2,'j');
               WriteLn('Ultimo erro:  ',e1,e2,'j');
               WriteLn('Entre novos valores para:');
               Write('Parte real da aproximacao: ');
               ReadLn(x1);
               Write('Parte imaginaria da aproximacao: ');
               ReadLn(x2);
               Write('Tolerancia: ');
               ReadLn(tol); tol:=Sqr(tol);
               nn:=0;
               END
            END
         END
      ELSE BEGIN {ULTIMA RAIZ}
           d:=-(Sqr(A1[1])+Sqr(A2[1]));
           x1:=(A1[0]*A1[1]+A2[0]*A2[1])/d;
           x2:=(A2[0]*A1[1]-A1[0]*A2[1])/d;
           feito:=TRUE; nn:=0;
           WriteLn('r(',n:2,')=',x1,x2,'j   (',nn:3,' iteracoes)');
           A1[n]:=x1; A2[n]:=x2
           END
   END;
WriteLn;
END; {BIV}

BEGIN
CLRSCR;
WriteLn('Calculo de raizes de polinomios pelo metodo de Birge-Vieta');
WriteLn('----------------------------------------------------------');
WriteLn('[Antonio Carlos Moreirao de Queiroz - COPPE/UFRJ - 1985] Versao 1.7');
WriteLn;
fim:=FALSE;
REPEAT
   BEGIN
   Write('O polinomio esta em arquivo? [nome do arquivo ou "n"] ');
   ReadLn(nome);
   IF ((nome[1]='N') OR (nome[1]='n')) THEN
      BEGIN
      Write('Grau do polinomio? ');
      ReadLn(grau);
      IF grau>MG THEN BEGIN WriteLn('Erro: grau maior que ',MG); Halt END;
      FOR i:=grau DOWNTO 0 DO
         BEGIN
         Write('a(',i:2,') = ');
         ReadLn(A[i])
         END;
      Write('Salvar o polinomio? [nome do arquivo ou "n"] ');
      ReadLn(nome);
      IF not((nome[1]='N') OR (nome[1]='n')) THEN
         BEGIN
         ASSIGN(arquivo,nome);
         ReWrite(arquivo);
         WriteLn(arquivo,grau:2);
         FOR i:=0 TO grau DO WriteLn(arquivo,A[i]);
         Close(arquivo)
         END
      END
   ELSE
      BEGIN
      REPEAT
         ASSIGN(arquivo,nome);
         {$I-} Reset(arquivo); {$I+}
         OK:=(IOResult=0);
         IF not OK THEN BEGIN Write('Arquivo inexistente; tente outro: '); ReadLn(nome) END
      UNTIL OK;
      Read(arquivo,grau);
      IF grau>MG THEN WriteLn('Erro: grau maior que ',MG);
      FOR i:=0 TO grau DO
         BEGIN
         Read(arquivo,A[i]);
         WriteLn('a(',i:2,') = ',A[i])
         END;
      Close(arquivo);
      END;
   Write('Tolerancia Aprox. inicial (Re Im) (Ex: 1E-12 1 1)? ');
   ReadLn(tol,x10,x20);
   tol:=Sqr(tol);
   WriteLn; WriteLn('Raizes:'); WriteLn;
   FOR i:=0 TO grau DO B[i]:=0;
   BIV(A,B,grau);
   Write('Salvar as raizes? [Nome do arquivo ou "n"] ');
   ReadLn(nome);
   IF not((nome[1]='N') OR (nome[1]='n')) THEN
      BEGIN
      ASSIGN(arquivo,nome);
      ReWrite(arquivo);
      WriteLn(arquivo,grau:2);
      FOR i:=1 TO grau DO WriteLn(arquivo,A[i],' ',B[i]);
      Close(arquivo)
      END;
   Write('Remontar o polinomio original para verificacao? [s/n] ');
   ReadLn(r);
   IF (r='s') OR (r='S') THEN REMONTA(A,B,grau);
   Write('Outro Polinomio? [s/n] ');
   ReadLn(r);
   IF (r='N') OR (r='n') THEN fim:=TRUE
   END
UNTIL fim
END.
