program Raizes;
uses lguerr,crt,dos;
var
   i:integer;
   Degree    : integer;
   GrauSalvo : integer;
   Poly      : TNCompVector;
   InitGuess : TNcomplex;
   Tol       : real;
   MaxIter   : integer;
   NumRoots  : integer;
   Roots     : TNCompVector;
   yRoots    : TNCompVector;
   Iter      : TNIntVector;
   Error     : byte;

begin
     clrscr;
     writeln('            PROGRAMA PARA CALCULO DAS RAIZES DE UM POLINOMIO');
     writeln;
     write('Entre com o grau do polinomio: ');
     readln(Degree);
     GrauSalvo := Degree;
     writeln;
     writeln
     ('Entrada dos coeficientes do polinomio(parte real parte imaginaria):');
     for i:= 0 to Degree do
         begin
              write('Coeficiente[',i,']= ');
              readln(Poly[i].Re,Poly[i].Im);
         end;
     writeln;
     write('Chute Inicial(parte real  parte imaginaria): ');
     readln(InitGuess.Re,InitGuess.Im);
     write('Tolerancia: ');
     readln(Tol);
     writeln;
     writeln('Numero maximo de iteracoes: ');
     readln(MaxIter);
     writeln;
     Laguerre(Degree,Poly,InitGuess,Tol,MaxIter,NumRoots,Roots,yRoots,
              Iter,Error);
     if Error > 0 then
        begin
             writeln;
             writeln;
             writeln('Erro no calculo das Raizes do Polinomio !');
             writeln;
             writeln('Codigo do erro: ',Error);
             Halt;
        end;
     clrscr;
     writeln('     RESULTADO DO CALCULO DAS RAIZES DO POLINOMIO');
     writeln;
     writeln('Grau do polinomio: ',Degree);
     writeln;
     writeln('Coeficientes do Polinomio:');
     for i := 0 to GrauSalvo do
         begin
           writeln('Coeficientes[',i,']= ',Poly[i].Re,' j*',Poly[i].Im);
         end;
     writeln;
     writeln('Numero de Raizes Calculadas: ',NumRoots);
     writeln;
     writeln
       ('____________ Raizes ____________               ___ Valor do Polinomio ___');
     for i := 1 to NumRoots do
      begin
       writeln
       (Roots[i].Re,' j*',Roots[i].Im,'   ',yRoots[i].Re,' j*',yRoots[i].Im);
      end;
     writeln;
     for i:= 1 to NumRoots do
      begin
       writeln('Raiz[',i,'] calculada em ',Iter[i],' iteracoes...');
      end;
     writeln;
     if (GrauSalvo <> NumRoots) then
     writeln('Nao foram calculadas: ',GrauSalvo - Degree,' raizes...');
      readln;
end.
