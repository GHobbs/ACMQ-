Program Eliptico;

Uses Crt;

Const Pi   = 3.14159235;
      cmax = 100;

Var   K, Ap, Aa, Kl, Q0, Q, D : real;
      Delta, T0, W, H0, Mi    : real;
      n, r, i, j              : integer;
      car                     : char;
      sim, poli               : boolean;
      arq                     : text;
      nome                    : string [16];
      M                       : array [0..4, 0..cmax] of real;
      A0, B0, B1, T           : array [0..cmax] of real;


{*****************************************************************************}

Function Eleva ( valor, expoente : real ) : real;
var aux : real;
begin
aux:= expoente * ln (valor);
if aux > 88 then writeln ('overflow em exponenciacao')
            else if aux < -88 then eleva:= 0
                              else eleva:= exp (aux)
end;

{*****************************************************************************}

Function Funcao (operando : real; op : integer ) : real;

Var numerador, denominador, parcnum, parcden : real;
    erro, anterior                           : real;
    m                                        : integer;

Function Trig ( x : real; op : integer ) : real;
begin
case op of
     0 : Trig:= sin (x);
     1 : Trig:= cos (x);
     2 : Trig:= ( exp (x) - exp (-x)) / 2;
     3 : Trig:= ( exp (x) + exp (-x)) / 2;
     end
end;

begin
parcnum:= Trig ( operando, op );
numerador:= parcnum;
denominador:= 0;
erro:= abs ( parcnum ) * 10E-10;
m:= 1;
Repeat
      anterior:= parcnum;
      parcnum:= Eleva (Q, m*(m+1)) * Trig ((2*m+1)*operando, op);
      parcden:= Eleva (Q, m*m) * Trig (2*m*operando, op+1);
      if odd (m) then
                     begin
                     numerador:= numerador - parcnum;
                     denominador:= denominador - parcden
                     end
                 else
                     begin
                     numerador:= numerador + parcnum;
                     denominador:= denominador + parcden
                     end;
      m:= m + 1
until (abs (abs (anterior) - abs (parcnum)) < erro) or (m > 15);
if m>15 then writeln ('Overflow');
funcao:= 2 * sqrt (sqrt (Q)) * numerador / (1 + 2 * denominador);
end;

{*****************************************************************************}

Procedure Coeficientes;
Var Omega, V             : real;

begin
H0:= 1;
for i:= 1 to r do
    begin
    writeln;
    if (sim) or not (poli) then writeln ('Calculo dos coeficientes A0',i,', B0',i,', B1',i,':');
    if odd (n) then Mi:= i
               else Mi:= i - 0.5;
    Omega:= Funcao (Pi * Mi / n, 0);
    if sim then writeln ('Omega= ',Omega);
    V:= sqrt ((1 - K * sqr (Omega)) * (1 - sqr (Omega) / K));
    if sim then writeln ('V= ',V);
    A0[i]:= 1 / sqr (Omega);
    if (sim) or not (poli) then writeln ('A0',i,'= ',A0[i]);
    B0[i]:= (sqr (T0*V) + sqr (Omega*W)) / sqr (1 + sqr (T0) * sqr (Omega));
    if (sim) or not (poli) then writeln ('B0',i,'= ',B0[i]);
    B1[i]:= 2 * T0 * V / (1 + sqr (T0) * sqr (Omega));
    if (sim) or not (poli) then writeln ('B1',i,'= ',B1[i]);
    H0:= H0 * B0[i] / A0[i]
    end;
if odd(n) then
              begin
              H0:= H0 * T0;
              if (sim) or not (poli) then writeln ('H0= ',H0);
              if (sim) or not (poli) then writeln ('D(s)=  s + ',T0);
              end
          else
              begin
              H0:= Eleva (10, -0.05*Ap)*H0;
              if (sim) or not (poli) then writeln ('H0= ',H0);
              if (sim) or not (poli) then writeln ('D(s)=  1');
              end
end;

{*****************************************************************************}

procedure CMS;
var l, j : integer;
begin
for l:= 0 to cmax do
        T[l]:= 0;
for l:= 0 to 4 do
    for j:= 0 to cmax do
        M[l, j]:= 0
end;

{*********************************************}

procedure RCL (i: integer);
var l : integer;
begin
i:= abs(i);
for l:= 0 to cmax do M[0, l]:= M[i, l]
end;

{*********************************************}

procedure STO (i: integer);
var l : integer;
begin
i:= abs(i);
for l:= 0 to cmax do  M[i, l]:=M[0, l]
end;

{*********************************************}

function GRAU (i: integer): integer;
var l : integer;
begin
i:= abs(i);
l:= cmax + 1;
repeat l:= l - 1 until (l=0) or (M[i, l]<>0);
grau:= l
end;

{*********************************************}

procedure CTE (i: integer; k : real);
var l : integer;
begin
i:= abs(i);
for l:= 0 to cmax do
    M[i, l]:= M[i, l] * k
end;

{*********************************************}

procedure PROD (i : integer);
var grauacc, graui, j, l : integer;
    a                    : real;
begin
i:= abs(i);
grauacc:= grau(0);
graui:= grau(i);
if graui + grauacc > cmax
   then
       begin
       writeln;
       writeln ('Produto incorreto: polinomio (',i,') de grau ',graui);
       writeln ('                 : polinomio (0) de grau ',grauacc)
       end
   else
       begin
       for l:= 0 to cmax do
           T[l]:= 0;
       for j:= 0 to graui do
           begin
           a:= M[i, j];
           if a<>0 then
                       for l:= 0 to grauacc do
                           T[l+j]:= T[l+j] + a * M[0, l]
           end
       end;
for l:= 0 to cmax do
    M[i, l]:= T[l]
end;

{*********************************************}

procedure ESCR (i : integer);
var l, n : integer;
begin
i:= abs(i);
n:= grau(i);
for l:=0 to n do
    begin
    write ('A(',l,')= ');
    writeln (M [i, l])
    end;
writeln;
write('Deseja gravar o polinomio? <n> ou <nome do arquivo>  [n] ');
readln (nome);
if not ((length (nome)=0) or (nome='n') or (nome='N'))
    then begin
         assign (arq, nome);
         rewrite (arq);
         writeln (arq,n);
         for l:=0 to n do
             writeln (arq, M [i, l]);
         close (arq)
         end
end;

{*****************************************************************************}

begin
repeat
      clrscr;
      highvideo;
      writeln ('Calculo de H(s) para um filtro passa baixa eliptico, normalizado');
      writeln ('COPPE/UFRJ - 1985 - Joao Amaro Baptista Pereira');
      lowvideo;
      writeln;
      repeat
            write ('Seletividade K (0<K<1): ');
            read (K);
            if (K<=0) or (K>=1) then writeln (' Valor incorreto.')
      until (K>0) and (K<1);
      writeln;
      write ('Maximo ripple na faixa de passagem : ');
      readln (Ap);
      write ('Minima atenuacao na faixa de rejeicao : ');
      readln (Aa);
      writeln;
      write ('Deseja impressao de valores intermediarios ? <s> ou <n>  [n]  ');
      readln (car);
      if (car='S') or (car='s') then sim:= true
                                else sim := false;
      writeln;
      writeln ('Deseja gerar H(s) : polinomial             (gravavel)     <p>');
      write   ('                  : em blocos de 2a. ordem (nao gravavel) <b> [p]  ');
      readln (car);
      writeln;
      if (car='b') or (car='B') then poli:= false
                                else poli:= true;
      Kl:= sqrt (1 - sqr (K));
      if sim then writeln ('Kl = ',Kl);
      Q0:= 0.5 * ((1 - sqrt (Kl)) / (1 + sqrt (Kl)));
      if sim then writeln ('Q0 = ',Q0);
      Q := Q0 + 2*Eleva (Q0, 5) + 15*Eleva(Q0, 9) + 150*Eleva(Q0, 13);
      if sim then writeln ('Q =  ',q);
      D := (Eleva (10, 0.1*Aa) - 1) / (Eleva (10, 0.1*Ap) - 1);
      if sim then writeln ('D =  ',D);
      n := round ( ln (16*D) / ln (1/Q));
      writeln;
      writeln('Ordem do filtro (n) : ',n);
      writeln;
      if odd(n) then r:= (n - 1) div 2
                else r:= n div 2;
      if sim then writeln ('r = ',r);
      Delta := 1 / (2*n) * ln ((Eleva (10, 0.05*Ap)+1) / (Eleva (10, 0.05*Ap)-1));
      if sim then writeln ('Delta = ',Delta);
      T0:= abs (funcao (Delta,2));
      if sim then writeln ('T0 = ',T0);
      W := sqrt ((1 + K*sqr (T0)) * (1 + sqr (T0)/K));
      if sim then writeln ('W = ',W);
      Coeficientes;
      if poli then
                  begin
                  cms;
                  M [1, 2]:= 1;
                  M [1, 1]:= 0;
                  M [3, 2]:= 1;
                  M [2, 0]:= 1;
                  M [4, 0]:= 1;
                  for i:= 1 to r do
                      begin
                      M [1, 0]:= A0 [i];
                      rcl (1);
                      prod (2);
                      M [3, 0]:= B0 [i];
                      M [3, 1]:= B1 [i];
                      rcl (3);
                      prod (4);
                      end;
                  cte (2, H0);
                  if odd (n) then
                                 begin
                                 j:= 2 * r + 1;
                                 M [1, 0]:= T0;
                                 M [1, 1]:= 1;
                                 M [1, 2]:= 0;
                                 rcl (1);
                                 prod (4);
                                 end
                             else
                                 j:= 2 * r;
                  writeln;
                  highvideo;
                  writeln ('Numerador de H(s)');
                  lowvideo;
                  writeln;
                  escr (2);
                  writeln;
                  highvideo;
                  writeln ('Denominador de H(s)');
                  lowvideo;
                  writeln;
                  escr (4)
                  end;
      writeln;
      highvideo;
      write ('Outro calculo ? <s> ou <n>  [n] ');
      lowvideo;
      readln (car);
      if (car<>'s') and (car<>'S') then sim:= true
                                   else sim:= false;
until sim
end.

