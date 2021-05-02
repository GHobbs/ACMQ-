{============================================================================}
UNIT LGUERR;     { Modulo de calculo das raizes de um polinomio }
{============================================================================}
INTERFACE

const
     TNArraySize = 100;

type
      TNcomplex    = record
                       Re, Im : real;
                     end;
      TNIntVector  = array[0..TNArraySize] of integer;
      TNCompVector = array[0..TNArraySize] of TNcomplex;


procedure Laguerre(var Degree    : integer;
                   var Poly      : TNCompVector;
                       InitGuess : TNcomplex;
                       Tol       : real;
                       MaxIter   : integer;
                   var NumRoots  : integer;
                   var Roots     : TNCompVector;
                   var yRoots    : TNCompVector;
                   var Iter      : TNIntVector;
                   var Error     : byte);

IMPLEMENTATION

procedure Laguerre(var Degree    : integer;
                   var Poly      : TNCompVector;
                       InitGuess : TNcomplex;
                       Tol       : real;
                       MaxIter   : integer;
                   var NumRoots  : integer;
                   var Roots     : TNCompVector;
                   var yRoots    : TNCompVector;
                   var Iter      : TNIntVector;
                   var Error     : byte);

{----------------------------------------------------------------------------}
{-                                                                          -}
{-     Turbo Pascal Numerical Methods Toolbox                               -}
{-     (C) Copyright 1986 Borland International.                            -}
{-                                                                          -}
{-            Input: Degree, Poly, InitGuess, Tol, MaxIter                  -}
{-           Output: Degree, Poly, NumRoots, Roots, yRoots, Iter, Error     -}
{-                                                                          -}
{-          Purpose: This unit provides a procedure for finding all the     -}
{-                   roots (real and complex) to a polynomial.              -}
{-                   Laguerre's method with deflation is used.              -}
{-                   The user must input the coefficients of the quadratic  -}
{-                   and the tolerance in the answers generated.            -}
{-                                                                          -}
{-  Pre-defined Types: TNcomplex    = record                                -}
{-                                      Re, Im : real;                      -}
{-                                    end;                                  -}
{-                                                                          -}
{-                     TNIntVector  = array[0..TNArraySize] of integer;     -}
{-                     TNCompVector = array[0..TNArraySize] of TNcomplex;   -}
{-                                                                          -}
{- Global Variables: Degree    : integer;      degree of deflated           -}
{-                                             polynomial                   -}
{-                   Poly      : TNCompVector; coefficients of deflated     -}
{-                                             polynomial where Poly[n] is  -}
{-                                             the coefficient of X^n       -}
{-                   InitGuess : TNcomplex;    initial guess to a root      -}
{-                                             (may be very crude)          -}
{-                   Tol       : real;         tolerance in the answer      -}
{-                   MaxIter   : integer;      number of iterations         -}
{-                   NumRoots  : integer;      number of roots calculated   -}
{-                   Roots     : TNCompVector; the roots calculated         -}
{-                   yRoots    : TNCompVector; the value of the function    -}
{-                                             at the calculated roots      -}
{-                   Iter      : TNIntVector;  number iteration it took to  -}
{-                                             find each root               -}
{-                   Error     : byte;         flags an error               -}
{-                                                                          -}
{-           Errors: 0: No error                                            -}
{-                   1: Iter > MaxIter                                      -}
{-                   2: Degree <= 0                                         -}
{-                   3: Tol <= 0                                            -}
{-                   4: MaxIter < 0                                         -}
{-                                                                          -}
{-     Version Date: 26 January 1987                                        -}
{-                                                                          -}
{----------------------------------------------------------------------------}

{$R+}  { Enable range checking }

const
  TNNearlyZero = 1E-015;    { If you get a syntax error here, you are    }
                            { not using Turbo-87.                        }
                            { TNNearlyZero = 1E-015 if using the 8087    }
                            {                      math co-processor.    }
                            { TNNearlyZero = 1E-08 if not using the 8087 }
                            {                      math co-processor.    }

type
  TNquadratic = record
                  A, B, C : real;
                end;

var
  AddIter    : integer;
  InitDegree : integer;
  InitPoly   : TNCompVector;
  GuessRoot  : TNcomplex;

{----------- Here are a few complex operations ------------}

procedure Conjugate(var C1, C2 : TNcomplex);
begin
  C2.Re := C1.Re;
  C2.Im := -C1.Im;
end; { procedure Conjugate }

function Modulus(var C1 : TNcomplex) : real;
begin
  Modulus := Sqrt(Sqr(C1.Re) + Sqr(C1.Im));
end; { function Modulus }

procedure Add(var C1, C2, C3 : TNcomplex);
begin
  C3.Re := C1.Re + C2.Re;
  C3.Im := C1.Im + C2.Im;
end; { procedure Add }

procedure Sub(var C1, C2, C3 : TNcomplex);
begin
  C3.Re := C1.Re - C2.Re;
  C3.Im := C1.Im - C2.Im;
end; { procedure Sub }

procedure Mult(var C1, C2, C3 : TNcomplex);
begin
  C3.Re := C1.Re * C2.Re - C1.Im * C2.Im;
  C3.Im := C1.Im * C2.Re + C1.Re * C2.Im;
end; { procedure Mult }

procedure Divide(var C1, C2, C3 : TNcomplex);
var
  Dum1, Dum2 : TNcomplex;
  E : real;
begin
  Conjugate(C2, Dum1);
  Mult(C1, Dum1, Dum2);
  E := Sqr(Modulus(C2));
  C3.Re := Dum2.Re / E;
  C3.Im := Dum2.Im / E;
end;  { procedure Divide }

procedure SquareRoot(var C1, C2 : TNcomplex);
const
  TNNearlyZero = 1E-15;
var
  R, Theta : real;
begin
  R := Sqrt(Sqr(C1.Re) + Sqr(C1.Im));
  if ABS(C1.Re) < TNNearlyZero then
    begin
      if C1.Im < 0 then
        Theta := Pi / 2
      else
        Theta := -Pi / 2;
    end
  else
    if C1.Re < 0 then
      Theta := ArcTan(C1.Im / C1.Re) + Pi
    else
      Theta := ArcTan(C1.Im / C1.Re);
  C2.Re := Sqrt(R) * Cos(Theta / 2);
  C2.Im := Sqrt(R) * Sin(Theta / 2);
end; { procedure SquareRoot }

procedure InitAndTest(var Degree     : integer;
                      var Poly       : TNCompVector;
                          Tol        : real;
                          MaxIter    : integer;
                          InitGuess  : TNcomplex;
                      var NumRoots   : integer;
                      var Roots      : TNCompVector;
                      var yRoots     : TNCompVector;
                      var Iter       : TNIntVector;
                      var GuessRoot  : TNcomplex;
                      var InitDegree : integer;
                      var InitPoly   : TNCompVector;
                      var Error      : byte);

{----------------------------------------------------------}
{- Input:  Degree, Poly, Tol, MaxIter, InitGuess          -}
{- Output: InitDegree, InitPoly, Degree, Poly, NumRoots,  -}
{-         Roots, yRoots, Iter, GuessRoot, Error          -}
{-                                                        -}
{- This procedure sets the initial value of the above     -}
{- variables.  This procedure also tests the tolerance    -}
{- (Tol), maximum number of iterations (MaxIter), and     -}
{- code.  Finally, it examines the coefficients of Poly.  -}
{- If the constant term is zero, then zero is one of the  -}
{- roots and the polynomial is deflated accordingly. Also -}
{- if the leading coefficient is zero, then Degree is     -}
{- reduced until the leading coefficient is non-zero.     -}
{----------------------------------------------------------}

var
  Term : integer;

begin
  Error := 0;
  if Degree <= 0 then
    Error := 2;      { degree is less than 2 }
  if Tol <= 0 then
    Error := 3;
  if MaxIter < 0 then
    Error := 4;

  if Error = 0 then
  begin
    NumRoots := 0;
    GuessRoot := InitGuess;
    InitDegree := Degree;
    InitPoly := Poly;
    { Reduce degree until leading coefficient <> zero }
    while (Degree > 0) and (Modulus(Poly[Degree]) < TNNearlyZero) do
      Degree := Pred(Degree);
    { Deflate polynomial until the constant term <> zero }
    while (Modulus(Poly[0]) = 0) and (Degree > 0) do
    begin
      { Zero is a root }
      NumRoots := Succ(NumRoots);
      Roots[NumRoots].Re := 0;
      Roots[NumRoots].Im := 0;
      yRoots[NumRoots].Re := 0;
      yRoots[NumRoots].Im := 0;
      Iter[NumRoots] := 0;
      Degree := Pred(Degree);
      for Term := 0 to Degree do
        Poly[Term] := Poly[Term + 1];
    end;
  end;
end; { procedure InitAndTest }

procedure FindOneRoot(Degree    : integer;
                      Poly      : TNCompVector;
                      GuessRoot : TNcomplex;
                      Tol       : real;
                      MaxIter   : integer;
                  var Root      : TNcomplex;
                  var yValue    : TNcomplex;
                  var Iter      : integer;
                  var Error     : byte);

{-------------------------------------------------------------------}
{- Input:  Degree, Poly, GuessRoot, Tol, MaxIter                   -}
{- Output: Root, yValue, Iter, Error                               -}
{-                                                                 -}
{- This procedure approximates a single root of the polynomial     -}
{- Poly.  The root must be approximated within MaxIter             -}
{- iterations to a tolerance of Tol.  The root, value of the       -}
{- polynomial at the root (yValue), and the number of iterations   -}
{- (Iter) are returned. If no root is found, the appropriate error -}
{- code (Error) is returned.                                       -}
{-------------------------------------------------------------------}

var
  Found : boolean;
  Dif : TNcomplex;
  yPrime, yDoublePrime : TNcomplex;

procedure EvaluatePoly(Degree       : integer;
                       Poly         : TNCompVector;
                       X            : TNcomplex;
                   var yValue       : TNcomplex;
                   var yPrime       : TNcomplex;
                   var yDoublePrime : TNcomplex);

{--------------------------------------------------------------------}
{- Input:  Degree, Poly, X                                          -}
{- Output: yValue, yPrime, yDoublePrime                             -}
{-                                                                  -}
{- This procedure applies the technique of synthetic division to    -}
{- determine value (yValue), first derivative (yPrime) and second   -}
{- derivative (yDoublePrime) of the  polynomial, Poly, at X.        -}
{- The 0th element of the first synthetic division is the           -}
{- value of Poly at X, the 1st element of the second synthetic      -}
{- division is the first derivative of Poly at X, and twice the     -}
{- 2nd element of the third synthetic division is the second        -}
{- derivative of Poly at X.                                         -}
{--------------------------------------------------------------------}

var
  Loop : integer;
  Dummy, yDPdummy : TNcomplex;
  Deriv, Deriv2 : TNCompVector;

begin
  Deriv[Degree] := Poly[Degree];
  for Loop := Degree - 1 downto 0 do
  begin
    Mult(Deriv[Loop + 1], X, Dummy);
    Add(Dummy, Poly[Loop], Deriv[Loop]);
  end;
  yValue := Deriv[0];    { Value of Poly at X }

  Deriv2[Degree] := Deriv[Degree];
  for Loop := Degree - 1 downto 1 do
  begin
    Mult(Deriv2[Loop + 1], X, Dummy);
    Add(Dummy, Deriv[Loop], Deriv2[Loop]);
  end;
  yPrime := Deriv2[1];   { 1st deriv. of Poly at X }

  yDPdummy := Deriv2[Degree];
  for Loop := Degree - 1 downto 2 do
  begin
    Mult(yDPdummy, X, Dummy);
    Add(Dummy, Deriv2[Loop], yDPdummy);
  end;
  yDoublePrime.Re := 2 * yDPdummy.Re;    { 2nd derivative of Poly at X }
  yDoublePrime.Im := 2 * yDPdummy.Im;
end; { procedure EvaluatePoly }

procedure ConstructDifference(Degree       : integer;
                              yValue       : TNcomplex;
                              yPrime       : TNcomplex;
                              yDoublePrime : TNcomplex;
                          var Dif          : TNcomplex);

{------------------------------------------------------------------}
{- Input:  Degree, yValue, yPrime, yDoublePrime                   -}
{- Output: Dif                                                    -}
{-                                                                -}
{- This procedure computes the difference between approximations; -}
{- given information about the function and its first two         -}
{- derivatives.                                                   -}
{-----------------------------------------------------------------}

var
  yPrimeSQR, yTimesyDPrime, Sum, SRoot,
  Numer1, Numer2, Numer, Denom : TNcomplex;

begin
  Mult(yPrime, yPrime, yPrimeSQR);
  yPrimeSQR.Re := Sqr(Degree - 1) * yPrimeSQR.Re;
  yPrimeSQR.Im := Sqr(Degree - 1) * yPrimeSQR.Im;
  Mult(yValue, yDoublePrime, yTimesyDPrime);
  yTimesyDPrime.Re := (Degree - 1) * Degree * yTimesyDPrime.Re;
  yTimesyDPrime.Im := (Degree - 1) * Degree * yTimesyDPrime.Im;
  Sub(yPrimeSQR, yTimesyDPrime, Sum);
  SquareRoot(Sum, SRoot);
  Add(yPrime, SRoot, Numer1);
  Sub(yPrime, SRoot, Numer2);
  if Modulus(Numer1) > Modulus(Numer2) then
    Numer := Numer1
  else
    Numer := Numer2;
  Denom.Re := Degree * yValue.Re;
  Denom.Im := Degree * yValue.Im;
  if Modulus(Numer) < TNNearlyZero then
    begin
      Dif.Re := 0;
      Dif.Im := 0;
    end
  else
    Divide(Denom, Numer, Dif);  { The difference is the   }
                                { inverse of the fraction }
end; { procedure ConstructDifference }

function TestForRoot(X, Dif, Y, Tol : real) : boolean;

{--------------------------------------------------------------------}
{-  These are the stopping criteria.  Four different ones are       -}
{-  provided.  If you wish to change the active criteria, simply    -}
{-  comment off the current criteria (including the appropriate OR) -}
{-  and remove the comment brackets from the criteria (including    -}
{-  the appropriate OR) you wish to be active.                      -}
{--------------------------------------------------------------------}

begin
  TestForRoot :=                      {---------------------------}
    (ABS(Y) <= TNNearlyZero)          {- Y=0                     -}
                                      {-                         -}
           or                         {-                         -}
                                      {-                         -}
    (ABS(Dif) < ABS(X * Tol))         {- Relative change in X    -}
                                      {-                         -}
                                      {-                         -}
 (*       or                      *)  {-                         -}
 (*                               *)  {-                         -}
 (* (ABS(Dif) < Tol)              *)  {- Absolute change in X    -}
 (*                               *)  {-                         -}
 (*       or                      *)  {-                         -}
 (*                               *)  {-                         -}
 (* (ABS(Y) <= Tol)               *)  {- Absolute change in Y    -}
                                      {---------------------------}

{-----------------------------------------------------------------------}
{- The first criteria simply checks to see if the value of the         -}
{- function is zero.  You should probably always keep this criteria    -}
{- active.                                                             -}
{-                                                                     -}
{- The second criteria checks the relative error in X. This criteria   -}
{- evaluates the fractional change in X between interations. Note      -}
{- that X has been multiplied throught the inequality to avoid divide  -}
{- by zero errors.                                                     -}
{-                                                                     -}
{- The third criteria checks the absolute difference in X between      -}
{- iterations.                                                         -}
{-                                                                     -}
{- The fourth criteria checks the absolute difference between          -}
{- the value of the function and zero.                                 -}
{-----------------------------------------------------------------------}

end; { procedure TestForRoot }

begin { procedure FindOneRoot }
  Root := GuessRoot;
  Found := false;
  Iter := 0;
  EvaluatePoly(Degree, Poly, Root, yValue, yPrime, yDoublePrime);
  while (Iter < MaxIter) and not(Found) do
  begin
    Iter := Succ(Iter);
    ConstructDifference(Degree, yValue, yPrime, yDoublePrime, Dif);
    Sub(Root, Dif, Root);
    EvaluatePoly(Degree, Poly, Root, yValue, yPrime, yDoublePrime);
    Found := TestForRoot(Modulus(Root), Modulus(Dif), Modulus(yValue), Tol);
  end;
  if not(Found) then Error := 1;   { Iterations execeeded MaxIter }
end; { procedure FindOneRoot }

procedure ReducePoly(var Degree : integer;
                     var Poly   : TNCompVector;
                     Root       : TNcomplex);

{------------------------------------------------------}
{- Input: Degree, Poly, Root                          -}
{- Output: Degree, Poly                               -}
{-                                                    -}
{- This procedure deflates the polynomial Poly by     -}
{- factoring out the Root.  Degree is reduced by one. -}
{------------------------------------------------------}

var
  Term : integer;
  NewPoly : TNCompVector;
  Dummy : TNcomplex;

begin
  NewPoly[Degree - 1] := Poly[Degree];
  for Term := Degree - 1 downto 1 do
  begin
    Mult(NewPoly[Term], Root, Dummy);
    Add(Dummy, Poly[Term], NewPoly[Term - 1]);
  end;
  Degree := Pred(Degree);
  Poly := NewPoly;
end; { procedure ReducePoly }

begin  { procedure Laguerre }
  InitAndTest(Degree, Poly, Tol, MaxIter, InitGuess, NumRoots, Roots,
              yRoots, Iter, GuessRoot, InitDegree, InitPoly, Error);
  while (Degree > 0) and (Error = 0) do
  begin
    FindOneRoot(Degree, Poly, GuessRoot, Tol, MaxIter,
                Roots[NumRoots + 1], yRoots[NumRoots + 1],
                Iter[NumRoots + 1], Error);
    if Error = 0 then
    begin
      {------------------------------------------------------}
      {- The next statement refines the approximate root by -}
      {- plugging it into the original polynomial.  This    -}
      {- eliminates a lot of the round-off error            -}
      {- accumulated through many iterations                -}
      {------------------------------------------------------}
      FindOneRoot(InitDegree, InitPoly, Roots[NumRoots + 1],
                  Tol, MaxIter, Roots[NumRoots + 1],
                  yRoots[NumRoots + 1], AddIter, Error);
      Iter[NumRoots + 1] := Iter[NumRoots + 1] + AddIter;
      NumRoots := Succ(NumRoots);
      ReducePoly(Degree, Poly, Roots[NumRoots]); { Reduce polynomial }
    end;
    GuessRoot := Roots[NumRoots];
  end;
end; { procedure Laguerre }

{==========================================================================}
begin
{==========================================================================}
end.
