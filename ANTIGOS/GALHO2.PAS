{This program produces an invalid number when taking the logarithm
 and an error when adding 1 to it (or any operation)
 using the ULSI 80387.
 Problem observed in 4/Nov/92
 by Antonio Carlos M. de Queiroz}
{$N+,E+}
VAR x:EXTENDED;
BEGIN
  x:=4;
  x:=x-2e-19;
  WriteLn('x=',x);
  x:=Ln(x);
  WriteLn('Ln(x)=',x);
  x:=x+1;
END.