CONST
  max=10;
  xmin=-max;
  xmax=max;
  ymin=-max;
  ymax=max;

VAR
  x,y:INTEGER;
  t:REAL;
  arquivo:TEXT;

BEGIN
  Assign(arquivo,'teste.d3d');
  ReWrite(arquivo);
  WriteLn(arquivo,xmin,' ',ymin,' ',xmax,' ',ymax,' -1 1');
  FOR x:=xmin TO xmax DO
    FOR y:=ymin TO ymax DO BEGIN
      t:=Sqrt(Sqr(x)+Sqr(y));
      IF t<>0 THEN t:=Sin(t)/t ELSE t:=1;
      Write(arquivo,t,' ')
    END;
  Close(arquivo)
END.