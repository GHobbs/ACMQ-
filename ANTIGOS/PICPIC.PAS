PROGRAM Picpic;

{$M 1024,0,0}

USES Dos;

PROCEDURE Fica; INTERRUPT;
CONST
  baseVGA=$A000;
VAR
  i,j,base:INTEGER;
  saida:FILE of BYTE;
BEGIN
  InLine($FB);
  Assign(saida,'temp.fig');
  ReWrite(saida);
  FOR i:=0 TO 199 DO BEGIN
    base:=i*320;
    FOR j:=0 TO 319 DO Write(saida,Mem[baseVGA:base+j])
  END;
  Close(saida)
END;

BEGIN
  SetIntVec(5,@Fica);
  WriteLn('PicPic instalado');
  WriteLn('Toque PrtSc para ativar');
  Keep(1)
END.