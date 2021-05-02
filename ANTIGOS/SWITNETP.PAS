PROGRAM SwitNet;

USES Crt,Tela;

VAR
  entrada,saida:TEXT;
  fonte,nome,default,nomein,nomeout:STRING;
  nfonte,nsaida,i,no1,no2,no3,fase,fases,pontosf,pontost:INTEGER;
  f1,f2,freqchav,valor,ganho:REAL;
  ch:CHAR;
  sss,tran,log,amostrar:BOOLEAN;
LABEL
  lerdenovo,fim;

BEGIN
  f1:=0; f2:=0.5; freqchav:=1; fases:=2; ganho:=1e6;
  nsaida:=1; log:=FALSE; amostrar:=TRUE; pontosf:=24; pontost:=24; sss:=TRUE; tran:=FALSE;
  ClrScr;
  WriteLn(tl,'Conversor de netlist [CAPZ-SWITCAP]');
  WriteLn(tl,'[-]-[-]-[-]-[-]-[-]-[-]-[-]-[-]-[-]-[-]-[-]-[-]-[-]-[-]-[-]-[-]-[-]');
  WriteLn;
  WriteLn('ACMQ - COPPE/UFRJ - VersÑo 1.1 de 23/6/89');
  WriteLn(tl,#10'Este programa transforma um net-list gerado pelo editor [EdFil] para um cir-');
  WriteLn(tl,'cuito a capacitor chaveado para o programa [CAPZ] para o formato do [SWITCAP].');
  WriteLn(tl,'Na forma gerada, o resultado da an†lise Ç idàntico ao do programa [CAPZ].');
  IF paramcount<>0 THEN default:=ParamStr(1) else default:='';
 lerdenovo:
  Write(tl,#10'Arquivo de entrada ([.red]): ([',default,']) ['); ReadLn(nomein);
  IF nomein='' THEN nomein:=default;
  IF Pos('.',nomein)=0 THEN nomein:=nomein+'.red';
  Assign(entrada,nomein);
  {$I-} ReSet(entrada); {$I+}
  IF IOResult<>0 THEN BEGIN
    WriteLn(tl,']Arquivo [',nomein,'] inexistente.');
    GoTo lerdenovo;
  END;
  default:=Copy(nomein,1,Pos('.',nomein)-1);
  Write(tl,']Arquivo de sa°da ([.in]): ([',default,']) ['); ReadLn(nomeout);
  IF nomeout='' THEN nomeout:=default;
  IF Pos('.',nomeout)=0 THEN nomeout:=nomeout+'.in';
  Write(tl,']N¢ de sa°da'); LerInt(nsaida);
  Write('N£mero de fases'); LerInt(fases);
  Write('Ganho dos amplificadores'); LerReal(ganho);
  Write('FreqÅància de chaveamento'); LerReal(freqchav);
  Assign(saida,nomeout);
  ReWrite(saida);
  WriteLn(saida,'TITLE: ',nomeout);
  WriteLn(saida,'TIMING;');
  WriteLn(saida,'   PERIOD ',1/freqchav,';');
  FOR i:=1 TO fases DO WriteLn(saida,'   CLOCK clk',i,' 1 (',i-1,'/',fases,' ',i,'/',fases,');');
  WriteLn(saida,'   END;');
  WriteLn(saida,'CIRCUIT;');
  ReadLn(entrada); {Pula o no. de nos}
  WHILE not SeekEof(entrada) DO BEGIN
    nome:='';
    REPEAT
      Read(entrada,ch);
      IF ch<>' ' THEN nome:=nome+ch;
    UNTIL ch=' ';
    CASE UpCase(nome[1]) OF
      'S':BEGIN
            Read(entrada,no1,no2);
            ch:='a';
            WHILE not Eoln(entrada) DO BEGIN
              Read(entrada,fase);
              WriteLn(saida,'   ',nome,ch,' (',no1,' ',no2,') clk',fase,';');
            END;
            ReadLn(entrada);
          END;
      'P':BEGIN
            ReadLn(entrada,no1,no2,no3);
            nome[1]:='S';
            WriteLn(saida,'   ',nome,'a (',no1,' ',no3,') clk1;');
            WriteLn(saida,'   ',nome,'b (',no2,' ',no3,') clk2;');
          END;
      'C':BEGIN
            ReadLn(entrada,no1,no2,valor);
            WriteLn(saida,'   ',nome,' (',no1,' ',no2,') ',valor,';');
          END;
      'V':BEGIN
            ReadLn(entrada,no1,no2);
            WriteLn(saida,'   ',nome,' (',no1,' ',no2,');');
            fonte:=nome; nfonte:=no1;
          END;
  'A','O':BEGIN
            ReadLn(entrada,no1,no2,no3);
            nome[1]:='E';
            WriteLn(saida,'   ',nome,' (',no3,' 0 ',no2,' ',no1,') ',ganho,';');
          END;
      ELSE BEGIN WriteLn(tl,'[*] Elemento desconhecido: [',nome); GoTo fim END;
    END;
  END;
  WriteLn(saida,'   END;');
  Write('Analisar resposta em freqÅància'); LerBool(sss);
  IF sss THEN BEGIN
    Write('Sample-and-hold na sa°da (uma amostra por fase)'); LerBool(amostrar);
    Write('Escala logar°tmica'); LerBool(log);
    Write('FreqÅància inicial (Hz)'); LerReal(f1);
    Write('FreqÅància final (Hz)'); LerReal(f2);
    Write('N£mero de pontos no gr†fico'); LerInt(pontosf);
    WriteLn(saida,'ANALYZE SSS;');
    IF log THEN nome:='LOG' ELSE nome:='LIN';
    WriteLn(saida,'   INFREQ ',f1,' ',f2,' ',nome,' ',pontosf,';');
    WriteLn(saida,'   SET ',fonte,' AC 1.0 0.0;');
    WriteLn(saida,'   SAMPLE INPUT HOLD 1/',fases,' 0+;');
    IF amostrar THEN
      WriteLn(saida,'   SAMPLE OUTPUT HOLD 1/',fases,' 0+;')
    ELSE
    WriteLn(saida,'   SAMPLE OUTPUT IMPULSE 1/',fases,' 0+;');
    WriteLn(saida,'   PRINT VDB(',nsaida,') VP (',nsaida,');');
    WriteLn(saida,'   PLOT VDB(',nsaida,') VP (',nsaida,');');
    WriteLn(saida,'   END;');
  END;
  Write('Analisar resposta no tempo (ao degrau)'); LerBool(tran);
  IF tran THEN BEGIN
    Write('N£mero de ciclos a calcular'); LerInt(pontost);
    WriteLn(saida,'ANALYZE TRAN;');
    WriteLn(saida,'   TIME 0- ',pontost,' 1/',fases,';');
    WriteLn(saida,'   SET ',fonte,' PULSE 0 1 0 0 0 ',pontost/freqchav,' ',(pontost+1)/freqchav,';');
    WriteLn(saida,'   SAMPLE INPUT HOLD 1/',fases,' 0+;');
    WriteLn(saida,'   PRINT V(',nfonte,') V(',nsaida,');');
    WriteLn(saida,'   PLOT V(',nfonte,') V(',nsaida,');');
    WriteLn(saida,'   END;');
  END;
  WriteLn(saida,'END;');
 fim:
  WriteLn(tl,#10'Net-list no formato [SWITCAP] criado.');
  Close(entrada);
  Close(saida);
END.