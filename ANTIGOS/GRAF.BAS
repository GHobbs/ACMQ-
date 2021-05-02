10 REM *****************************************************************
20 REM *    PROGRAMA PARA TRACAR GRAFICOS DE RESPOSTA EM FREQUENCIA    *
30 REM *    Autor: Antonio Carlos Moreirao de Queiroz  COPPE/UFRJ      *
40 REM *    Versao 2.6 13/08/1985 Correcao na gravacao da tabela       *
50 REM *    Versao 2.7 21/11/1985 Modificadoes na gravacao de tabelas  *
60 REM *    Versao 2.8 19/03/1986 Tabela compativel com GrafXY         *
70 REM *    Versao 2.9 25/03/1986 Tabela compativel com Grafico tambem *
80 REM *    Versao 3.0 03/04/1989 Versao para Turbo Basic              *
90 REM *****************************************************************
100 DEFDBL U,D,K,X,L
110 DEFSNG I,J,M,N,C
120 DIM PC(60),U(400),D(400),FRQ(639),GAN(639),FAS(639)
130 DPI=6.283185307795895#
140 LN10=LOG(10!)
150 SCREEN 2
160 REM ========== Leitura do numerador e do denominador
170 CLS
180 PRINT"Grafico de Funcoes de Transferencia em Transformada de Laplace ou Z"
190 PRINT"-------------------------------------------------------------------"
200 PRINT"Antonio Carlos Moreirao de Queiroz - COPPE/UFRJ - 1984 - Versao 3.0": PRINT
210 INPUT"Funcao de [s] ou [Z]? (s) ",X$
220 IF X$="z" OR X$="Z" THEN IZ=1 ELSE IZ=0
230 IF IZ=1 THEN INPUT"Frequencia de chaveamento? (Hz) ",F: T=1/F
240 INPUT"O numerador esta em arquivo? [nome ou 'n'] (n) ",X$
250 IF X$="n" OR X$="N" OR X$="" THEN 390
260 OPEN "I",#1,X$
270 INPUT #1,NN
280 FOR I=0 TO NN
290 INPUT #1,U(I)
300 NEXT I
310 INPUT #1,K,IP
320 IF IZ=1 THEN INPUT"Incremento nas potencias de Z no numerador: ",P1 ELSE P1=1
330 PRINT"Grau do numerador=";NN*P1+IP
340 FOR I=0 TO NN
350 PRINT"n(";I*P1+IP;")=";U(I)
360 NEXT I
370 PRINT"Cte. de ganho=";K
380 GOTO 540
390 IF IZ=0 THEN INPUT"Grau do numerador? ",NN: P1=1: IP=0
400 IF IZ=1 THEN INPUT"Numero de coeficientes no numerador? ",NN: NN=NN-1
410 IF IZ=1 THEN INPUT"Menor potencia,incremento nas potencias sucessivas de Z: ",IP,P1
420 FOR I=0 TO NN
430 PRINT"n(";I*P1+IP;: INPUT")? ",U(I)
440 NEXT I
450 INPUT"Cte. de ganho? ",K
460 INPUT"Deseja gravar o numerador? [nome do arquivo ou 'n'] (n) ",X$
470 IF X$="n" OR X$="N" OR X$="" THEN 550
480 OPEN "O",#1,X$
490 PRINT #1,NN
500 FOR I=0 TO NN
510 PRINT #1,U(I)
520 NEXT I
530 PRINT #1,K;IP
540 CLOSE #1
550 INPUT"O denominador esta em arquivo? [nome ou 'n'] (n) ",X$
560 IF X$="n" OR X$="N" OR X$="" THEN 630
570 OPEN "I",#1,X$
580 INPUT #1,ND: PRINT"Grau do denominador=";ND
590 FOR I=0 TO ND
600 INPUT #1,D(I): PRINT"d(";I;")=";D(I)
610 NEXT I
620 GOTO 740
630 INPUT"Grau do denominador? ",ND
640 FOR I=0 TO ND
650 PRINT"d(";I;: INPUT")? ",D(I)
660 NEXT I
670 INPUT"Deseja gravar o denominador? [nome do arquivo ou 'n'] (n) ",X$
680 IF X$="n" OR X$="N" OR X$="" THEN 750
690 OPEN "O",#1,X$
700 PRINT #1,ND
710 FOR I=0 TO ND
720 PRINT #1,D(I)
730 NEXT I
740 CLOSE #1
750 INPUT"Frequencias em [H]ertz ou [R]adianos? (R) ",X$
760 IF X$="H" OR X$="h" THEN IH=1: U$="Hz" ELSE IH=0: U$="Rd/s"
770 INPUT"Escala horizontal [L]inear ou L[o]garitmica? (o) ",X$
780 IF X$="L" OR X$="l" THEN IL=1 ELSE IL=0
790 INPUT"Escala vertical [L]inear ou em [D]ecibeis? (D) ",X$
800 IF X$="L" OR X$="l" THEN IV=1 ELSE IV=0
810 REM ==========Inicalizacao do grafico
820 CLS: F1=0: F2=0
830 LOCATE 1,1: PRINT SPC(79): LOCATE  1,1: INPUT"Freq. inicial, final, Modulo min, max: ",F3,F4,B1,B2
840 IF NOT(F1=F3 AND F2=F4) THEN CL=-1: F1=F3: F2=F4
850 CLS: DB=(B2-B1)/180: IF IL=1 THEN DF=(F2-F1)/639 ELSE DF=(F2/F1)^(1/639)
860 LINE (0,19)-(0,199): LINE -(639,199)
870 GET (0,19)-(0,199),PC
880 LOCATE 2,1: PRINT"Vertical:";B1;"a";B2;
890 IF IV=0 THEN PRINT"dB";
900 PRINT"; Horizontal:";F1;"a";F2;U$;
910 F=F1: M1=199: C1=0
920 REM ========== Ciclo de avaliacao da funcao
930 FOR J=0 TO 639
940 IF J<=CL THEN 1190
950 IF IH THEN W=DPI*F ELSE W=F
960 IF IZ=1 THEN Z1=COS(W*T): Z2=SIN(W*T) ELSE Z1=0: Z2=W
970 D1=0: D2=0
980 FOR I=ND TO 0 STEP -1
990 D=D1*Z1-D2*Z2+D(I)
1000 D2=D1*Z2+D2*Z1
1010 D1=D
1020 NEXT I
1030 U1=0: U2=0
1040 IF IZ=1 THEN Z1=COS(W*T*P1): Z2=SIN(W*T*P1)
1050 FOR I=NN TO 0 STEP -1
1060 D=U1*Z1-U2*Z2+U(I)
1070 U2=U1*Z2+U2*Z1
1080 U1=D
1090 NEXT I
1100 D=K/(D1*D1+D2*D2)
1110 X1=(U1*D1+U2*D2)*D: X2=(U2*D1-U1*D2)*D
1120 IF IZ=1 AND IP<>0 THEN Z1=COS(W*T*IP): Z2=SIN(W*T*IP): D=X1*Z1-X2*Z2: X2=X1*Z2+X2*Z1: X1=D 'Estava faltando X1=D (5/6/89)
1130 FASE=ATN(X2/X1)*57.29577951#
1140 IF IV=0 THEN GAN(J)=10*LOG(X1*X1+X2*X2)/LN10 ELSE GAN(J)=SQR(X1*X1+X2*X2)
1150 IF X1>0 THEN 1170
1160 IF X2>0 THEN FASE=180+FASE ELSE FASE=FASE-180
1170 FAS(J)=FASE: FRQ(J)=F
1180 REM ========== Calculo das posicoes a plotar
1190 M2=INT((B1-GAN(J))/DB+199.5)
1200 MF2=INT((-180-FAS(J))/2+199.5)
1210 C2=J
1220 REM ========== Tracado do grafico
1230 LINE (C1,M1)-(C2,M2)
1240 PSET (C2,MF2)
1250 M1=M2: C1=C2
1260 IF IL=1 THEN F=F+DF ELSE F=F*DF
1270 X$=INKEY$
1280 IF X$<>"" THEN CL=J: GOTO 1320
1290 NEXT J
1300 CL=639
1310 REM ========== Opcoes com grafico pronto
1320 C1=0: I=16
1330 LOCATE  1,1: PRINT SPC(79);: LOCATE 1,1: PRINT"Imprimir Gravar Outro Fim Recomecar (cursor com as setas)";
1340 REM ========== Exame do teclado
1350 X$=INKEY$
1360 REM ========== Cursor para a esquerda
1370 IF X$<>CHR$(0)+"K" THEN 1400
1380 IF C1-I>=0 THEN C2=C1-I: GOTO 1420 ELSE 1350
1390 REM ========== Cursor para a direita
1400 IF X$<>CHR$(0)+"M" THEN 1510
1410 IF C1+I<=CL THEN C2=C1+I ELSE 1350
1420 LOCATE  1,1:PRINT SPC(79)
1430 LOCATE  1,1: PRINT FRQ(C2);U$;"; ";GAN(C2);
1440 IF IV=0 THEN PRINT"dB";
1450 PRINT"; ";
1460 PRINT FAS(C2);"graus"
1470 PUT (C2,19),PC: PUT(C1,19),PC
1480 C1=C2
1490 GOTO 1350
1500 REM ========== Aumentar deslocamento do cursor
1510 IF X$<>CHR$(0)+"I" THEN 1550
1520 I=16
1530 GOTO 1350
1540 REM ========== Diminuir deslocamento do cursor
1550 IF X$<>CHR$(0)+"Q" THEN 1590
1560 I=1
1570 GOTO 1350
1580 REM ========== Gravar resultados
1590 IF X$<>"G" AND X$<>"g" THEN 1800
1600 LOCATE 1,1: PRINT SPC(79): LOCATE 1,1: INPUT"Nome do arquivo onde guardar os valores: ",X$
1610 OPEN "O",#3,X$
1620 LOCATE 1,1: PRINT SPC(79): LOCATE 1,1: PRINT"Gravar quantos pontos? (Max=";CL+1;: INPUT") ",CF
1630 IF CF>=CL+1 THEN CF=CL+1:
1640 CP=(CL+1)/CF
1650 LOCATE 1,1: PRINT SPC(79): LOCATE 1,1: INPUT"Gravar  apenas [m]odulo, apenas [f]ase, ou [t]udo (fr.,mo.,fa.)? (t) ",X$
1660 IF X$="m" OR X$="M" OR X$="f" OR X$="F" THEN PRINT #3,CF,1: GOTO 1710
1670 FOR J=0 TO CL STEP CP
1680 PRINT #3,FRQ(J);TAB(15);GAN(J);TAB(30);FAS(J)
1690 NEXT J
1700 GOTO 1770
1710 LOCATE 1,1: PRINT SPC(79): LOCATE 1,1: INPUT"Gravar as frequencias tambem? [s/n] (n) ",S$
1720 FOR J=0 TO CL STEP CP
1730 IF S$="s" OR S$="S" THEN PRINT #3,FRQ(J);
1740 IF X$="m" OR X$="M" THEN PRINT #3,GAN(J): GOTO 1760
1750 IF X$="f" OR X$="F" THEN PRINT #3,FAS(J)
1760 NEXT J
1770 CLOSE #3
1780 GOTO 1330
1790 REM ========== Imprimir grafico
1800 IF X$<>"I" AND X$<>"i" THEN 1950
1810 LOCATE 1,1: PRINT SPC(79);: LOCATE  1,1: INPUT"Titulo: ",X$
1820 'WIDTH LPRINT 255
1830 DEF SEG = &HB800
1840 LPRINT CHR$(27);"A";CHR$(8);
1850 FOR I=0 TO 79
1860 LPRINT SPC(10);CHR$(27);"L";CHR$(144);CHR$(1);
1870 FOR J=7920+I TO I STEP -80
1880 LPRINT CHR$(PEEK(J+8192));CHR$(PEEK(J+8192));CHR$(PEEK(J));CHR$(PEEK(J));
1890 NEXT J
1900 LPRINT
1910 NEXT I
1920 LPRINT CHR$(27);"A";CHR$(10)
1930 GOTO 1330
1940 REM ========== Fim
1950 IF X$<>"F" AND X$<>"f" THEN 1980
1960 SCREEN 0: END
1970 REM ========== Recomecar o programa
1980 IF X$<>"R" AND X$<>"r" THEN 2010
1990 GOTO 170
2000 REM ========== Outro grafico da mesma funcao
2010 IF X$<>"O" AND X$<>"o" THEN 1350
2020 GOTO 830
