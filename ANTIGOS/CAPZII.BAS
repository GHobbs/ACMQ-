10 REM *************************************************************************
20 REM * Calculo de f. de T. de filtros a capacitor chaveado multifasicos      *
30 REM * Autor: Antonio Carlos Moreirao de Queiroz - COPPE/UFRJ - 1985         *
40 REM * Versao 1.3 de 03/06/1985 Corrigido para no. impar de incognitas       *
60 REM * Versao 1.4 de 15/07/1985 Formato p/ amp corrigido                     *
65 REM * Versao 1.5 de 18/11/1985 Incluido raio variavel                       *
67 REM * Versao 1.6 de 30/06/1988 Saida sem break; Pequenas alteracoes         *
68 REM * Versao 1.7 de 30/05/1989 Alteracao do formato de entrada              *
70 REM *************************************************************************
80 DEFDBL R,D,V,T,P,X,Y,Z,E
90 DEFINT A,B,C,F,I,J,K,L,G,M,N,S,U,W
100 DIM HZ(35,43),C(200),L(200),Z1(26,34),Z2(26,34),E1(200,8),E2(200,8),X(15),Y(15),D1(8),D2(8),C1(8),C2(8),L1(8),L2(8)
110 REM ========== Inicializacao
120 NX=35: FX=8: NE=26
130 SCREEN 0: WIDTH 80: COLOR 15
140 PRINT"FUNCOES DE TRANSFERENCIA DE FILTROS A CAPACITOR CHAVEADO MULTIFASICOS": COLOR 7
150 PRINT"---------------------------------------------------------------------": COLOR 7
160 PRINT"Antonio Carlos Moreirao de Queiroz - COPPE/UFRJ - 1985 - Versao 1.7": PRINT
170 COLOR 15: INPUT"Nome do arquivo com a descricao do circuito ou '?': ",N$
180 IF N$<>"?" THEN 380
190 REM ========== Instrucoes
200 CLS: COLOR 15: PRINT"INSTRUCOES PARA O USO DO PROGRAMA 'CAPZII':": COLOR 7
210 PRINT"-------------------------------------------": PRINT
220 PRINT"Crie, usando um editor, um arquivo ASCII contendo os seguintes dados:"
230 PRINT: PRINT"Primeira linha: Numero de nos do circuito (terra=0).": PRINT
240 PRINT"Nas linhas seguintes, a descricao dos elementos, um por linha:": PRINT
250 PRINT"   Capacitor:        C<nome>,<no>,<no>,<valor>"
260 PRINT"   Chave:            S<nome>,<no>,<no>,<fase>"
270 PRINT"   Chave dupla:      P<nome>,<no fase 1>,<no fase 2>,<no polo>
280 PRINT"   Amp. operacional: O<nome>,<no ->,<no +>,<saida>"
290 PRINT"   Fonte de sinal:   V<nome>,<no +>,0,<valor>"
300 PRINT:PRINT"- A(s) fonte(s) de sinal devem vir por ultimo."
310 PRINT"- Guarde os polinomios encontrados se desejar encontrar suas raizes posterior-"
320 PRINT"  mente ou plotar um grafico do resposta em frequencia com o programa `GRAF'."
330 PRINT"- O programa calculara as funcoes de transferencia em Z da(s) entrada(s) para"
340 PRINT"  qualquer no da rede .Transferencias triviais serao indicadas, apenas."
350 PRINT"- Use o raio de interpolacao diferente de 1 somente para circuitos que possuam"
360 PRINT"  frequencias naturais sobre o circulo unitario."
365 PRINT
370 GOTO 170
380 OPEN "I",1,N$
390 INPUT #1,N0
395 PRINT: INPUT"Numero de fases";F0
400 IF N0>NX THEN PRINT"Numero excessivo de nos (Max=";NX;")": END
410 IF F0>FX THEN PRINT"Numero excessivo de fases (Max=";FX;")": END
420 PRINT: PRINT"O circuito possui";N0;"nos e";F0;"fases": PRINT: COLOR 7
430 N=F0*N0: N2=N: DPI=6.283185307179612#
440 FOR I=0 TO N2: C(I)=I: L(I)=I: NEXT I
450 REM ========== Leitura da descricao do circuito
460 REM (Em outra linguagem sera necessario zerar a matriz HZ(0-N0,0-N0+F0))
470 IF NOT EOF(1) THEN INPUT #1,N$,A,B,V ELSE 1150
480 ON INSTR("CSPVO",LEFT$(N$,1))+1 GOSUB 500,510,580,620,910,1040
490 GOTO 470
500 PRINT"Elemento nao reconhecido: ";N$: STOP: RETURN
510 REM ========== Capacitor
520 PRINT"Capacitor ";N$;" de";V;"pF entre";A;"e";B
530 HZ(A,A)=HZ(A,A)+V
540 HZ(B,B)=HZ(B,B)+V
550 HZ(A,B)=HZ(A,B)-V
560 HZ(B,A)=HZ(B,A)-V
570 RETURN
580 REM ========== Chave
585 IF V<0 OR V>F0 OR V<>INT(V) THEN 500
590 F=V
600 PRINT"Chave ";N$;" na fase";F;"entre";A;"e";B;TAB(50);CHR$(205)+CHR$(16);" V";A;F;" = V";B;F
610 GOSUB 700: GOSUB 830: RETURN
620 REM ========== Chave dupla
630 F=2
640 A2=A: A=V: V=A2
650 GOSUB 600
660 F=1
670 A2=V: V=B: B=A2
680 GOSUB 600
690 RETURN
700 REM ========== Somar colunas
710 A2=0: B2=0
720 IF A<>0 THEN A2=A+(F-1)*N0
730 IF B<>0 THEN B2=B+(F-1)*N0
740 IF C(A2)<C(B2) THEN A1=C(A2): B1=C(B2) ELSE A1=C(B2): B1=C(A2)
750 IF A1=B1 THEN 820
760 FOR I=1 TO N2
770 IF C(I)=B1 THEN C(I)=A1
780 IF C(I)>B1 THEN C(I)=C(I)-1
790 NEXT I
800 N=N-1
810 RETURN
820 PRINT"Circuito proibido (curto-circuito); verifique a descricao.";CHR$(7): STOP
830 REM ========== Somar linhas
840 IF L(A2)<L(B2) THEN A1=L(A2): B1=L(B2) ELSE A1=L(B2): B1=L(A2)
850 IF A1=B1 THEN 820
860 FOR I=1 TO N2
870 IF L(I)=B1 THEN L(I)=A1
880 IF L(I)>B1 THEN L(I)=L(I)-1
890 NEXT I
900 RETURN
910 REM ========== Fonte independente
920 PRINT "Fonte ";N$;" de";V;"V entre";B;"e";A;TAB(50);CHR$(205)+CHR$(16);" V";A;"* = V";B;"* +";V;"Vin *"
930 IF B<>0 THEN 820
940 FOR F=1 TO F0
950 K=(F-1)*N0: B1=A+K: N1=N0+F
960 FOR I=1 TO N0
970 FOR J=1 TO N0
980 IF C(J+K)=C(B1) THEN HZ(I,N1)=HZ(I,N1)-V*HZ(I,J)
990 NEXT J: NEXT I: NEXT F
1000 FOR F=1 TO F0
1010 GOSUB 610
1020 NEXT F
1030 RETURN
1040 REM ========== Amplificador operacional
1050 PRINT "Amp. Op. ";N$;A;"(-)";B;"(+)";V;"(s)";TAB(50);CHR$(205);CHR$(16);" V";A;"* = V";B;"*"
1060 FOR F=1 TO F0
1070 GOSUB 700
1080 NEXT F
1090 A=V: B2=0
1100 FOR F=1 TO F0
1110 A2=A+(F-1)*N0
1120 GOSUB 830
1130 NEXT F
1140 RETURN
1150 REM ========== Fim dos dados
1160 G=1: M=0: N1=N+F0
1170 IF G<=N/F0 THEN G=G*2: M=M+1: GOTO 1170
1180 COLOR 15: PRINT: PRINT"Ordem do sistema:";N;"x";N1;"; Grau da FFT:";G
1190 IF N>NE THEN PRINT"Ordem do sistema excessiva (Max=";NE;")": STOP
1200 REM ========== Geracao do sistema de equacoes reduzido
1210 REM (Em outra linguagem deve ser zerada a matriz Z1(0-N,0-N1))
1220 FOR F=1 TO F0
1230 C1(F)=N: L1(F)=N
1240 C2(F)=1: L2(F)=1
1250 NEXT F
1260 FOR F=1 TO F0
1270 K=(F-1)*N0
1280 FOR I=1 TO N0
1290 A=L(K+I): A1=L(1+(K+I+N0-1) MOD N2)
1300 Z1(A,N+F)=Z1(A,N+F)+HZ(I,N0+F):  REM Diagonal principal da excitacao
1310 Z1(A1,N+F)=Z1(A1,N+F)-HZ(I,N0+F):REM Diagonal inferior da excitacao
1320 IF A>0 AND A<L1(F) THEN L1(F)=A
1330 IF A>L2(F) THEN L2(F)=A
1340 B=C(K+I)
1350 IF B>0 AND B<C1(F) THEN C1(F)=B
1360 IF B>C2(F) THEN C2(F)=B
1370 FOR J=1 TO N0
1380 B=C(J+K)
1390 Z1(A,B)=Z1(A,B)+HZ(I,J):   REM Diagonal principal de submatrizes
1400 Z1(A1,B)=Z1(A1,B)-HZ(I,J): REM Diagonal inferior de submatrizes
1410 NEXT J: NEXT I: NEXT F
1420 REM ========== Transferencia do sistema reduzido para a posicao final
1430 FOR I=1 TO N
1440 FOR J=1 TO N1
1450 HZ(I,J)=Z1(I,J)
1460 NEXT J: NEXT I
1470 REM ========== Avaliacao do sistema de equacoes sobre o circulo unitario
1475 COLOR 15: PRINT: INPUT"Raio do circulo de interpolacao: ",R
1480 PRINT: PRINT"Calculando...";
1490 FOR L=0 TO G/2: PRINT G/2-L;
1500 R1=R^(-1/F0): Z=DPI*L/G/F0: Z1=R1*COS(Z): Z2=-R1*SIN(Z)
1510 REM ========== Montagem do sistema de equacoes
1520 FOR I=1 TO N
1530 FOR J=1 TO N1
1540 Z1(I,J)=HZ(I,J)
1550 Z2(I,J)=0.0
1560 NEXT J: NEXT I
1570 FOR F=1 TO F0
1580 K=N+F
1590 IF F<F0 THEN A=F+1 ELSE A=1
1600 FOR I=L1(A) TO L2(A)
1610 D=Z1(I,K)*Z1-Z2(I,K)*Z2: Z2(I,K)=Z1(I,K)*Z2+Z1*Z2(I,K): Z1(I,K)=D
1620 FOR J=C1(F) TO C2(F)
1630 D=Z1(I,J)*Z1-Z2(I,J)*Z2: Z2(I,J)=Z1(I,J)*Z2+Z1*Z2(I,J): Z1(I,J)=D
1640 NEXT J: NEXT I: NEXT F
1650 REM ========== Resolucao do sistemas de equacoes
1660 R1=R^(INT(N/F0)): D=F0*Z*INT(N/F0): D1=R1*COS(D): D2=R1*SIN(D)
1670 FOR I=1 TO N
1680 T1=0: T2=0: U=I
1690 FOR K=I TO N
1700 IF ABS(Z1(K,I))+ABS(Z2(K,I))>ABS(T1)+ABS(T2) THEN U=K: T1=Z1(K,I): T2=Z2(K,I)
1710 NEXT K
1720 IF I=U THEN 1780
1730 D1=-D1: D2=-D2
1740 FOR K=I TO N1
1750 D=Z1(I,K): Z1(I,K)=Z1(U,K): Z1(U,K)=D
1760 D=Z2(I,K): Z2(I,K)=Z2(U,K): Z2(U,K)=D
1770 NEXT K
1780 D=D1*T1-D2*T2: D2=D1*T2+D2*T1: D1=D
1790 FOR J=N1 TO I+1 STEP -1
1800 D=T1*T1+T2*T2
1810 IF ABS(D)<1E-28 THEN PRINT "Solucao impossivel; polo sobre o circulo de raio";R;"ou elemento suspenso.": STOP
1820 P=(Z1(I,J)*T1+Z2(I,J)*T2)/D
1830 P2=(Z2(I,J)*T1-Z1(I,J)*T2)/D: Z2(I,J)=P2
1840 P1=P: Z1(I,J)=P
1850 FOR K=1 TO N
1860 IF I=K THEN 1890
1870 Z1(K,J)=Z1(K,J)-(Z1(K,I)*P1-Z2(K,I)*P2)
1880 Z2(K,J)=Z2(K,J)-(Z1(K,I)*P2+Z2(K,I)*P1)
1890 NEXT K: NEXT J: NEXT I
1900 REM ========== Guardar resultados
1910 D1(L)=D1: D2(L)=D2
1920 REM ========== Correcao para transferencias cruzadas
1930 FOR F=1 TO F0
1940 K=N+F
1950 FOR I=1 TO F0
1960 IF I=F THEN 2020
1970 R1=R^(-((F-I+F0) MOD F0)/F0): D=-Z*((F-I+F0) MOD F0)
1980 T1=R1*COS(D): T2=R1*SIN(D)
1990 FOR J=L1(I) TO L2(I)
2000 D=Z1(J,K)*T1-Z2(J,K)*T2: Z2(J,K)=Z1(J,K)*T2+T1*Z2(J,K): Z1(J,K)=D
2010 NEXT J
2020 NEXT I: NEXT F
2030 FOR I=1 TO N
2040 FOR F=1 TO F0
2050 J=(I-1)*F0+F-1: K=N+F
2060 E1(J,L)=Z1(I,K)*D1-Z2(I,K)*D2: E2(J,L)=Z1(I,K)*D2+D1*Z2(I,K)
2070 NEXT F: NEXT I: NEXT L
2080 REM ========== Calculo do denominador
2090 PRINT: COLOR 15: PRINT: PRINT"Denominador:": COLOR 7
2100 FOR I=0 TO G/2
2110 L=(G-I)
2120 X(I)=D1(I): X(L)=D1(I)
2130 Y(I)=D2(I): Y(L)=-D2(I)
2140 NEXT I
2150 P=0: V=0: GOSUB 2330
2160 REM ========== Calculo dos numeradores
2170 COLOR 15: PRINT: INPUT"No de saida: ",W: COLOR 7
2180 IF W>N0 OR W<1 THEN 2170
2190 FOR A=1 TO F0
2200 A2=C(W+N0*(A-1))
2210 IF A2=0 THEN PRINT"V";STR$(W);STR$(A);" e' trivial": GOTO 2310
2220 FOR B=1 TO F0
2230 FOR I=0 TO G/2
2240 L=(G-I): J=(A2-1)*F0+B-1
2250 X(L)=E1(J,I): X(I)=E1(J,I)
2260 Y(L)=-E2(J,I): Y(I)=E2(J,I)
2270 NEXT I
2280 PRINT: COLOR 15: PRINT"Numerador de V";STR$(W);"(";STR$(A);")/Vin(";STR$(B);"):": COLOR 7
2290 P=((B-A+F0) MOD F0)/F0: GOSUB 2330
2300 NEXT B
2310 NEXT A
2315 COLOR 15: PRINT: INPUT"Outra saida? (s/n) ",N$
2320 IF N$="S" OR N$="s" THEN 2170
2325 STOP
2330 REM ========== Algoritmo FFT
2340 FOR K=M-1 TO 0 STEP -1
2350 A1=2^K
2360 FOR L=0 TO G-1 STEP 2*A1
2370 X=L/A1: GOSUB 2770
2380 X1=COS(DPI*S/G): Y1=-SIN(DPI*S/G)
2390 FOR J=0 TO A1-1
2400 U=J+L: S=U+A1
2410 X2=X(S)*X1-Y(S)*Y1: X3=X(S)*Y1+Y(S)*X1
2420 X(U)=X(U)+X2: Y(U)=Y(U)+X3
2430 X(S)=X(U)-X2-X2
2440 Y(S)=Y(U)-X3-X3
2450 NEXT J: NEXT L: NEXT K
2460 FOR I=0 TO G-1
2470 X=I: GOSUB 2770
2480 IF S<=I THEN 2520
2490 X3=X(I): Y3=Y(I)
2500 X(I)=X(S): Y(I)=Y(S)
2510 X(S)=X3: Y(S)=Y3
2520 NEXT I
2530 REM ========== Apresentacao de resultados
2540 S=0: K=0: X1=0
2550 FOR I=0 TO G-1
2560 X(I)=X(I)/G
2570 IF ABS(X(I))>X1 THEN X1=ABS(X(I))
2580 NEXT I
2590 X1=X1*.000001
2600 FOR I=G-1 TO 0 STEP -1
2610 IF ABS(X(I))>X1 AND S=0 THEN S=1: K=I
2620 IF ABS(X(I))>X1 THEN PRINT"Z^(";I+P;"):";X(I)/X(K)*R^(K-I)
2630 NEXT I
2640 IF S=0 THEN PRINT "Zero": RETURN
2650 IF V=0 THEN V=X(K)/R^K ELSE PRINT "Cte. de ganho=";X(K)/(V*R^K)
2660 INPUT"Guardar o polinomio? [nome do arquivo ou 'n'] (n) ",N$
2670 IF N$="" OR N$="n" OR N$="N" THEN RETURN
2680 OPEN "O",#2,N$: WRITE #2,K
2690 INPUT"Guardar desnormalizado? [s/n] (s) ";N$
2700 IF N$="N" OR N$="n" THEN 2730
2710 FOR I=0 TO K: WRITE #2,X(I)/V/R^I: NEXT I
2720 WRITE #2,1,P: GOTO 2750
2730 FOR I=0 TO K: WRITE #2,X(I)/X(K)*R^(K-I): NEXT I
2740 WRITE #2,X(K)/(V*R^K),P
2750 CLOSE #2: RETURN
2760 REM ========== Bit inverso para FFT
2770 S=0
2780 B1=G/2
2790 D=X/2
2800 IF D-INT(D)<>0 THEN S=S+B1
2810 B1=B1/2
2820 X=INT(D)
2830 IF X<>0 THEN 2790
2840 RETURN
