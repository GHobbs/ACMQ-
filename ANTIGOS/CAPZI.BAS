10 REM *************************************************************************
20 REM * Calculo de f. de t. de filtros a capacitor chaveado de duas fases     *
30 REM * Autor: Antonio Carlos Moreirao de Queiroz - COPPE/UFRJ - 1984         *
40 REM * Versao 2.6 de 14/06/1985 Versao colorida                              *
50 REM * Versao 2.7 de 15/07/1985 Correcao de format amp op                    *
55 REM * Versao 2.8 de 18/11/1985 Incluido raio variavel                       *
56 REM * Versao 2.9 de 30/06/1988 Saida sem break, pequenas alteracoes         *
57 REM * Versao 3.0 de 13/08/1988 Mudancas no formato de entrada               *
58 REM * Versao 3.1 de 12/09/1988 Correcoes                                    *
59 REM * Versao 3.2 de 30/05/1989 Adaptacao ao novo EdFil. (P deve ser mudado) *
70 REM *************************************************************************
80 DEFDBL D,V,T,P,X,Y,Z,E,O,R
90 DEFINT A,B,C,F,I,J,K,L,G,M,N,S,U,W
100 DIM Z(40,42),C(60),L(60),Z1(40,42),Z2(40,42),E1(39,16),E2(39,16),O1(39,16),O2(39,16),X(31),Y(31),D1(16),D2(16)
110 NMAX=40: OMAX=40: GMAX=32: DISP=1E+06
120 SCREEN 0: WIDTH 80: COLOR 15
130 PRINT"FUNCOES DE TRANSFERENCIA DE FILTROS A CAPACITOR CHAVEADO DE 2 FASES"
140 COLOR 7: PRINT"-------------------------------------------------------------------"
150 PRINT"Antonio Carlos Moreirao de Queiroz - COPPE/UFRJ - 1984 - Versao 3.2": PRINT
160 COLOR 15: INPUT"Nome do arquivo com a descricao do circuito ou '?': ",N$
170 IF N$<>"?" THEN 360
180 CLS: COLOR 15: PRINT"INSTRUCOES PARA O USO DO PROGRAMA 'CAPZ':"
190 COLOR 7: PRINT"-----------------------------------------"
195 PRINT
200 PRINT"Crie, usando um editor, um arquivo ASCII contendo os seguintes dados:"
210 PRINT
215 PRINT"Primeira linha: Numero de nos do circuito (terra=0)."
220 PRINT"Nas linhas seguintes, a descricao dos elementos, um por linha:"
225 PRINT
230 PRINT"   Capacitor:        C<nome>,<no>,<no>,<valor>"
240 PRINT"   Chave simples:    S<nome>,<no>,<no>,<fase>"
250 PRINT"   Chave dupla:      P<nome>,<no1>,<no2>,<no polo, ligado em 'e'>"
260 PRINT"   Amp. operacional: O<nome>,<no>,<no>,<no saida>"
270 PRINT"   Fonte de sinal:   V<nome>,<no +>,<no ->,<valor>"
280 PRINT
285 PRINT"- A(s) fonte(s) de sinal devem vir por ultimo, e <no -> deve ser 0 p/elas."
287 PRINT"- <fase> deve valer 'e'(even) ou 'o'(odd), fase em que a chave esta ligada."
290 PRINT"- Salve os polinomios encontrados se desejar encontrar suas raizes posterior-"
300 PRINT"  mente ou plotar um grafico da resposta em frequencia com o programa `GRAF'."
310 PRINT"- O programa calculara as funcoes de transferencia em Z da(s) entrada(s) para"
320 PRINT"  qualquer no da rede (transferencias triviais serao indicadas, se pedidas)."
330 PRINT"- Use o raio de interpolacao diferente de 1 somente quando o circuito possuir"
340 PRINT"  frequencias naturais sobre o circulo unitario.": PRINT
350 GOTO 160
360 OPEN "I",1,N$
370 INPUT #1,N0
380 PRINT: COLOR 15: PRINT"O circuito possui";N0;"nos": PRINT
390 IF N0>NMAX THEN PRINT"O numero maximo de nos e",NMAX,". Execucao interrompida.": STOP
400 N=2*N0: N2=N: M0=N0+1: M1=N0+2: DPI=6.283185307179601#: COLOR 7
410 FOR I=0 TO N2: C(I)=I: L(I)=I: NEXT I
420 IF NOT EOF(1) THEN INPUT #1,N$,A,B,T$ ELSE 990
425 T$=UCASE$(T$)
430 ON INSTR("CcSsVvOoPp",LEFT$(N$,1))+1 GOSUB 450,460,460,540,540,750,750,870,870,940,940
440 GOTO 420
450 COLOR 15: PRINT"Elemento nao reconhecido: ";N$: STOP: RETURN
460 REM ========== Capacitor
470 V=VAL(T$)
480 PRINT"Capacitor ";N$;" de";V;"F entre";A;"e";B
490 Z(A,A)=Z(A,A)+V
500 Z(B,B)=Z(B,B)+V
510 Z(A,B)=Z(A,B)-V
520 Z(B,A)=Z(B,A)-V
530 RETURN
540 REM ========== Chave
545 IF T$<>"O" AND T$<>"E" THEN 450
550 V=-(T$="O")
560 PRINT"Chave ";N$;" na fase ";T$;" entre";A;"e";B;TAB(50);CHR$(205)+CHR$(16);" V";A;T$;" = V";B;T$
570 GOSUB 580: GOSUB 680: RETURN
580 IF A<>0 THEN A=A+V*N0
590 IF B<>0 THEN B=B+V*N0
600 IF C(A)<C(B) THEN A1=C(A): B1=C(B) ELSE A1=C(B): B1=C(A)
610 IF A1=B1 THEN 670
620 FOR I=1 TO N2
630 IF C(I)=B1 THEN C(I)=A1
640 IF C(I)>B1 THEN C(I)=C(I)-1
650 NEXT I
660 N=N-1: RETURN
670 COLOR 15: PRINT"Circuito proibido (curto-circuito); verifique a descricao.";CHR$(7): STOP
680 IF L(A)<L(B) THEN A1=L(A): B1=L(B) ELSE A1=L(B): B1=L(A)
690 IF A1=B1 THEN 670
700 FOR I=1 TO N2
710 IF L(I)=B1 THEN L(I)=A1
720 IF L(I)>B1 THEN L(I)=L(I)-1
730 NEXT I
740 RETURN
750 REM ========== Fonte independente
760 PRINT "Fonte ";N$;" de ";T$;" V entre";A;"(+) e";B;"(-)";TAB(50);CHR$(205)+CHR$(16);" V";A;"* = V";B;"* +";T$;"Vin *"
770 V=VAL(T$): B1=A+N0
780 IF B<>0 THEN PRINT"Somente fontes aterradas sao permitidas";CHR$(7): STOP
790 FOR I=1 TO N0
800 FOR J=1 TO N0
810 IF C(J)=C(A) THEN Z(I,M0)=Z(I,M0)-V*Z(I,J)
820 IF C(J+N0)=C(B1) THEN Z(I,M1)=Z(I,M1)-V*Z(I,J)
830 NEXT J,I
840 V=0: GOSUB 570
850 V=1: GOSUB 570
860 RETURN
870 REM ========== Amplificador operacional
880 PRINT "Amp. Op. ";N$;A;"(1),";B;"(2) e ";T$;" (saida)";TAB(50);CHR$(205);CHR$(16);" V";A;"* = V";B;"*"
890 V=0: GOSUB 580
900 V=1: GOSUB 580
910 A=VAL(T$): B=0: GOSUB 680
920 A=A+N0: GOSUB 680
930 RETURN
940 REM ========== Chave dupla
950 S=VAL(T$): S1=B
960 T$="E": B=S: GOSUB 540
970 T$="O": A=S: B=S1: GOSUB 540
980 RETURN
990 REM ========== Fim dos dados
1000 G=1: M2=N+1: M3=N+2: M=0
1010 IF G<=N/2 THEN G=G*2: M=M+1: GOTO 1010
1020 F=0
1030 FOR I=1 TO N0
1040 IF F<C(I) THEN F=C(I)
1050 NEXT I
1060 COLOR 15: PRINT: PRINT"Ordem do sistema:";N;"x";M3;"; Grau para FFT:";G
1070 IF N>OMAX THEN PRINT"Ordem excessiva. O maximo e de",OMAX,". Execucao interrompida": STOP
1080 IF G>GMAX THEN PRINT"Grau excessivo. O maximo e de",GMAX,". Execucao interrompida": STOP
1090 REM ========== Reducao do sistema de equacoes
1100 FOR I=1 TO N0
1110 A=L(I): A1=L(I+N0)
1120 Z1(A,M2)=Z1(A,M2)+Z(I,M0)
1130 Z1(A,M3)=Z1(A,M3)-Z(I,M1)
1140 Z1(A1,M2)=Z1(A1,M2)-Z(I,M0)
1150 Z1(A1,M3)=Z1(A1,M3)+Z(I,M1)
1160 FOR J=1 TO N0
1170 B=C(J): B1=C(J+N0)
1180 Z1(A,B)=Z1(A,B)+Z(I,J)
1190 Z1(A1,B1)=Z1(A1,B1)+Z(I,J)
1200 Z1(A,B1)=Z1(A,B1)-Z(I,J)
1210 Z1(A1,B)=Z1(A1,B)-Z(I,J)
1220 NEXT J: NEXT I
1230 FOR I=1 TO N
1240 FOR J=1 TO M3
1250 Z(I,J)=Z1(I,J)
1260 NEXT J: NEXT I
1270 REM ========== Avaliacao do sistema de equacoes
1275 COLOR 15: PRINT: INPUT"Raio do circulo de interpolacao: ",R
1280 PRINT: PRINT"Calculando...";
1290 FOR L=0 TO G/2: PRINT G/2-L;
1300 Z=3.141592653589796#*L/G: R1=1/SQR(R): Z1=R1*COS(Z): Z2=-R1*SIN(Z)
1310 REM ========== Montagem do sistema de equacoes
1320 FOR I=1 TO N
1330 IF I>F THEN B=M2: A=M3 ELSE B=M3: A=M2
1340 Z1(I,B)=Z1*Z(I,B): Z2(I,B)=Z2*Z(I,B)
1350 Z1(I,A)=Z(I,A): Z2(I,A)=0
1360 FOR J=1 TO N
1370 IF NOT(I>F EQV J>F) THEN Z1(I,J)=Z1*Z(I,J): Z2(I,J)=Z2*Z(I,J): GOTO 1390
1380 Z1(I,J)=Z(I,J): Z2(I,J)=0
1390 NEXT J,I
1400 REM ========== Resolucao do sistemas de equacoes
1410 D=2*Z*INT(N/2): R1=R^(INT(N/2)): D1=R1*COS(D): D2=R1*SIN(D)
1420 FOR I=1 TO N
1430 T1=0: T2=0: U=I
1440 FOR K=I TO N
1450 IF ABS(Z1(K,I))+ABS(Z2(K,I))>ABS(T1)+ABS(T2) THEN U=K: T1=Z1(K,I): T2=Z2(K,I)
1460 NEXT K
1470 IF I=U THEN 1530
1480 D1=-D1: D2=-D2
1490 FOR K=I TO M3
1500 D=Z1(I,K): Z1(I,K)=Z1(U,K): Z1(U,K)=D
1510 D=Z2(I,K): Z2(I,K)=Z2(U,K): Z2(U,K)=D
1520 NEXT K
1530 D=D1*T1-D2*T2: D2=D1*T2+D2*T1: D1=D
1540 FOR J=M3 TO I+1 STEP -1
1550 D=T1*T1+T2*T2
1560 IF ABS(D)<1E-10 THEN PRINT: PRINT "Solucao impossivel; polo sobre o circulo de raio";R;"ou elemento suspenso.": STOP
1570 P=(Z1(I,J)*T1+Z2(I,J)*T2)/D
1580 P2=(Z2(I,J)*T1-Z1(I,J)*T2)/D: Z2(I,J)=P2
1590 P1=P: Z1(I,J)=P
1600 FOR K=1 TO N
1610 IF I=K THEN 1640
1620 Z1(K,J)=Z1(K,J)-(Z1(K,I)*P1-Z2(K,I)*P2)
1630 Z2(K,J)=Z2(K,J)-(Z1(K,I)*P2+Z2(K,I)*P1)
1640 NEXT K: NEXT J: NEXT I
1650 REM ========== Guardar resultados
1660 D1(L)=D1: D2(L)=D2
1670 FOR I=1 TO N
1680 K=I-1
1690 E1(K,L)=Z1(I,M2)*D1-Z2(I,M2)*D2: E2(K,L)=Z1(I,M2)*D2+Z2(I,M2)*D1
1700 O1(K,L)=Z1(I,M3)*D1-Z2(I,M3)*D2: O2(K,L)=Z1(I,M3)*D2+Z2(I,M3)*D1
1710 REM ========== Correcao e/o o/e
1720 IF I>F THEN D=E1(K,L)*Z1-E2(K,L)*Z2: E2(K,L)=E1(K,L)*Z2+E2(K,L)*Z1: E1(K,L)=D
1730 IF I<=F THEN D=O1(K,L)*Z1-O2(K,L)*Z2: O2(K,L)=O1(K,L)*Z2+O2(K,L)*Z1: O1(K,L)=D
1740 NEXT I,L
1750 REM ========== Calculo do denominador
1760 PRINT: PRINT: PRINT"Denominador:"
1770 FOR I=0 TO G/2
1780 L=(G-I) MOD G
1790 X(I)=D1(I): X(L)=D1(I)
1800 Y(I)=D2(I): Y(L)=-D2(I)
1810 NEXT I
1820 P=0: V=0: GOSUB 2000
1830 REM ========== Calculo dos numeradores
1840 COLOR 15: PRINT: INPUT"No, fase de saida, fase de entrada: ",W,N$,T$
1850 IF W>N0 OR W<1 THEN 1910
1860 ON INSTR("eo",N$)+1 GOTO 1910,1870,1880
1870 Y=C(W)-1: GOTO 1890
1880 Y=C(W+N0)-1
1890 IF Y=-1 THEN COLOR 7: PRINT"V";STR$(W);N$;" e' trivial": GOTO 1840
1900 IF T$="e" OR T$="o" THEN 1920
1910 COLOR 7: PRINT"Transferencia inexistente ou invalida.": GOTO 1840
1920 FOR I=0 TO G/2
1930 L=(G-I) MOD G
1940 IF T$="e" THEN P1=E1(Y,I): P2=E2(Y,I) ELSE P1=O1(Y,I): P2=O2(Y,I)
1950 X(L)=P1: X(I)=P1: Y(L)=-P2: Y(I)=P2
1960 NEXT I
1970 PRINT"Numerador de V";STR$(W);N$;"/vin";T$;":"
1980 P=-(N$<>T$)/2: GOSUB 2000
1985 COLOR 7: PRINT: INPUT"Outra transferencia? [s/n] (n) ",N$
1990 IF N$="S" OR N$="s" THEN GOTO 1840
1995 STOP
2000 REM ========== Algoritmo FFT
2010 FOR K=M-1 TO 0 STEP -1
2020 K1=2^K
2030 FOR L=0 TO G-1 STEP 2*K1
2040 X=L/K1: GOSUB 2400
2050 X1=COS(DPI*S/G): Y1=-SIN(DPI*S/G)
2060 FOR J=0 TO K1-1
2070 U=J+L: S=U+K1
2080 X2=X(S)*X1-Y(S)*Y1: X3=X(S)*Y1+Y(S)*X1
2090 X(U)=X(U)+X2: Y(U)=Y(U)+X3
2100 X(S)=X(U)-X2-X2
2110 Y(S)=Y(U)-X3-X3
2120 NEXT J: NEXT L: NEXT K
2130 FOR I=0 TO G-1
2140 X=I: GOSUB 2400
2150 IF S<=I THEN 2190
2160 X3=X(I): Y3=Y(I)
2170 X(I)=X(S): Y(I)=Y(S)
2180 X(S)=X3: Y(S)=Y3
2190 NEXT I
2200 REM ========== Apresentacao de resultados
2210 S=0: K=0: X1=0: COLOR 7
2220 FOR I=0 TO G-1
2230 X(I)=X(I)/G
2240 IF ABS(X(I))>X1 THEN X1=ABS(X(I))
2250 NEXT I
2260 X1=X1/DISP
2270 FOR I=G-1 TO 0 STEP -1
2280 IF ABS(X(I))>X1 AND S=0 THEN S=1: K=I
2290 IF ABS(X(I))>X1 THEN PRINT"z^(";I+P;"):";X(I)/X(K)*R^(K-I)
2300 NEXT I
2310 IF S=0 THEN PRINT "Zero": RETURN
2320 IF V=0 THEN V=X(K)/R^K ELSE PRINT "Cte. multiplicativa:";X(K)/(V*R^K)
2330 INPUT"Guardar o polinomio? (nome do arquivo ou CR) ",N$
2340 IF N$="" THEN RETURN
2350 OPEN "O",#2,N$: WRITE #2,K
2360 FOR I=0 TO K: WRITE #2,X(I)/X(K)*R^(K-I): NEXT I
2370 WRITE #2,X(K)/(V*R^K),P
2380 CLOSE #2: RETURN
2390 REM ========== Bit inverso para FFT
2400 S=0
2410 A=G/2
2420 D=X/2
2430 IF D-INT(D)<>0 THEN S=S+A
2440 A=A/2
2450 X=INT(D)
2460 IF X<>0 THEN 2420
2470 RETURN
