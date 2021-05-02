10 KEY OFF
20 DEFDBL A-Z
30 DEFINT I,J,L,A,N,M,C,B,E,S
40 DIM H(20,41)
50 CLS
60 PRINT"An lise de Amplificadores"
70 PRINT STRING$(25,"-")
80 PRINT"Ant“nio Carlos M. de Queiroz - UFRJ/1986"
90 'PRINT"Vers„o 1.0 de 16/04/86"
100 'PRINT"Vers„o 1.1 de 02/09/88"
110 PRINT"Vers„o 1.2 de 11/10/88"
120 PRINT
130 REM ===== Entrada do arquivo de descri‡„o
140 INPUT"Arquivo de entrada: (.RED) ou ? ", N$
150 IF N$="?" THEN GOSUB 990: GOTO 140
160 N$=N$+".RED"
170 OPEN N$ FOR INPUT AS #1
180 REM ===== Leitura da descri‡„o e montagem do sistema nodal
190 INPUT#1,N
200 PRINT: PRINT "N¢s=";N: M=2*N+1
210 FOR I=0 TO N: FOR J=0 TO M: H(I,J)=0: NEXT J: NEXT I 'Zera o sistema
220 FOR I=1 TO N: H(I,N+1+I)=1: NEXT I 'Monta uma identidade ao lado
230 IF EOF(1) THEN CLOSE #1: GOTO 680
240 INPUT#1,T$
250 ON INSTR("RQFGI",LEFT$(T$,1))+1 GOSUB 270,290,560,440,370,520
260 GOTO 230
270 PRINT "Erro na descri‡„o: ";T$: END
280 REM ===== Resistor
290 INPUT#1,N1,N2,R: G=1/R
300 PRINT T$;" r=";R;"Ohms, entre";N1;"e";N2
310 H(N1,N1)=H(N1,N1)+G
320 H(N2,N2)=H(N2,N2)+G
330 H(N1,N2)=H(N1,N2)-G
340 H(N2,N1)=H(N2,N1)-G
350 RETURN
360 REM ===== Fonte de corrente controlada a tens„o
370 INPUT#1,N1,N2,N3,N4,G: PRINT T$;" gm=";G;"Mhos, entre";N1;"(v+),";N2;"(v-),";N3;"(i+) e";N4;"(i-)"
380 H(N3,N1)=H(N3,N1)+G
390 H(N4,N2)=H(N4,N2)+G
400 H(N3,N2)=H(N3,N2)-G
410 H(N4,N1)=H(N4,N1)-G
420 RETURN
430 REM ===== Fonte de tens„o com resistor em s‚rie
440 INPUT#1,N1,N2,R,V: GOTO 450
450 PRINT T$;" v=";V;"Volts, rs=";R;"Ohms, entre";N1;"(v-) e";N2;"(v+)"
460 G=1/R: GOSUB 310
470 X=V/R
480 H(N1,N+1)=H(N1,N+1)-X
490 H(N2,N+1)=H(N2,N+1)+X
500 RETURN
510 REM ===== Fonte de corrente
520 INPUT#1,N1,N2,X
530 PRINT T$;" i=";X;"Amperes entre";N1;"(i+) e";N2;"(i-)"
540 GOSUB 480: RETURN
550 REM ===== Transistor bipolar - modelo h completo
560 INPUT#1,C,B,E,S,H1,H2,H3,H4,V ' Transistor: c,b,e,s,hfe,hie,hre,hoe,vbe
570 PRINT T$;" hfe=";H1;",hie=";H2;"Ohms ,hre=";H3;",hoe=";H4;"Mhos"
580 PRINT" Vbe=";V;"Volts, entre";C;"(c),";B;"(b),";E;"(e) e";S;"(s)"
590 G=1/H2: N1=B: N2=E: GOSUB 310 ' hie
600 G=H4: N1=C: N2=E: GOSUB 310 ' hoe
610 G=H1/H2: N1=B: N2=E: N3=C: N4=E: GOSUB 380 ' hfe/hie
620 G=H3/H2: N1=C: N2=E: N3=E: N4=B: GOSUB 380 ' hre/hie
630 G=H3*H1/H2: N1=E: N2=C: N3=C: N4=E: GOSUB 380 ' hre*hfe/hie
640 X=V/H2: N1=E: N2=B: GOSUB 480 ' vbe/hie
650 X=H1*V/H2: N1=E: N2=C: GOSUB 480 ' hfe*vbe/hie
660 RETURN
670 REM ===== Resolu‡„o do sistema com invers„o da matriz Yn (H)
680 PRINT: PRINT "Resolvendo...";CHR$(13);
690 FOR I=1 TO N
700 T=0: A=I
710 FOR L=I TO N
720 IF ABS(H(L,I))>ABS(T) THEN A=L: T=H(L,I)
730 NEXT L
740 IF I=A THEN 780
750 FOR L=I TO M
760 P=H(I,L): H(I,L)=H(A,L): H(A,L)=P
770 NEXT L
780 IF ABS(T)<1E-10 THEN PRINT: PRINT"Matriz singular": STOP
790 FOR J=M TO I+1 STEP -1
800 H(I,J)=H(I,J)/T: P=H(I,J)
810 FOR L=1 TO N
820 IF I=L THEN 840
830 H(L,J)=H(L,J)-H(L,I)*P
840 NEXT L: NEXT J: NEXT I
850 REM ===== Apresenta‡„o dos resultados
860 PRINT: PRINT"[I]mpedƒncias [T]ens”es [R]ein¡cio [F]im"
870 ON INSTR("TtIiFfRr",INPUT$(1))+1 GOTO 870,880,880,930,930,1240,1240,50,50
880 PRINT "Tens”es nodais:" 'As solu‡”es do sistema nodal
890 FOR I=1 TO N
900 PRINT "V";I;":";H(I,N+1)
910 NEXT I
920 GOTO 860
930 PRINT "Impedƒncias nodais:" 'A diagonal da inversa de Yn
940 FOR I=1 TO N
950 PRINT "Z";I;":";H(I,N+1+I)
960 NEXT I
970 GOTO 860
980 REM ===== Instru‡”es
990 CLS
1000 PRINT"Instru‡”es:"
1010 PRINT"Este programa calcula tens”es e impedƒncias de n¢, em CC ou CA, para circuitos"
1020 PRINT"compostos de transistores bipolares linearizados e outros componentes resisti-"
1030 PRINT"vos. O circuito a analisar ‚ descrito em arquivo no formato:"
1040 PRINT
1050 PRINT"1a. linha: No. de n¢s (exceto o terra, n¢ 0)"
1060 PRINT"Linhas seguintes: Uma descri‡„o de componente por linha:"
1070 PRINT" - Resistor: R<nome>,<n¢1>,<n¢2>,<resistˆncia em Ohms>"
1080 PRINT" - Fonte de corrente: I<nome>,<n¢I+>,<n¢I->,<corrente em Amperes>"
1090 PRINT" - Fonte de tens„o: F<nome>,<n¢V->,<n¢V+>,<rs‚rie em Ohms>,<tens„o em Volts>"
1100 PRINT" - Fonte de corrente controlada a tens„o:"
1110 PRINT"   G<nome>,<n¢V+>,<n¢V-><n¢I+>,<n¢I->,<transcondutƒncia (Gm) em Mhos>"
1120 PRINT" - Transistor: Q<nome>,<n¢Coletor>,<n¢Base>,<n¢Emissor>,<n¢Substrato>,"
1130 PRINT"   <hfe>,<hie>,<hre>,<hoe>,<vbe>"
1140 PRINT
1150 PRINT"-O arquivo pode ser gerado pelo programa EdFil."
1160 PRINT"-No EdFil, use ',' como caracter separador na lista (comando Ctrl-S)."
1170 PRINT"-O n¢ de substrato e ignorado. Coloque zero (terra no EdFil)."
1180 PRINT"-Fontes de tens„o devem possuir resistor em s‚rie n„o nulo."
1190 PRINT"-Correntes saem pelo n¢ I-."
1200 PRINT"-Para an lise CA, zere as fontes constantes e os vbes."
1210 PRINT"-Transistores PNP devem possuir vbe negativo."
1220 PRINT
1230 RETURN
1240 END
