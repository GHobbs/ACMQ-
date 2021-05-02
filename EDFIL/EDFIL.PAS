PROGRAM Edfil;
{**************************************************************
 * Editor de filtros                                          *
 * Ant“nio Carlos Moreir„o de Queiroz                         *
 * V. 1.0 de 27/10/87                                         *
 * V. 1.1 de 06/11/87                                         *
 * V. 1.2 de 13/11/87  Sa¡da mais r pida                      *
 * V. 1.3 de 17/11/87  128x128 n¢s                            *
 * V. 1.4 de 26/11/87  Mudadas perguntas                      *
 * V. 1.5 de 13/01/88  Pontos mantidos                        *
 * V. 1.6 de 22/01/88  Ordena‡„o e opera‡”es com valores      *
 * V. 1.7 de 09/04/88  Inclu¡do transistor                    *
 * V. 1.8 de 30/04/88  Inclu¡do X, mudados nomes, ^N          *
 * V. 1.9 de 17/05/88  ^Y, Nomes com 4 caracteres             *
 * V. 2.0 de 26/05/88  Nova avalia‡„o de express”es           *
 * V. 2.1 de 31/08/88  Parƒmetros em string, novos elementos  *
 * V. 2.2 de 03/09/88  Plotagem de n¢s, edi‡„o de parƒmetros  *
 * V. 2.3 de 01/10/88  Sem "fantasmas", sem help c/parƒmetro  *
 * V. 2.4 de 22/10/88  Saida com ESC de ^X, novos default     *
 * V. 2.5 de 08/11/88  Mudadaos LT e URC, edi‡„o de tudo      *
 * V. 2.5b de 09/01/89 Vers„o para turbo 5.0                  *
 * V. 2.6 de 20/01/89  Incluido OTA simples (g) e auto-pan    *
 * V. 2.7 de 08/03/89  Execu‡„o de programa, LT e URC 3 trm.  *
 * V. 2.7b de 03/06/89 Compativel com novo CAPZ               *
 * V. 2.7c de 07/06 89 Apaga tela ao executar                 *
 * V. 2.8 de 17/07/89  Rotinas Gr ficas do Turbo 5.0          *
 * V. 2.8a de 09/10/89 Turbo 5.5, atualiza‡„o                 *
 * V. 2.9 de 30/03/90  Atualiza‡„o, melhor avalia‡„o          *
 * V. 2.9a de 18/01/91 Novos defaults                         *
 * V. 3.0 de 19/01/91  De ac“rdo com a vers„o 3.0d do EdFil   *
 * V. 3.1 de 09/09/91  De ac“rdo com a vers„o 3.1 do EdFil    *
 * V. 3.1 de 29/02/92  Versao em Ingles, TPBGI                *
 * V. 3.2 de 22/10/92  Compativel com a versao 3.2 em Port.   *
 * V. 3.2a de 24/04/93 Melhor ^Y                              *
 * V. 3.2b de 15/06/93 Av no amplificador                     *
 * V. 3.3  de 25/09/93 Operacoes com blocos, etc.             *
 * V. 3.3a de 19/10/93 Dos, labels, escrita protegida         *
 * V. 3.3b de 18/01/94 Limitacao para blocos corrigida        *
 * V. 3.3c de 06/03/94 Ajustes nas coordenadas                *
 * V. 3.3d de 29/10/94 Label 0, Tentativa de listar nomes (^N)*
 * V. 3.3e de 26/07/98 Mudados parametros                     *
 * V. 3.4  de 05/03/01 Transformador com k, elementos em pe'  *
 * V. 3.4a de 03/10/02 Melhor diret¢rio, esc interrompe ^X    *
 * V. 3.5  de 25/07/03 Implementados coment rios.             *
 * V. 3.5a de 25/08/03 Ctrl-X corrigido, Espa‡o=Tab           *
 * V. 3.5b de 28/08/03 Implementados comandos "."             *
 * V. 3.6  de 29/08/03 Mudada avalia‡ao de f¢rmulas           *
 * V. 3.6a de 30/09/04 Ctrl-W corrigido, "writing"            *
 * V. 3.6b de 16/05/07 Salva comentarios e comandos           *
 * V. 3.7  de 30/10/08 Amp. op. com 4 terminais, "o"          *
 * V. 3.7a de 06/11/08 Amplificador com 4 terminais, "a"      *
 * V. 3.8  de 15/09/09 Capacitor controlado a tensao, "B"     *
 * V. 3.8a de 27/10/09 MOS com 4 terminais W. N e K alterados *
 * V. 3.9  de 25/01/10 Chave com controle $                   *
 * V. 4.0  de 19/08/11 Ota balanceado "#", Exp(), Log=Ln      *
 * V. 4.1  de 06/12/11 Elemento "&", multiplicador            *
 **************************************************************}
{$M $4000,$4000,$4000}
USES Dos,Crt,Graph,Tela_e;
CONST
  versao='4.1 de 06/12/11';
  sufdes='.cir'; {sufixos}
  sufnet='.net';
  sufval='.val';
  maxlista=700;  {Maximo numero de elementos}
  maxn=400;      {Maximo numero de nos}
  maxlv=200;     {Maximo numero de valores}
  maxnos=4;
  maxtipos=53;   {No. de tipos}
  curto=37;      {1o. "curto"}
  tnome=5;       {Tamanho m ximo de nome}
  tvalor=50;     {Tamanho m ximo de valor}
  tedit=56;      {Tamanho do buffer de edi‡„o}
  inserir:BOOLEAN=FALSE;
TYPE
  txtvalor=STRING[tvalor];
  txtedit=STRING[tedit];
  txtlongo=STRING[255];
  texto2=STRING[2];
  nos=ARRAY[1..maxnos] of INTEGER;
  elemento=
    RECORD
      tp:BYTE;
      grade,no:nos;
      nome:STRING[tnome];
      valor:txtvalor;
    END;
  descricao=
    RECORD
      tipo:CHAR;
      nnos:INTEGER;
      parametro,default:txtvalor;
      ds:ARRAY[0..15] of WORD;
    END;
  letras=SET of CHAR;
VAR
  lista:ARRAY[1..maxlista] of elemento;

  lv: ARRAY[1..maxlv] of
    RECORD
      codigo:STRING[tnome];
      valor:REAL
    END;
  texto,rede,prog,lisval,ulttxt:txtedit;
  arquivo:TEXT;
  interromper,mudado,nada,ok,vert,fim,outro,fora_o,fora_d,cp,haparam,salvarc,valido:BOOLEAN;
  ylinha,mptx,mpty,placa,modo,numnos,ne,nr,nx,nv,i,j,k,l,x,y,
  xmin,ymin,xmax,ymax,pxmax,pymax,no1,no2:INTEGER;
  s,r:CHAR;
  sufixo:STRING[4];

CONST
  biblioteca: ARRAY [1..maxtipos] of descricao=
    (
    (tipo:'R'; nnos:2; parametro:'Resistance'; default:'1';
     ds:($0000,$0080,$0080,$0080,
         $0080,$0300,$0080,$0060,
         $0080,$0300,$0080,$0060,
         $0080,$0080,$0080,$0080)),
    (tipo:'L'; nnos:2; parametro:'Inductance'; default:'1';
     ds:($0000,$0080,$0080,$00E0,
         $0010,$0010,$03D0,$0420,
         $0420,$03D0,$0010,$0010,
         $00E0,$0080,$0080,$0080)),
    (tipo:'C'; nnos:2; parametro:'Capacitance'; default:'1';
     ds:($0000,$0080,$0080,$0080,
         $0080,$0080,$03E0,$0000,
         $0000,$03E0,$0080,$0080,
         $0080,$0080,$0080,$0080)),
    (tipo:'N'; nnos:2; parametro:'v1 j1 v2 j2 v3 j3 v4 j4'; default:'-1000 0 0 0 0.6 1e-3 2 10';
     ds:($0000,$0080,$0080,$07F0,
         $0490,$0510,$0490,$0450,
         $0490,$0510,$0490,$0450,
         $0490,$07F0,$07F0,$0080)),
    (tipo:'K'; nnos:4; parametro:'Inductances L1 L2 k12 (or M12 M21)'; default:'1 1 0.9';
     ds:($0001,$8001,$8811,$8001,
         $F24F,$0A50,$0A50,$724E,
         $8A51,$724E,$0A50,$0A50,
         $F24F,$8001,$8001,$8001)),
    (tipo:'X'; nnos:2; parametro:'Reactance'; default:'1';
     ds:($0000,$0080,$0080,$0080,
         $07F0,$0410,$0410,$0410,
         $0410,$0410,$0410,$07F0,
         $0080,$0080,$0080,$0080)),
    (tipo:'G'; nnos:4; parametro:'Transconductance'; default:'1';
     ds:($0000,$8001,$FC11,$0439,
         $0A10,$1100,$2480,$4440,
         $9F20,$4E40,$2480,$1100,
         $0A00,$0439,$FC01,$8001)),
    (tipo:'g'; nnos:4; parametro:'Transconductance'; default:'1';
     ds:($0000,$0001,$0019,$0069,
         $0189,$0649,$04EF,$0448,
         $3C08,$2408,$24EF,$2609,
         $2189,$2069,$2019,$6001)),
    (tipo:'#'; nnos:4; parametro:'Gm Gc'; default:'1 0.1';
     ds:($0000,$8001,$803D,$83C5,
         $BC05,$A025,$E777,$2024,
         $2004,$2204,$E777,$A205,
         $BC05,$83C5,$803D,$8001)),
    (tipo:'&'; nnos:4; parametro:'Mult. gain'; default:'1';
     ds:($0000,$8001,$8FFD,$9005,
         $A105,$EB97,$2524,$2244,
         $2184,$2184,$2244,$2425,
         $EB97,$A005,$9005,$8FFD)),
    (tipo:'Q'; nnos:3; parametro:'hfe hie hre hoe'; default:'100 1 0 0';
     ds:($6003,$27F2,$280A,$1004,
         $283A,$4419,$4229,$4141,
         $5FFD,$4081,$2082,$1084,
         $0888,$07F0,$0080,$FF80)),
    (tipo:'q'; nnos:3; parametro:'hfe hie hre hoe'; default:'100 1 0 0';
     ds:($6003,$27F2,$280A,$1004,
         $282A,$4431,$4239,$4141,
         $5FFD,$4081,$2082,$1084,
         $0888,$07F0,$0080,$FF80)),
    (tipo:'M'; nnos:3; parametro:'Gm Gds'; default:'1 0';
     ds:($701F,$1010,$1010,$1010,
         $1010,$1010,$1038,$107C,
         $1010,$3FF8,$0000,$3FF8,
         $0100,$0100,$3F00,$4000)),
    (tipo:'m'; nnos:3; parametro:'Gm Gds'; default:'1 0';
     ds:($701F,$1010,$1010,$1010,
         $1010,$1010,$107C,$1038,
         $1010,$3FF8,$0000,$3FF8,
         $0100,$0100,$3F00,$4000)),
    (tipo:'W'; nnos:4; parametro:'NMOS L= W= K Vt0 Lambda Gama Fi'; default:'NMOS L=1e-6 W=1e-6 1e-4 1 0.01 0.3 0.6';
     ds:($701F,$1010,$1010,$1010,
         $11D6,$1112,$17D2,$1392,
         $1112,$3BBA,$0002,$3FFA,
         $0102,$0102,$3F02,$4001)),
    (tipo:'w'; nnos:4; parametro:'PMOS L= W= K Vt0 Lambda Gama Fi'; default:'PMOS L=1e-6 W=1e-6 1e-4 1 0.01 0.3 0.6';
     ds:($701F,$1010,$1010,$1010,
         $11D6,$1112,$1392,$17D2,
         $1112,$3BBA,$0002,$3FFA,
         $0102,$0102,$3F02,$4001)),
    (tipo:'J'; nnos:3; parametro:'Gm Gds'; default:'1 0';
     ds:($780F,$0808,$0808,$0808,
         $0808,$0808,$3FFE,$0080,
         $01C0,$03E0,$0080,$0080,
         $0080,$0080,$0080,$FF80)),
    (tipo:'j'; nnos:3; parametro:'Gm Gds'; default:'1 0';
     ds:($780F,$0808,$0808,$0808,
         $0808,$0808,$3FFE,$0080,
         $03E0,$01C0,$0080,$0080,
         $0080,$0080,$0080,$FF80)),
    (tipo:'A'; nnos:3; parametro:'GB Rout (or Av)'; default:'100 0.01';
     ds:($0001,$8001,$B001,$AC01,
         $A301,$A0C1,$EE31,$200D,
         $2003,$240C,$EE30,$A4C0,
         $A300,$AC00,$B000,$8000)),
    (tipo:'a'; nnos:4; parametro:'GB Rout (or Av)'; default:'100 0.01';
     ds:($0000,$8001,$800D,$8035,
         $80C7,$8304,$8C74,$B004,
         $C004,$3024,$0C74,$0324,
         $02C7,$0235,$020D,$FE01)),
    (tipo:'E'; nnos:4; parametro:'Av'; default:'1';
     ds:($0000,$8001,$FC11,$0439,
         $0A10,$1500,$2E80,$4440,
         $8020,$4040,$2E80,$1100,
         $0A00,$0439,$FC01,$8001)),
    (tipo:'F'; nnos:4; parametro:'Ai'; default:'1';
     ds:($8000,$8001,$FC07,$0404,
         $0A1F,$110E,$2484,$4444,
         $9F24,$4E44,$2484,$1104,
         $0A04,$0404,$FC07,$8001)),
    (tipo:'H'; nnos:4; parametro:'Rm'; default:'1';
     ds:($8000,$8001,$FC07,$0404,
         $0A1F,$150E,$2E84,$4444,
         $8024,$4044,$2E84,$1104,
         $0A04,$0404,$FC07,$8001)),
    (tipo:'B'; nnos:4; parametro:'C/v IC=Qinit'; default:'1';
     ds:($0000,$8001,$FC11,$0439,
         $0410,$0400,$0400,$3F80,
         $0000,$3F80,$0400,$0400,
         $0400,$0439,$FC01,$8001)),
    (tipo:'Y'; nnos:4; parametro:'Gyration resistance'; default:'1';
     ds:($0001,$8001,$8001,$8001,
         $8081,$F3CF,$8891,$8421,
         $8421,$8421,$8811,$F00F,
         $8001,$8001,$8001,$8001)),
    (tipo:'S'; nnos:2; parametro:'Phase(s)'; default:'1';
     ds:($0000,$0080,$0080,$0080,
         $0080,$0040,$0020,$0014,
         $000C,$001C,$0000,$0080,
         $0080,$0080,$0080,$0080)),
    (tipo:'s'; nnos:2; parametro:'Phase(s)'; default:'2';
     ds:($0000,$0080,$0080,$0080,
         $0080,$0050,$0020,$0054,
         $000C,$001C,$0000,$0080,
         $0080,$0080,$0080,$0080)),
    (tipo:'$'; nnos:4; parametro:'Gon Goff Vref'; default:'1 0 1';
     ds:($0000,$8001,$FC11,$0439,
         $0410,$0400,$0200,$0100,
         $00A0,$0060,$00E0,$0400,
         $0400,$0439,$FC01,$8001)),
    (tipo:'P'; nnos:3; parametro:'Phase(s)'; default:'';
     ds:($0007,$E004,$2004,$2E04,
         $0C04,$0A04,$0104,$0084,
         $007C,$0000,$0000,$0000,
         $0000,$2000,$2000,$E000)),
    (tipo:'O'; nnos:3; parametro:''; default:'';
     ds:($0001,$8001,$B001,$AC01,
         $A301,$A0C1,$E631,$290D,
         $2603,$290C,$E630,$A0C0,
         $A300,$AC00,$B000,$8000)),
    (tipo:'o'; nnos:4; parametro:''; default:'';
     ds:($0000,$8001,$800D,$8035,
         $80C7,$8304,$8C64,$B094,
         $C064,$3094,$0C64,$0304,
         $02C7,$0235,$020D,$FE01)),
    (tipo:'T'; nnos:3; parametro:'Impedance Delay'; default:'1 1';
     ds:($6003,$2002,$2002,$2002,
         $27F2,$2A0A,$3106,$3106,
         $3D06,$1104,$1104,$0A08,
         $07F0,$0080,$FF80,$8000)),
    (tipo:'U'; nnos:3; parametro:'Resistance Capacitance'; default:'1 1';
     ds:($6003,$2002,$2002,$2112,
         $2112,$3AAE,$0440,$0440,
         $0000,$0000,$3FFE,$0080,
         $0080,$0080,$FF80,$8000)),
    (tipo:'D'; nnos:2; parametro:'Parameters'; default:'';
     ds:($0000,$0080,$0080,$0080,
         $0080,$0080,$07F0,$03E0,
         $01C0,$0080,$07F0,$0080,
         $0080,$0080,$0080,$0080)),
    (tipo:'Z'; nnos:2; parametro:'Resistance Voltage'; default:'1 1';
     ds:($0000,$0080,$01C0,$0220,
         $0410,$0410,$0410,$1220,
         $39C0,$1080,$0080,$0300,
         $0080,$0060,$0080,$0080)),
    (tipo:'I'; nnos:2; parametro:'Current'; default:'1';
     ds:($0080,$0080,$0080,$0080,
         $03E0,$0410,$0888,$0888,
         $0888,$09C8,$0888,$0410,
         $03E0,$0080,$0080,$0080)),
    (tipo:'V'; nnos:2; parametro:'Voltage'; default:'1';
     ds:($0080,$0080,$0080,$0080,
         $03E0,$0410,$0888,$09C8,
         $0888,$0808,$09C8,$0410,
         $03E0,$0080,$0080,$0080)),
    (tipo:'='; nnos:2; parametro:''; default:'';
     ds:($0000,$0000,$0000,$0000,
         $0000,$0000,$0000,$0000,
         $0000,$01C0,$0000,$03E0,
         $0080,$0080,$0080,$0080)),
    (tipo:'-'; nnos:2; parametro:''; default:'';
     ds:($0000,$0080,$0080,$0080,
         $0080,$0080,$0080,$0080,
         $0080,$0080,$0080,$0080,
         $0080,$0080,$0080,$0080)),
    (tipo:'\'; nnos:3; parametro:''; default:'';
     ds:($0001,$0002,$0004,$0008,
         $0010,$0020,$0040,$0080,
         $0100,$0200,$0400,$0800,
         $1000,$2000,$4000,$8000)),
    (tipo:'+'; nnos:4; parametro:''; default:'';
     ds:($0001,$4002,$2004,$1008,
         $0810,$0420,$0240,$0480,
         $0400,$0240,$01A0,$0810,
         $1008,$2004,$4002,$8001)),
    (tipo:'0'; nnos:2; parametro:'Comment'; default:'';
     ds:($0000,$0000,$0000,$0000,
         $03E0,$0410,$09C8,$0948,
         $0948,$0948,$09C8,$0410,
         $03E0,$0080,$0080,$0080)),
    (tipo:'1'; nnos:2; parametro:'Comment'; default:'';
     ds:($0000,$0000,$0000,$0000,
         $03E0,$0410,$09C8,$0888,
         $0888,$0988,$0888,$0410,
         $03E0,$0080,$0080,$0080)),
    (tipo:'2'; nnos:2; parametro:'Comment'; default:'';
     ds:($0000,$0000,$0000,$0000,
         $03E0,$0410,$09C8,$0888,
         $0848,$0848,$0988,$0410,
         $03E0,$0080,$0080,$0080)),
    (tipo:'3'; nnos:2; parametro:'Comment'; default:'';
     ds:($0000,$0000,$0000,$0000,
         $03E0,$0410,$09C8,$0848,
         $08C8,$0848,$09C8,$0410,
         $03E0,$0080,$0080,$0080)),
    (tipo:'4'; nnos:2; parametro:'Comment'; default:'';
     ds:($0000,$0000,$0000,$0000,
         $03E0,$0410,$0848,$0848,
         $09C8,$0948,$0948,$0410,
         $03E0,$0080,$0080,$0080)),
    (tipo:'5'; nnos:2; parametro:'Comment'; default:'';
     ds:($0000,$0000,$0000,$0000,
         $03E0,$0410,$0988,$0848,
         $0988,$0908,$09C8,$0410,
         $03E0,$0080,$0080,$0080)),
    (tipo:'6'; nnos:2; parametro:'Comment'; default:'';
     ds:($0000,$0000,$0000,$0000,
         $03E0,$0410,$0888,$0948,
         $0988,$0908,$08C8,$0410,
         $03E0,$0080,$0080,$0080)),
    (tipo:'7'; nnos:2; parametro:'Comment'; default:'';
     ds:($0000,$0000,$0000,$0000,
         $03E0,$0410,$0888,$0888,
         $0888,$0848,$09C8,$0410,
         $03E0,$0080,$0080,$0080)),
    (tipo:'8'; nnos:2; parametro:'Comment'; default:'';
     ds:($0000,$0000,$0000,$0000,
         $03E0,$0410,$0888,$0948,
         $0888,$0948,$0888,$0410,
         $03E0,$0080,$0080,$0080)),
    (tipo:'9'; nnos:2; parametro:'Comment'; default:'';
     ds:($0000,$0000,$0000,$0000,
         $03E0,$0410,$0988,$0848,
         $08C8,$0948,$0888,$0410,
         $03E0,$0080,$0080,$0080)),
    (tipo:'*'; nnos:2; parametro:'Comment'; default:'';
     ds:($0000,$0000,$0000,$0000,
         $0000,$0000,$06C0,$0380,
         $0FE0,$0380,$06C0,$0000,
         $0000,$0000,$0000,$0000)),
    (tipo:'.'; nnos:2; parametro:'Command'; default:'';
     ds:($0000,$0000,$0000,$0000,
         $0000,$0000,$0000,$0000,
         $00C0,$00C0,$0000,$0000,
         $0000,$0000,$0000,$0000)){,
    (tipo:'K'; nnos:2; parametro:'Inductors coupling'; default:'';
     ds:($0000,$0000,$0000,$0000,
         $0000,$0880,$0900,$0A00,
         $0C00,$0A00,$0900,$0880,
         $0000,$0000,$0000,$0000)});
LABEL
  inicio;

TYPE
  cores=ARRAY[1..3] OF BYTE;

CONST
  cor:cores=(12,10,15);
  corCGA:cores=(2,1,3);
  cormono:cores=(1,1,1);
  sprite:ARRAY[1..8] OF PointType=((x:0;y:0),(x:7;y:0),(x:7;y:7),(x:5;y:5),
                                   (x:3;y:7),(x:0;y:4),(x:2;y:2),(x:0;y:0));
VAR
  xseta,yseta:INTEGER;
  pt:ARRAY[1..64] OF BYTE;
  estado:(normal,marcando,marcado);
  bi,bf:INTEGER;

FUNCTION Si(x:INTEGER):txtvalor;
VAR
  txt:txtvalor;
BEGIN
  Str(x,txt);
  Si:=txt;
END;

PROCEDURE PutSprite(x,y:INTEGER);
BEGIN
  PutImage(xseta,yseta,pt,XORput);
  xseta:=x;
  yseta:=y;
  PutImage(xseta,yseta,pt,XORput);
END;

PROCEDURE RemoveSprite;
BEGIN
  xseta:=-10;
  yseta:=-10
END;

PROCEDURE InitSprite(borda,fundo:INTEGER);
BEGIN
  SetColor(borda);
  SetFillStyle(solidfill,fundo);
  FillPoly(SizeOf(sprite) div SizeOf(PointType),sprite);
  GetImage(0,0,7,7,pt);
  RemoveSprite;
END;

PROCEDURE PlotXor(x,y:INTEGER);
BEGIN
  PutPixel(x,y,GetPixel(x,y) xor cor[3]);
END;

PROCEDURE Help;
BEGIN
  Write(tl,'[±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±');
  Write(tl,'± esc] -Save/Execute/Interrupt/End      [± ^P]  -Show nodes [^W]  -Show connections [±');
  Write(tl,'± ^L ] -Erase circuit or erase text     [±] Connections are made with [=],[-],[\],[+],    [±');
  Write(tl,'± ^K ] -Redraw screen                   [±] and [0]..[9]. These ([labels]) are for long [±');
  Write(tl,'± del] -Erase element under cursor      [±] connections. For more labels, change  [±');
  Write(tl,'± space] -Invert element under cursor   [±] the second letter of the label names. [±');
  Write(tl,'± ^R ] -Center cursor/Repeat last text  [±] The [parameters] are a text that is in- [±');
  Write(tl,'± bs ] -Reflect element under cursor    [±] terpreted in the netlist generation.  [±');
  Write(tl,'± ^X ] -Edit all elements (esc to end)  [±] [Formulas] can be used, between [()], u-  [±');
  Write(tl,'± cr ] -Idem, to element under cursor   [±] sing constants and values of the [va-]  [±');
  Write(tl,'± ^B ] -Start/End/Remove [block]          [±] [lue list]. Valid operators:[(],[)],[+],[-],[*],[/],[±');
  Write(tl,'± ^C ^V ^Y ] -Copy/Move/Erase block     [±] [^],[|](//),[sin],[cos],[tan],[log],[exp].          [±');
  Write(tl,'± ^Z ] -List component list             [±] [Assignments] name[=]value create/change  [±');
  Write(tl,'± ^O ] -Sort component list             [±] values in the value list.             [±');
  Write(tl,'± ^Q ] -Generate [netlist]                [±] Spaces must not be used in formulas.  [±');
  Write(tl,'± ^U ] -Read value list                 [±] Invalid formulas are listed with a [?]  [±');
  Write(tl,'± ^T ] -List value list                 [±] Example (observe the priority of "[=]"):[±');
  Write(tl,'± ^S ] -Change separator char           [±] [(1/X=2+3)] returns [3.5] and creates [X=2] [±');
  Write(tl,'± ^A ] -Texts ("[*],[.]") in the netlist    [±] [Spice] commands can be added with "[.]"  [±');
  Write(tl,'±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±±]');
END;

PROCEDURE EdLin(VAR linha:txtedit; cursor,xlinha:INTEGER; VAR mudado:BOOLEAN);
VAR
  base,tlinha,i:INTEGER;
  fim:BOOLEAN;
BEGIN
  tlinha:=(GetMaxX-xlinha) div 8;
  base:=1;
  fim:=FALSE;
  REPEAT
    MoveTo(xlinha,ylinha);
    i:=base;
    WHILE (i-base<=tlinha) and ((i<=Length(linha)) or (i=cursor)) DO BEGIN
      Bar(GetX,ylinha,GetX+7,ylinha+7);
      IF i=cursor THEN BEGIN
        IF inserir THEN SetColor(cor[2]) ELSE SetColor(cor[1]);
        IF  (cursor>Length(linha)) or (linha[i]=' ') THEN r:='_'
        ELSE r:=linha[i]
      END
      ELSE r:=linha[i];
      OutText(r);
      SetColor(cor[3]);
      Inc(i)
    END;
    Bar(GetX,ylinha,GetMaxX,GetMaxY);
    r:=ReadKey;
    CASE r OF
      #0:CASE ReadKey OF
           'K':IF cursor>1 THEN cursor:=cursor-1;
           'M':IF (cursor<=Length(linha)) and (cursor<tedit) THEN cursor:=cursor+1;
           'G':cursor:=1;
           'O':cursor:=Length(linha)+1;
           'R':inserir:=not inserir;
           'S':BEGIN linha:=Copy(linha,1,cursor-1)+Copy(linha,cursor+1,tedit); mudado:=TRUE END;
         END;
      #8:IF cursor>1 THEN BEGIN
           linha:=Copy(linha,1,cursor-2)+Copy(linha,cursor,tedit);
           cursor:=cursor-1;
           mudado:=TRUE;
         END;
      {#10:;}
      ^L:BEGIN
           linha:='';
           cursor:=1;
           mudado:=TRUE;
         END;
      #13:fim:=TRUE;
      ^U,#27:BEGIN fim:=TRUE; interromper:=TRUE END;
      ^R :BEGIN linha:=Copy(linha,1,cursor-1)+Copy(ulttxt,cursor,255); mudado:=TRUE END
      ELSE BEGIN
        IF inserir THEN linha:=Copy(linha,1,cursor-1)+r+Copy(linha,cursor,tedit)
        ELSE linha:=Copy(linha,1,cursor-1)+r+Copy(linha,cursor+1,tedit);
        IF cursor<tedit THEN cursor:=cursor+1;
        mudado:=TRUE;
      END;
    END;
    IF cursor<base THEN base:=cursor
    ELSE
      IF cursor>=base+tlinha THEN base:=cursor-tlinha+1;
  UNTIL fim;
  ulttxt:=linha
END;

PROCEDURE ModoGrafico;
BEGIN
  SetGraphMode(modo);
  SetFillStyle(EmptyFill,0);
END;

FUNCTION Sim:BOOLEAN;
BEGIN
  OutText('? (y/n) ');
  REPEAT
    r:=UpCase(ReadKey)
  UNTIL r in ['Y','N'];
  OutText(r);
  Sim:=(r='Y')
END;

PROCEDURE Ultima;
BEGIN
  Bar(0,ylinha,GetMaxX,GetMaxY);
  MoveTo(0,ylinha);
END;

PROCEDURE Penultima;
BEGIN
  Bar(0,GetMaxY-15,GetMaxX,GetMaxY-8);
  MoveTo(0,GetMaxY-15);
END;

FUNCTION ProximoGrupo(VAR texto:txtvalor; VAR p:INTEGER; delimitador:letras):STRING;
  VAR
    p2,nivel:INTEGER;
  BEGIN
    p2:=p;
    WHILE (p2<=Length(texto)) and (texto[p2] IN delimitador) DO Inc(p2);
    WHILE (p2<=Length(texto)) and (not (texto[p2] IN delimitador) or
      ((texto[p2] IN ['+','-']) and (UpCase(texto[p2-1]) IN ['E','=']))) DO BEGIN
      IF texto[p2]='(' THEN BEGIN
        nivel:=1;
        WHILE (p2<Length(texto)) and (nivel>0) DO BEGIN
          Inc(p2);
          IF texto[p2]=')' THEN Dec(nivel)
          ELSE
            IF texto[p2]='(' THEN Inc(nivel)
        END
      END;
      Inc(p2);
    END;
    ProximoGrupo:=Copy(texto,p,p2-p);
    p:=p2;
  END;

FUNCTION Avaliar(txt:txtvalor):REAL;
{funciona corretamente, com o bug do - em função corrigido.}
VAR
  partes,partep,partef:txtvalor;
  p,pp,ppp,pppp,c:INTEGER;
  somas,produtos,funcoes:letras;
  soma,produto,funcao,operando,t:REAL;
  operadors,operadorp,operadorf:CHAR;
  nfuncao:STRING[3];
BEGIN
  valido:=TRUE;
  Avaliar:=0;
  somas:=['+','-'];
  produtos:=['*','/'];
  funcoes:=['^','|'];
  {Msg('Interpretar: '+txt);}
  {separa somas}
  soma:=0;
  p:=1;
  WHILE p<=length(txt) DO BEGIN
    partes:=Proximogrupo(txt,p,somas);
    {Msg('Soma: '+partes);}
    operadors:=partes[1];
    IF operadors IN somas THEN partes:=Copy(partes,2,length(partes)-1)
    ELSE operadors:='+';
    {separa produtos}
    pp:=1;
    produto:=1;
    WHILE pp<=length(partes) DO BEGIN
      partep:=Proximogrupo(partes,pp,produtos);
      {Msg('Produto: '+partep);}
      operadorp:=partep[1];
      IF operadorp IN produtos THEN partep:=Copy(partep,2,length(partep)-1)
      ELSE operadorp:='*';
      {separa outras funções}
      ppp:=1;
      WHILE ppp<=length(partep) DO BEGIN
        partef:=Proximogrupo(partep,ppp,funcoes);
        {Msg('Funcoes: '+partef);}
        operadorf:=partef[1];
        IF operadorf IN funcoes THEN partef:=Copy(partef,2,length(partef)-1)
        ELSE operadorf:='+';
        {se tem parêntesis, entra em recursão}
        IF (partef[1]='(') and (partef[length(partef)]=')') THEN BEGIN
          operando:=Avaliar(Copy(partef,2,length(partef)-2))
        END
        ELSE BEGIN
          {identifica o operando}
          val(partef,operando,c);
          IF c<>0 THEN BEGIN {Não é número}
            c:=1;
            WHILE (c<nv) and (lv[c].codigo<>partef) DO Inc(c);
            IF lv[c].codigo=partef THEN operando:=lv[c].valor
            ELSE BEGIN
              nfuncao:=Copy(partef,1,3);
              IF (nfuncao='SIN') or (nfuncao='COS') or (nfuncao='TAN') or (nfuncao='LOG') THEN BEGIN
                t:=Avaliar(Copy(partef,4,Length(partef)-3));
                IF valido THEN BEGIN {É função}
                  CASE nfuncao[1] OF
                    'E':operando:=Exp(t);
                    'S':operando:=Sin(t);
                    'C':operando:=Cos(t);
                    'T':IF Cos(t)<>0 THEN operando:=Sin(t)/Cos(t) ELSE BEGIN valido:=FALSE; Exit END;
                    'L':IF t>0 THEN operando:=Ln(t){/Ln(10)} ELSE BEGIN valido:=FALSE; Exit END;
                  END;
                END
                ELSE BEGIN
                  {Msg('Error in function argument');}
                  valido:=FALSE;
                  Exit
                END
              END
              ELSE BEGIN {Vê se é atribuição}
                pppp:=Pos('=',partef);
                IF (pppp>1) and (pppp<=tnome+1) and (nv<maxlv) THEN BEGIN
                  c:=0;
                  REPEAT Inc(c) UNTIL (lv[c].codigo=Copy(partef,1,pppp-1)) or (c>nv);
                  IF (c>nv) THEN BEGIN
                    Inc(nv);
                    lv[c].codigo:=Copy(partef,1,pppp-1);
                    lv[c].valor:=0;
                  END;
                  t:=Avaliar(Copy(partef,pppp+1,Length(partef)-pppp));
                  IF valido THEN BEGIN
                    lv[c].valor:=t;
                    {Msg('Created value '+lv[c].codigo+'='+Cpct(t));}
                    operando:=t;
                  END
                  ELSE BEGIN
                    {Msg('Error in attribution');}
                    Exit
                  END
                END
                ELSE BEGIN
                  {Não é nada identificável}
                  {Msg('Unknown operand: '+partef);}
                  valido:=FALSE;
                  Exit
                END
              END
            END
          END
        END;
        {Msg('Operador de funcao='+operadorf);}
        CASE operadorf OF
          '+':funcao:=operando;
          '^':IF funcao>0 THEN
                funcao:=exp(operando*ln(funcao))
              ELSE BEGIN
                {Msg('Invalid exponent');}
                valido:=FALSE;
                Exit
              END;
          '|':IF funcao+operando<>0 THEN
                funcao:=funcao*operando/(funcao+operando)
              ELSE BEGIN
                {Msg('Invalid // operation');}
                valido:=FALSE;
                Exit
              END;
          ELSE BEGIN
            {Msg('Invalid operator');}
            valido:=FALSE;
            Exit
          END
        END
      END;
      {Msg('Operador de produto='+operadorp);}
      IF operadorp='*' THEN produto:=produto*funcao
      ELSE IF funcao<>0 THEN produto:=produto/funcao
        ELSE BEGIN
          {Msg('Division by zero');}
          valido:=FALSE;
          Exit
        END
    END;
    {Msg('Operador de soma='+operadors);}
    IF operadors='+' THEN soma:=soma+produto
    ELSE soma:=soma-produto;
  END;
  Avaliar:=soma;
END;

FUNCTION Interpreta(VAR texto:txtvalor):txtlongo;
VAR
  buffer:txtlongo;
  grupo:txtvalor;
  p:INTEGER;
  valor:REAL;

BEGIN
  p:=1;
  buffer:='';
  REPEAT
    grupo:=ProximoGrupo(texto,p,[' ']);
    Inc(p);
    IF (grupo[1]='(') and (grupo[Length(grupo)]=')') THEN BEGIN
      valido:=TRUE;
      valor:=Avaliar(Copy(grupo,2,Length(grupo)-2));
      IF valido THEN grupo:=Cpct(valor)
      ELSE grupo:=grupo+'?';
    END;
    buffer:=buffer+s+grupo
  UNTIL p>Length(texto);
  Interpreta:=buffer;
END;

PROCEDURE LerLv;
BEGIN
  REPEAT
    Ultima;
    OutText('Read value list');
    IF not Sim THEN Exit;
    Ultima;
    OutText('File to read: ');
    texto:=lisval+sufval;
    EdLin(texto,1,GetX,nada);
    IF Pos('.',texto)=0 THEN texto:=texto+sufval;
    lisval:=Copy(texto,1,Pos('.',texto)-1);
    Assign(arquivo,texto);
    {$I-} Reset(arquivo); {$I+}
    ok:=(IOResult=0);
    IF not ok THEN BEGIN
      Ultima;
      OutText('* File '+texto+' inexistent');
      Delay(1000)
    END
  UNTIL ok;
  Ultima;
  OutText('Reading file '+texto);
  nv:=0;
  WHILE (not SeekEof(arquivo)) and (nv<maxlv) DO BEGIN
    Inc(nv);
    WITH lv[nv] DO BEGIN
      codigo:='';
      REPEAT
        Read(arquivo,r);
        IF r<>' ' THEN codigo:=codigo+UpCase(r)
      UNTIL (r=' ') or (Length(codigo)=tnome);
      ReadLn(arquivo,valor);
    END
  END;
  Close(arquivo);
END;

PROCEDURE ListarLv;
BEGIN
  TextMode(80);
  WriteLn(tl,'[Value list:]');
  WriteLn;
  i:=1;
  REPEAT
    j:=1;
    REPEAT
      WITH lv[i] DO WriteLn(tl,'[',codigo,'] ',valor);
      j:=j+1;
      i:=i+1
    UNTIL (j>20) or (i>nv);
    IF i<=nv THEN WriteLn('More...')
    ELSE WriteLn(tl,'--[//]--');
    r:=ReadKey;
  UNTIL (i>nv) or (r=#27);
  ModoGrafico
END;

{$V-}
PROCEDURE LerLista;
VAR
  c:CHAR;
BEGIN
  IF haparam THEN BEGIN
    texto:=ParamStr(1);
    haparam:=FALSE
  END
  ELSE
    REPEAT
      texto:=rede;
      Write(tl,'File to edit ([',sufdes,']) or [?]: ');
      EditarLinha(texto,WhereX,WhereY,1);
      WriteLn(tl,']');
      IF texto='?' THEN BEGIN
        ClrScr;
        texto:=Diretorio('*.cir');
      END;
    UNTIL texto<>'?';
  k:=Pos('.',texto);
  IF k=0 THEN BEGIN k:=Length(texto)+1; texto:=texto+sufdes END;
  rede:=Copy(texto,1,k-1);
  lisval:=rede;
  Assign(arquivo,texto);
  {$I-} Reset(arquivo); {$I+}
  ok:=(IOResult=0);
  IF not ok THEN BEGIN
    Write('New file');
    Delay(1000);
    Exit
  END;
  ne:=0;
  Write(tl,'Reading file [',texto,']');
   WHILE not SeekEof(arquivo) DO BEGIN
    ne:=ne+1;
    WITH lista[ne] DO BEGIN
      REPEAT
        nome:='';
        REPEAT
          Read(arquivo,r);
          IF r<>' ' THEN nome:=nome+r
        UNTIL (r=' ') or (r=#10) or (Length(nome)=tnome);
      UNTIL r<>#10;
      r:=nome[1]; k:=0;
      REPEAT
        k:=k+1;
        ok:=biblioteca[k].tipo=r
      UNTIL ok or (k=maxtipos);
      IF not ok THEN BEGIN
        ClrScr;
        WriteLn(tl,'[*] Invalid element on line ',ne,' : ',nome);
        Halt
      END;
      tp:=k;
      WITH biblioteca[tp] DO BEGIN
        FOR i:=1 TO nnos DO Read(arquivo,grade[i]);
        IF parametro<>'' THEN BEGIN
          IF not SeekEoln(arquivo) THEN ReadLn(arquivo,valor)
          ELSE valor:=''
        END
        ELSE ReadLn(arquivo);
        IF nnos=2 THEN BEGIN
          grade[3]:=grade[1];
          grade[4]:=grade[2]
        END
        ELSE IF nnos=3 THEN grade[4]:=grade[2]+(grade[3]-grade[1]);
      END
    END
  END;
  Close(arquivo)
END;
{$V+}

FUNCTION Up(txt:txtvalor):txtvalor;
VAR
  i:INTEGER;
BEGIN
  FOR i:=1 TO Length(txt) DO txt[i]:=UpCase(txt[i]);
  Up:=txt
END;

FUNCTION Val2(i:INTEGER):texto2;
BEGIN
  Str(i,texto);
  IF Length(texto)=1 THEN Val2:='0'+texto
  ELSE Val2:=texto
END;

PROCEDURE SalvarLista(reduzida:BOOLEAN);
LABEL
  inicio;
BEGIN
  inicio:
  Ultima;
  IF reduzida THEN BEGIN
    nx:=nr;
    sufixo:=sufnet;
    OutText('Save netlist')
  END
  ELSE BEGIN
    nx:=ne;
    sufixo:=sufdes;
    OutText('Save component list')
  END;
  IF not Sim THEN Exit;
  Ultima;
  OutText('Output file: ');
  texto:=rede+sufixo;
  EdLin(texto,1,GetX,nada);
  IF Pos('.',texto)=0 THEN texto:=texto+sufixo;
  rede:=Copy(texto,1,Pos('.',texto)-1);
  Ultima;
  OutText('Writing file '+texto);
  {$I-}
  Assign(arquivo,texto);
  ReWrite(arquivo);
  IF reduzida THEN BEGIN
    WriteLn(arquivo,numnos);
    IF salvarc THEN FOR i:=ne DOWNTO 1 DO
     IF biblioteca[lista[i].tp].tipo='*' THEN
       WriteLn(arquivo,'* ',lista[i].valor);
  END;
  FOR i:=1 TO nx DO
    WITH lista[i] DO
      WITH biblioteca[tp] DO BEGIN
        IF reduzida THEN BEGIN
          texto:=nome;
          IF texto[1]='#' THEN texto[1]:='G';
          Write(arquivo,Up(texto))
        END
        ELSE Write(arquivo,nome);
        FOR j:=1 TO nnos DO
          IF reduzida THEN Write(arquivo,s,no[j])
          ELSE Write(arquivo,' ',grade[j]);
        IF parametro<>'' THEN BEGIN
          IF reduzida THEN WriteLn(arquivo,Interpreta(valor))
          ELSE WriteLn(arquivo,' ',valor)
        END
        ELSE WriteLn(arquivo)
      END;
  IF reduzida THEN BEGIN
    IF salvarc THEN FOR i:=ne DOWNTO 1 DO
     IF biblioteca[lista[i].tp].tipo='.' THEN
       WriteLn(arquivo,'.',lista[i].valor);
  END;
  Close(arquivo);
  {$I+}
  IF IOResult=0 THEN BEGIN
    IF not reduzida THEN mudado:=FALSE
  END
  ELSE BEGIN
    Ultima;
    Outtext('Impossible to write file');
    Delay(1000);
    GoTo inicio
  END
END;

PROCEDURE ListarLista(reduzida:BOOLEAN);
VAR
  l:INTEGER;
BEGIN
  TextMode(80);
  WriteLn(tl,'[Component list:]');
  WriteLn;
  IF reduzida THEN nx:=nr ELSE nx:=ne;
  IF reduzida and salvarc THEN
    FOR i:=ne DOWNTO 1 DO
      IF biblioteca[lista[i].tp].tipo='*' THEN
        WriteLn(tl,'* [',lista[i].valor,']');
  FOR i:=1 TO nx DO
    WITH lista[i] DO
      WITH biblioteca[tp] DO BEGIN
        Write(tl,'[',nome,']');
        FOR l:=1 TO nnos DO
          IF reduzida THEN Write(s,no[l])
          ELSE Write(' ',grade[l]);
        IF parametro<>'' THEN BEGIN
          IF reduzida THEN WriteLn(Interpreta(valor))
          ELSE WriteLn(' ',valor)
        END
        ELSE WriteLn;
        IF (WhereY=19) and (i<nx) THEN BEGIN
          WriteLn('More...');
          r:=ReadKey;
         ClrScr
        END
      END;
  IF reduzida and salvarc THEN
    FOR i:=ne DOWNTO 1 DO
      IF biblioteca[lista[i].tp].tipo='.' THEN
        WriteLn(tl,'.[',lista[i].valor,']');
  WriteLn(tl,'--[//]--');
  IF reduzida THEN WriteLn(tl,'Number of nodes: [',numnos,']');
  r:=ReadKey;
  ModoGrafico
END;

FUNCTION Vertical:BOOLEAN;
BEGIN
  Vertical:=(y and 8)=8
END;

FUNCTION Pontox(grade:INTEGER):INTEGER;
BEGIN
  Pontox:=(Lo(grade)-xmin) shl 4
END;

FUNCTION Pontoy(grade:INTEGER):INTEGER;
BEGIN
  Pontoy:=pymax-((Hi(grade)-ymin) shl 4)
END;

FUNCTION NaTela(el:INTEGER):BOOLEAN;
VAR
  n,i:INTEGER;
LABEL
  nao;
BEGIN
  i:=1;
  REPEAT
    n:=lista[el].grade[i];
    IF Lo(n)<xmin THEN GoTo nao;
    IF Lo(n)>xmax THEN GoTo nao;
    IF Hi(n)<ymin THEN GoTo nao;
    IF Hi(n)>ymax THEN GoTo nao;
    i:=i+3
  UNTIL i>4;
  NaTela:=TRUE; Exit;
  nao: NaTela:=FALSE;
END;

PROCEDURE Cursor(n1,n2:INTEGER);
BEGIN
  x:=(Pontox(n1)+Pontox(n2)) shr 1;
  y:=(Pontoy(n1)+Pontoy(n2)) shr 1;
  PutSprite(x-8,y+1);
END;

PROCEDURE ListarValor(el:INTEGER;mostrar:BOOLEAN);
VAR
  x0,y0:INTEGER;
  vert:BOOLEAN;
BEGIN
  WITH lista[el] DO WITH biblioteca[tp] DO BEGIN
    vert:=(Lo(grade[2])=Lo(grade[1]));
    x0:=(Pontox(grade[1])+Pontox(grade[2])) div 2+10;
    y0:=(Pontoy(grade[1])+Pontoy(grade[2])) div 2-6;
    SetTextStyle(SmallFont,HorizDir,4);
    IF mostrar THEN Setcolor(yellow)
    ELSE SetColor(black);
    {Bar3d(x0-2,y0,x0+TextWidth(valor)+1,y0+12,0,FALSE);}
    Bar(x0-2,y0,x0+TextWidth(valor)+1,y0+12);
    OutTextXY(x0,y0,valor)
  END;
  SetTextStyle(DefaultFont,HorizDir,1);
  SetColor(white)
END;

PROCEDURE PlotarElemento(el:INTEGER;mostrar:BOOLEAN);
VAR
  x0,y0,ii,jj,xx,yy,i,j:INTEGER;
  invertido,refletido:BOOLEAN;
  k:WORD;
BEGIN
  IF NaTela(el) THEN
    WITH lista[el] DO
      WITH biblioteca[tp] DO BEGIN
        vert:=(Lo(grade[2])=Lo(grade[1]));
        invertido:=(grade[1]>grade[3]);
        refletido:=(grade[1]>grade[2]);
        x0:=Pontox(grade[1]);
        y0:=Pontoy(grade[1]);
        IF nnos=2 THEN
          IF vert THEN x0:=x0-8
          ELSE y0:=y0+8;
        FOR i:=0 TO 15 DO BEGIN
          IF refletido THEN ii:=-i ELSE ii:=i;
          k:=ds[i];
          FOR j:=15 DOWNTO 0 DO BEGIN
            IF invertido THEN jj:=-j ELSE jj:=j;
            IF Odd(k) THEN
              IF vert THEN PlotXor(x0+jj,y0-ii)
              ELSE PlotXor(x0+ii,y0-jj);
            k:=k shr 1
          END
        END;
        IF (tipo='*') or (tipo='.') THEN ListarValor(el,mostrar)
      END
   END;

PROCEDURE PlotarLista;
VAR
  i:INTEGER;
BEGIN
  FOR i:=1 TO ne DO PlotarElemento(i,TRUE)
END;

FUNCTION CursorSobreElemento(VAR i:INTEGER):BOOLEAN;
BEGIN
  IF ne>0 THEN BEGIN
    i:=ne;
    CursorSobreElemento:=TRUE;
    REPEAT
      WITH lista[i] DO
        IF (grade[1]=no1) and (grade[2]=no2) or (grade[1]=no2) and (grade[2]=no1) THEN Exit;
      i:=i-1
    UNTIL i<=0
  END;
  CursorSobreElemento:=FALSE
END;

PROCEDURE Inverter;
LABEL
  fim;
VAR
  i:INTEGER;
BEGIN
  IF CursorSobreElemento(i) THEN WITH lista[i] DO BEGIN
    IF biblioteca[tp].nnos=2 THEN Exit;
    PlotarElemento(i,FALSE);
    k:=grade[1];
    IF Abs(grade[2]-grade[1])<>1 THEN BEGIN
      IF (Lo(k)<=xmin) or (Lo(k)>=xmax) THEN GoTo fim;
    END
    ELSE
      IF (Hi(k)<=ymin) or (Hi(k)>=ymax) THEN GoTo fim;
    k:=grade[3]-grade[1];
    grade[3]:=grade[1]-k;
    grade[4]:=grade[2]-k;
   fim:
    PlotarElemento(i,TRUE);
    mudado:=TRUE
  END
END;

PROCEDURE Refletir;
VAR
  i:INTEGER;
BEGIN
  IF CursorSobreElemento(i) THEN WITH lista[i] DO BEGIN
    PlotarElemento(i,FALSE);
    k:=grade[1]; grade[1]:=grade[2]; grade[2]:=k;
    k:=grade[3]; grade[3]:=grade[4]; grade[4]:=k;
    PlotarElemento(i,TRUE);
    mudado:=TRUE;
  END
END;

PROCEDURE Remover(i:INTEGER);
BEGIN
  FOR j:=i+1 TO ne DO lista[j-1]:=lista[j];
  Dec(ne)
END;

PROCEDURE Eliminar;
VAR
  i:INTEGER;
BEGIN
  IF CursorSobreElemento(i) THEN WITH lista[i] DO BEGIN
    PlotarElemento(i,FALSE);
    Remover(i);
    mudado:=TRUE
  END
END;

PROCEDURE Menu;
VAR
  i:INTEGER;
BEGIN
  Penultima;
  FOR i:=1 TO maxtipos-12 DO OutText(biblioteca[i].tipo);
  OutText('0..9*.?');
END;

PROCEDURE DesenharBloco;
BEGIN
  SetViewPort(0,0,GetMaxX,GetMaxY-17,ClipOn);
  SetWriteMode(XorPut);
  SetColor(cor[1]);
  Rectangle(Pontox(bi),Pontoy(bi),Pontox(bf),Pontoy(bf));
  SetWriteMode(NormalPut);
  SetColor(cor[3]);
  SetViewPort(0,0,GetMaxX,GetMaxY,ClipOn)
END;

PROCEDURE DesenharTela;
BEGIN
  xmax:=xmin+mptx; ymax:=ymin+mpty;
  RemoveSprite;
  FOR i:=0 TO mptx DO
    FOR j:=0 TO mpty DO
      PutPixel(i shl 4,j shl 4,cor[2]);
  SetColor(cor[3]);
  IF estado<>normal THEN DesenharBloco;
  Menu
END;

PROCEDURE Redesenhar;
BEGIN
  ModoGrafico;
  DesenharTela;
  PlotarLista;
  Cursor(no1,no2);
END;

PROCEDURE LerCursor;
VAR
  listar:BOOLEAN;

  PROCEDURE Centrar;
  BEGIN
    r:=^R;
    ok:=TRUE
  END;

BEGIN
  ok:=FALSE; listar:=FALSE;
  REPEAT
    r:=ReadKey;
    CASE r OF
       #0:CASE ReadKey OF
            'M':IF (x+16<=pxmax) THEN x:=x+16 ELSE Centrar;
            'K':IF (x>=16) THEN x:=x-16 ELSE Centrar;
            'P':IF (y+8<=pymax) and (x<pxmax) THEN BEGIN
                  y:=y+8;
                  IF Vertical THEN x:=x-8 ELSE x:=x+8
                END ELSE Centrar;
            'H':IF (y>=8) and (x<pxmax) THEN BEGIN
                  y:=y-8;
                  IF Vertical THEN x:=x-8 ELSE x:=x+8;
                END ELSE Centrar;
            'S':BEGIN r:=#127; ok:=TRUE END;
          END;
      '!':BEGIN
            listar:=TRUE;
            ok:=TRUE
          END;
      '@':BEGIN
            Ultima;
            OutText('X: '+Si(xmin)+' to '+Si(xmax)+' Y: '+Si(ymin)+' to '+Si(ymax));
            ok:=TRUE
          END
      ELSE ok:=TRUE;
    END;
    IF not ok THEN BEGIN
      PutSprite(x-8,y+1);
      IF estado=marcando THEN BEGIN
        DesenharBloco;
        bf:=x shr 4+xmin+Swap((pymax-y) shr 4+ymin);
        IF Vertical THEN Inc(bf,256) ELSE Inc(bf);
        DesenharBloco
      END
    END
  UNTIL ok;
  no1:=x shr 4+xmin+Swap((pymax-y) shr 4+ymin);
  IF Vertical THEN no2:=no1+256 ELSE no2:=no1+1;
  IF listar THEN BEGIN
    Ultima;
    OutText(Si(ne)+' ('+Si(Lo(no1))+','+Si(Hi(no1))+')-('+Si(Lo(no2))+','+Si(Hi(no2))+') ['+Si(no1)+','+Si(no2)+']');
    IF estado<>normal THEN OutText(' Block:['+Si(bi)+','+Si(bf)+']');
  END
END;

PROCEDURE Incluir;
LABEL
  naopode;
BEGIN
  k:=0;
  IF r in ['A'..'Z'] THEN r:=Chr(Ord(r)+32)
  ELSE r:=UpCase(r);
  REPEAT
    k:=k+1;
    ok:=biblioteca[k].tipo=r
  UNTIL ok or (k=maxtipos);
  IF not ok THEN Exit;
  IF ne=maxlista THEN Exit;
  ne:=ne+1;
  IF r in ['Z','=','\','0'..'9'] THEN BEGIN i:=no1; no1:=no2; no2:=i END; {Para manter na orienta‡„o de antes}
  FOR i:=1 TO ne-1 DO
    WITH lista[i] DO
      IF (grade[1]=no2) and (grade[2]=no1) and (tp=k) THEN GoTo naopode; {era no1, no2}
  WITH lista[ne] DO BEGIN
    tp:=k;
    grade[2]:=no1;  {era no1}
    grade[1]:=no2;  {era no2}
    IF biblioteca[tp].nnos>2 THEN BEGIN
      IF Vertical THEN BEGIN
        IF x>=pxmax THEN GoTo naopode;
        k:=1;
      END
      ELSE BEGIN
        IF y>=pymax THEN GoTo naopode; {era y<16}
        k:=-256;                       {era +256}
      END
    END
    ELSE k:=0;
    grade[3]:=no2+k; {era no1}
    grade[4]:=no1+k; {era no2}
    valor:=biblioteca[tp].default;
    nome:=r;
  END;
  PlotarElemento(ne,TRUE);
  mudado:=TRUE;
  Exit;
  naopode:
  ne:=ne-1
END;

PROCEDURE LerParametros(el:INTEGER);
BEGIN
  IF NaTela(el) THEN
    WITH lista[el] DO
      WITH biblioteca[tp] DO
        IF parametro<>'' THEN BEGIN
          REPEAT
            IF (tipo='*') or (tipo='.') THEN ListarValor(el,FALSE);
            Cursor(grade[1],grade[2]);
            Penultima;
            OutText('Name  '+parametro);
            texto:=Copy(nome+'     ',1,6)+valor;
            EdLin(texto,7,0,mudado);
            ok:=(UpCase(texto[1])=UpCase(tipo)) and (Pos(' ',texto)<7);
            IF not ok THEN BEGIN
              Ultima;
              OutText('Invalid name');
              Delay(1000)
            END
            ELSE BEGIN
              nome:=tipo+Up(Copy(texto,2,Pos(' ',texto)-2));
              valor:=Copy(texto,7,tvalor);
              IF tipo<>'*' THEN valor:=Up(valor);
              ok:=TRUE;
            END
          UNTIL ok;
          IF (tipo='*') or (tipo='.') THEN ListarValor(el,TRUE);
        END
END;

PROCEDURE ParametrosDeUm;
BEGIN
  ok:=FALSE;
  FOR i:=1 TO ne DO
    WITH lista[i] DO
      IF (grade[1]=no1) and (grade[2]=no2) or (grade[2]=no1) and (grade[1]=no2) THEN BEGIN
        LerParametros(i);
        ok:=TRUE
      END;
  IF ok THEN BEGIN
    Ultima;
    Menu
  END
END;

PROCEDURE TodosOsParametros;
BEGIN
  i:=0;
  interromper:=FALSE;
  WHILE (i<ne) and not interromper DO BEGIN
    i:=i+1;
    WITH lista[i] DO LerParametros(i);
  END;
  Ultima;
  Menu;
END;

PROCEDURE Ordenar;
VAR
  ordenado:BOOLEAN;
  temp:elemento;
BEGIN
  Ultima;
  OutText('Sorting...');
  REPEAT
    ordenado:=TRUE;
    FOR i:=1 TO ne-1 DO
      IF (lista[i].tp>lista[i+1].tp)
      or (lista[i].tp=lista[i+1].tp)
      and (lista[i].grade[2]>lista[i+1].grade[2]) THEN BEGIN
        temp:=lista[i];
        lista[i]:=lista[i+1];
        lista[i+1]:=temp;
        ordenado:=FALSE
      END
  UNTIL ordenado
END;

PROCEDURE ConverterLista;
  {A lista deve estar ordenada}
VAR
  i,j,k,l,no1,no2:INTEGER;
  tabela: ARRAY[1..maxn] of INTEGER;

  PROCEDURE Renumerar;
  VAR
    l,k:INTEGER;
  BEGIN
    FOR l:=1 TO j DO
      WITH lista[l] DO
        FOR k:=1 TO biblioteca[tp].nnos DO
          IF no[k]=no2 THEN no[k]:=no1
  END;

BEGIN
  {=====Eliminar curto-circuitos}
  Ultima;
  OutText('Eliminating short-circuits...');
  nr:=ne;
  FOR i:=1 TO nr DO WITH lista[i] DO no:=grade;
  i:=0;
  REPEAT
    i:=i+1;
    WITH lista[i] DO BEGIN
      IF biblioteca[tp].tipo='g' THEN no[1]:=0; {Tratamento especial para o OTA}
      ok:=tp>curto
    END
  UNTIL ok or (i=nr);
  IF ok THEN BEGIN
    FOR j:=nr DOWNTO i DO
      WITH lista[j] DO
        CASE biblioteca[tp].tipo OF
          '-':BEGIN
                no1:=no[1];
                no2:=no[2];
                Renumerar
              END;
          '\':BEGIN
                no1:=no[2];
                no2:=no[3];
                Renumerar
              END;
          '=':BEGIN
                no2:=no[2];
                no1:=0;
                Renumerar
              END;
     '0'..'9':BEGIN
                no2:=no[2];
                no1:=-Ord(nome[1]);
                IF Length(nome)>1 THEN no1:=no1-256*Ord(nome[2]);
                Renumerar
              END;
          '+':BEGIN
                no1:=no[1];
                no2:=no[4];
                Renumerar;
                no1:=no[2];
                no2:=no[3];
                Renumerar
              END
        END;
    nr:=i-1
  END
  ELSE nr:=i;
  {=====Identificar n¢s usados}
  Ultima;
  OutText('Renumbering nodes...');
  numnos:=0;
  FOR j:=1 TO nr DO
    WITH lista[j] DO
      FOR k:=1 TO biblioteca[tp].nnos DO
        IF no[k]<>0 THEN BEGIN
          l:=0;
          REPEAT l:=l+1 UNTIL (l>numnos) or (tabela[l]=no[k]);
          IF l>numnos THEN
            IF l<=maxn THEN BEGIN
              numnos:=l;
              tabela[l]:=no[k]
            END
            ELSE BEGIN
              Ultima;
              OutText('Too many nodes');
              ok:=FALSE;
              Exit
            END
        END;
  {=====Renomear n¢s}
  FOR j:=1 TO numnos DO
    FOR k:=1 TO nr DO
      WITH lista[k] DO
        FOR l:=1 TO biblioteca[tp].nnos DO
          IF no[l]=tabela[j] THEN no[l]:=j;
  {=====Renomear elementos}
  FOR k:=1 TO nr DO
    WITH lista[k] DO BEGIN
      ok:=Length(nome)=5;
      IF ok THEN
        FOR j:=2 TO 5 DO ok:=ok and (nome[j] in ['0'..'9']);
      IF (Length(nome)=1) or ok THEN nome:=nome[1]+Val2(no[1])+Val2(no[2])
    END;
  ok:=TRUE
END;

PROCEDURE PlotarNos;
BEGIN
  SetTextStyle(SmallFont,HorizDir,4);
  FOR i:=1 TO ne DO
    IF NaTela(i) THEN
      WITH lista[i] DO
        IF tp<=curto THEN
          FOR j:=1 TO biblioteca[tp].nnos DO
            IF no[j]>0 THEN BEGIN
              MoveTo(PontoX(grade[j])+3,PontoY(grade[j])-11);
              IF Odd(grade[j]) THEN SetColor(cor[2]) ELSE SetColor(cor[1]);
              OutText(Si(no[j]));
            END;
  SetColor(cor[3]);
  SetTextStyle(DefaultFont,HorizDir,1);
END;

PROCEDURE Reportar;
BEGIN
  IF DosError<>0 THEN BEGIN
    Ultima;
    Case DosError OF
      2,3:OutText('Executable program not found');
      8:OutText('Not enough memory');
      ELSE OutText('Execution Impossible: Dos error '+Si(DosError))
    END;
    Delay(1000);
    Ultima
  END
END;

PROCEDURE TestarFim;
BEGIN
  IF mudado THEN SalvarLista(FALSE);
  Ultima;
  ok:=FALSE;
  OutText('Execute Dos Restart Quit Continue');
  CASE UpKey OF
    'E':BEGIN
          ok:=TRUE;
          Ultima;
          OutText('Program to execute: '); EdLin(prog,1,GetX,nada);
          TextMode(80);
          IF Pos('.',prog)=0 THEN prog:=prog+'.exe';
          SwapVectors;
          Exec(prog,rede);
          SwapVectors;
          IF DosExitCode<>0 THEN Delay(1000);
          Redesenhar;
          Reportar
        END;
    'D':BEGIN
          Ultima;
          OutText('Type EXIT to return');
          Delay(1000);
          TextMode(80);
          SwapVectors;
          Exec(GetEnv('COMSPEC'),'');
          SwapVectors;
          Redesenhar;
          Reportar;
        END;
    'R':BEGIN
          Ultima;
          OutText('Edit another circuit');
          IF Sim THEN BEGIN outro:=TRUE; fim:=TRUE END
          ELSE Ultima
        END;
    'Q':BEGIN
          Ultima;
          OutText('Quit');
          IF Sim THEN fim:=TRUE
          ELSE Ultima
        END;
    ELSE Ultima
  END;
END;

FUNCTION Fora(grade,b1,b2:INTEGER):BOOLEAN;
BEGIN
  Fora:=(Lo(grade)<Lo(b1)) or (Lo(grade)>Lo(b2)) or
        (Hi(grade)<Hi(b1)) or (Hi(grade)>Hi(b2))
END;

BEGIN
  haparam:=ParamCount<>0;
  s:=' '; prog:=''; rede:='';
  DetectGraph(placa,modo);
  IF placa=CGA THEN modo:=CGAC2;
  IF paramcount=3 THEN BEGIN
    Val(ParamStr(2),placa,i);
    Val(ParamStr(3),modo,i);
  END;
  InitGraph(placa,modo,GetEnv('TPBGI'));
  IF placa=CGA THEN cor:=corCGA;
  IF GetMaxColor=1 THEN cor:=cormono;
  InitSprite(cor[3],cor[1]);
  mptx:=(GetMaxX-15) div 16;
  mpty:=(GetMaxY-23) div 16;
  nv:=0; pxmax:=mptx*16; pymax:=mpty*16;
  estado:=normal;
  ylinha:=GetMaxY-7;
  salvarc:=TRUE;
 Inicio:
  xmin:=64; ymin:=64;
  fim:=FALSE; outro:=FALSE; ne:=0; numnos:=0;
  no1:=xmin+mptx shr 1+Swap(ymin+mpty shr 1);
  no2:=no1+1;
  TextMode(80);
  WriteLn(tl,'[Ed]itor for [Fil]ters');
  WriteLn(tl,'[ÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍÍ]');
  WriteLn('Ant“nio Carlos Moreir„o de Queiroz - COPPE/EE/UFRJ - acmq@ufrj.br');
  WriteLn('Version ',versao);
  IF haparam or outro THEN WriteLn ELSE Help;
  LerLista;
  mudado:=FALSE;
  Redesenhar;
  REPEAT
    LerCursor;
    Incluir;
    IF not ok THEN
      CASE r of
        #127:Eliminar;
          ^I,' ':Inverter;
          ^H:Refletir;
          ^K:Redesenhar;
          ^M:ParametrosDeUm;
          ^X:TodosOsParametros;
          ^Z:IF ne>0 THEN BEGIN
               ListarLista(FALSE);
               Redesenhar
             END;
          ^L:BEGIN
               Ultima;
               OutText('Erase all the circuit');
               IF Sim THEN BEGIN
                 ne:=0;
                 Redesenhar
               END
               ELSE Ultima
             END;
          ^O:IF ne>0 THEN BEGIN
               Ordenar;
               Redesenhar
             END;
          ^Q:IF ne>0 THEN BEGIN
               Ordenar;
               ConverterLista;
               IF ok THEN BEGIN
                 ListarLista(TRUE);
                 SalvarLista(TRUE);
                 TestarFim;
                 IF not fim and not ok THEN BEGIN
                   Redesenhar;
                   PlotarNos
                 END
               END
             END;
          ^R:BEGIN
               xmin:=Lo(no1)-mptx shr 1;
               IF xmin<0 THEN xmin:=0;
               IF xmin+mptx>128 THEN xmin:=128-mptx;
               ymin:=Hi(no1)-mpty shr 1;
               IF ymin<0 THEN ymin:=0;
               IF ymin+mpty>128 THEN ymin:=127-mpty;
               Redesenhar
             END;
          ^U:BEGIN
               LerLv;
               Ultima
             END;
          ^T:IF nv=0 THEN BEGIN
               Ultima;
               OutText('* No active value list');
               Delay(1000);
               Ultima
             END
             ELSE BEGIN
               ListarLv;
               Redesenhar
             END;
          ^A:BEGIN
               Ultima;
               OutText('Save comments and commands in netlist');
               salvarc:=Sim;
               Ultima
             END;
          ^S:BEGIN
               Ultima;
               OutText('Separator character: ("'+s+'") ');
               r:=ReadKey;
               IF r<>#13 THEN s:=r;
               Ultima
             END;
          ^P:IF ne>0 THEN BEGIN
               Ordenar;
               ConverterLista;
               IF ok THEN BEGIN
                 PlotarNos;
                 Ultima
               END
             END;
          {
          ^N:IF ne>0 THEN BEGIN
               SetColor(0);
               FOR i:=1 TO ne DO
                 IF NaTela(i) THEN
                   WITH lista[i] DO
                     IF tp<=curto THEN BEGIN
                       SetFillStyle(SolidFill,cor[Ord(Odd(grade[1]))+1]);
                       MoveTo((PontoX(grade[1])+PontoX(grade[2])) div 2,(PontoY(grade[1])+PontoY(grade[2])) div 2-3);
                       Bar(GetX-1,GetY-1,GetX+TextWidth(nome)-1,GetY+TextHeight(nome)-1);
                       OutText(nome)
                     END;
               SetFillStyle(EmptyFill,0);
               SetColor(cor[3]);
             END;
           }
         #27:TestarFim;
         '?':BEGIN
               TextMode(80);
               Help;
               r:=ReadKey;
               Redesenhar
             END;
         ^B:IF estado=normal THEN BEGIN
              estado:=marcando;
              bi:=no2; bf:=no2;
              DesenharBloco;
              Ultima;
              OutText('Marking block')
            END
            ELSE IF estado=marcando THEN BEGIN
              Ultima;
              OutText('Block marked');
              estado:=marcado;
              IF bi>bf THEN BEGIN k:=bi; bi:=bf; bf:=k END;
              IF Lo(bi)>Lo(bf) THEN BEGIN
                k:=Lo(bi);
                bi:=bi and $FF00 or Lo(bf);
                bf:=bf and $FF00 or k
              END;
            END
            ELSE BEGIN
              DesenharBloco;
              Ultima;
              OutText('Block unmarked');
              estado:=normal
            END;
         ^Y:IF estado=marcado THEN BEGIN
              Ultima;
              OutText('Delete block');
              IF Sim THEN BEGIN
                k:=0;
                WHILE k<ne DO BEGIN
                  Inc(k);
                  WITH lista[k] DO BEGIN
                    fora_o:=FALSE;
                    FOR j:=1 TO biblioteca[tp].nnos DO
                      IF Fora(grade[j],bi,bf) THEN fora_o:=TRUE;
                    IF not fora_o THEN BEGIN
                      PlotarElemento(k,FALSE); Remover(k); Dec(k)
                    END
                  END
                END;
                mudado:=TRUE;
                Ultima
              END
              ELSE Ultima
            END
            ELSE BEGIN
              Ultima;
              OutText('No block marked')
            END;
         ^C,^V:IF estado=marcado THEN BEGIN
              cp:=r=^C;
              {Testar se o bloco cabe na tela}
              j:=Lo(no2)+Lo(bf)-Lo(bi);
              k:=Hi(no2)+Hi(bf)-Hi(bi);
              ok:=(j<=128) and (k<128);
              {Testar se ha elementos no destino}
              IF ok THEN BEGIN
                l:=256;
                k:=l*k+j;
                i:=0;
                WHILE ok and (i<ne) DO BEGIN
                  Inc(i);
                  fora_o:=FALSE; fora_d:=FALSE;
                  WITH lista[i] DO
                    FOR l:=1 TO biblioteca[tp].nnos DO BEGIN
                      IF Fora(grade[l],no2,k) THEN fora_d:=TRUE;
                      IF Fora(grade[l],bi,bf) THEN fora_o:=TRUE;
                    END;
                  ok:=((not cp) and ((not fora_o) or fora_d)) or (cp and fora_d);
                  IF not ok THEN BEGIN
                    Ultima;
                    OutText('Block overlaps elements');
                  END
                END
              END
              ELSE BEGIN
                Ultima;
                OutText('Block beyond limits')
              END;
              {Copiar/mover bloco}
              IF ok THEN BEGIN
                DesenharBloco;
                k:=ne;
                FOR i:=1 TO k DO IF ne<maxlista THEN BEGIN
                  ok:=TRUE;
                  WITH lista[i] DO
                    FOR j:=1 TO biblioteca[tp].nnos DO
                      IF Fora(grade[j],bi,bf) THEN ok:=FALSE;
                  IF ok THEN BEGIN
                    IF r=^C THEN BEGIN
                      inc(ne);
                      lista[ne]:=lista[i];
                      l:=ne
                    END
                    ELSE l:=i;
                    WITH lista[l] DO BEGIN
                      IF r=^V THEN PlotarElemento(l,FALSE);
                      FOR j:=1 TO 4 DO BEGIN
                        k:=256; {senao da overflow?!}
                        grade[j]:=grade[j]+Lo(no2)-Lo(bi)+k*(Hi(no2)-Hi(bi));
                      END;
                      tp:=tp+128; {Marca para redesenhar depois}
                    END;
                  END
                END;
                FOR i:=1 TO ne DO WITH lista[i] DO
                  IF tp>128 THEN BEGIN
                    tp:=tp-128;
                    PlotarElemento(i,TRUE)
                  END;
                k:=256; {senao da overflow?!}
                l:=Lo(no2)-Lo(bi)+k*(Hi(no2)-Hi(bi));
                bi:=bi+l; bf:=bf+l;
                DesenharBloco;
                mudado:=TRUE;
                Ultima;
              END
            END
            ELSE BEGIN
              Ultima;
              OutText('No block marked')
            END;
       ^W:BEGIN
            SetColor(cor[1]);
            SetViewPort(0,0,GetMaxX,GetMaxY-17,ClipOn);
            SetLineStyle(DottedLn,0,NormWidth);
            FOR k:=1 TO ne DO WITH lista[k] DO
              IF (nome[1] in ['0'..'9']) THEN BEGIN
                i:=k;
                REPEAT Dec(i) UNTIL (i<1) or (Copy(lista[i].nome,1,2)=Copy(lista[k].nome,1,2));
                IF i>0 THEN Line(pontox(lista[k].grade[2]),pontoy(lista[k].grade[2]),
                pontox(lista[i].grade[2]),pontoy(lista[i].grade[2]));
              END;
            SetColor(cor[3]);
            SetLineStyle(SolidLn,0,NormWidth);
            SetViewPort(0,0,GetMaxX,GetMaxY,ClipOn)
          END
      END
  UNTIL fim;
  IF outro THEN GoTo inicio;
  TextMode(80);
END.
