/*
EdFil - Editor de Filtros - Versao XView/XView-PC
Antonio Carlos Moreirao de Queiroz - COPPE/EE
Universidade Federal do Rio de Janeiro - 1994
*/
/*
V. 1.4j 30/10/94 Label 0, correcao no uso de "up", mudado comando de bloco.
V. 1.4k 30/11/94 Eliminada janela de mensagens na versao Sun.
V. 1.4l 13/12/94 Cortado excesso de espacos na netlist.
V. 1.4m 04/01/95 Corrigido nome inicial para elemento. Confirma saida.
V. 1.4n 20/03/95 Substituida XDrawRectangle.
V. 1.4o 01/01/98 Colocado short int em incluir. Ainda ha estranha lentidao.
V. 1.5  14/03/01 Elementos em pe, transformador com k.
V. 1.6  29/08/03 Comentarios e comandos. Versao DOS apenas.
*/

#define versao "Version 1.6 of 29/08/2003"

/* SUNXV=versao Sun XView XV_PC=versao XView-PC */

#define XV_PC

#ifdef __GNUC__
#define BIG_CIRCUITS
#endif
#ifdef SUNXV
#define BIG_CIRCUITS
#endif

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>

#ifdef SUNXV
#include <X11/Xlib.h>
#include <xview/xview.h>
#include <xview/canvas.h>
#include <xview/xv_xrect.h>
#include <xview/cms.h>
#include <xview/textsw.h>
#include <xview/notice.h>
#include <xview/panel.h>
#include <xview/svrimage.h>
#include <xview/icon.h>
#define KTAB 9
#define KBS 8
#define KDEL 127
#define KCTRLA 1
#define KCTRLB 2
/* #define KCTRLC 3 */
#define KCTRLK 11
#define KCTRLL 12
#define KCTRLO 15
/* #define KCTRLP 16 */
#define KCTRLQ 17
#define KCTRLR 18
#define KCTRLS 19
#define KCTRLT 20
#define KCTRLU 21
#define KCTRLV 22
#define KCTRLW 23
#define KCTRLY 25
#define KCTRLZ 26
#define KESC 27
#define KF1 0
#define close_window(w) xv_set(w,XV_SHOW,FALSE,NULL)
#define open_window(w) xv_set(w,XV_SHOW,TRUE,NULL)
#endif

#ifdef XV_PC
#define USE_XV_GET
#include <dir.h>
#include "xview.h"
#include "notice.h"
#include "xv_var.h"
#include "xlib.h"
#include "extkeys.h"
#include "xv_sun.h"
#endif

#define hi(x) (x/256)
#define lo(x) (x & 255)
#define odd(x) (x & 1)
#define sufdes ".cir"  /* Sufixos */
#define sufnet ".net"
#define sufval ".val"
#ifndef BIG_CIRCUITS
#define maxlista 600   /* Maximo numero de elementos */
#define maxn 200       /* Maximo numero de nos */
#endif
#ifdef BIG_CIRCUITS
#define maxlista 4000  /* Maximo numero de elementos */
#define maxn 1000      /* Maximo numero de nos */
#endif
#define maxlv 200      /* Maximo numero de valores */
#define maxnos 4
#define maxtipos 44    /* No. de tipos */
#define curto 28       /* 1o. "curto" */
#define tnome 5        /* Tamanho maximo de nome */
#define tvalor 50      /* Tamanho maximo de valor */
#define tedit 56       /* Tamanho do buffer de edicao */
#define ZOOM_MAX 3     /* Maximo nivel de zoom */
#define inset(x,y) strchr(y,x)

typedef char txtvalor[tvalor+1];
typedef char txtedit[tedit+1];
typedef char txtlongo[256];
typedef int nos[maxnos];
typedef struct {
  unsigned short int tp;
  nos grade,no;
  char nome[tnome+1];
  txtvalor evalor;
} elemento;
typedef struct {
  char tipo;
  int nnos;
  txtvalor parametro,nafalta;
  unsigned short ds[16];
} descricao;
typedef struct {
  char codigo[tnome+1];
  double valor;
} elv;

#ifdef SUNXV
typedef unsigned long* cores;
unsigned long c_element,c_block;
#endif
#ifdef XV_PC
typedef int cores[5];
int c_element,c_block;
#endif

typedef enum { ler_cir,ler_val,salvar_lista, dar_parametro } a_fazer;

Xv_opaque
  menufim,
  fedfil,cgrafico,multima,
#ifdef XV_PC
  ftty,ttymsg,
#endif
#ifdef SUNXV
  ptexto,painelgrafico,
#endif
  ftexto,ttexto;

#ifdef XV_PC
Xv_opaque fdiretorio,cdiretorio,tmask;
short nomes,total;
#endif

#ifdef SUNXV
Cms cms;
GC Ggc;
Display *Gdisplay;
Window Gxid;
short closed_bits[]= {
#include "closed.icon"
};
Server_image closed_image;
Icon icon;
#endif

int inserir=0;
int pronto=0;
int z=1;
elemento lista[maxlista];
elv lv[maxlv];
txtedit texto,rede,prog,lisval;
txtlongo buf;
FILE* arquivo;
int interromper,mudado,editado,ok;
int vert,fim,fora_o,fora_d,cp,haparam;
int mptx,mpty,placa,modo,numnos;
int ne,nr,nx,nv,i,j,k,l,x,y,eledit;
int xmin,ymin,xmax,ymax,pxmax,pymax,no1,no2;
char s,r;
char sufixo[5];
int valido,lreduzida;
int tlinha,cursor,base;
cores pcor;
int xseta,yseta;
enum { normal,marcando,marcado } tipo_estado;
a_fazer afazer;
int bi,bf;
int estado;
int salvarc=0;

descricao biblioteca[maxtipos]={
    {'R',2,"Resistance","1",
     {0x0000,0x0080,0x0080,0x0080,
      0x0080,0x0300,0x0080,0x0060,
      0x0080,0x0300,0x0080,0x0060,
      0x0080,0x0080,0x0080,0x0080}},
    {'L',2,"Inductance","1",
     {0x0000,0x0080,0x0080,0x00E0,
      0x0010,0x0010,0x03D0,0x0420,
      0x0420,0x03D0,0x0010,0x0010,
      0x00E0,0x0080,0x0080,0x0080}},
    {'C',2,"Capacitance","1",
     {0x0000,0x0080,0x0080,0x0080,
      0x0080,0x0080,0x03E0,0x0000,
      0x0000,0x03E0,0x0080,0x0080,
      0x0080,0x0080,0x0080,0x0080}},
    {'N',4,"Inductances L1 L2 k12","1 1 0.9",
     {0x0001,0x8001,0x8811,0x8001,
      0xF24F,0x0A50,0x0A50,0x724E,
      0x8A51,0x724E,0x0A50,0x0A50,
      0xF24F,0x8001,0x8001,0x8001}},
    {'X',2,"Reactance","1",
     {0x0000,0x0080,0x0080,0x0080,
      0x07F0,0x0410,0x0410,0x0410,
      0x0410,0x0410,0x0410,0x07F0,
      0x0080,0x0080,0x0080,0x0080}},
    {'G',4,"Transconductance","1",
     {0x0000,0x8001,0xFC11,0x0439,
      0x0A10,0x1100,0x2480,0x4440,
      0x9F20,0x4E40,0x2480,0x1100,
      0x0A00,0x0439,0xFC01,0x8001}},
    {'g',4,"Transconductance","1",
     {0x0000,0x0001,0x0019,0x0069,
      0x0189,0x0649,0x04EF,0x0448,
      0x3C08,0x2408,0x24EF,0x2609,
      0x2189,0x2069,0x2019,0x6001}},
    {'Q',3,"hfe hie hre hoe","100 1 0 0",
     {0x6003,0x27F2,0x280A,0x1004,
      0x283A,0x4419,0x4229,0x4141,
      0x5FFD,0x4081,0x2082,0x1084,
      0x0888,0x07F0,0x0080,0xFF80}},
    {'q',3,"hfe hie hre hoe","100 1 0 0",
     {0x6003,0x27F2,0x280A,0x1004,
      0x282A,0x4431,0x4239,0x4141,
      0x5FFD,0x4081,0x2082,0x1084,
      0x0888,0x07F0,0x0080,0xFF80}},
    {'M',3,"Gm Gds","1 0",
     {0x701F,0x1010,0x1010,0x1010,
      0x1010,0x1010,0x1038,0x107C,
      0x1010,0x3FF8,0x0000,0x3FF8,
      0x0100,0x0100,0x3F00,0x4000}},
    {'m',3,"Gm Gds","1 0",
     {0x701F,0x1010,0x1010,0x1010,
      0x1010,0x1010,0x107C,0x1038,
      0x1010,0x3FF8,0x0000,0x3FF8,
      0x0100,0x0100,0x3F00,0x4000}},
    {'J',3,"Gm Gds","1 0",
     {0x780F,0x0808,0x0808,0x0808,
      0x0808,0x0808,0x3FFE,0x0080,
      0x01C0,0x03E0,0x0080,0x0080,
      0x0080,0x0080,0x0080,0xFF80}},
    {'j',3,"Gm Gds","1 0",
     {0x780F,0x0808,0x0808,0x0808,
      0x0808,0x0808,0x3FFE,0x0080,
      0x03E0,0x01C0,0x0080,0x0080,
      0x0080,0x0080,0x0080,0xFF80}},
    {'A',3,"Av (or GB (rad/s) Rout)","100 0.01",
     {0x0001,0x8001,0xB001,0xAC01,
      0xA301,0xA0C1,0xEE31,0x200D,
      0x2003,0x240C,0xEE30,0xA4C0,
      0xA300,0xAC00,0xB000,0x8000}},
    {'E',4,"Av","1",
     {0x0000,0x8001,0xFC11,0x0439,
      0x0A10,0x1500,0x2E80,0x4440,
      0x8020,0x4040,0x2E80,0x1100,
      0x0A00,0x0439,0xFC01,0x8001}},
    {'F',4,"Ai","1",
     {0x8000,0x8001,0xFC07,0x0404,
      0x0A1F,0x110E,0x2484,0x4444,
      0x9F24,0x4E44,0x2484,0x1104,
      0x0A04,0x0404,0xFC07,0x8001}},
    {'H',4,"Rm","1",
     {0x8000,0x8001,0xFC07,0x0404,
      0x0A1F,0x150E,0x2E84,0x4444,
      0x8024,0x4044,0x2E84,0x1104,
      0x0A04,0x0404,0xFC07,0x8001}},
    {'Y',4,"Gyration resistance","1",
     {0x0001,0x8001,0x8001,0x8001,
      0x8081,0xF3CF,0x8891,0x8421,
      0x8421,0x8421,0x8811,0xF00F,
      0x8001,0x8001,0x8001,0x8001}},
    {'S',2,"Phase(s)","1",
     {0x0000,0x0080,0x0080,0x0080,
      0x0080,0x0040,0x0020,0x0014,
      0x000C,0x001C,0x0000,0x0080,
      0x0080,0x0080,0x0080,0x0080}},
    {'s',2,"Phase(s)","2",
     {0x0000,0x0080,0x0080,0x0080,
      0x0080,0x0050,0x0020,0x0054,
      0x000C,0x001C,0x0000,0x0080,
      0x0080,0x0080,0x0080,0x0080}},
    {'P',3,"Phase(s)","",
     {0x0007,0xE004,0x2004,0x2E04,
      0x0C04,0x0A04,0x0104,0x0084,
      0x007C,0x0000,0x0000,0x0000,
      0x0000,0x2000,0x2000,0xE000}},
    {'O',3,"","",
     {0x0001,0x8001,0xB001,0xAC01,
      0xA301,0xA0C1,0xE631,0x290D,
      0x2603,0x290C,0xE630,0xA0C0,
      0xA300,0xAC00,0xB000,0x8000}},
    {'T',3,"Impedance and delay","1 1",
     {0x6003,0x2002,0x2002,0x2002,
      0x27F2,0x2A0A,0x3106,0x3106,
      0x3D06,0x1104,0x1104,0x0A08,
      0x07F0,0x0080,0xFF80,0x8000}},
    {'U',3,"Resistance and capacitance","1 1",
     {0x6003,0x2002,0x2002,0x2112,
      0x2112,0x3AAE,0x0440,0x0440,
      0x0000,0x0000,0x3FFE,0x0080,
      0x0080,0x0080,0xFF80,0x8000}},
    {'D',2,"Parameters","",
     {0x0000,0x0080,0x0080,0x0080,
      0x0080,0x0080,0x07F0,0x03E0,
      0x01C0,0x0080,0x07F0,0x0080,
      0x0080,0x0080,0x0080,0x0080}},
    {'Z',2,"Resistance voltage","1 1",
     {0x0000,0x0080,0x01C0,0x0220,
      0x0410,0x0410,0x0410,0x1220,
      0x39C0,0x1080,0x0080,0x0300,
      0x0080,0x0060,0x0080,0x0080}},
    {'I',2,"Current","1",
     {0x0080,0x0080,0x0080,0x0080,
      0x03E0,0x0410,0x0888,0x0888,
      0x0888,0x09C8,0x0888,0x0410,
      0x03E0,0x0080,0x0080,0x0080}},
    {'V',2,"Voltage","1",
     {0x0080,0x0080,0x0080,0x0080,
      0x03E0,0x0410,0x0888,0x09C8,
      0x0888,0x0808,0x09C8,0x0410,
      0x03E0,0x0080,0x0080,0x0080}},
    {'=',2,"","",
     {0x0000,0x0000,0x0000,0x0000,
      0x0000,0x0000,0x0000,0x0000,
      0x0000,0x01C0,0x0000,0x03E0,
      0x0080,0x0080,0x0080,0x0080}},
    {'-',2,"","",
     {0x0000,0x0080,0x0080,0x0080,
      0x0080,0x0080,0x0080,0x0080,
      0x0080,0x0080,0x0080,0x0080,
      0x0080,0x0080,0x0080,0x0080}},
    {'\\',3,"","",
     {0x0001,0x0002,0x0004,0x0008,
      0x0010,0x0020,0x0040,0x0080,
      0x0100,0x0200,0x0400,0x0800,
      0x1000,0x2000,0x4000,0x8000}},
    {'+',4,"","",
     {0x0001,0x4002,0x2004,0x1008,
      0x0810,0x0420,0x0240,0x0480,
      0x0400,0x0240,0x01A0,0x0810,
      0x1008,0x2004,0x4002,0x8001}},
    {'0',2,"Label comment","",
     {0x0000,0x0000,0x0000,0x0000,
      0x03E0,0x0410,0x09C8,0x0948,
      0x0948,0x0948,0x09C8,0x0410,
      0x03E0,0x0080,0x0080,0x0080}},
    {'1',2,"Label comment","",
     {0x0000,0x0000,0x0000,0x0000,
      0x03E0,0x0410,0x09C8,0x0888,
      0x0888,0x0988,0x0888,0x0410,
      0x03E0,0x0080,0x0080,0x0080}},
    {'2',2,"Label comment","",
     {0x0000,0x0000,0x0000,0x0000,
      0x03E0,0x0410,0x09C8,0x0888,
      0x0848,0x0848,0x0988,0x0410,
      0x03E0,0x0080,0x0080,0x0080}},
    {'3',2,"Label comment","",
     {0x0000,0x0000,0x0000,0x0000,
      0x03E0,0x0410,0x09C8,0x0848,
      0x08C8,0x0848,0x09C8,0x0410,
      0x03E0,0x0080,0x0080,0x0080}},
    {'4',2,"Label comment","",
     {0x0000,0x0000,0x0000,0x0000,
      0x03E0,0x0410,0x0848,0x0848,
      0x09C8,0x0948,0x0948,0x0410,
      0x03E0,0x0080,0x0080,0x0080}},
    {'5',2,"Label comment","",
     {0x0000,0x0000,0x0000,0x0000,
      0x03E0,0x0410,0x0988,0x0848,
      0x0988,0x0908,0x09C8,0x0410,
      0x03E0,0x0080,0x0080,0x0080}},
    {'6',2,"Label comment","",
     {0x0000,0x0000,0x0000,0x0000,
      0x03E0,0x0410,0x0888,0x0948,
      0x0988,0x0908,0x08C8,0x0410,
      0x03E0,0x0080,0x0080,0x0080}},
    {'7',2,"Label comment","",
     {0x0000,0x0000,0x0000,0x0000,
      0x03E0,0x0410,0x0888,0x0888,
      0x0888,0x0848,0x09C8,0x0410,
      0x03E0,0x0080,0x0080,0x0080}},
    {'8',2,"Label comment","",
     {0x0000,0x0000,0x0000,0x0000,
      0x03E0,0x0410,0x0888,0x0948,
      0x0888,0x0948,0x0888,0x0410,
      0x03E0,0x0080,0x0080,0x0080}},
    {'9',2,"Label comment","",
     {0x0000,0x0000,0x0000,0x0000,
      0x03E0,0x0410,0x0988,0x0848,
      0x08C8,0x0948,0x0888,0x0410,
      0x03E0,0x0080,0x0080,0x0080}},
    {'*',2,"Comment","",
     {0x0000,0x0000,0x0000,0x0000,
      0x0000,0x0000,0x06C0,0x0380,
      0x0FE0,0x0380,0x06C0,0x0000,
      0x0000,0x0000,0x0000,0x0000}},
    {'.',2,"Command","",
     {0x0000,0x0000,0x0000,0x0000,
      0x0000,0x0000,0x0000,0x0000,
      0x00C0,0x00C0,0x0000,0x0000,
      0x0000,0x0000,0x0000,0x0000}}};

char upcase(char r)
{
  if ((r>='a') && (r<='z')) r-=32;
  return r;
}

void msg(char* txt)
{
#ifdef SUNXV
  puts(txt);
#endif
#ifdef XV_PC
  txtlongo buf;

  strcpy(buf,txt);
  strcat(buf,"\r\n");
  textsw_insert(ttymsg,buf,strlen(buf));
#endif
}

txtlongo bufcpy;

char* copy(char* str, int from, int len)
{
  bufcpy[0]=0;
  if (from>strlen(str)) return (char*)(bufcpy);
  strcpy(bufcpy,str+from-1);
  bufcpy[len]=0;
  return (char*)(bufcpy);
}

char* up(char* txt) /* Notar que altera o argumento */
{
  int i,k;
  k=strlen(txt);
  for (i=0; i<k; i++) txt[i]=upcase(txt[i]);
  return txt;
}

int pos(char c, char* str2)
{
   char* res;
   res=strchr(str2,c);
   if (res==NULL) return 0;
   else return res-str2+1;
}

void ultima(char* texto)
{
#ifdef SUNXV
  xv_set(fedfil,FRAME_LEFT_FOOTER,texto,NULL);
#endif
#ifdef XV_PC
  xv_set(multima,texto);
#endif
}


int vertical(void)
{
  return((y&8)==8);
}

int pontox(int grade)
{
  return((lo(grade)-xmin)*16);
}

int pontoy(int grade)
{
  return(pymax-(hi(grade)-ymin)*16);
}

/*
Versao alternativa para XDrawRectangle
*/

void quadrado(int x,int y,int dx,int dy)
{
  XDrawLine(Gdisplay,Gxid,Ggc,x,y,x+dx,y);
  XDrawLine(Gdisplay,Gxid,Ggc,x+dx,y,x+dx,y+dy);
  XDrawLine(Gdisplay,Gxid,Ggc,x+dx,y+dy,x,y+dy);
  XDrawLine(Gdisplay,Gxid,Ggc,x,y+dy,x,y);
}

#define XDrawRectangle(gd,gx,gg,x,y,dx,dy) quadrado(x,y,dx,dy)

void desenharbloco(void)
{
  XSetForeground(Gdisplay,Ggc,c_block);
  XSetFunction(Gdisplay,Ggc,GXxor);
  XDrawRectangle(Gdisplay,Gxid,Ggc,pontox(bi)*z,pontoy(bi)*z,
  z*(pontox(bf)-pontox(bi)),z*(pontoy(bf)-pontoy(bi)));
  XSetFunction(Gdisplay,Ggc,GXcopy);
}

int natela(int el)
{
  int n,i;
  i=0;
  do {
    n=lista[el-1].grade[i];
    if (lo(n)<xmin) goto nao;
    if (lo(n)>xmax) goto nao;
    if (hi(n)<ymin) goto nao;
    if (hi(n)>ymax) goto nao;
    i=i+3;
  } while (!(i>3));
  return(1);
  nao: return(0);
}

void listarvalor(int el,int mostrar)
{
int x0,y0;

  { elemento* with1=(elemento*)(&(lista[el-1]));
    { descricao * with2=(descricao*)(&(biblioteca[with1->tp-1]));
      x0=z*(pontox(with1->grade[0])+pontox(with1->grade[2]))/2;
      y0=z*(pontoy(with1->grade[0])+pontoy(with1->grade[2]))/2;
      if (mostrar) XSetForeground(Gdisplay,Ggc,pcor[2]);
      else XSetForeground(Gdisplay,Ggc,pcor[0]);
      settextstyle(SMALL_FONT,HORIZ_DIR,4*z);
      outtextxy(x0+5*z,y0+2*z,with1->evalor);
      settextstyle(DEFAULT_FONT,HORIZ_DIR,1);
    }
  }
}

void plotarelemento(int el,int mostrar)
{
  int x0,y0,ii,jj,i,j;
  int invertido,refletido;
  unsigned int k;

  if (natela(el))
    { elemento * with1=(elemento*)(&(lista[el-1]));
      XSetFunction(Gdisplay,Ggc,GXxor);
      XSetForeground(Gdisplay,Ggc,c_element);
      { descricao * with2=(descricao*)(&(biblioteca[with1->tp-1]));
        vert=(lo(with1->grade[1])==lo(with1->grade[0]));
	invertido=(with1->grade[0]>with1->grade[2]);
	refletido=(with1->grade[0]>with1->grade[1]);
	x0=pontox(with1->grade[0]);
	y0=pontoy(with1->grade[0]);
	if (with2->nnos==2)
          if (vert) x0=x0-8;
          else y0=y0+8;
        for (i=0; i<=15; i++) {
          if (refletido) ii=-i;
          else ii=i;
          k=with2->ds[i];
          for (j=15; j >= 0; j--) {
            if (invertido) jj=-j;
            else jj=j;
	    if (odd(k))
              if (vert)
                XFillRectangle(Gdisplay,Gxid, Ggc,z*(x0+jj),z*(y0-ii),z,z);
              else XFillRectangle(Gdisplay,Gxid,Ggc,z*(x0+ii),z*(y0-jj),z,z);
	    k=k>>1;
	  }
	}
        XSetFunction(Gdisplay,Ggc,GXcopy);
        if (with2->tipo=='*' || with2->tipo=='.') listarvalor(el,mostrar);
      }
    }
}

void plotarlista(void)
{ 
  int i;
  for (i=1; i<=ne; i++) plotarelemento(i,1);
}

char* mmenu(void)
{
  int i;

  for (i=1; i<=maxtipos-12; i++) buf[i-1]=biblioteca[i-1].tipo;
  buf[maxtipos-12]='\0';
  strcat(buf,"0..9*.?");
  return (char*)(buf);
}

void cleartty(void)
{
#ifdef XV_PC
  close_window(ftty);
  ttymsg->v.stty.tstart=ttymsg->v.stty.tend;
#endif
}

void help(void)
{
  cleartty();
  ultima(mmenu());
  msg("EdFil - Schematic edition and capture program");
  msg(versao);
  msg("By Antonio Carlos M. de Queiroz - acmq@coe.ufrj.br");
  msg("COPPE/EE/Universidade Federal do Rio de Janeiro");
  msg("Direct commands:");
  msg("Middle mouse or Ctrl-B: Start/End/Remove block");
  msg("Left mouse: Edit parameters");
  msg("Tab: Invert component under cursor");
  msg("Bs:  Reflect component under cursor");
  msg("Del: Delete component under cursor");
  msg("F1:  Help");
  msg("F2:  Copy block");
  msg("F3 or Ctrl-V: Move block");
  msg("F4 or Ctrl-Y: Delete block");
  msg("F9 or Ctrl-S:  Change zoom level");
  msg("F10: Plot nodes");
  msg("Ctrl-K: Redraw");
  msg("Ctrl-L: Delete all");
  msg("Ctrl-W: Show connections");
  msg("Ctrl-Z: List components");
  msg("Ctrl-O: Sort components");
  msg("Ctrl-Q: Generate netlist");
  msg("Ctrl-U: Read value list");
  msg("Ctrl-T: List value list");
  msg("Ctrl-R, Right mouse: Center cursor");
  msg("Ctrl-A, Save comments and commands in the netlist");
#ifdef XV_PC
  msg("Esc:  See messages");
#endif
  msg("The parameters are a text that is interpreted in the");
  msg("netlist generation. Formulas can be used, enclosed in ()");
  msg("and without internal spaces, involving constants and");
  msg("values of the value list. Accepted operators are:");
  msg("sin(),cos(),tan(),log(),*,/,|(//),^,=,+,-,().");
  msg("Assignments (=) can be used to create values in the");
  msg("value list. Evaluation is from bottom-top, left-right.");
  msg("Comments and commands can be included with * and .");
}

void desenhartela(void)
{
int i,j;
  xmax=xmin+mptx; ymax=ymin+mpty;
  XSetForeground(Gdisplay,Ggc,pcor[0]);
  XFillRectangle(Gdisplay,Gxid,Ggc,0,0,
    (int)xv_get(cgrafico,XV_WIDTH),
    (int)xv_get(cgrafico,XV_HEIGHT)
  );
  XSetForeground(Gdisplay,Ggc,pcor[4]);
  for (i=0;i<=mptx;i++) {
    for (j=0;j<=mpty;j++) XFillRectangle(Gdisplay,Gxid,Ggc,16*i*z,16*j*z,z,z);
  }
  if (estado!=normal) desenharbloco();
}

int incluir(short int code)
{
  char r;

  if (code>126) return 0;
  r=code;
  if ((r>='A') && (r<='Z')) r+=32;
  else if((r>='a') && (r<='z')) r-=32;
  k=0;
  do {
    k++;
    ok=biblioteca[k-1].tipo==r; }  while (!(ok || (k==maxtipos)));
  if (!ok) return 0;
  if (ne==maxlista) return 1;
  ne++;
  if (inset(r,"=Z0123456789")) {i=no1; no1=no2; no2=i;} /* Para manter estes elementos invertidos */
  for (i=1; i<=ne-1; i++)
    { elemento * with1=&lista[i-1];
      if ((with1->grade[0]==no2) && (with1->grade[1]==no1) && (with1->tp==k)) goto naopode; /* era no1 no2 */
    }
  { elemento * with1=&lista[ne-1];
    with1->tp=k;
    with1->grade[1]=no1;  /* era assim? */
    with1->grade[0]=no2;
    if (biblioteca[with1->tp-1].nnos>2) {
      if (vertical()) {
        if (x >= pxmax) goto naopode;
        k=1;
      }
      else {
        if (y >= pymax) goto naopode; /* era y<16 */
        k=-256;                       /* era +256 */
      }
    }
    else k=0;
    with1->grade[2]=no2+k; /* era no1 */
    with1->grade[3]=no1+k; /* era no2 */
    strcpy(with1->evalor,biblioteca[with1->tp-1].nafalta);
    with1->nome[0]=r;
    with1->nome[1]='\0';
  }
  plotarelemento(ne,1);
  mudado=1;
  return 1;
  naopode: ne--;
  return 1;
}

int cursorsobreelemento(int * i)
{
  if (ne>0) {
    *i=ne;
    do {
      { elemento * with1=&lista[*i-1];
        if (((with1->grade[0]==no1) && (with1->grade[1]==no2)) || ((with1->grade[0]==no2) && (with1->grade[1]==no1))) return(1);
      }
      *i=*i-1;
    } while (!(*i<=0));
  }
  return(0);
}

void inverter(void)
{ 
  int i;

  if (cursorsobreelemento(&i)) { elemento * with1=&lista[i-1];
    if (biblioteca[with1->tp-1].nnos==2) return;
    plotarelemento(i,0);
    k=with1->grade[0];
    if (abs(with1->grade[1]-with1->grade[0])!=1) {
      if ((lo(k)<=xmin) || (lo(k) >= xmax)) goto fim;
    } 
    else 
      if ((hi(k)<=ymin) || (hi(k) >= ymax)) goto fim;
    k=with1->grade[2]-with1->grade[0];
    with1->grade[2]=with1->grade[0]-k;
    with1->grade[3]=with1->grade[1]-k;
    fim: plotarelemento(i,1);
    mudado=1;
  }
}

void refletir(void)
{ 
  int i;

  if (cursorsobreelemento(&i)) { elemento * with1=&lista[i-1];
    plotarelemento(i,0);
    k=with1->grade[0]; with1->grade[0]=with1->grade[1]; with1->grade[1]=k;
    k=with1->grade[2]; with1->grade[2]=with1->grade[3]; with1->grade[3]=k;
    plotarelemento(i,1);
    mudado=1;
  }
}

void remover(int i)
{ 
  for (j=i+1; j<=ne; j++) lista[j-1-1]=lista[j-1];
  ne--;
}

void eliminar(void)
{ 
  int i;

  if (cursorsobreelemento(&i)) {
    plotarelemento(i,0);
    remover(i);
    mudado=1;
    close_window(ftexto);
   } 
} 

#ifdef SUNXV
int notice(char* titulo)
{
  return (NOTICE_YES==
    notice_prompt(fedfil,NULL,
      NOTICE_MESSAGE_STRINGS,titulo,NULL,
      NOTICE_BUTTON_YES,"Yes",
      NOTICE_BUTTON_NO,"No",
    NULL)
  );
}
#endif

void edlin(a_fazer oque, char* mensagem, char* texto)
{
  afazer=oque;
#ifdef XV_PC
  strcpy(ttexto->v.stextfield.panel_value,texto);
  xv_set(ftexto,mensagem);
  xv_set(ttexto,"");
  if (oque==ler_cir || oque==ler_val) {
    close_window(fdiretorio);
    open_window(fdiretorio);
  }
#endif
#ifdef SUNXV
  xv_set(ftexto,
    XV_LABEL,mensagem,
    XV_SHOW,TRUE,
    NULL);
  xv_set(ttexto,
    PANEL_VALUE,texto,
    NULL);
#endif
}

void lerparametros(int el)
{
  if (natela(el))
    { elemento * with1=&lista[el-1];
      { descricao * with2=&biblioteca[with1->tp-1];
        if (strcmp(with2->parametro,"")!=0) {
          if (with2->tipo=='*'|| with2->tipo=='.') listarvalor(el,0);
          /* Posicionamento do cursor sobre o elemento em edicao
             (Nao implementado) */
          /* pcursor(with1->grade[0],with1->grade[1]); */
          sprintf(buf,"Name  %s",with2->parametro);
          sprintf(texto,"%-6s%s",with1->nome,with1->evalor);
          eledit=el;
          edlin(dar_parametro,buf,texto);
        }
      }
    }
}

void parametrosdeum(int inicio)
{
  ok=0;
  for (i=inicio; (i<=ne) && (!ok); i++)
    { elemento * with1=&lista[i-1];
      ok=(((with1->grade[0]==no1) && (with1->grade[1]==no2)) || ((with1->grade[1]==no1) && (with1->grade[0]==no2)));
      if (ok) lerparametros(i);
      else eledit=1;
    }
}

char* proximogrupo(char* texto, int* p, char* delimitador)
{
  int p2,nivel;

  p2=*p;
  while ((p2<=strlen(texto)) && inset(texto[p2-1],delimitador)) p2++;
  while ((((p2<=strlen(texto)) && !inset(texto[p2-1],delimitador)) || (inset(texto[p2-1],"+-") && inset(upcase(texto[p2-1-1]),"E=")))) {
    if (texto[p2-1]=='(') {
      nivel=1;
      while ((p2<strlen(texto)) && (nivel>0)) {
        p2++;
        if (texto[p2-1]==')') nivel--;
        else
          if (texto[p2-1]=='(') nivel++;
      }
    }
    p2++;
  }
  strcpy(buf,copy(texto,*p,p2-*p));
  *p=p2;
  return buf;
}

double somasde(char* expr);

void operar(double* acum, char* expr0)
{
  double t;
  int c,p;
  char operador;
  char funcao[4];
  txtvalor expr; /* trabalho */

  strcpy(expr,expr0);
  if (inset(expr[0],"+-*^|/")) {
    operador=expr[0];
    strcpy(expr,copy(expr,2,255));
  }
  else operador='+';
  if ((expr[0]=='(') && (expr[strlen(expr)-1]==')')) t=somasde(copy(expr,2,strlen(expr)-2));
  else {
    t=atof(expr);   /* Zero nao pode ser convertido! */
    if (t==0.0) {   /* Nao e numero (ou e 0) */
      c=1;
      while ((c<nv) && (strcmp(lv[c-1].codigo,expr)!=0)) c++;
      if (strcmp(lv[c-1].codigo,expr)==0) t=lv[c-1].valor;
      else {
        strcpy(funcao,copy(expr,1,3));
        if ((strcmp(funcao,"SIN")==0) || (strcmp(funcao,"COS")==0) || (strcmp(funcao,"TAN")==0) || (strcmp(funcao,"LOG")==0)) {
          t=somasde(copy(expr,4,strlen(expr)-3));
          if (valido)
            switch (funcao[0]) {
              case 'S': t=sin(t);
              break;
              case 'C': t=cos(t);
              break;
              case 'T': if (cos(t)!=0) t=sin(t)/cos(t); else valido=0;
              break;
              case 'L': if (t>0) t=log10(t); else valido=0;
            }
          }
          else {   /* Nao e funcao */
            p=pos('=',expr);
            if ((p>1) && (p<=tnome+1) && (nv<maxlv)) {
              c=0;
              do { c++; }  while (!((strcmp(lv[c-1].codigo,copy(expr,1,p-1))==0) || (c>nv)));
              if ((c>nv)) {
                nv++;
                strcpy(lv[c-1].codigo,copy(expr,1,p-1));
                lv[c-1].valor=0;
              } 
              t=somasde(copy(expr,p+1,strlen(expr)-p));
              lv[c-1].valor=t;
            }
            else   /* Nao e nada identificavel */
            valido=0;
          } 
        } 
      } 
    } 
    if (valido) 
      switch (operador) {
        case '+': *acum=*acum+t;
        break;
        case '-': *acum=*acum-t;
        break;
        case '*': *acum=*acum * t;
        break;
        case '/': if (t==0) valido=0;
        else *acum=*acum/t;
        break;
        case '^': if (*acum<=0) valido=0;
        else *acum=exp(t*log(*acum));
        break;
        case '|': if ((t==0) || (*acum==0)) valido=0;
        else *acum=(1/(1/(*acum)+1/t)); break;
      }
}

double produtosde(char* expr0)
{
  double acum;
  int p;
  txtvalor expr; /* trabalho (necessario?) */

  strcpy(expr,expr0);
  acum=0;
  p=1;
  do {
    operar(&acum,proximogrupo(expr,&p,"*^|/"));
  } while (!((p>strlen(expr)) || !valido));
  return acum;
}

double somasde(char* expr0)
{
  int p;
  double acum;
  txtvalor expr; /* trabalho */

  strcpy(expr,expr0);
  acum=0;
  p=1;
  do {
    acum=acum+produtosde(proximogrupo(expr,&p,"+-"));
  } while (!((p>strlen(expr)) || !valido));
  return acum;
}

char* interpreta(char* texto)
{
  txtlongo buffer; /* parece seguro */
  txtvalor grupo;
  int p;
  double valor;

  p=1;
  strcpy(buffer,"");
  do {
    strcpy(grupo,proximogrupo(texto,&p," "));
    p++;
    if ((grupo[0]=='(') && (grupo[strlen(grupo)-1]==')')) {
      valido=1;
      valor=somasde(copy(grupo,2,strlen(grupo)-2));
      if (valido) sprintf(grupo,"%.9E",valor);
      else strcat(grupo,"?");
    }
    sprintf(buf,"%c%s",s,grupo);
    strcat(buffer,buf);
  } while (!(p>strlen(texto)));
  p=strlen(buffer);
  while(p>0 && buffer[p-1]==' ') {buffer[p-1]='\0'; p--;}
  return buffer;
}

void lerlv(void)
{
  if (!notice("Read value list?")) return;
  sprintf(texto,"%s%s",lisval,sufval);
  edlin(ler_val,"Value list file to read:",texto);
}

void listarlv(void)
{
  cleartty();
  msg("Value list:");
  for (i=1;i<=nv;i++)
    { elv* with1=&lv[i-1];
      sprintf(buf,"%s %10g",with1->codigo,with1->valor);
      msg(buf);
    }
  msg("--//--");
}

void lerlista(void)
{
  strcpy(texto,rede);
  sprintf(buf,"File to edit (%s): ",sufdes);
  edlin(ler_cir,buf,texto);
}

void salvarlista(int reduzida)
{
  lreduzida=reduzida;
  if (reduzida) {
    nx=nr;
    strcpy(sufixo,sufnet);
    strcpy(buf,"Save net-list");
  }
  else {
    nx=ne;
    strcpy(sufixo,sufdes);
    strcpy(buf,"Save component list?");
  }
  if (notice(buf)) {
    sprintf(texto,"%s%s",rede,sufixo);
    edlin(salvar_lista,"Output file",texto);
  }
  else close_window(ftexto);
}

void listarlista(int reduzida)
{
  int l;
  txtlongo buf1,buf;

  cleartty();
  msg("Component list:");
  if (reduzida) nx=nr;
  else nx=ne;
  if (reduzida && salvarc)
    for (i=ne; i>=1; i--)
      if (biblioteca[lista[i-1].tp-1].tipo=='*') {
        sprintf(buf,"* %s",lista[i-1].evalor);
        msg(buf);
      }
  for (i=1;i<=nx;i++) {
    { elemento* with1=&lista[i-1];
      { descricao* with2=&biblioteca[with1->tp-1];
        strcpy(buf,with1->nome);
        for (l=0; l<with2->nnos; l++) {
          if (reduzida) sprintf(buf1,"%c%d",s,with1->no[l]);
          else sprintf(buf1," %d",with1->grade[l]);
          strcat(buf,buf1);
        }
        if (strcmp(with2->parametro,"")!=0) {
          if (reduzida) strcat(buf,interpreta(with1->evalor));
          else {
            sprintf(buf1," %s",with1->evalor);
            strcat(buf,buf1);
          }
        }
      }
    }
    msg(buf);
  }
  if (reduzida) {
    if (salvarc) for (i=ne; i>=1; i--)
      if (biblioteca[lista[i-1].tp-1].tipo=='.') {
        sprintf(buf,".%s",lista[i-1].evalor);
        msg(buf);
      }
    sprintf(buf,"Number of nodes: %d",numnos);
    msg(buf);
  }
  msg("--//--");
}

void ordenar(void)
{
  int ordenado;
  elemento temp;

  ultima("Sorting...");
  do { 
    ordenado=1;
    for (i=1; i<=ne-1; i++)
      if ((lista[i-1].tp>lista[i+1-1].tp) || ((lista[i-1].tp==lista[i+1-1].tp) && (lista[i-1].grade[1]>lista[i+1-1].grade[1]))) {
        temp=lista[i-1];
        lista[i-1]=lista[i+1-1];
        lista[i+1-1]=temp;
        ordenado=0;
      }
  }  while (!(ordenado));
}
  
void renumerar(void)
{
  int l,k;

  for (l=1; l<=j; l++)
    { elemento* with1=&lista[l-1];
      for (k=0; k<biblioteca[with1->tp-1].nnos; k++)
        if (with1->no[k]==no2) with1->no[k]=no1;
    }
}

void converterlista(void)
/* A lista deve estar ordenada */
{
  int i,k,l;
  int tabela[maxn];

  /* =====Eliminar curto-circuitos */
  ultima("Eliminating short-circuits...");
  nr=ne;
  for (i=1; i<=nr; i++)
    { elemento* with1=&lista[i-1];
      for (j=0;j<4;j++) with1->no[j]=with1->grade[j];
    }
  i=0;
  do { 
    i=i+1;
    { elemento* with1=&lista[i-1];
      if (biblioteca[with1->tp-1].tipo=='g') with1->no[0]=0; /* Tratamento especial para o OTA */
      ok=with1->tp>curto;
    }
  } while (!(ok || (i==nr)));
  if (ok) {
    for (j=nr; j >= i; j--)
      { elemento* with1=&lista[j-1];
        switch (biblioteca[with1->tp-1].tipo) {
          case '-':
            no1=with1->no[0];
            no2=with1->no[1];
            renumerar();
          break;
          case '\\':
            no1=with1->no[1];
            no2=with1->no[2];
            renumerar();
          break;
          case '=':
            no2=with1->no[1];
            no1=0;
            renumerar();
          break;
          case '0':
          case '1':
          case '2':
          case '3':
          case '4':
          case '5':
          case '6':
          case '7':
          case '8':
          case '9':
            no2=with1->no[1];
            no1=-with1->nome[0];
            if (strlen(with1->nome)>1) no1=no1-256 * with1->nome[1];
            renumerar();
          break;
          case '+':
            no1=with1->no[0];
            no2=with1->no[3];
            renumerar();
            no1=with1->no[1];
            no2=with1->no[2];
            renumerar();
          break;
        }
      }
    nr=i-1;
  }
  else nr=i;
  /* =====Identificar nos usados */
  ultima("Renumbering nodes...");
  numnos=0;
  for (j=1; j<=nr; j++)
    { elemento* with1=&lista[j-1];
      for (k=0; k<biblioteca[with1->tp-1].nnos; k++)
        if (with1->no[k]!=0) {
          l=0;
          do { l=l+1; }  while (!((l>numnos) || (tabela[l-1]==with1->no[k])));
          if (l>numnos)
            if (l<=maxn) {
              numnos=l;
              tabela[l-1]=with1->no[k];
            }
            else {
              ultima("Too many nodes");
              ok=0;
              return;
            }
        }
     }
  /* =====Renomear nos */
  for (j=0; j<numnos; j++)
    for (k=1; k<=nr; k++)
      { elemento* with1=&lista[k-1];
        for (l=0; l<biblioteca[with1->tp-1].nnos; l++)
          if (with1->no[l]==tabela[j]) with1->no[l]=j+1;
      }
  /* =====Renomear elementos */
  for (k=1; k<=nr; k++)
    { elemento* with1=&lista[k-1];
      ok=strlen(with1->nome)==5;
      if (ok)
        for (j=2; j<=5; j++) ok=ok && (inset(with1->nome[j-1],"0123456789"));
      if ((strlen(with1->nome)==1) || ok)
        {
          sprintf(with1->nome,"%c%04d",with1->nome[0],k);
        }
    }
  ok=1;
}

void plotarnos(void)
{
#ifdef XV_PC
  settextjustify(LEFT_TEXT,BOTTOM_TEXT);
#endif
  for (i=1; i<=ne; i++)
    if (natela(i))
      { elemento* with1=&lista[i-1];
        if (with1->tp<=curto)
          for (j=0; j<biblioteca[with1->tp-1].nnos; j++)
            if (with1->no[j]>0) {
              if (odd(with1->grade[j]))
                XSetForeground(Gdisplay,Ggc,pcor[4]);
              else
                XSetForeground(Gdisplay,Ggc,pcor[2]);
                sprintf(texto,"%d",with1->no[j]);
                XDrawString(Gdisplay,Gxid,Ggc,
                z*pontox(with1->grade[j])+2+z,
                z*pontoy(with1->grade[j])-2-z,
                texto,strlen(texto)
              );
            }
      }
}

int fora(int grade, int b1, int b2)
{
  return (lo(grade)<lo(b1)) || (lo(grade)>lo(b2)) || (hi(grade)<hi(b1)) || (hi(grade)>hi(b2));
}

void redesenhar(void)
{
  if (!ne) {
    xmin=64; ymin=64;
  }
  mptx=((int)xv_get(cgrafico,XV_WIDTH)-2)/(16*z);
  mpty=((int)xv_get(cgrafico,XV_HEIGHT)-2)/(16*z);
  pxmax=mptx*16; pymax=mpty*16;
  desenhartela();
  ultima(mmenu());
  plotarlista();
}

void gerarnetlist(void)
{
  if (ne>0) {
    ordenar();
    converterlista();
    if (ok) {
     listarlista(1);
     salvarlista(1);
    }
  }
}

/* Callbacks */

#ifdef XV_PC
void abremenufim(Xv_opaque obj)
{
  menu_show(menufim);
}
#endif

#ifdef SUNXV
void tratarmenu(Menu menu, Menu_item menu_item)
#endif
#ifdef XV_PC
void tratarmenu(Xv_opaque menu_item)
#endif
{
  close_window(ftexto);
  switch((int)xv_get(menu_item,MENU_VALUE)
#ifdef SUNXV
  -1
#endif
    ) {
      case 1:
        if (mudado && ne) strcpy(buf,"Circuit not saved. Edit another?");
        else strcpy(buf,"Edit another circuit?");
        if (notice(buf)) {
          ne=0;
          redesenhar();
          lerlista();
        }
      break;
      case 2:
        salvarlista(0);
      break;
      case 3:
        lerlv();
      break;
      case 4:
        gerarnetlist();
      break;
      case 5:
        help();
      break;
      case 6:
        if (mudado && ne) strcpy(buf,"Circuit not saved. Quit anyway?");
        else strcpy(buf,"Quit EdFil?"); 
        if (notice(buf)) notify_stop();
      break;
    }
}

#ifdef SUNXV
void processaredicao(Xv_Window window, Event* event)
#endif
#ifdef XV_PC
void processaredicao(Xv_opaque obj)
#endif
{
  close_window(ftexto);
#ifdef XV_PC
  close_window(ftty);
  close_window(fdiretorio);
#endif
  strcpy(texto,copy((char*)xv_get(ttexto,PANEL_VALUE),1,tedit));
  switch (afazer) {
    case dar_parametro:
      { elemento * with1=&lista[eledit-1];
        { descricao * with2=&biblioteca[with1->tp-1];
          ok=(upcase(texto[0])==upcase(with2->tipo)) && (pos(' ',texto)<7);
          if (!ok) {
            ultima("Invalid name");
            if (with2->tipo=='*' || with2->tipo=='.') listarvalor(eledit,1);
          }
          else {
#ifdef XV_PC
            if (obj==ttexto) mudado=1; /* mudado se editado */
#endif
            buf[0]='\0';
            if (with2->tipo!='*') up(texto);
            sscanf(strcat(texto,"\n"),"%s %[^\n]",with1->nome,buf);
            with1->nome[0]=with2->tipo;
            strcpy(with1->evalor,copy(buf,1,tvalor));
/*
            sprintf(with1->nome,"%c%s",with2->tipo,up(copy(texto,2,pos(' ',texto)-2)));
            strcpy(with1->evalor,up(copy(texto,7,tvalor)));
*/
            if (with2->tipo=='*' || with2->tipo=='.') listarvalor(eledit,1);
            parametrosdeum(eledit+1);
          }
        }
      }
    break;
    case ler_val:
      if (pos('.',texto)==0) strcat(texto,sufval);
      strcpy(lisval,copy(texto,1,pos('.',texto)-1));
      arquivo=fopen(texto,"r");
      ok=(int)arquivo;
      if (!ok) {
        sprintf(buf,"* File %s not found",texto);
        ultima(buf);
        return;
      }
      sprintf(buf,"Reading file %s",texto);
      ultima(buf);
      nv=0;
      while ((fscanf(arquivo,"%s",buf)!=EOF) && (nv<maxlv)) {
        nv++;
        { elv* with1=&lv[nv-1];
          fscanf(arquivo,"%lg%*[^\n]",&with1->valor);
          buf[5]='\0';
          strcpy(with1->codigo,up(buf));
        }
      }
      fclose(arquivo);
      ultima("Value list loaded");
    break;
    case ler_cir:
      k=pos('.',texto);
      if (k==0) {
        k=strlen(texto)+1; strcat(texto,sufdes);
      }
      strcpy(rede,copy(texto,1,k-1));
      strcpy(lisval,rede);
      arquivo=fopen(texto,"r");
      ok=(arquivo!=NULL);
      if (!ok) {
        ultima("New file");
        return;
      }
      ne=0;
      sprintf(buf,"Reading file %s",texto);
      ultima(buf);
      while ((fscanf(arquivo,"%s",buf)!=EOF) && (ne<maxlista)) {
        ne++;
        { elemento* with1=&lista[ne-1];
          r=buf[0]; k=0;
          buf[5]='\0';
          strcpy(with1->nome,buf);
          do {
            k=k+1;
            ok=biblioteca[k-1].tipo==r;
          } while (!(ok || (k==maxtipos)));
          if (!ok) {
            sprintf(buf,"* Invalid element on line %d : %s",ne,with1->nome);
            ultima(buf);
            ne=0;
            return;
          }
          with1->tp=k;
          { descricao* with2=&biblioteca[with1->tp-1];
            for (i=0; i<with2->nnos; i++) fscanf(arquivo,"%d",&with1->grade[i]);
            fscanf(arquivo,"%[^\n]",buf);
            j=strlen(buf);
            if (buf[j-1]=='\r') buf[j-1]='\0';
            if ((strcmp(with2->parametro,"")!=0) && (strlen(buf)!=0))
              strcpy(with1->evalor,copy(buf,2,strlen(buf)));
            else {
              with1->evalor[0]='\0';
            }
            if (with2->nnos==2) {
              with1->grade[2]=with1->grade[0];
              with1->grade[3]=with1->grade[1];
            }
            else if (with2->nnos==3) with1->grade[3]=with1->grade[1]+(with1->grade[2]-with1->grade[0]);
          }
        }
      }
      fclose(arquivo);
      mudado=0;
      redesenhar();
    break;
    case salvar_lista:
      if (pos('.',texto)==0) strcat(texto,sufixo);
      strcpy(rede,copy(texto,1,pos('.',texto)-1));
      arquivo=fopen(texto,"w"); ok=(arquivo!=NULL);
      if (ok) {
        if (lreduzida) {
          ok=fprintf(arquivo,"%d\n",numnos);
          if (salvarc) for (i=ne; i>=1; i--)
           if (biblioteca[lista[i-1].tp-1].tipo=='*')
             fprintf(arquivo,"* %s",lista[i].evalor);
        }
        for (i=1; i<=nx; i++)
          { elemento* with1=&lista[i-1];
            { descricao* with2=&biblioteca[with1->tp-1];
              strcpy(buf,with1->nome);
              if (lreduzida) fprintf(arquivo,"%s",up(buf));
              else fprintf(arquivo,"%s",buf);
              for (j=0; j<with2->nnos; j++)
                if (lreduzida) fprintf(arquivo,"%c%d",s,with1->no[j]);
                else fprintf(arquivo," %d",with1->grade[j]);
              if (strcmp(with2->parametro,"")!=0) {
                if (lreduzida) fprintf(arquivo,"%s\n",interpreta(with1->evalor));
                else fprintf(arquivo," %s\n",with1->evalor);
              }
              else fprintf(arquivo,"\n");
            }
          }
        if (lreduzida && salvarc)
          for (i=ne; i>=1; i--)
           if (biblioteca[lista[i-1].tp-1].tipo=='.')
             fprintf(arquivo,".%s",lista[i].evalor);
        ok=(fclose(arquivo)!=EOF);
        if (ok && !lreduzida) mudado=0;
      }
      if (ok) {
        sprintf(buf,"List saved in file %s",texto);
        ultima(buf);
      }
      else ultima("Impossible to write file");
      if (lreduzida) plotarnos();
    break;
  }
}

#ifdef SUNXV
void desenhargrafico(Canvas canvas, Xv_Window paint_window, Display* dpy, Window xwin, Xv_xrectlist* xrects)
#endif
#ifdef XV_PC
void desenhargrafico(Xv_opaque obj)
#endif
{
#ifdef SUNXV
  Gdisplay=dpy;
  Gxid=xwin;
  Ggc=DefaultGC(dpy,DefaultScreen(dpy));
#endif
  redesenhar();
  pronto=1;
}

#ifdef SUNXV
void tratareventos(Xv_window window, Event* event)
#endif
#ifdef XV_PC
void tratareventos(Xv_opaque obj)
#endif
{
  int xkey,k1;

  if (!pronto) return;
  if ((event_id(event)==LOC_MOVE) && (estado!=marcando)) return;
  /* Locate cursor */
  x=((event_x(event)+8*z)/(16*z))*16;
  y=((event_y(event)+8*z)/(16*z))*16;
  if (abs(event_y(event)-y*z)>abs(event_x(event)-x*z)) {
    if (event_y(event)>y*z) y=y+8; else y=y-8;
  }
  else {
    if (event_x(event)>x*z) x=x+8; else x=x-8;
  }
  if (x<0 || x>pxmax || y<0 || y>pymax) return;
  if (estado==marcando) {
    desenharbloco();
    bf=x/16+xmin+256*((pymax-y)/16+ymin);
    if (vertical()) bf+=256; else bf++;
    desenharbloco();
  }
  no1=x/16+xmin+256*((pymax-y)/16+ymin);
  if (vertical()) no2=no1+256; else no2=no1+1;
  xkey=event_id(event);
  if (incluir((short int) xkey)) return;
  switch(xkey) {
    case MS_LEFT: parametrosdeum(1);
    break;
    case KCTRLB:
    case MS_MIDDLE: /* Start/end/remove block */
      if (estado==normal) {
	estado=marcando;
	bi=no2; bf=no2;
	desenharbloco();
	ultima("Marking block");
      }
      else if (estado==marcando) {
	ultima("Block marked");
	estado=marcado;
	if (bi>bf) { k=bi; bi=bf; bf=k;}
	if (lo(bi)>lo(bf)) {
	  k=lo(bi);
	  bi=(bi & 0xFF00) | lo(bf);
	  bf=(bf & 0xFF00) | k;
	}
      }
      else {
	desenharbloco();
	ultima("Block unmarked");
	estado=normal;
      }
    break;
    case KTAB: inverter();
    break;
    case KBS: refletir();
    break;
    case KDEL: eliminar();
    break;
    case '?':
    case KF1:
#ifdef SUNXV
    if event_is_down(event)
#endif
      help();
    break;
    case KCTRLV:
    case KEY_TOP(2): /* Block copy */
    case KEY_TOP(3): /* Block move */
      if (estado==marcado) {
        cp=(xkey==KEY_TOP(2));
        /* Testar se o bloco cabe na tela */
        j=lo(no2)+lo(bf)-lo(bi);
        k=hi(no2)+hi(bf)-hi(bi);
        ok=(j<=128) && (k<128);
        /* Testar se ha elementos no destino */
        if (ok) {
          l=256;
          k=l*k+j;
          i=0;
          while (ok && (i<ne)) {
            i++;
            fora_o=0; fora_d=0;
            { elemento* with1=&lista[i-1];
              for (l=0; l<biblioteca[with1->tp-1].nnos; l++) {
                if (fora(with1->grade[l],no2,k)) fora_d=1;
                if (fora(with1->grade[l],bi,bf)) fora_o=1;
              }
            }
            ok=((!cp) && ((!fora_o) || fora_d)) || (cp && fora_d);
            if (!ok) ultima("Block overlaps elements");
          }
        }
        else ultima("Block beyond limits");
        /* Copiar/mover bloco */
        if (ok) {
          k1=ne;
          for (i=1; i<=k1; i++) if ((!cp) || (ne<maxlista)) {
            ok=1;
            { elemento* with1=&lista[i-1];
              for (j=0; j<biblioteca[with1->tp-1].nnos; j++)
              if (fora(with1->grade[j],bi,bf)) ok=0;
            }
            if (ok) {
              if (cp) {
                ne++;
                lista[ne-1]=lista[i-1];
                l=ne;
              }
              else l=i;
              { elemento* with1=&lista[l-1];
                if (!cp) plotarelemento(l,0);
                for (j=0; j<4; j++) {
                  k=256;   /* senao da overflow?! */
                  with1->grade[j]=with1->grade[j]+lo(no2)-lo(bi)+k * (hi(no2)-hi(bi));
                }
              }
              plotarelemento(l,1);
            }
          }
          desenharbloco();
          k=256;   /* senao da overflow?! */
          l=lo(no2)-lo(bi)+k * (hi(no2)-hi(bi));
          bi=bi+l; bf=bf+l;
          desenharbloco();
          mudado=1;
          ultima("");
        }
      }
      else ultima("No block marked");
    break;
    case KCTRLY:
    case KEY_TOP(4): /* Delete block */
      if (estado==marcado) {
        if (notice("Delete block?")) {
          k=0;
          while (k<ne) {
            k++;
            { elemento* with1=&lista[k-1];
              fora_o=0;
              for (j=0; j<biblioteca[with1->tp-1].nnos; j++)
                if (fora(with1->grade[j],bi,bf)) fora_o=1;
              if (!fora_o) {
                plotarelemento(k,0); remover(k); k--;
              }
            }
          }
          mudado=1;
          close_window(ftexto);
        }
        ultima("");
      }
      else ultima("No block marked");
    break;
    case KEY_TOP(10): /* Plot nodes */
      if (ne>0) {
        ordenar();
        converterlista();
        if (ok) {
          plotarnos();
          ultima("");
        }
      }
    break;
    case KCTRLK: redesenhar();
    break;
    case KCTRLL:
      if (notice("Erase everything?")) {
	ne=0;
	redesenhar();
      }
    break;
    case KCTRLW: /* Show connections */
      XSetForeground(Gdisplay,Ggc,pcor[3]);
      XSetLineAttributes(Gdisplay,Ggc,z,LineOnOffDash,CapButt,JoinMiter);
      for (k=1; k<=ne; k++)
        { elemento* with1=&lista[k-1];
          if ((with1->nome[0]>='0') && (with1->nome[0]<='9')) {
            i=k;
            do { i--; }  while (!((i<1) || (strcmp(lista[i-1].nome,lista[k-1].nome)==0)));
            if (i>0) XDrawLine(Gdisplay,Gxid,Ggc,
              pontox(lista[k-1].grade[1])*z,
              pontoy(lista[k-1].grade[1])*z,
              pontox(lista[i-1].grade[1])*z,
              pontoy(lista[i-1].grade[1])*z
            );
          }
        }
      XSetLineAttributes(Gdisplay,Ggc,z,LineSolid,CapButt,JoinMiter);
    break;
    case KCTRLZ: /* List .cir */
      if (ne>0) listarlista(0);
    break;
    case KCTRLO: /* Sort */
      if (ne>0) {
	ordenar();
	redesenhar();
      }
    break;
    case KCTRLQ: gerarnetlist();
    break;
    case KCTRLU: /* Read value list */
      lerlv();
    break;
    case KEY_TOP(9):
    case KCTRLS: /* Change zoom level */
      if (z<ZOOM_MAX) z++;
      else z=1;
      redesenhar();
    break;
    case KCTRLT: /* List value list */
      if (nv==0) {
        ultima("* No active value list");
      }
      else listarlv();
    break;
    case KCTRLA:salvarc=(notice("Save texts in netlist?"));
      if (salvarc) msg("Comments and commands will be saved");
      else msg("Comments and commands will not be saved");
    break;
    case MS_RIGHT:
    case KCTRLR: /* Center */
      xmin=lo(no1)-(mptx>>1);
      if (xmin<0) xmin=0;
      if (xmin+mptx>128) xmin=128-mptx;
      ymin=hi(no1)-(mpty>>1);
      if (ymin<0) ymin=0;
      if (ymin+mpty>128) ymin=127-mpty;
      redesenhar();
    break;
#ifdef XV_PC
    case KESC:
      open_window(ftty);
    break;
#endif
    case '!':
      sprintf(buf,"ne=%d no1=%d no2=%d xmin=%d ymin=%d xmax=%d ymax=%d (%d-%d)-(%d-%d)",
              ne,no1,no2,xmin,ymin,xmax,ymax,lo(no1),hi(no1),lo(no2),hi(no2));
      msg(buf);
      break;
  }
}

#ifdef XV_PC
/* Diretorio */

void LerDiretorio(Xv_opaque obj)
{

  struct ffblk srec;
  short done;

  settextstyle(SMALL_FONT,HORIZ_DIR,4);
  if (obj!=cdiretorio) {
    setfillstyle(SOLID_FILL,cdiretorio->back_color);
    bar(0,0,cdiretorio->dx,cdiretorio->dy);
  }
  nomes=cdiretorio->dx/78;
  total=0;
  done=findfirst(tmask->v.stextfield.panel_value,&srec,0);
  while (!done) {
    outtextxy(total%nomes*78+3,total/nomes*8,srec.ff_name);
    done=findnext(&srec);
    total++;
  }
  total--;
}

void EscolherArquivo(Xv_opaque obj)
{
  struct ffblk srec;
  char drive[MAXDRIVE];
  char dir[MAXDIR];
  char file[MAXFILE];
  char ext[MAXEXT];
  short i,k,done;

  if (ie_code!=MS_LEFT)
    return;
  k=(ie_locx-3)/78;
  if (k>=nomes)
    return;
  k+=(ie_locy-3)/8*nomes;
  if (k>total)
    return;
  i=0;
  done=findfirst(tmask->v.stextfield.panel_value,&srec,0);
  while ((!done)&&(i<k)) {
    done=findnext(&srec);
    i++;
  }
  fnsplit(tmask->v.stextfield.panel_value,drive,dir,file,ext);
  sprintf(ttexto->v.stextfield.panel_value,"%s%s%s",drive,dir,srec.ff_name);
  xv_set(ttexto,ttexto->xv_label);
}
#endif

void main(int argc,char *argv[])
{
#ifdef SUNXV
  printf("\nEdFil, %s\nBy Antonio Carlos M. de Queiroz\n",versao);
  xv_init(XV_INIT_ARGC_PTR_ARGV,&argc,argv,NULL);
#endif
#ifdef XV_PC
  xv_init(0,0);
  normal_bsize=20000;
#endif
  nv=0;
  estado=normal;
  ne=0; numnos=0;
  mudado=0;
  eledit=1;
  s=' ';
  lisval[0]='\0';
  prog[0]='\0';
  afazer=ler_cir;
  if (argc>1) strcpy(rede,argv[1]);
  else rede[0]='\0';
  /* Criacao da interface */
  menufim=xv_create(NULL,MENU,
    MENU_TITLE_ITEM,"Options:",
    MENU_STRINGS,"Load circuit","Save circuit","Read value list","Generate netlist","Help","Quit",NULL,
    MENU_NOTIFY_PROC,tratarmenu,
    NULL);
  fedfil=xv_create(NULL,FRAME,
    XV_LABEL,"X_EdFil",
    XV_WIDTH,639,
    XV_HEIGHT,479,
    XV_X,0,
    XV_Y,0,
#ifdef SUNXV
    FRAME_SHOW_FOOTER,TRUE,
    FRAME_NO_CONFIRM,FALSE,
#endif
#ifdef XV_PC
    ADJUST_EXIT,0,
#endif
  NULL);
#ifdef SUNXV
  closed_image=(Server_image)xv_create(NULL,SERVER_IMAGE,
    XV_WIDTH,64,
    XV_HEIGHT,64,
    SERVER_IMAGE_BITS,closed_bits,
    NULL);
  icon=(Icon)xv_create(fedfil,ICON,
    ICON_IMAGE,closed_image,
    XV_X,100,
    XV_Y,100,
    NULL);
  xv_set(fedfil,FRAME_ICON,icon,NULL);  
#endif
#ifdef XV_PC
  multima=xv_create(fedfil,message,XV_X,40,NULL);
#define painelgrafico fedfil
#endif
#ifdef SUNXV
  painelgrafico=(Panel)xv_create(fedfil,PANEL,
    XV_X,0,
    XV_Y,0,
    XV_WIDTH,  WIN_EXTEND_TO_EDGE,
    XV_HEIGHT, 30,
    PANEL_LAYOUT,PANEL_HORIZONTAL,
    NULL);
#endif
  xv_create(painelgrafico,PANEL_BUTTON,
    PANEL_LABEL_STRING, "File",
    PANEL_ITEM_MENU, menufim,
#ifdef XV_PC
    NOTIFY_HANDLER, abremenufim,
#endif
    NULL);
#ifdef SUNXV
  {Display *dpy=(Display*)xv_get(fedfil,XV_DISPLAY);
    if (DefaultDepth(dpy,DefaultScreen(dpy))>1)
      cms=xv_create(NULL,CMS,
        CMS_TYPE, XV_STATIC_CMS,
        CMS_SIZE,5,
        CMS_NAMED_COLORS, "black","white","green","red","gold",NULL,
        NULL);
    else {
      printf("EdFil in black and white mode\n");
      cms=xv_create(NULL,CMS,
        CMS_SIZE,5,
        CMS_TYPE, XV_STATIC_CMS,
        CMS_NAMED_COLORS, "black","white","white","white","white",NULL,
        NULL);
    }
    pcor=(unsigned long *)xv_get(cms,CMS_INDEX_TABLE);
  }
  if (cms==NULL) printf("Problems in colormap segment creation\n");
#endif
#ifdef XV_PC
  pcor[0]=BLACK;
  pcor[1]=WHITE;
  pcor[2]=YELLOW;
  pcor[3]=BROWN;
  pcor[4]=GREEN;
#endif
  c_element=pcor[0]^pcor[1];
  c_block=pcor[3]^pcor[0];
  cgrafico=xv_create(fedfil,CANVAS,
#ifdef SUNXV
    WIN_CMS,cms,
    XV_Y,30,
    CANVAS_X_PAINT_WINDOW,TRUE,
    CANVAS_REPAINT_PROC,desenhargrafico,
#endif
#ifdef XV_PC
    NOTIFY_HANDLER,desenhargrafico,
    EVENT_HANDLER,tratareventos,
    FORE_COLOR,c_white,
    BACK_COLOR,c_black,
    XV_Y,15,
#endif
    NULL);
#ifdef SUNXV
  xv_set(canvas_paint_window(cgrafico),
    WIN_EVENT_PROC,tratareventos,
    WIN_CONSUME_EVENTS,
      WIN_ASCII_EVENTS, LOC_DRAG, LOC_MOVE, WIN_MOUSE_BUTTONS,
      WIN_TOP_KEYS, WIN_META_EVENTS,
      NULL,
    WIN_IGNORE_EVENTS, WIN_UP_EVENTS, WIN_UP_ASCII_EVENTS,
      NULL,
    NULL);
#endif
#ifdef XV_PC
  ftty=xv_create(fedfil,FRAME,
    XV_LABEL,"EdFil - Messages",
    XV_X,7,
    XV_Y,39,
    XV_WIDTH,360,
    XV_HEIGHT,360,
    NULL);
  ttymsg=xv_create(ftty,TEXTSW,NULL);
#endif
  ftexto=xv_create(fedfil,FRAME_CMD,
    XV_LABEL,"File to edit (.cir)",
    XV_WIDTH,510,
    XV_HEIGHT,40,
    XV_X,65,
    XV_Y,70,
#ifdef XV_PC
    DYMIN,40,
#endif
    NULL);
#ifdef SUNXV
  ptexto=xv_create(ftexto,PANEL,
    XV_X,0,XV_Y,0,
    XV_WIDTH,WIN_EXTEND_TO_EDGE,
    XV_HEIGHT,WIN_EXTEND_TO_EDGE,
    PANEL_LAYOUT,PANEL_HORIZONTAL,
    NULL);
#endif
#ifdef XV_PC
#define ptexto ftexto
#endif
  ttexto=xv_create(ptexto,PANEL_TEXT,
    PANEL_NOTIFY_PROC, processaredicao,
    PANEL_VALUE_DISPLAY_LENGTH,57,
    NULL);
#ifdef XV_PC
  strcpy(ttexto->v.stextfield.panel_value,rede);
  ftexto->v.sframe.mouse_obj=o_base;
#endif
#ifdef SUNXV
  xv_set(ttexto,PANEL_VALUE,rede,NULL);
#endif
  xv_create(ptexto,PANEL_BUTTON,
    PANEL_LABEL_STRING,"ok",
    XV_X,470,
    PANEL_NOTIFY_PROC, processaredicao,
    NULL);
#ifdef XV_PC
  fdiretorio=xv_create(NULL,FRAME,
    XV_LABEL,"Directory",
    DX,255,
    X,ftexto->x,
    Y,ftexto->y+ftexto->dy+1,
    DY,159,
    NULL);
  tmask=xv_create(fdiretorio,TEXTFIELD,
    XV_LABEL,"Mask",
    VALUE_LENGTH,24,
    PANEL_VALUE,"*.cir",
    NOTIFY_HANDLER,LerDiretorio,
    NULL);
  cdiretorio=xv_create(fdiretorio,CANVAS,
    Y,15,
    NOTIFY_HANDLER,LerDiretorio,
    EVENT_HANDLER,EscolherArquivo,
    NULL);
#endif
  open_window(fedfil);
#ifdef XV_PC
  open_window(fdiretorio);
#endif
  xv_main_loop(ftexto);
#ifdef XV_PC
  restorecrtmode();
#endif
  printf("EdFil terminated\n");
#ifdef SUNXV
  exit(0);
#endif
}
