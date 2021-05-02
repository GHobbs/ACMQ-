/*
This program generates all possible Tuckerman traverses for given orders
of hexaflexagons, and finds the corresponding strips that when folded
result in hexaflexagons with those maps.

By Antonio Carlos M. de Queiroz - acmq@coe.ufrj.br

Version 0.0 28/01/1999 Interface in development
Version 1.0 04/02/1999 Old method and new method implemented
Version 1.1 05/02/1999 Drawing one TT
Version 1.2 07/02/1999 Marks start and "1" corners, colors overlaps
Version 1.3 09/02/1999 Using long long ints and gnu C
Version 1.4 10/02/1999 Marks "0" corners, plots several TTs
Version 1.5 11/02/1999 Plots only by orders
Version 1.6 03/03/1999 Plots face numbers
Version 1.7 25/03/1999 Strip generation
Version 1.8 29/03/1999 Complete strips
Version 1.9 01/04/1999 Normalized strips
*/

#define version "1.9 01/04/1999"
#include <string.h>
#include <values.h>
#include <math.h>
/* From the XView-PC interface (http://www.coe.ufrj.br/~acmq/xview-pc.html) */
#include "xview.h"
#include "xv_var.h"
#include "xprintf.h"
#include "extkeys.h"

#define s_int int
#define INT v.stextfield.panel_int
#define SEL v.ssetting.sel_setting

/* To compile with my 1977 TT generation code (inefficient) */
/* #define OLDMETHOD */
#define l_int long long int
#define LIMIT 500000
#define MAXLONGLONG 0x7fffffffffffffffll
#define MAXORDER 17

l_int H[LIMIT];
s_int last[MAXORDER];
l_int test,base,mask;
s_int n,ni,last_found,b,bmax,nbase,generated=0;
char buf[256];
FILE *outfile;

/* Declaration of the interface objects */
Xv_opaque menu1,menu2;
Xv_opaque fmessages,tty1;
Xv_opaque fparameters,tomax,tfile,torder,tnumber,
  tview,bgenerate,bview,sshow,sfaces,sview,scomplete,snorm;
Xv_opaque fmain,canvas1;

char* printbin(l_int x, s_int bmax)
{
  s_int bb;

  for (bb=bmax; bb>=0; bb--)
    if (x & (1ll<<bb)) buf[bmax-bb]='1'; else buf[bmax-bb]='0';
  buf[bmax+1]=0;
  return buf;
}

l_int inverse(l_int x, s_int bmax)
{
s_int i;
l_int t,m,k;

  t=0; m=1;
  for (i=0; i<=bmax; i++) {
    if (x&m) k=1; else k=0;
    t=(t<<1)|k;
    m=m<<1;
  }
  return t;
}

void draw_tt(int nn, int sxmin, int sxmax, int symin, int symax)
{
/* For the arrows */
#define ANGLE 30
#define LENGTH 0.2
#define CARROW LIGHTGRAY
  s_int g,b,bmax,ix,iy,ix0,iy0,c,cl,c1,len,lf,bb,i,found;
  double x,y,dx,dy,x60,y60,x240,y240,t,ax,bx,ay,by,xmax,xmin,ymax,ymin,a1x,a2x,a1y,a2y;
  char buf[256], buf1[5];
  char bin[3*(MAXORDER-2)+1],num[3*(MAXORDER-2)+1];
  double xx[3*(MAXORDER-2)+1],yy[3*(MAXORDER-2)+1];
  char number[3*(MAXORDER-2)+1][8]; /* ok for 8 overlaps */

  if (nn>last[tomax->INT]) return;
  xmin=0; xmax=1; ymin=0; ymax=0;
  x60=0.5;
  y60=sqrt(3)/2;
  x240=-x60;
  y240=-y60;
  for (g=3; nn>last[g]; g++);
  bmax=3*(g-2)-1;
  if (tnumber->INT==1) {
    sprintf(buf,"#%d (n=%d #%d): %llo",nn,g,nn-last[g-1],H[nn]);
    xv_set(fmain,buf);
  }
  /* Finds the limits of the drawing */
  dx=x60; dy=-y60;
  x=dx;
  y=dy;
  xx[0]=0; yy[0]=0;
  for (b=bmax; b>0; b--) {
    xx[b]=x; yy[b]=y;
    if ((H[nn]&(1ll<<b))!=0ll) {
      t=dx*x60-dy*y60;
      dy=dx*y60+dy*x60;
      dx=t;
    }
    else {
      t=dx*x240-dy*y240;
      dy=dx*y240+dy*x240;
      dx=t;
    }
    x+=dx;
    y+=dy;
    if (x>xmax) xmax=x;
    else if (x<xmin) xmin=x;
    if (y>ymax) ymax=y;
    else if (y<ymin) ymin=y;
  }
  /* Compute mapping factors */
  ax=(sxmax-sxmin)/(xmax-xmin);
  ay=(symin-symax)/(ymax-ymin);
  if (ax>(-ay)) ax=-ay; else ay=-ax;
  bx=sxmin-ax*xmin;
  by=symin-ay*ymax;
  /* Draws TT */
  setlinestyle(SOLID_LINE,0,THICK_WIDTH);
  moveto(bx,by);
  setcolor(WHITE);
  setfillstyle(SOLID_FILL,GREEN);
  ix0=(int)(bx+0.499);
  iy0=(int)(by+0.499);
  for (b=bmax; b>=0; b--) {
    ix=(int)(ax*xx[b]+bx+0.499);
    iy=(int)(ay*yy[b]+by+0.499);
    c=getpixel((ix+ix0)/2,(iy+iy0)/2);
    if (c!=BLACK) setcolor(c-1);
    else setcolor(WHITE);
    lineto(ix,iy);
    if ((H[nn]&1ll<<b)==0ll) bar(ix-3,iy-3,ix+3,iy+3);
    ix0=ix;
    iy0=iy;
  }
  setfillstyle(SOLID_FILL,RED);
  ix=(int)(bx+0.499);
  iy=(int)(by+0.499);
  bar(ix-3,iy-3,ix+3,iy+3);
  /* Plots arrows and face numbers */
  if (sfaces->SEL==2) {
    settextstyle(SMALL_FONT,HORIZ_DIR,4);
    /*setlinestyle(SOLID_LINE,0,1);*/
    t=M_PI/180*(120-ANGLE);
    a1x=LENGTH*cos(t);
    a1y=LENGTH*sin(t);
    t=M_PI/180*(120+ANGLE);
    a2x=LENGTH*cos(t);
    a2y=LENGTH*sin(t);
    bin[0]=bin[1]=bin[2]=0;
    num[0]=3; num[1]=1; num[2]=2;
    len=2;
    lf=3;
    for (b=bmax; b>=0; b--) {
      ix0=ix; /* Must be the last face */
      iy0=iy;
      ix=(int)(ax*xx[b]+bx+0.499);
      iy=(int)(ay*yy[b]+by+0.499);
      setcolor(CARROW);
      ix0=(2*ix0+3*ix)/5;
      iy0=(2*iy0+3*iy)/5;
      line(ix0,iy0,ix0+ax*a1x,iy0+ay*a1y);
      line(ix0,iy0,ix0+ax*a2x,iy0+ay*a2y);
      if ((H[nn]&(1ll<<b))!=0ll) {
        t=a1x*x60-a1y*y60;
        a1y=a1x*y60+a1y*x60;
        a1x=t;
        t=a2x*x60-a2y*y60;
        a2y=a2x*y60+a2y*x60;
        a2x=t;
        c1=1;
      }
      else {
        t=a1x*x240-a1y*y240;
        a1y=a1x*y240+a1y*x240;
        a1x=t;
        t=a2x*x240-a2y*y240;
        a2y=a2x*y240+a2y*x240;
        a2x=t;
        c1=0;
      }
      if (b>0) {
        if (c1==1) cl=GREEN;
        else cl=LIGHTBLUE;
      }
      else cl=RED;
      setfillstyle(SOLID_FILL,cl);
      setcolor(cl);
      /* Finds next face number */
      bb=bmax-b;
      if ((c1==1) & (bin[bb]==0)) {
        for (i=len+3; i>=bb+3; i--) {
          bin[i]=bin[i-3];
          num[i]=num[i-3];
        }
        bin[bb]=1;
        bin[bb+1]=0;
        bin[bb+2]=0;
        bin[bb+3]=1;
        num[bb+1]=lf+1;
        if (bb==0) num[bb+2]=num[len+3]; /* Always 2 */
        else num[bb+2]=num[bb-1];
        num[bb+3]=num[bb];
        len+=3;
        lf++;
      }
      /* Checks for overlaps and plots face number */
      found=0;
      if (b!=bmax) {
        for (i=b+1; i<=bmax; i++) {
          c=(fabs(xx[b]-xx[i])<0.01)&&(fabs(yy[b]-yy[i])<0.01);
          if (c) {
            found=1; c1=i;
            break;
          }
        }
      }
      if (!found) {
        number[b][0]=num[bb];
        number[b][1]=0;
      }
      else {
        strcpy(number[b],number[c1]);
        if (strchr(number[b],num[bb])==NULL) {
          c=strlen(number[b]);
          number[b][c]=num[bb];
          number[b][c+1]=0;
        }
      }
      buf[0]=0;
      for (i=0; i<strlen(number[b]); i++) {
        sprintf(buf1,"%d,",number[b][i]);
        strcat(buf,buf1);
      }
      buf[strlen(buf)-1]=0;
      c=textwidth(buf)/2+2;
      if (c<7) c=7;
      pieslice(ix,iy,0,359,c);
      setcolor(WHITE);
      outtextxy(ix-textwidth(buf)/2+1,iy-textheight(buf)/2-2,buf);
    }
  }
}

void draw_strip(int nn, int sxmin, int sxmax, int symin, int symax)
{
  s_int g,b,bmax,lf,bb,i,j,f1,f2,len,ix,iy,ix0,iy0,c,found,c1;
  double x,y,dx,dy,x60,y60,x300,y300,t,ax,bx,ay,by,xmax,xmin,ymax,ymin,x1,y1,x2,y2;
  char buf[256],bufb[256],buf1[5];
  char bin[3*(MAXORDER-2)+1],num[3*(MAXORDER-2)+1];
  char ss[3*MAXORDER],sA[3*MAXORDER],sB[3*MAXORDER];
  char tA[3*MAXORDER],tB[3*MAXORDER];
  double xx[3*MAXORDER],yy[3*MAXORDER];
  char number[3*MAXORDER][8]; /* ok for 8 overlaps */
  l_int testd,testi,testdm,testim,largest,xodd;

  if (nn>last[tomax->INT]) return;
  for (g=3; nn>last[g]; g++);
  bmax=3*(g-2)-1;
  /* Rebuilds the TT and the strip, both numbered */
  bin[0]=bin[1]=bin[2]=0;
  num[0]=3; num[1]=1; num[2]=2;
  len=2;
  lf=3;
  ss[0]=1; ss[1]=0; ss[2]=1;
  sA[0]=1; sA[1]=2; sA[2]=2;
  sB[0]=3; sB[1]=3; sB[2]=1;
  for (b=bmax; b>=0; b--) {
    bb=bmax-b;
    if (((H[nn]&(1ll<<b))!=0ll) && (bin[bb]==0)) {
      /* Saves face numbers */
      f1=num[bb];
      if (bb==0) f2=num[len];
      else f2=num[bb-1];
      /* Shifts right the remaining of the TT */
      for (i=len+3; i>=bb+3; i--) {
        bin[i]=bin[i-3];
        num[i]=num[i-3];
      }
      /* Adds new triangle and face numbers */
      bin[bb]=1;
      bin[bb+1]=0;
      bin[bb+2]=0;
      bin[bb+3]=1;
      num[bb+1]=lf+1;
      if (bb==0) num[bb+2]=num[len+3]; /* Always 2 */
      else num[bb+2]=num[bb-1];
      num[bb+3]=num[bb];
      /* Finds face number pair in the strip */
      for (i=0; i<=lf; i++)
        if (((sA[i]==f1)&&(sB[i]==f2)) || ((sA[i]==f2)&&(sB[i]==f1))) {
          j=i;
          goto ok;
        }
      xprintf(tty1,"Face pair not found!\n");
      close_window(active_w);
      return;
      ok:
      /* Reflectoclone at face j */
      /* Shifts right the remaining of the strip, inverting it */
      for (i=lf+1; i>j+1; i--) {
        sA[i]=sB[i-1];
        sB[i]=sA[i-1];
        ss[i]=1-ss[i-1];
      }
      /* Adds new fold in the strip and new face number */
      if (ss[j]==1) {/* Reflectoclone by the front side */
        ss[j]=0; ss[j+1]=1;
        sB[j+1]=sA[j];
        sA[j]=sA[j+1]=lf+1;
      }
      else {/* Reflectoclone by the back side */
        ss[j]=1; ss[j+1]=0;
        sA[j+1]=sB[j];
        sB[j]=sB[j+1]=lf+1;
      }
      len+=3;
      lf++;
    }
  }
  if (snorm->SEL==2) { /* Normalizes strip to maximum binary representation */
    testd=testi=0ll;
    for (b=0; b<g; b++)
      if (ss[g-b-1]==1) testd|=1ll<<b;
      else testi|=1ll<<b;
    /* Necessary to test mirror images too */
    testdm=inverse(testd,g-1);
    testim=inverse(testi,g-1);
    largest=0ll; i=0; j=0;
    if ((g&1)==1) xodd=1ll; else xodd=0ll;
    for (b=0; b<g; b++) {
      if (testd>largest) {largest=testd; i=b; j=0;}
      if (testi>largest) {largest=testi; i=b; j=1;}
      if (testdm>largest) {largest=testdm; i=b; j=2;}
      if (testim>largest) {largest=testim; i=b; j=3;}
      testd=(testd>>1)|(((testd&1ll)^xodd)<<(g-1));
      testi=(testi>>1)|(((testi&1ll)^xodd)<<(g-1));
      testdm=(testdm>>1)|(((testdm&1ll)^xodd)<<(g-1));
      testim=(testim>>1)|(((testim&1ll)^xodd)<<(g-1));
    }
    for (b=0; b<g; b++) {
      ss[b]=((largest&1ll<<(g-b-1))!=0ll);
      switch (j) {
        case 0: /* Just rotate */
          if (b>=i) {
            tA[b]=sA[b-i];
            tB[b]=sB[b-i];
          }
          else
            if ((g&1)==1) {
              tA[b]=sB[b-i+g];
              tB[b]=sA[b-i+g];
            }
            else {
              tA[b]=sA[b-i+g];
              tB[b]=sB[b-i+g];
            }
        break;
        case 1: /* Rotate and invert (flip strip) */
          if (b>=i) {
            tA[b]=sB[b-i];
            tB[b]=sA[b-i];
          }
          else
            if ((g&1)==1) {
              tA[b]=sA[b-i+g];
              tB[b]=sB[b-i+g];
            }
            else {
              tA[b]=sB[b-i+g];
              tB[b]=sA[b-i+g];
            }
        break;
        case 2: /* Rotate mirror (flip strip, but not numbers) */
          if (b>=i) {
            tA[b]=sA[g-1-(b-i)];
            tB[b]=sB[g-1-(b-i)];
          }
          else
            if ((g&1)==1) {
              tA[b]=sB[-1-(b-i)];
              tB[b]=sA[-1-(b-i)];
            }
            else {
              tA[b]=sA[-1-(b-i)];
              tB[b]=sB[-1-(b-i)];
            }
        break;
        case 3: /* Rotate and invert mirror (flip strip and numbers ) */
          if (b>=i) {
            tA[b]=sB[g-1-(b-i)];
            tB[b]=sA[g-1-(b-i)];
          }
          else
            if ((g&1)==1) {
              tA[b]=sA[-1-(b-i)];
              tB[b]=sB[-1-(b-i)];
            }
            else {
              tA[b]=sB[-1-(b-i)];
              tB[b]=sA[-1-(b-i)];
            }
        break;
      }
    }
    for (b=0; b<g; b++) {
      sA[b]=tA[b];
      sB[b]=tB[b];
    }
  }
  if (sview->SEL==3) { /* Just lists results */
    xprintf(tty1,"\n#%d (n=%d #%d): %llo\n",nn,g,nn-last[g-1],H[nn]);
    buf[0]=0;
    for (bb=0; bb<=bmax; bb++) {
      sprintf(buf1,"%2d",bin[bb]);
      strcat(buf,buf1);
    }
    xprintf(tty1,"TT:\t%s\n",buf);
    buf[0]=0;
    for (bb=0; bb<=bmax; bb++) {
      sprintf(buf1,"%2d",num[bb]);
      strcat(buf,buf1);
    }
    xprintf(tty1,"Faces:\t%s\n",buf);
    buf[0]=0;
    for (bb=0; bb<g; bb++) {
      sprintf(buf1,"%2d",ss[bb]);
      strcat(buf,buf1);
    }
    xprintf(tty1,"Strip:\t\t%s\n",buf);
    buf[0]=0;
    for (bb=0; bb<g; bb++) {
      sprintf(buf1,"%2d",sA[bb]);
      strcat(buf,buf1);
    }
    xprintf(tty1,"Upper faces:\t%s\n",buf);
    buf[0]=0;
    for (bb=0; bb<g; bb++) {
      sprintf(buf1,"%2d",sB[bb]);
      strcat(buf,buf1);
    }
    xprintf(tty1,"Lower faces:\t%s\n",buf);
  }
  else { /* Draws strip */
    /* Update header (lists 1/3 of the strip only, as there is no space for a too long string) */
    if (tnumber->INT==1) {
      sprintf(buf,"#%d (n=%d #%d):",nn,g,nn-last[g-1]);
      i=strlen(buf);
      for (bb=0; bb<g; bb++) buf[i+bb]='0'+ss[bb];
      buf[i+g]=0;
      xv_set(fmain,buf);
    }
    if (scomplete->SEL==2) { /* Complete strip */
      for (b=0; b<g; b++) {
        if ((g&1)==0) {
          ss[b+g]=ss[b];
          sA[b+g]=sA[b];
          sB[b+g]=sB[b];
        }
        else {
          ss[b+g]=1-ss[b];
          sA[b+g]=sB[b];
          sB[b+g]=sA[b];
        }
        ss[b+2*g]=ss[b];
        sA[b+2*g]=sA[b];
        sB[b+2*g]=sB[b];
      }
      g=3*g;
      bmax=3*(g-2)-1;
    }
    /* Computes normalized coordinates of the face centers */
    x60=0.5;
    y60=sqrt(3)/2;
    x300=0.5;
    y300=-y60;
    xmin=-y60; xmax=y60;
    ymin=-1; ymax=0.5;
    dx=y60;
    dy=x60;
    x=y=0;
    for (bb=0; bb<g; bb++) {
      xx[bb]=x; yy[bb]=y;
      if (ss[bb]==1) {
        t=dx*x300-dy*y300;
        dy=dx*y300+dy*x300;
        dx=t;
      }
      else {
        t=dx*x60-dy*y60;
        dy=dx*y60+dy*x60;
        dx=t;
      }
      x+=dx;
      y+=dy;
      if (bb<g-1) {
        t=x+dx;
        if (t>xmax) xmax=t;
        else if (t<xmin) xmin=t;
        t=y+dy;
        if (t>ymax) ymax=t;
        else if (t<ymin) ymin=t;
      }
    }
    /* Computes mapping factors */
    ax=(sxmax-sxmin)/(xmax-xmin);
    ay=(symin-symax)/(ymax-ymin);
    if (ax>(-ay)) ax=-ay; else ay=-ax;
    bx=sxmin-ax*xmin;
    by=symin-ay*ymax;
    /* Draws ministrip */
    setlinestyle(SOLID_LINE,0,THICK_WIDTH);
    dx=y60;
    dy=x60;
    /* Draws skeleton */
    setcolor(DARKGRAY);
    moveto((int)(bx+0.499),(int)(by+0.499));
    for (bb=1; bb<g; bb++)
      lineto((int)(ax*xx[bb]+bx+0.499),(int)(ay*yy[bb]+by+0.499));
    /* Draws triangles, two edges per face */
    for (bb=0; bb<g; bb++) {
      if (bb) {
        dx=xx[bb]-xx[bb-1];
        dy=yy[bb]-yy[bb-1];
      }
      x1=xx[bb]-(dx*x300-dy*y300);
      y1=yy[bb]-(dx*y300+dy*x300);
      x2=xx[bb]-(dx*x60-dy*y60);
      y2=yy[bb]-(dx*y60+dy*x60);
      ix0=(int)(ax*x1+bx+0.499);
      iy0=(int)(ay*y1+by+0.499);
      moveto(ix0,iy0);
      /* Overlaps: Change color if the central point of the line is painted */
      ix=(int)(ax*(xx[bb]+dx)+bx+0.499);
      iy=(int)(ay*(yy[bb]+dy)+by+0.499);
      c=getpixel((ix+ix0)/2,(iy+iy0)/2);
      if (bb==g-1 && ss[bb]==0) setcolor(GREEN);
      else
        if (c!=BLACK && ss[bb]==1) setcolor(c-1);
        else setcolor(WHITE);
      lineto(ix,iy);
      ix0=ix; iy0=iy;
      ix=(int)(ax*x2+bx+0.499);
      iy=(int)(ay*y2+by+0.499);
      c=getpixel((ix+ix0)/2,(iy+iy0)/2);
      if (bb==g-1 && ss[bb]==1) setcolor(GREEN);
      else
        if (c!=BLACK && ss[bb]==0) setcolor(c-1);
        else setcolor(WHITE);
      lineto(ix,iy);
    }
    /* Start edge */
    setcolor(LIGHTRED);
    moveto((int)(ax*(-y60)+bx+0.499),(int)(ay*0.5+by+0.499));
    lineto((int)(bx+0.499),(int)(-ay+by+0.499));
    /* Plots face numbers */
    if (sfaces->SEL==2) {
      /* Checks for overlaps */
      settextstyle(SMALL_FONT,HORIZ_DIR,4);
      setfillstyle(SOLID_FILL,BLACK);
      for (bb=0; bb<g; bb++) {
        found=0;
        c1=0; /* Just to remove warning */
        if (bb!=0) {
          for (i=bb-1; i>=0; i--) {
            c=(fabs(xx[bb]-xx[i])<0.01)&&(fabs(yy[bb]-yy[i])<0.01);
            if (c) {
              found=1; c1=i;
              break;
            }
          }
        }
        if (!found) {
          number[bb][0]=bb+1; /* index in sA and sB +1 */
          number[bb][1]=0;
        }
        else {
          strcpy(number[bb],number[c1]);
          c=strlen(number[bb]);
          number[bb][c]=bb+1;
          number[bb][c+1]=0;
          number[c1][0]=0;
        }
      }
      /* Plots */
      for (bb=0; bb<g; bb++) if (number[bb][0]!=0) {
        buf[0]=0; bufb[0]=0;
        for (i=0; i<strlen(number[bb]); i++) {
          sprintf(buf1,"%d,",sA[number[bb][i]-1]);
          strcat(buf,buf1);
          sprintf(buf1,"%d,",sB[number[bb][i]-1]);
          strcat(bufb,buf1);
        }
        buf[strlen(buf)-1]=0;
        bufb[strlen(bufb)-1]=0;
        ix=(int)(ax*xx[bb]+bx+0.499);
        iy=(int)(ay*yy[bb]+by+0.499);
        setcolor(WHITE);
        outtextxy(ix-textwidth(buf)/2+1,iy-textheight(buf)/2-7,buf);
        setcolor(YELLOW);
        outtextxy(ix-textwidth(bufb)/2+1,iy-textheight(bufb)/2+3,bufb);
      }
    }
  }
}

/* Callback procedures */

void process_button(Xv_opaque obj)
{
  /* Notify handler for bgenerate */
  s_int new_one,p,list,save;
  l_int testd,testi,largest;
#ifdef OLDMETHOD
  s_int i;
  l_int known;
#endif

  list=((sshow->SEL&1)==1);
  save=((sshow->SEL&2)==2);
  last_found=1;
  H[1]=0;
  last[2]=0;
  last[3]=1;
  xprintf(tty1,"Starting:\n");
  if (save) outfile=fopen(tfile->v.stextfield.panel_value,"wt");
  if (list) xprintf(tty1,"Order 3\n   1    1 000 (0o 0)\n");
  else xprintf(tty1,"Order 3: 1\n");
  if (save) fprintf(outfile,"Order 3\n   1    1 000 (0o 0)\n");
  for (n=4; n<=tomax->INT; n++) {
    if (list) xprintf(tty1,"Order %d\n",n);
    else xprintf(tty1,"Order %d: ",n);
    if (save) fprintf(outfile,"Order %d\n",n);
    ni=0;
    /* For all the orders to be generated */
    last[n]=last[n-1];
    bmax=3*(n-3)-1;
    for (nbase=last[n-2]+1; nbase<=last[n-1]; nbase++) {
      /* For all the known hexaflexagons of order n-1 */
      base=H[nbase];
      mask=0ll;
      for (b=bmax; b>=0; b--) {
        mask=(mask>>1)|(1ll<<bmax);
        if ((base & (1ll<<b))==0ll) {
        /* For all the "0" bits */
          test=((base & mask)<<3)|(0x9ll<<b)|(base & (mask^MAXLONGLONG));
          testd=test;
          testi=inverse(test,bmax+3);
#ifdef OLDMETHOD
          /* Compares all rotations and reflections with all the known TTs */
          new_one=1;
          for (i=last[n-1]+1; i<=last[n]; i++) {
            /* For all the known hexaflexagons of order n */
            known=H[i];
            for (p=0; p<=bmax+3; p++) {
              /* For all rotations and inversions */
              if ((known==testd) || (known==testi)) new_one=0;
              if (new_one==0) goto NotNew;
              testd=(testd>>1)|((testd&1)<<(bmax+3));
              testi=(testi>>1)|((testi&1)<<(bmax+3));
            }
          }
          NotNew:
#else
          /* Finds the largest number within all rotations and inversions */
          largest=0;
          for (p=0; p<=bmax+3; p++) {
            /* For all rotations and inversions */
            if (testd>largest) largest=testd;
            if (testi>largest) largest=testi;
            testd=(testd>>1)|((testd&1ll)<<(bmax+3));
            testi=(testi>>1)|((testi&1ll)<<(bmax+3));
          }
          /* If it is smaller than the previous or is the first of this order, it is new */
          new_one=((largest<H[last[n]])||(last[n]==last[n-1]));
#endif
          if (new_one) {
            if (last[n]>=LIMIT) {
              xprintf(tty1,"Table limit (%d) reached\n",LIMIT);
              goto Abort;
            }
            last[n]++;
            ni++;
            if (list) xprintf(tty1,"%4d %4d %s (%lloo)\n",last[n],ni,printbin(test,bmax+3),test);
            if (save) fprintf(outfile,"%4d %4d %s (%lloo)\n",last[n],ni,printbin(test,bmax+3),test);
            H[last[n]]=test;
          }
        }
      }
    }
    xprintf(tty1,"%d types.\n",ni);
  }
  Abort:
  if (save) {
    fclose(outfile);
    xprintf(tty1,"Results saved in file %s\n",tfile->v.stextfield.panel_value);
  }
  generated=1;
}

void redraw_canvas(Xv_opaque obj)
{
  int sides,sidex,sidey,k,i,j,n,margin;
  char buf[100];

  /* Notify handler for canvas1 */
  if (!generated) return;
  if ((sfaces->SEL==2)&&(sview->SEL!=3))
    if ((scomplete->SEL==2)&&(sview->SEL==2)) tnumber->INT=1;
    else if (tnumber->INT>4) tnumber->INT=4;
  if (torder->INT>tomax->INT) torder->INT=tomax->INT;
  k=last[torder->INT]-last[torder->INT-1];
  if (tnumber->INT>k) tnumber->INT=k;
  if (tview->INT>k) tview->INT=k;
  sides=(int)(0.99+sqrt(tnumber->INT));
  sidex=canvas1->dx/sides;
  sidey=canvas1->dy/sides;
  n=last[torder->INT-1]+tview->INT;
  k=0;
  if (tnumber->INT!=1) {
    i=tview->INT+tnumber->INT-1;
    j=last[torder->INT]-last[torder->INT-1];
    if (i>j) i=j;
    sprintf(buf,"Order %d: #%d - #%d",
      torder->INT,
      tview->INT,
      i);
    xv_set(fmain,buf);
  }
  if (sfaces->SEL==1) margin=10;
  else margin=20;
  if (sview->SEL!=3) {
    setfillstyle(SOLID_FILL,BLACK);
    bar(0,0,canvas1->dx,canvas1->dy);
  }
  for (i=1; i<=sides; i++)
    for (j=1; j<=sides; j++) {
      if (sview->SEL==1)
        draw_tt(n+k,(j-1)*sidex+margin,j*sidex-margin,(i-1)*sidey+margin,i*sidey-margin);
      else
        draw_strip(n+k,(j-1)*sidex+margin,j*sidex-margin,(i-1)*sidey+margin,i*sidey-margin);
      k++;
      if ((k>=tnumber->INT) || (n+k>last[torder->INT])) goto End;
    }
  End:
}

void event_canvas(Xv_opaque obj)
{
  /* Event handler for canvas1 */
  if (!generated || sview->SEL==3) return;
  switch (ie_code) {
  case '+':
    if (tview->INT<last[torder->INT]-last[torder->INT-1]) {
      tview->INT++;
      redraw_canvas(NULL);
    }
    break;
  case '-':
    if (tview->INT>1) {
      tview->INT--;
      redraw_canvas(NULL);
    }
    break;
  case KPGUP:
    tview->INT+=tnumber->INT;
    if (tview->INT>last[torder->INT]-last[torder->INT-1])
      tview->INT=last[torder->INT]-last[torder->INT-1];
    redraw_canvas(NULL);
    break;
  case KPGDN:
    tview->INT-=tnumber->INT;
    if (tview->INT<1)
      tview->INT=1;
    redraw_canvas(NULL);
    break;
  case KTAB:
    if (sview->SEL==1) sview->SEL=2;
    else sview->SEL=1;
    redraw_canvas(NULL);
    break;
  case KF1:
    if (snorm->SEL==1) snorm->SEL=2;
    else snorm->SEL=1;
    redraw_canvas(NULL);
    break;
  }
}

void process_menu(Xv_opaque obj)
{
  /* Notify handler for menu1 */
  switch (obj->v.smenu.sel_menu) {
  case 1: open_window(fparameters);
          break;
  case 2: open_window(fmessages);
          break;
  case 3: if (active_w!=fmain) close_window(active_w);
          break;
  case 4: xv_end=1;
          break;
  }
}

void process_msgs(Xv_opaque obj)
{
  /* Notify handler for menu2 */
  int i;

  switch (obj->v.smenu.sel_menu) {
  case 1: tty1->v.stty.bstart=0;
          tty1->v.stty.tstart=0;
          tty1->v.stty.tend=0;
          ttysw_output(tty1,"");
          break;
  case 2: outfile=fopen("hexa.msg","wt");
          i=tty1->v.stty.bstart;
          while (i!=tty1->v.stty.tend) {
            putc(tty1->v.stty.Pb[i],outfile);
            if (i<tty1->v.stty.bsize) i++; else i=0;
          }
          fclose(outfile);
          xprintf(tty1,"Messages saved in file hexa.msg\n");
          break;
  }
}

void process_drawing(Xv_opaque obj)
{
  /* Notify handler for bshow */
  while (active_w!=fmain) close_window(active_w);
  redraw_canvas(NULL);
}

void main()
{
  /* Inicialization */
  normal_bsize=65000;
  normal_length=8;
  xv_init(0,0);
  /* Menu creation */
  menu1=xv_create(NULL,MENU,
    XV_LABEL,"Menu",
    ITEM_MENU,
      "Parameters",
      "Messages",
      "Close",
      "Exit",
    NULL,
    SEL_MENU,2,
    NOTIFY_HANDLER,process_menu,
    NULL);
  menu2=xv_create(NULL,MENU,
    XV_LABEL,"Messages",
    ITEM_MENU,
      "Clear",
      "Save",
    NULL,
    NOTIFY_HANDLER,process_msgs,
    NULL);
  /* Interface objects creation */
  fmain=xv_create(NULL,FRAME,
    XV_LABEL,"Hexaflexagon map finder",
    DX,getmaxx(),
    DY,getmaxy(),
    MENU_NAME,menu1,
    ADJUST_EXIT,0,
    NULL);
  canvas1=xv_create(fmain,CANVAS,
    NOTIFY_HANDLER,redraw_canvas,
    EVENT_HANDLER,event_canvas,
    MENU_NAME,menu1,
    FORE_COLOR,WHITE,
    BACK_COLOR,BLACK,
    NULL);
  fparameters=xv_create(NULL,FRAME,
    XV_LABEL,"Parameters",
    DX,280,
    DY,190,
    MENU_NAME,menu1,
    NULL);
  tomax=xv_create(fparameters,TEXTFIELD,
    XV_LABEL,"Last order",
    FIELD_TYPE,int_field,
    PANEL_INT,10,
    MIN_VALUE,3,
    MAX_VALUE,MAXORDER,
    NULL);
  tfile=xv_create(fparameters,TEXTFIELD,
    XV_LABEL,"Output file",
    Y,15,
    PANEL_VALUE,"hexa.out",
    NULL);
  bgenerate=xv_create(fparameters,BUTTON,
    XV_LABEL,"Generate",
    Y,30,
    NOTIFY_HANDLER,process_button,
    NULL);
  sshow=xv_create(fparameters,SETTING,
    XV_LABEL,"List",
    ITEM_SETTING,
    "screen","file",NULL,
    SEL_SETTING,0,
    X,80,
    Y,30,
    NULL);
  torder=xv_create(fparameters,TEXTFIELD,
    XV_LABEL,"Order to view",
    Y,45,
    FIELD_TYPE,int_field,
    PANEL_INT,10,
    MIN_VALUE,3,
    NULL);
  tnumber=xv_create(fparameters,TEXTFIELD,
    XV_LABEL,"Number to view",
    Y,60,
    FIELD_TYPE,int_field,
    PANEL_INT,25,
    MIN_VALUE,1,
    NULL);
  tview=xv_create(fparameters,TEXTFIELD,
    XV_LABEL,"1st in order to view",
    Y,75,
    FIELD_TYPE,int_field,
    PANEL_INT,1,
    MIN_VALUE,1,
    MAX_VALUE,LIMIT,
    NULL);
  bview=xv_create(fparameters,BUTTON,
    XV_LABEL,"View",
    Y,150,
    NOTIFY_HANDLER,process_drawing,
    NULL);
  sview=xv_create(fparameters,SETTING,
    XV_LABEL,"Show",
    Y,120,
    ITEM_SETTING,"maps","strips","strip lists",NULL,
    EXCLUSIVE,1,
    SEL_SETTING,1,
    NULL);
  scomplete=xv_create(fparameters,SETTING,
    XV_LABEL,"Strip",
    Y,105,
    ITEM_SETTING,"1/3","complete",NULL,
    EXCLUSIVE,1,
    SEL_SETTING,1,
    NULL);
  sfaces=xv_create(fparameters,SETTING,
    XV_LABEL,"Show face numbers",
    Y,90,
    ITEM_SETTING,"no","yes",NULL,
    EXCLUSIVE,1,
    SEL_SETTING,1,
    NULL);
  snorm=xv_create(fparameters,SETTING,
    XV_LABEL,"Normalize strips",
    Y,135,
    ITEM_SETTING,"no","yes",NULL,
    EXCLUSIVE,1,
    SEL_SETTING,1,
    NULL);
  fparameters->v.sframe.mouse_obj=bgenerate;
  fmessages=xv_create(NULL,FRAME,
    XV_LABEL,"Messages",
    X,0,
    Y,500,
    DX,640,
    DY,159,
    MENU_NAME,menu1,
    NULL);
  tty1=xv_create(fmessages,TTY,
    MENU_NAME,menu2,
    NULL);
  open_window(fmain);
  xprintf(tty1,"Hexaflexagon finder\nVersion %s\nBy Antonio Carlos M. de Queiroz (acmq@coe.ufrj.br)\n\n",version);
  xv_main_loop(fparameters);
  /* Exit */
  restorecrtmode();
}
