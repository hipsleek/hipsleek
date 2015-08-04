relation R(int x,int y,int a,int b).
relation R2(int x,int y,int a,int b).

void loo (ref int x, ref int y,int a, int b)
     infer [R]
     requires R(x,y,a,b)
     ensures true;
{

  if (x>0 || y>0) {
    a=a+1;
    x = x+a-b-1;
    a=a-1;
    y = y+b-a-1;
    if (x > 100) {
      loo2(x,y,a,b);
    } else {
      x = x + 100000;
      loo(x,y,a,b);
    }
  };
}

void loo2 (ref int xx, ref int yy,int aa, int bb)
     infer [R2]
     requires R2(xx,yy,aa,bb)
     ensures true;
{

  if (xx>0 || yy>0) {
    aa=aa+1;
    xx = xx+aa-bb-1;
    aa=aa-1;
    yy = yy+bb-aa-1;
    loo(xx,yy,aa,bb);
    dprint;
  };
}

/*
# ex21h.ss

[RELDEFN R: ( xx=(bb'-aa')+xx' & yy=(aa'-bb')+yy'+1 & aa'<(bb'+xx') & bb'<=(aa'+yy') & R(xx,yy,aa',bb')) -->  R(xx',yy',aa',bb'),
RELDEFN R: ( yy=(aa'-bb')+yy'+1 & xx=(bb'-aa')+xx' & (aa'+yy')<bb' & aa'<(bb'+xx') & R(xx,yy,aa',bb')) -->  R(xx',yy',aa',bb'),
RELDEFN R: ( xx=(bb'-aa')+xx' & yy=(aa'-bb')+yy'+1 & (bb'+xx')<=aa' & bb'<=(aa'+yy') & R(xx,yy,aa',bb')) -->  R(xx',yy',aa',bb'),

RELDEFN R: ( x=(b'-a')+x' & y=(a'-b')+y'+1 & a'<(b'+x') & b'<=(a'+y') & R(x,y,a',b')) -->  R(x',y',a',b'),
RELDEFN R: ( y=(a'-b')+y'+1 & x=(b'-a')+x' & (a'+y')<b' & a'<(b'+x') & R(x,y,a',b')) -->  R(x',y',a',b'),
RELDEFN R: ( x=(b'-a')+x' & y=(a'-b')+y'+1 & (b'+x')<=a' & b'<=(a'+y') & R(x,y,a',b')) -->  R(x',y',a',b')]


=============================================

missing push for v_bool_30_1392
  {((boolean v_bool_30_1392;
  (v_bool_30_1392 = {((boolean v_boolean_30_1347;

!!! **typechecker.ml#2042:block:[xx,yy,aa,bb]
!!! **typechecker.ml#2042:block:[v_boolean_30_1347,v_boolean_30_1346,xx,yy,aa,bb]
!!! **typechecker.ml#2042:block:[v_int_30_1336,v_boolean_30_1347,v_boolean_30_1346,xx,yy,aa,bb]
!!! **typechecker.ml#2042:block:[v_int_30_1341,v_boolean_30_1347,v_boolean_30_1346,xx,yy,aa,bb]
!!! **typechecker.ml#2042:block:[xx,yy,aa,bb]
!!! **typechecker.ml#2042:block:[v_int_31_1352,xx,yy,aa,bb]
!!! **typechecker.ml#2042:block:[v_int_32_1367,v_int_32_1366,xx,yy,aa,bb]
!!! **typechecker.ml#2042:block:[v_int_32_1361,v_int_32_1367,v_int_32_1366,xx,yy,aa,bb]
!!! **typechecker.ml#2042:block:[v_int_32_1361,v_int_32_1367,v_int_32_1366,xx,yy,aa,bb]
!!! **typechecker.ml#2042:block:[v_int_33_1372,xx,yy,aa,bb]
!!! **typechecker.ml#2042:block:[v_int_34_1387,v_int_34_1386,xx,yy,aa,bb]
!!! **typechecker.ml#2042:block:[v_int_34_1381,v_int_34_1387,v_int_34_1386,xx,yy,aa,bb]
!!! **typechecker.ml#2042:block:[v_int_34_1381,v_int_34_1387,v_int_34_1386,xx,yy,aa,bb]
!!! **typechecker.ml#2042:block:[xx,yy,aa,bb]
St
 */
