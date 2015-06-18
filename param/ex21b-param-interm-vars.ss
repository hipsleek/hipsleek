
relation R(int x,int y,int a,int b).

void loo (ref int x, ref int y,int a, int b)
     infer [R]
     requires R(x,y,a,b)
     ensures true;
{

  if (x>0 || y>0) {
    int c=a-b;
    x = x+c-1;
    y = y-c-1;
    loo(x,y,a,b);
  };
}

/*
# ex21b.ss

e[RELDEFN R: ( y=((y'+a')-b')+1 & x=(b'-a')+x'+1 & b'<=(y'+a') & a'<=(b'+x') & R(x,y,a',b')) -->  R(x',y',a',b'),
RELDEFN R: ( y=((y'+a')-b')+1 & x=(b'-a')+x'+1 & (y'+a')<b' & a'<=(b'+x') & R(x,y,a',b')) -->  R(x',y',a',b'),
RELDEFN R: ( x=((x'+b')-a')+1 & y=(a'-b')+y'+1 & (x'+b')<a' & b'<=(a'+y') & R(x,y,a',b')) -->  R(x',y',a',b')]


 */
