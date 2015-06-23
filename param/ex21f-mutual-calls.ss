
relation R(int x,int y,int a,int b).

void loo (int x, int y,int a, int b)
     infer [R]
     requires R(x,y,a,b)
     ensures true;
{

  if (x>0 || y>0) {
    a=a+1;
    x = x+a-b-1;
    a=a-1;
    y = y+b-a-1;
    loo(x,y,b,a);
    loo(x,y,a,b);
  };
}

/*
# ex21f.ss

[RELDEFN R: ( x=(b'-a')+x' & y=(a'-b')+y'+1 & a'<(b'+x') & b'<=(a'+y') & R(x,y,a',b')) -->  R(x',y',b',a'),
RELDEFN R: ( y=(a'-b')+y'+1 & x=(b'-a')+x' & (a'+y')<b' & a'<(b'+x') & R(x,y,a',b')) -->  R(x',y',b',a'),
RELDEFN R: ( x=(b'-a')+x' & y=(a'-b')+y'+1 & (b'+x')<=a' & b'<=(a'+y') & R(x,y,a',b')) -->  R(x',y',b',a'),
RELDEFN R: ( x=(b'-a')+x' & y=(a'-b')+y'+1 & a'<(b'+x') & b'<=(a'+y') & R(x,y,a',b')) -->  R(x',y',a',b'),
RELDEFN R: ( y=(a'-b')+y'+1 & x=(b'-a')+x' & (a'+y')<b' & a'<(b'+x') & R(x,y,a',b')) -->  R(x',y',a',b'),
RELDEFN R: ( x=(b'-a')+x' & y=(a'-b')+y'+1 & (b'+x')<=a' & b'<=(a'+y') & R(x,y,a',b')) -->  R(x',y',a',b')]



 */
