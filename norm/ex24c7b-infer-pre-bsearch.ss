
relation P(int x, int y).

bool rand()
  requires true
  ensures res or !res;

int bsearch(int x,int y)
  infer [P,@classic] 
 requires P(x,y) & x<=y
 ensures true;
/*
 requires P(x,y) 
 ensures false;
 requires x>y
 ensures false;
 // verifies
*/
{
  if (x==y) return 1;
  else {
    int m=(x+y)/2;
    if (rand()) return bsearch(x,m);
    else return bsearch(m+1,y);
  }
}

/*
# ex24c7b.ss

 infer [P] 
 requires P(x,y) 
 ensures false;
/*
 requires x>y
 ensures false;
 // verifies
*/
{
  if (x==y) return 1;
  else {
    int m=(x+y)/2;
    if (rand()) return bsearch(x,m);
    else return bsearch(m+1,y);
  }
}

 requires P(x,y) & x<=y
 ensures true;

[RELDEFN P: 
( 0<=m' & m'<y & (2*m')<=(x'+y) & (x'+y)<=(1+(2*m')) & P(x',y)) 
  -->  P(x',m'),
RELDEFN P: 
( m'<=(0-1) & m'<=(y-1) & (2*m')<=(x'+y) & (x'+y)<=(1+(2*m')) & P(x',y)) -->  P(x',m'),
RELDEFN P: 
( 1<=v_int_24_1763' & v_int_24_1763'<=y' & (2*v_int_24_1763')<=(2+y'+x) & 
 (y'+x)<(2*v_int_24_1763') & P(x,y')) -->  P(v_int_24_1763',y'),
RELDEFN P: 
( v_int_24_1763'<=0 & v_int_24_1763'<=y' & (2*v_int_24_1763')<=(2+y'+x) & 
 (y'+x)<(2*v_int_24_1763') & P(x,y')) -->  P(v_int_24_1763',y')]


# why are there so many reldefns? can gfp derive x>y

!!! **typechecker.ml#845:WARNING : Spurious RelInferred (not collected):[RELDEFN P: ( P(x',y) & 0<=m' & (x'+y)<=(1+(2*m')) & (2*m')<=(x'+y) & m'<y) -->  P(x',m'),RELDEFN P: ( P(x',y) & 0<=m' & (x'+y)<=(1+(2*m')) & (2*m')<=(x'+y) & m'<x') -->  P(x',m'),RELDEFN P: ( P(x',y) & m'<=(0-1) & (x'+y)<=(1+(2*m')) & (2*m')<=(x'+y) & m'<y) -->  P(x',m'),RELDEFN P: ( P(x',y) & m'<=(0-1) & (x'+y)<=(1+(2*m')) & (2*m')<=(x'+y) & m'<x') -->  P(x',m'),RELDEFN P: ( P(x,y') & 1<=v_int_22_1761' & (2*v_int_22_1761')<=(2+y'+x) & 
 (y'+x)<(2*v_int_22_1761') & v_int_22_1761'<=y') -->  P(v_int_22_1761',y'),RELDEFN P: ( P(x,y') & 1<=v_int_22_1761' & (2*v_int_22_1761')<=(2+y'+x) & 
 (y'+x)<(2*v_int_22_1761') & v_int_22_1761'<=x) -->  P(v_int_22_1761',y'),RELDEFN P: ( P(x,y') & v_int_22_1761'<=0 & (2*v_int_22_1761')<=(2+y'+x) & 
 (y'+x)<(2*v_int_22_1761') & v_int_22_1761'<=y') -->  P(v_int_22_1761',y'),RELDEFN P: ( P(x,y') & v_int_22_1761'<=0 & (2*v_int_22_1761')<=(2+y'+x) & 
 (y'+x)<(2*v_int_22_1761') & v_int_22_1761'<=x) -->  P(v_int_22_1761',y')]

*/
