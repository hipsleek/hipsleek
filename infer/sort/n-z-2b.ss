/* zip - numeric */

relation R(int a,int b,int c).
relation P(int a,int b).

void error()
  requires false
  ensures true;

int zip(int x, int y)
//  infer [x,y]
  infer [P]
  requires y>=0 & x>=0 
    & P(x,y)
  ensures  true;

/*

Checking procedure zip$int~int... 
*************************************
*******pure relation assumption ******
*************************************
[RELASS [P]: ( P(x,y)) -->  y!=0 | 1>x]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[]
*************************************

*/

{
  if (x==0) return 0;
  else {
    if (y==0) {
       error();
       return -1;
    }
    else 
      return 1;
  }
}










