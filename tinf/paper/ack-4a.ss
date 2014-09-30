int Ack(int m, int n)
infer [@term]
  requires true
  ensures res>=n+1;
{ 
	if (m==0) return n+1;
	else if (n==0) {
		int m1 = m-1;
                //assert m'-m1'>0; //'
                //assert m1'>=0; //'
    return Ack(m1, 1);
  }
 	else {
		int m1=m-1;
   	int n1=n-1;
   	//assert m'=m' & /* n1'>=0 & */ n'-n1'>0; //'
   	int r = Ack(m, n1);
   	//assert m'-m1'>0 /* & m1'>=0 */; //'
   	return Ack(m-1, r);
 	}
}
/*
# ack-4a.ss

infer [@term]
  requires true
  ensures res>=n+1;


Can it be more precise?

Ack:  case {
  m=0 -> 
   requires emp & Term[3,1]
   ensures emp & (1+n)<=res; 
  1<=m -> 
   requires emp & MayLoop[]
   ensures emp & (1+n)<=res; 
  m<=(0-1) -> 
   requires emp & Loop[]
   ensures false & false; 
  }

*/

