int Ack(int m, int n)
infer [@term]
 case {
  m=0 -> requires Term[] ensures res>=n+1;
  m>=1 -> 
    case {
      n>=0 ->  requires Term[m,n] ensures res>=n+1;
      n<0 ->  requires MayLoop ensures res>=n+1;
    }
  m<0 -> requires Loop ensures false;
}
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
# ack-4bv.ss

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

