int Ack(int m, int n)
infer [@term]
 requires true
  ensures res>=1 | res>=n+1;
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
# ack-4.ss

infer [@term]
 requires true
  ensures res>=1 | res>=n+1;

Why a non-terminating loop here?

TNT @ ITER 0
Ack:  case {
  m=0 -> requires emp & Term[3,1]
 ensures emp & true; 
  1<=n & 1<=m -> requires emp & MayLoop[]
 ensures emp & true; 
  n<=(0-1) & 1<=m -> requires emp & MayLoop[]
 ensures emp & true; 
  m<=(0-1) & 1<=n -> requires emp & MayLoop[]
 ensures emp & true; 
  n<=(0-1) & m<=(0-1) -> requires emp & MayLoop[]
 ensures emp & true; 
  n=0 & 1<=m -> requires emp & MayLoop[]
 ensures emp & true; 
  n=0 & m<=(0-1) -> requires emp & MayLoop[]
 ensures emp & true; 
  }
TNT @ ITER 0
Ack:  case {
  m=0 -> requires emp & Term[3,1]
 ensures emp & true; 
  1<=n & 1<=m -> requires emp & MayLoop[]
 ensures emp & true; 
  n<=(0-1) & 1<=m -> requires emp & MayLoop[]
 ensures emp & true; 
  m<=(0-1) & 1<=n -> requires emp & Loop[]
 ensures false & false; 
  n<=(0-1) & m<=(0-1) -> requires emp & Loop[]
 ensures false & false; 
  n=0 & 1<=m -> requires emp & MayLoop[]
 ensures emp & true; 
  n=0 & m<=(0-1) -> requires emp & Loop[]
 ensures false & false; 
  }
TNT @ ITER 1
Ack:  case {
  m=0 -> requires emp & Term[3,1]
 ensures emp & true; 
  1<=n & 
  1<=m -> case {
           2<=n & 1<=m -> requires emp & MayLoop[]
 ensures emp & true; 
           n<=1 -> requires emp & MayLoop[]
 ensures emp & true; 
           }
  
  n<=(0-1) & 1<=m -> requires emp & MayLoop[]
 ensures emp & true; 
  m<=(0-1) & 1<=n -> requires emp & Loop[]
 ensures false & false; 
  n<=(0-1) & m<=(0-1) -> requires emp & Loop[]
 ensures false & false; 
  n=0 & 1<=m -> requires emp & MayLoop[]
 ensures emp & true; 
  n=0 & m<=(0-1) -> requires emp & Loop[]
 ensures false & false; 
  }

Ack:  case {
  m=0 -> requires emp & Term[3,1]
 ensures emp & (1+n)<=res; 
  1<=m -> requires emp & MayLoop[]
 ensures emp & (1+n)<=res; 
  m<=(0-1) -> requires emp & Loop[]
 ensures false & false; 
  }

*/

