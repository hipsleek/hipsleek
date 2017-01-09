int Ack(int m, int n)
 infer [@term]
 case {
  m<0 -> requires true ensures true;
  m>=0 -> 
   case {
    n<0 -> requires true ensures true;
    n>=0 -> requires true ensures true;
   }
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
# ack3.ss

Above case analysis did not seem to help.
We obtained:

Base/Rec Case Splitting:
[	Ack: [[11] m=0 & 0<=n@B,[12] m=0 & n<=(0-1)@B,[13] 1<=n & 1<=m@R,[14] n=0 & 1<=m@R,[15] n<=(0-1) & 1<=m@R,[16] m<=(0-1) & 1<=n@R,[17] m<=(0-1) & n<=(0-1)@R,[18] n=0 & m<=(0-1)@R]
]
Termination Inference Result:
Ack:  case {
  m<=(0-1) -> requires emp & MayLoop[]
 ensures emp & true; 
  0<=m -> case {
           n<0 -> case {
                   m=0 & 
                   0<=n -> requires false & false
 ensures false & false; 
                   m=0 & n<=(0-
                   1) -> requires emp & Term[3,2]
 ensures emp & true; 
                   ((n<=(0-1) & m<=(0-1)) | (0<=n & 1<=m) | (m<=(0-1) & 
                   0<=n)) -> requires false & false
 ensures false & false; 
                   n<=(0-1) & 
                   1<=m -> requires emp & Loop[]
 ensures false & false; 
                   }
           
           0<=n -> case {
                    m=0 & 
                    0<=n -> requires emp & Term[3,1]
 ensures emp & true; 
                    m=0 & n<=(0-
                    1) -> requires false & false
 ensures false & false; 
                    ((n<=(0-1) & m<=(0-1)) | (0<=n & 1<=m) | (m<=(0-1) & 
                    0<=n)) -> requires emp & MayLoop[]
 ensures emp & true; 
                    n<=(0-1) & 
                    1<=m -> requires false & false
 ensures false & false; 
                    }
           
           }
  
  }


*/

