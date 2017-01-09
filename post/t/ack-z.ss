int Ack(int m, int n)
  /* infer [//@post_n, */
  /* @term] */
 requires true
 ensures true;
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
# ack-z.ss

[@post_n]

Post Inference result:
Ack$int~int
 requires emp & MayLoop[]
 ensures emp & (0<=n | (m=0 & n=res-1));


[@post_n,@term] --infer-lex

 infer [@post_n,@term]
 requires true
 ensures true;

Base/Rec Case Splitting:
[	Ack: [[4] m=0@B,[5] 1<=n & 1<=m@R,[6] m<=(0-1) & 1<=n@R,[7] n=0 & 1<=m@R,[8] n=0 & m<=(0-1)@R]
]
Termination Inference Result:
Ack:  case {
  m=0 -> requires emp & Term[3,1]
 ensures emp & (0<=n | (m=0 & n=res-1)); 
  1<=n & 1<=m -> requires emp & Term[3,2,0+(0*m)+(0*n),-1+(1*m)+(0*n),-1+(0*
  m)+(1*n)]
 ensures emp & (0<=n | (m=0 & n=res-1)); 
  m<=(0-1) & 0<=n -> requires emp & Loop[]
 ensures false & false; 
  n=0 & 1<=m -> requires emp & Term[3,2,0+(0*m)+(0*n),-1+(1*m)+(0*n),-1+(0*
  m)+(1*n)]
 ensures emp & (0<=n | (m=0 & n=res-1)); 
  }

*/

