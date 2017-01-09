int Ack(int m, int n)
infer [@term]
 case {
  m=0 -> requires Term[] ensures res>=n+1;
  m>=1 -> 
    case {
    n>=0 ->  requires MayLoop //why lexi not working here Term[m,n] 
             ensures res>=n+1;
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
# ack-4b.ss

infer [@term]
 case {
  m=0 -> requires Term[] ensures res>=n+1;
  m>=1 -> 
    case {
    n>=0 ->  requires MayLoop //why lexi not working here Term[m,n] 
             ensures res>=n+1;
      n<0 ->  requires MayLoop ensures res>=n+1;
    }
  m<0 -> requires Loop ensures false;
}

# why isn't lexi ranking not inferred above?


Base/Rec Case Splitting:
[	Ack: [[10] m=0@B,[11] n<=(0-1) & 1<=m@R,[12] 1<=n & 1<=m@R,[13] n=0 & 1<=m@R]
]
Termination Inference Result:
Ack:  case {
  m=0 -> requires emp & Term[3]
 ensures emp & (1+n)<=res; 
  1<=m -> case {
           0<=n -> requires emp & MayLoop[]
 ensures emp & (1+n)<=res; 
           n<0 -> requires emp & MayLoop[]
 ensures emp & (1+n)<=res; 
           }
  
  m<=(0-1) -> requires emp & Loop[]
 ensures false & false; 
  }



*/

