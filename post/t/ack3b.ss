int Ack(int m, int n)
 infer [@term]
 case {
  m<0 -> requires Loop ensures false;
  m>=0 -> 
   case {
    n<0 -> requires MayLoop ensures true;
    n>=0 -> requires true ensures res>=0;
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
# ack3b.ss

Base/Rec Case Splitting:
[	Ack: [[7] m=0 & 0<=n@B,[8] m=0 & n<=(0-1)@B,[9] 1<=n & 1<=m@R,[10] n=0 & 1<=m@R,[11] n<=(0-1) & 1<=m@R]
]
Termination Inference Result:
Ack:  case {
  m<=(0-1) -> requires emp & Loop[]
              ensures false & false; 
  0<=m -> case {
           n<0 -> case {
                   // why did we not combine require false ensures false?
                   m=0 & 0<=n -> 
                     requires false & false
                     ensures false & false; 
                   1<=n &  1<=m -> 
                     requires false & false
                     ensures false & false; 
                   n=0 & 1<=m -> 
                     requires false & false
                     ensures false & false; 
                   m=0 & n<=(0-1) -> 
                     requires emp & Term[3,2]
                     ensures emp & true; 
                   n<=(0-1) & 1<=m -> 
                     requires emp & Loop[]
                     ensures false & false; 
                   }
           
           0<=n -> case {
                 //can we combine the  cases?
                    m=0 & 0<=n -> 
                      requires emp & Term[3,1]
                      ensures emp & 0<=res; 
                    1<=n & 1<=m -> 
                     requires emp & Term[3,3,0+(1*m)+(0*n),0+(1*m)+(1*n)]
                     ensures emp & 0<=res; 
                    n=0 & 1<=m -> 
                     requires emp & Term[3,3,0+(1*m)+(0*n),0+(1*m)+(1*n)]
                     ensures emp & 0<=res; 
                    m=0 & n<=(0-1) -> 
                      requires false & false
                      ensures false & false; 
                    n<=(0-1) &  1<=m -> 
                      requires false & false
                      ensures false & false; 
                    }
           
           }
  
  }


 infer [@term]
 case {
  m<0 -> requires Loop ensures false;
  m>=0 -> 
   case {
    n<0 -> requires MayLoop ensures true;
    n>=0 -> requires true ensures res>=0;
   }
  }

Case analysis did not help..
We need lexi ranking..

Termination Inference Result:
Ack:  case {
  m<=(0-1) -> requires emp & Loop[]
 ensures false & false; 
  0<=m -> case {
           n<0 -> case {
             m=0 & 0<=n -> 
               requires false & false
               ensures false & false; 
             m=0 & n<=(0-1) -> 
               requires emp & Term[3,2]
               ensures emp & true; 
             1<=m -> 
               requires emp & MayLoop[]
               ensures emp & true; 
                   }
           
      0<=n -> case {
                    m=0 & 
                    0<=n -> 
                      requires emp & Term[3,1]
                      ensures emp & 0<=res; 
                    m=0 & n<=(0-
                    1) -> requires false & false
 ensures false & false; 
                    1<=m -> requires emp & MayLoop[]
 ensures emp & 0<=res; 
                    }
           
           }
  
  }


*/

