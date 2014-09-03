UTPre@fact fpre(int x).
UTPost@fact fpost1(int x).
UTPost@fact fpost2(int x).

int fact(int x)
  infer [@term]
  /*
  case {
    x = 0 -> requires Term[] ensures res>=1 & fpost1(x);
    x != 0 -> requires fpre(x) ensures res>=1 & fpost2(x);
  }
  */
  
  case {
    x = 0 -> requires Term[] ensures res>=1;
    x != 0 -> requires true ensures res>=1;
  }
  
{
  if (x==0) return 1;
  else return 1+fact(x - 1);
}
/*
# fact2c.ss

Two problems
(i) We seems to have lost the res>=1 post-state.
(ii) I think too many base cases here.

Fixing (i) is critical. Fixing (ii) is desirable.

For (i)0, why did we getfour (4)4 termination assumption.
If we had 3, we would obtain the right number of
cases, as follows:

# exp-fact2c1.slk

Temporal Assumptions:
 termAssume 1<=r & res=r+1 & x=x'+1 & x!=0 & fpost(x') --> fpost(x).

 termAssume res=1 & x=0 --> fpost(x).

 termAssume x=x'+1 & x!=0 & fpre(x) --> fpre(x').


Base/Rec Case Splitting:
[	f: [[2] 1<=x@R,[3] x<=(0-1)@R,[4] x=0@B]
]
Starting z3... 
Termination Inference Result:
f:  case {
  1<=x -> requires emp & Term[3,-1+(1*x)]
 ensures emp & true; 
  x<=(0-1) -> requires emp & Loop[]
 ensures false & false; 
  x=0 -> requires emp & Term[1]
 ensures emp & true; 
  }

Expecting:

fact:  case {
  x=0 -> requires emp & Term[1]
 ensures emp & res>=1; 
  1<=x -> requires emp & Term[4,-1+(1*x)]
 ensures emp & res>=1; 
  x<=(0-1) -> requires emp & Loop[]
 ensures false & false; 
  }

Instead, GOT:

fact:  case {
  x=1 -> requires emp & Term[3]
 ensures emp & true; 
  x=0 -> requires emp & Term[1]
 ensures emp & true; 
  2<=x -> requires emp & Term[4,-2+(1*x)]
 ensures emp & true; 
  x<=(0-1) -> requires emp & Loop[]
 ensures false & false; 
  }



*/


