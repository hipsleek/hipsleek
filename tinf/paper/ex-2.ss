void f(int x, int y)
  infer [@term]
  case {
    x < 0 -> requires Term ensures true;
    x >= 0 -> requires true ensures true;
  }

 //infer [@term]
 //requires true
 //ensures true;
 
{
  if (x < 0) return;
  else { 
    f(x + y, y);
  }
}

/*

# ex-2.ss
 (i) can we have a better pretty-printer?
 (ii) can we do [@term,@post] now?
 (iii) how come post(..) is being inferred
       for one case but not another.


infer [@term]
  case {
    x < 0 -> requires Term ensures true;
    x >= 0 -> requires true ensures true;
  }

Base/Rec Case Splitting:
[	f: [[3] x<=(0-1)@B,[4] 0<=x@R]
]

Termination Inference Result:
f:  case {
  x<=(0-1) -> 
   requires emp & Term[29]
   ensures emp & x<0; 
  0<=x -> case {
    0<=y -> requires emp & Loop[]
            ensures false & false; 
   y<=(0-1) -> 
         requires emp & Term[29,2,0+(1*x)+(0* y)]
          ensures emp & 0<=x; 
           }
  
  }


 infer [@term]
 requires true
 ensures true;


Base/Rec Case Splitting:
[	f: [[2] x<=(0-1)@B,[3] 0<=x@R]
]
Termination Inference Result:
f:  case {
  x<=(0-1) -> 
    requires emp & Term[29,1]
    ensures emp & true; 
  0<=x -> case {
      0<=y -> 
       requires emp & Loop[]
       ensures false & false; 
   y<=(0-1) -> requires emp & Term[29,2,0+(1*x)+(0* y)]
            ensures emp & true; 
           }
  
  }
*/
