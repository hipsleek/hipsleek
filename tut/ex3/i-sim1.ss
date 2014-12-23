int sumE(int n)
infer [@term] 
//infer [@post_n]
requires true ensures true;
//requires true & (n=0 | exists(k: k>=0 & n=2*k)) & Term[n] ensures true;
//requires  true & (n<0 | exists(k:k>=0 & n!=2*k)) & Loop ensures false;
/*
 case {
   (exists k: k>=0 & n=2*k) -> requires Term[n] ensures true;
   (exists k: n<0 | n!=2*k) -> requires Loop ensures false;
 }
*/
{ if (n==0) return 0;
  else return n+sumE(n-2);
}

/*
i-sim1-sum-even.ss

I suppose we cannot infer even pred?

Can we write pre/post spec for
  sim1-sum-even.ss


Starting z3... 
Termination Inference Result:
sumE:  requires true & truecase {
                      n=0 -> requires emp & Term[99,1]
     ensures true & true;
                      
                      5<=n -> requires emp & MayLoop[]
     ensures true & true;
                      
                      (n=1 | n<=(0-1) | n=3) -> requires emp & Loop
                      { 14:16}[]
     ensures false & false; 
                      n=4 -> requires emp & Term[99,3]
     ensures true & true;
                      
                      n=2 -> requires emp & Term[99,2]
     ensures true & true;
                      
                      }

*/
