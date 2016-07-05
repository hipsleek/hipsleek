// McCarthy 91
//f(n,k) = if k <= n then n else f(f(n+1,k),k)
// 90 -> 91
int f91(int n)
/*
  infer [@post_n
         ,
         @term
  ]
  requires true
  ensures true;
*/
 case {
  //  n>91 -> requires Term[] ensures res=n;
  n>=91 -> requires Term[] ensures res=n;
  n<91 -> requires Term[91-n] ensures res=91;
 }
/*
 case {
  //  n>91 -> requires Term[] ensures res=n;
  n>=91 -> ensures res=n;
  n<91 -> ensures res=91;
}
*/
{
  if (91<=n) return n;
  else return f91(f91(n+1));
}
/*
# f91-rec5.ss

 case {
  //  n>91 -> requires Term[] ensures res=n;
  n>=91 -> requires Term[] ensures res=n;
  n<91 -> requires Term[91-n] ensures res=91;

Why Term measure not captured?
static  ECase case {
        91<=n -> EBase emp&Term[31,pv_1326]&{FLOW,(4,5)=__norm#E}[]
                         EAssume 
                            emp&res=n&{FLOW,(4,5)=__norm#E}[]
                            ;
        n<91 -> EBase emp&Term[31,pv_1327]&{FLOW,(4,5)=__norm#E}[]
                        EAssume 
                          emp&res=91&{FLOW,(4,5)=__norm#E}[]
                           
        }

# f91-rec3.ss

(1) use only @post_n

Why this combination not working?
 Has the verify of @term been done concurrently 
 with @post, as it will be complex if so.

Below seems wrong. How to fix it?

Post Inference result:
f91$int
 requires emp & MayLoop[]
 ensures emp & ((res=91 & n<=90) | (n=res & 
91<=res));

(1) use only @term

Termination Inference Result:
f91:  case {
  91<=n -> requires emp & Term[29,1]
 ensures emp & ((res=91 & n<=90) | 
  (n=res & 91<=res)); 
  n<=90 -> requires emp & MayLoop[]
 ensures emp & ((res=91 & n<=90) | 
  (n=res & 91<=res)); 
  }

*/
