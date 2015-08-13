/*
while(x>=0) {
  if b {
      x=x-1;
    };
  b=not(b);
}
*/

int cycle(int i,int n) 
  requires 0<=i<=n 
  ensures (i=0 & res=n | i>0 & res=i-1);
{
  if (i==0) return n;
  else return i-1;
}

void foo(int b,int x,int n)
 infer [@term]
 requires 0<=b<=n
  ensures true;
{ 
  if (x>=0) {
    if (b==0) x=x-1;
    b=cycle(b,n);
    foo(b,x,n);
  }
}

/*
# ex41c.ss

# cannot handle..

!!! **ti2.ml#1957:Analyzing scc: [47389984,32897]
!!! **ti2.ml#1957:Analyzing scc: [396880784788426,396669340607048,396669312440779,567053328,47370513,47360779,29104636,33155]
!!! **terminf.ml#374:#ctx of infer-lex: 56
!!! **ti2.ml#1697:assume_nondet:[]
!!! **ti2.ml#1697:assume_nondet:[]
!!! **ti2.ml#1697:assume_nondet:[]
!!! **ti2.ml#1697:assume_nondet:[]
!!! **ti2.ml#1697:assume_nondet:[]
!!! **ti2.ml#1697:assume_nondet:[]
!!! **ti2.ml#1697:assume_nondet:[]
!!! **ti2.ml#1697:assume_nondet:[]
!!! **ti2.ml#1697:assume_nondet:[]
!!! **ti2.ml#1957:Analyzing scc: [1070795059982885885,1070398390670445103,1121521764784591,396880784788426,567053328,47370513,29104636,33155,-349869337465623154]
!!! **terminf.ml#374:#ctx of infer-lex: 64

Procedure foo: UNKNOWN
 requires emp & 0<=b & b<=n
 case {
   x<=(0-1) -> requires emp & Term[35,1]
               ensures true & true;
               
                 
   ((6<=b & 0<=x) | (b<=0 & 2<=x & 2<=n)) -> 
   requires emp & MayLoop[]
   ensures true & true;
   



 */
