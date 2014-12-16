
relation P(int n).
relation Q(int n,int r).


int id(int n)
  infer [P,Q]
  requires P(n) ensures Q(n,res);
{
  if (n==0) return 0;
  else return 1+id(n-1);
}

/*
# sim3-id.ss

[RELDEFN P: ( P(n) & n=1+v_int_11_1313' & (v_int_11_1313'+1)!=0) 
  -->  P(v_int_11_1313'),
RELDEFN Q: ( n=0 & res=0 & P(n)) -->  Q(n,res),
RELDEFN Q: ( res=1+v_int_11_1351 & n!=0 & Q(n-1,v_int_11_1351) & P(n)) 
       -->  Q(n,res)]

Post Inference result:
id$int
 EBase emp&0<=n & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           emp&n=res & 0<=res&{FLOW,(4,5)=__norm#E}[]

*/
