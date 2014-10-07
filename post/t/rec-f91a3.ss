
// 90 -> 91
relation postA(int n, int r).
relation postB(int n, int r).

int f91(int n)
  infer [postA,postB
         //,@term
  ]
 case {
  n>=91 ->  ensures postA(n,res);
  n<91 -> ensures postB(n,res);
 }
{
  if (91<=n) return n;
  else return f91(f91(n+1));
}

/*
# rec-f91a3.ss -infer "@term"

Why below produce the correct result:

  infer [postA,postB,@term]
 case {
  n>=91 ->  ensures postA(n,res);
  n<91 -> ensures postB(n,res);
 }

but not below with -infer "@term":
  infer [postA,postB]
 case {
  n>=91 ->  ensures postA(n,res);
  n<91 -> ensures postB(n,res);
 }

It seems like post infer & @term were being done simultaneously..

!!! proc_specs:[ EInfer [postA,postB]
   ECase case {
          91<=n -> EBase emp&f91pre_0(n)[30]&{FLOW,(4,5)=__norm}[]
                           EAssume 
                             emp&postA(n,res) & f91post_1164(n)[] & 91<=n&
                             {FLOW,(4,5)=__norm}[]
                              ;
          n<91 -> EBase emp&f91pre_0(n)[30]&{FLOW,(4,5)=__norm}[]
                          EAssume 
                            emp&postB(n,res) & f91post_1165(n)[] & n<91&
                            {FLOW,(4,5)=__norm}[]
                             
          }]



*/
