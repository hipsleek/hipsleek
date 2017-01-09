void loop()
  requires Loop
  ensures false;

/*  
prim_pred ND<>
inv true;
*/

relation ND_Int(int x).
relation ND_Bool(bool x).


bool nondet()
  requires Term
  ensures true & ND_Bool(res);
  
void f(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else {
    bool b = nondet();
    if (b) 
      loop();
    else f(x - 1);
  }
}

/*
# nondet-1.ss

{
  if (x < 0) return;
  else 
    if (nondet()) loop();
    else f(x - 1);
}


Successful States:
[
 Label: [(,1 ); (,2 )]
 State:emp&0<=x' & x'=x & !(v_bool_23_1396') & 0<=x' & !(v_bool_23_1396') & ND_Bool(b_38')&{FLOW,(4,5)=__norm#E}[]
       es_ho_vars_map: []emp&0<=x' & x'=x & !(v_bool_23_1396') & 0<=x' & !(v_bool_23_1396') & ND_Bool(b_38')

 ]

This currently infers MayLoop which will be treated as a maybe.
I wonder if we can have another temporal category, called NDLoop, which
denotes a loop from non-deterministic value.

                 {S * cex<K filter if_n> }   e1  {S1 * cex<L1>}
                 {S * cex<K filter else_n> } e2  {S2 * cex<L2>}
                       L1={} \/ L2={}  K2=K filterNot if_n
         --------------------------------------------------------------
         {S*cex<K>} n:if * then e1 else e2 {S1 * cex<K2> \/ S2 * cex<K2>}

                  {S * cex<K filter if_n> & v}        e1  {S1}
                  {S * cex<K filter else_n> & not(v)} e2  {S2}
                               K2=K filterNot if_n
         ----------------------------------------------------------
         {S*cex<K>} n:if v then e1 else e2 {S1 * cex<K2> \/ S2 * cex<K2>}


         {K+e1[if_n]+e2[else_n]} filter if_n   --> {e1[if_n]} 
         {K+e1[if_n]}   filter if_n            --> {e1[if_n]} 
         {K+e2[else_n]} filter if_n            --> {e2[else_n]} 
         {K+e1[if_n]+e2[else_n]} filter else_n --> {e2[else_n]} 
         {K+e1[if_n]}   filter else_n          --> {e1[if_n]} 
         {K+e2[else_n]} filter else_n          --> {e2[else_n]} 

         {K+e1[if_n]+e2[else_n]} filterNot if_n --> {K} 
         {K+e1[if_n]}   filterNot if_n          --> {K}
         {K+e2[else_n]} filterNot if_n          --> {K}

Expecting:
f:  case {
  x<=(0-1) -> requires emp & Term[36,1]
     ensures emp & true; 
  0<=x -> requires emp & NDLoop[] (must have a counter-example?)
     ensures emp & true; 

Current:
Termination Inference Result:
f:  case {
  x<=(0-1) -> requires emp & Term[36,1]
     ensures emp & true; 
  0<=x -> requires emp & MayLoop[]
     ensures emp & true; 
*/
