pred_prim Thrd{+%Q@Split}<>;
pred_prim dead<>;

data cell { int val; }

void join2(Thrd t)
  requires t::Thrd{+%Q}<>
  ensures %Q * t::dead<>;

/********************************************/
void foo(ref int n)
//infer[@leak]
  requires @full[n] & n>=0
  ensures @full[n] & n'=n+1;
{
  n = n+1;
}


Thrd fork_foo(ref int n)
  requires @full[n] & n>=0
  ensures res::Thrd{+ @full[n] & n'=n+1}<> ;//& n'=n;

int main(int nn)
 requires @value[nn]
 ensures res=1;
{
  nn=0;
  //State:emp*U@value[nn]&nn'=0 & MayLoop[] & nn_1394=nn&{FLOW,(4,5)=__norm#E}[]
  dprint;
  Thrd t = fork_foo(nn);
  //State:(exists nn_1399: t_36'::Thrd{ + emp*U@full[nn]&nn'=1+nn_1399&{FLOW,(4,5)=__norm#E}[]}<>*N
  // @full[t_36]@zero[nn]&nn_1399=0 & nn_1396=nn & 0<=nn_1399&{FLOW,(4,5)=__norm#E}[]
  dprint;
  join2(t);
  //State:t_36'::dead{}<>*U@full[nn,t_36]&nn'=1+nn_1403 & 0<=nn_1403 & nn_1396=nn & nn_1403=0&{FLOW,(4,5)=__norm#E}[]
  dprint;
  return nn;
 }
/*
# ex131a.ss --ann-vp (fixed)

check_pre_post(2)@1
check_pre_post(2) inp1 : EBase emp*U@full[n]&0<=n&{FLOW,(4,5)=__norm#E}[]
         EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                 EAssume ref [n]
                   res::Thrd{ + emp*U@full[n]&n'=1+n&{FLOW,(4,5)=__norm#E}[]}<>&
                   {FLOW,(4,5)=__norm#E}[]
check_pre_post(2) inp2 : List of Failesc Context: [FEC(0, 0, 1  [])]
 State:emp*U@full[t_36]@value[nn]&nn'=0 & MayLoop[] & nn_1396=nn&{FLOW,(4,5)=__norm#E}[]
check_pre_post(2)@1 EXIT: List of Failesc Context: [FEC(0, 0, 1  [])]
 State:(exists nn_1399: res::Thrd{ + emp*U@full[nn]&nn'=1+nn&{FLOW,(4,5)=__norm#E}[]}<>*N@full[t_36]@zero[nn]&0<=nn_1399 & nn_1396=nn & nn_1399=0&{FLOW,(4,5)=__norm#E}[]


compose_context_formula@1
compose_context_formula inp1 : es_formula: 
  emp*N@full[t_36]@zero[nn]&0<=nn' & nn_1396=nn & nn'=0&
compose_context_formula inp2 : 
  res::Thrd{ + emp*U@full[nn]&nn'=1+nn&{FLOW,(4,5)=__norm#E}[]}<>&
{FLOW,(4,5)=__norm#E}[]
compose_context_formula inp3 :[nn]
compose_context_formula@1 EXIT: es_formula: 
  (exists nn_1399: res::Thrd{ + emp*U@full[nn]&nn'=1+nn&{FLOW,(4,5)=__norm#E}[]}<>*
  N@full[t_36]@zero[nn]&0<=nn_1399 & nn_1396=nn & nn_1399=0&


compose_context_formula@1
compose_context_formula inp1 : 
 es_formula: emp*N@zero[nn]&0<=nn' & nn_1391=nn & nn'=0&{FLOW,(4,5)=__norm#E}[]
compose_context_formula inp2 : emp*U@full[nn]&nn'=1+nn&{FLOW,(4,5)=__norm#E}[]
compose_context_formula inp3 :[nn]
compose_context_formula@1 EXIT: es_formula: 
  (exists nn_1394: emp*U@full[nn]&0<=nn_1394 & nn_1391=nn & nn_1394=0 & 
  nn'=1+nn_1394&{FLOW,(4,5)=__norm#E}[]

*/
