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
  requires @full[n]
  ensures res::Thrd{+ @full[n] & n'=n+1}<> ;//& n'=n;

int main(int nn)
 requires @value[nn]
 ensures res=1;
{
  nn=0;
  //U@value[nn]&nn'=0 & MayLoop[] & nn_1391=nn&{FLOW,(4,5)=__norm#E}[]
  dprint;
  foo(nn);
  //State:emp*U@full[nn]&nn'=1+0 & nn_1391=nn&{FLOW,(4,5)=__norm#E}[]
  dprint;
  return nn;
 }
/*
# ex13a2.ss --ann-vp

check_pre_post(2) inp1 : EBase emp*U@full[n]&0<=n&{FLOW,(4,5)=__norm#E}[]
         EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                 EAssume ref [n]
                   emp*U@full[n]&n'=1+n&{FLOW,(4,5)=__norm#E}[]
check_pre_post(2) inp2 : List of Failesc Context: [FEC(0, 0, 1  [])]
 State:emp*U@value[nn]&nn'=0 & MayLoop[] & nn_1391=nn&{FLOW,(4,5)=__norm#E}[]
check_pre_post(2)@1 EXIT: List of Failesc Context: [FEC(0, 0, 1  [])]

 State:(exists nn_1394: emp*U@full[nn]&0<=nn_1394 & nn_1391=nn 
     & nn_1394=0 & nn'=1+nn_1394&{FLOW,(4,5)=__norm#E}[]

*/
