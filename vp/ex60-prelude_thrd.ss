pred_prim Thrd{-%P,+%Q}<>;
pred_prim Thrd2{+%Q@Split}<>;
pred_prim dead<>;


thrd create_thread(ref int n) 
  requires true
  ensures res::Thrd{-@full[n],+@full[n]& n'=n+1}<>;//'

void forkk(thrd t)
  requires t::Thrd{-%P,+%Q}<> * %P
  ensures  t::Thrd2{+%Q}<>;

void join(thrd t)
  requires t::Thrd2{+%Q}<>
  ensures %Q * t::dead<>;

int main(int x)
  requires @full[x] & x=5
  ensures res=6;
{
  thrd t = create_thread(x);
  //x=x+1;
  dprint;
  forkk(t);
  //dprint;
  /*
  join(t);
  dprint;
  */
  return 6;
}
/*
# ex60

how to support with %P,%Q ?

id: 5; caller: []; line: 25; classic: false; kind: PRE; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp
 checkentail t_39'::Thrd{ + emp*N@full[x]&x'=1+x&{FLOW,(4,5)=__norm#E}[], - htrue*N@full[x]&{FLOW,(4,5)=__norm#E}[]}<>*
N@full[t_39,x]&x=5&{FLOW,(4,5)=__norm#E}[]
 |-  t_39'::Thrd{ + HVar Q&{FLOW,(4,5)=__norm#E}[], - HVar P&{FLOW,(4,5)=__norm#E}[]}<> * 
(HVar P)&{FLOW,(4,5)=__norm#E}[]. 
h
*/
