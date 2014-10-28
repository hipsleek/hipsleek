
pred_prim state<x:list(int)>
inv true;

pred_prim cex<x:list(int)>
inv true;

global cex cx;
global state st;

pred_prim add<n:int>
inv true;

lemma_prop "lemma_prop_list" self::state<L1> * self::add<n> & true
-> self::state<L2> & L2 = append(L1,[n]);


void inf_loop()
  requires cx::cex<[1]> & Loop
  ensures  false; // []


void main()
  requires cx::cex<[2]> &  Loop
  ensures false; // []
{
  int x;
  x=x-1;
  inf_loop();
}
