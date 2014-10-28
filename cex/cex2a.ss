
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
  requires cx::cex<[#inf_loop]> & Loop
  ensures  false; // []


void main()
  requires cx::cex<[#main,#inf_loop]> &  Loop
  ensures false; // []
{
  int x;
  x=x-1;
  inf_loop();
}


void aux()
  requires cx::cex<[#aux,#if_1,#inf_loop]> &  MayLoop
  ensures true; // []
{
  int x;
  x=x-1;
  if (x>0) inf_loop();
}


/*
$ cex2.ss

 #if_1
 #else_1
 #fname
 #main
 #inf_loop


# cex2.ss
cx used for reading; so no need for ref
in this example.

void main$cex(  cex cx_16)
@ref cx_16

static  EBase (exists flted_24_44: cx_16::cex{}<flted_24_44>&flted_24_44=[2] & 
       Loop[]&{FLOW,(4,5)=__norm})[]
         EAssume ref [cx_16]
           hfalse&false&{FLOW,(4,5)=__norm}[]


if_i   --> i*2-1
else_i --> i*2

 */
