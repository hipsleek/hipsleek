
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

pred_prim ND<>
inv true;

bool non_det()
  requires true
  ensures res::ND<>;

int non_det_int()
  requires true
  ensures res::ND<>;

void inf_loop()
//requires cx::cex<[#inf_loop]> & Loop
  requires cx::cex<[-1]> & Loop
  ensures  false; // []


void main()
//requires cx::cex<[#main,#inf_loop]> &  Loop
  requires cx::cex<[-2,-1]> &  Loop
  ensures false; // []
{
  //assume cx'::cex<[-2]> & true; //'
  int x;
  x=x-1;
  //assume x'>4; //'
  //assume cx'::add<-1> & true; //'
  assume cx'::cex<[-1]> ; //'
    dprint;
  inf_loop();
}

void aux()
//requires cx::cex<[#aux,#if_1,#main]> &  MayLoop
  requires cx::cex<[-3,1,-1]> &  MayLoop
  ensures true; // []
{
  int x;
  x=non_det_int();
  if (x>0) main();
}

void aux2(int x)
//requires cx::cex<[#aux2,#if_1,#main]> &  MayLoop
 case {
  x>1 -> requires cx::cex<[-4,1,-1]> &  Loop ensures false;
  x<=1 -> requires true ensures true;
 }
{
  x=x-1;
  if (x>0) main();
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
