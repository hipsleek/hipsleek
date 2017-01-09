data node {
  int val;
  node next;
}

/*
ll<n> == emp & self=null & n=0
  or self::node<_,q>*q::ll<n-1>
  inv n>=0;
*/

relation P(int n).
  relation Q(int n, int m, int r).

HeapPred PP(node x, node@NI y).
PostPred QQ(node x, node y).

ll<> == emp & self=null 
  or self::node<_,q>*q::ll<>
  inv true;

void append(node x, node y)
/*
  requires x::ll<n> * y::ll<m> & n>0
  ensures x::ll<n+m>;
*/
  infer [PP,QQ]
  requires PP(x,y)
  ensures QQ(x,y);
{
  if (x.next==null) x.next=y;
  else append(x.next,y);
}

/*
# ex22-11-app.ss

PROBLEM : why wasn't 2nd parameter of HP_1395 eliminated?
Do we need to invoke option?

let pred_elim_useless = ref true

[ PP(x_1414,y_1415) ::= x_1414::node<val_25_1393,next_25_1394> * HP_1395(next_25_1394,y_1415)&
y_1415=DP_DP_HP_1396(4,5),
 QQ(x_1421,y_1422) ::= 
 x_1421::node<val_25_1393,next_25_1394> * QQ(next_25_1394,y_1422)&
 next_25_1394!=null
 or x_1421::node<val_25_1393,y_1422>&y_1422=DP_DP_HP_1396
 (4,5),
 HP_1395(next_25_1419,y_1420) ::= 
 next_25_1419::node<val_25_1393,next_25_1394> * HP_1395(next_25_1394,y_1420)&
 y_1420=DP_DP_HP_1396
 or emp&next_25_1419=null
 (4,5)]
*************************************

PROBLEM : where did HP_1389(x) and HP_1390(y) came from?

!!! INFERRED SHAPE SPEC: EBase HP_1389(x) * HP_1390(y)&{FLOW,(4,5)=__norm#E}[]
         EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                 EAssume 
                   x::QQ{}<y>&{FLOW,(4,5)=__norm#E}[]



*/
