data node {
  int val;
  node next;
}


HeapPred G2(node a, node b).
HeapPred G1(node a).
HeapPred G3(node b,node c, node d).

HeapPred H1(node a).
HeapPred H1a(node a).
HeapPred H1b(node a).
HeapPred H2(node a, node b).

ll<> == self=null
  or self::node<_,q>*q::ll<>
  inv true;

lseg<p> == self=p
  or self::node<_,q>*q::lseg<p>
  inv true;

l2<y> == self::node<a,null> & y=self
  or self::node<_,q>*q::l2<y> 
  inv y!=null;

void append(node x, node y)

  infer[H1,H1a,H1b,G2]
  requires H1(x) * H1a(y)
     ensures G2(x,y) * H1b(y);
  /*

ERROR : why not make H1a(y) --> H1b(y)?

!!! HP_579([v_node_57_596])
!!!  =:  
     emp&v_node_57_596=null
  or H1(v_node_57_596)&true // WHY?
  or v_node_57_596::node<val_57_560',next_57_561'> * H1(next_57_561')&true
 
!!! >>>>>> generalize_one_hp: <<<<<<
!!! HP_612([x])
!!!  =:  
 H1a(y) * x::node<val_57_585,y>&true
 or x::node<val_57_587,v_node_57_602> * HP_612(v_node_57_602)&
    v_node_57_602!=null
 
!!! >>>>>> generalize_one_hp: <<<<<<
!!! H1([x])
!!!  =:  
 x::node<val_57_560',next_57_561'>&next_57_561'=null
 or x::node<val_57_560',next_57_561'> * H1(next_57_561')&true
 
!!! >>>>>> unk hps equivalent: <<<<<<
!!! H1a([y])= H1b(y)&true
!!! H1a([y])= HP_611(y)&true
!!! >>>>>> unknown hps: <<<<<<
!!! H1a([y])= htrue&true
!!! HP_611([y])= htrue&true
!!! H1b([y])= htrue&true
!!! >>>>>> equivalent hps: <<<<<<
!!! [HP_RELDEFN G2:  G2(x,y)::  
 x::node<val_57_587,v_node_57_602> * HP_612(v_node_57_602)&
 v_node_57_602!=null
 or H1a(y) * x::node<val_57_585,y>&true
 ]


   */
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

