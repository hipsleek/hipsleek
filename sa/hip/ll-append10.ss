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

!!! G2([x,y])
!!!  =:  
 H1a(y) * x::node<val_45_585,y>&true
 or x::node<val_45_587,v_node_45_602> * G2(v_node_45_602,y)&
    v_node_45_602!=null
 
!!! >>>>>> generalize_one_cs_hp: <<<<<<
!!! H1([x])= x::node<val_45_560',next_45_561'> * HP_579(next_45_561')&true
!!! >>>>>> equivalent hps: <<<<<<
!!! >>>>>> unknown hps: <<<<<<
!!! H1a([y])= htrue&true
!!! H1b([y])= htrue&true
!!!  remains: [ RELASS [H1a,HP_579,G2,H1b] unknown svl: [y];  unknown hps: [H1a; 
  H1b];  predefined: [x]; H1a(y) * x::node<val_45_585,y>&true --> G2(x,y) * 
  H1b(y)&true]
Procedure append$node~node SUCCESS


   */
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

