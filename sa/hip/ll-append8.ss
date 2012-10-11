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
HeapPred HP1(node a, node b).
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

  infer[H1,H1a,G2]
  requires H1(x) * H1a(y)
  ensures G2(x,y);
  /*

G2 base case should contain H1a(y)

!!! HP_578([v_node_50_595])
!!!  =:  
 emp&v_node_50_595=null
 or v_node_50_595::node<val_50_559',next_50_560'> * HP_578(next_50_560')&true
 
!!! >>>>>> generalize_one_hp: <<<<<<
!!! G2([x,y])
!!!  =:  
 x::node<val_50_584,y>&true
 or x::node<val_50_586,v_node_50_601> * G2(v_node_50_601,y)&
    v_node_50_601!=null
 


   */
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

