/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<> == self = null
	or self::node<_, q> * q::ll<> 
  inv true;

lseg<p> == self=p
  or self::node<_, q> * q::lseg<p>
  inv true;


HeapPred P(node x, node y,node z).

node append(node x, node y)
  infer [P,@classic]
  requires x::ll<>
  ensures P(x,y,res);
{    
  if (x==null) return y;
  else {
      x.next = append(x.next, y);
      return x;
  }
}


/*
# ex21p2.ss
  node append(node x, node y)
  requires x::ll<>
  ensures P(x,y,res);
*******relational definition********
*********************************************************
[ P(x_1661,y_1662,res_1663) ::= emp&x_1661=null & y_1662=res_1663
 or x_1661::node<Anon_1664,v_node_31_1659>@M * 
    P(q_1647,y_1662,v_node_31_1659)&
    x_1661!=null & res_1663!=null & x_1661=res_1663
 (4,5)]
*************************************

=========================
[ // POST
(2;0)res::node<Anon_1646,v_node_31_1659>@M * 
     GP_1660(v_node_31_1659,y,res,x@NI)&x=res & res!=null --> P(x,y,res)&
true,
 // POST
(2;0)P(q_1647,y,v_node_31_1659)&
res!=null & x=res --> GP_1660(v_node_31_1659,y,res,x@NI)&
true,
 // POST
(1;0)x::ll<>@M * GP_1658(y,res,x@NI)&y=res & x=null --> P(x,y,res)&
true,
 // POST
(1;0)emp&x=null & y=res --> GP_1658(y,res,x@NI)&
true]

=======================================

res::node<Anon_1646,v_node_31_1659>@M * 
  GP_1660(v_node_31_1659,y,res,x@NI)&x=res & res!=null --> P(x,y,res).

P(q_1647,y,v_node_31_1659)&
res!=null & x=res --> GP_1660(v_node_31_1659,y,res,x@NI).


x::ll<>@M * GP_1658(y,res,x@NI)&y=res & x=null 
   --> P(x,y,res).
 
emp&x=null & y=res --> GP_1658(y,res,x@NI).

=========================================


GP_1658(y,res,x@NI) <--  emp&x=null & y=res
// defn
GP_1658(y,res,x@NI) ==  emp&x=null & y=res


GP_1660(v_node_31_1659,y,res,x@NI) <-
  P(q_1647,y,v_node_31_1659)& res!=null & x=res 

GP_1660(v_node_31_1659,y,res,x@NI) ==
  P(q_1647,y,v_node_31_1659)& res!=null & x=res 

P(x,y,res) <-
  x::ll<>@M * GP_1658(y,res,x@NI)&y=res & x=null 
// unfold GP
P(x,y,res) <-
  x::ll<>@M * x=null & y=res &y=res & x=null 
// unfold ll
P(x,y,res) <-
  x=null & y=res &y=res & x=null 

P(x,y,res) <-
 res::node<Anon_1646,v_node_31_1659>@M * 
  GP_1660(v_node_31_1659,y,res,x@NI)&x=res & res!=null
// unfold GP
P(x,y,res) <-
 res::node<Anon_1646,v_node_31_1659>@M * 
  P(q_1647,y,v_node_31_1659)& res!=null & x=res &x=res & res!=null

  P <- B \/ C
----------------
P <- B /\ P <- C

P(x,y,res) <-
  x=null & y=res 
  \/  res::node<Anon_1646,v_node_31_1659>@M * 
       P(q_1647,y,v_node_31_1659)& res!=null & x=res 

P(x,y,res) <->
  x=null & y=res 
  \/  res::node<Anon_1646,v_node_31_1659>@M * 
       P(q_1647,y,v_node_31_1659)& x=res 

  res::lseg<y> & (x=null or x=res) 

*/
