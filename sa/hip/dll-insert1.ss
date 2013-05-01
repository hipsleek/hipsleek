data node2 {
	int val;
	node2 prev;
	node2 next;
}

dll<p,n> == self = null & n = 0
  or self::node2<_ ,p , q> * q::dll<self, n-1> // = q1
	inv n >= 0;

HeapPred G1(node2 a).
HeapPred H1(node2 a).

void insert(node2 x, int a)
  /* infer[n] */
  /* requires x::dll<p, n> & n>0 //&  x!=null */
  /* ensures x::dll<p, m> & m>n; */

  infer[H1,G1]
  requires H1(x)
  ensures G1(x);
{
  bool l = x.next == null;
  if (l)
    x.next = new node2(a, x, null);
  else
    insert(x.next, a);
}

/*
 HP_553(prev_23_560,v_node2_23_575) * v_node2_25_592::node2<a,x,v_null_25_576>@M * x::node2<val_23_559,prev_23_560,v_node2_25_592>@M * HP_596(prev_23_560)&  v_null_25_576=null & v_node2_23_575=null --> G1(x)&true,
 H1(x)& true --> x::node2<val_23_530',prev_23_531',next_23_532'>@M * HP_553(prev_23_531',next_23_532') * HP_596(prev_23_531')&true,
 HP_553(prev_23_564,v_node2_23_582)&  v_node2_23_582!=null --> H1(v_node2_23_582)&true,
 HP_553(prev_23_564,v_node2_23_582) * HP_596(prev_23_564)&true --> HP_589(prev_23_564)&true,
 x::node2<val_23_563,prev_23_564,v_node2_23_582>@M * HP_589(prev_23_564) * G1(v_node2_23_582)&v_node2_23_582!=null --> G1(x)&true


get_longest_common_hnodes_list inp1 :G1
get_longest_common_hnodes_list inp2 :[x_796]
get_longest_common_hnodes_list inp3 :[
 v_node2_25_592::node2<a,x_796,v_null_25_576>@M * x_796::node2<val_23_559,prev_23_560,v_node2_25_592>@M * HP_596(prev_23_560)&
v_null_25_576=null,
 x_796::node2<val_23_559,prev_23_560,v_node2_25_592>@M * HP_589(prev_23_560) * G1(v_node2_25_592)&true
 */
