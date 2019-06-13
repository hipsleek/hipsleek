data node {
	node next;	
}

ll<n> == self = null & n = 0 
	or self::node<q> * q::ll<n-1>;

node copy(node x)
requires x::ll<n>
ensures res::ll<n> * x::ll<n>;
{
  if (x == null) return x;
  else {
      node tmp = copy(x.next);
      node k = new node(tmp);
      return k.next;
      // return k;
  }
}

// [LABEL! 100,1: {(((node tmp;
// tmp = {((node v_node_15_1899;
// v_node_15_1899 = bind x to (val_15_1895,next_15_1896) [read] in 
// next_15_1896);
// copy$node(v_node_15_1899) rec)});
// (node n;
// n = {((int v_int_16_1902;
// v_int_16_1902 = bind x to (val_16_1900,next_16_1901) [read] in 
// val_16_1900);
// new node(v_int_16_1902,tmp))}));
// ret# n)}]

