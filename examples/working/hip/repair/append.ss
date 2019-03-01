data node {
  int val;
	node next;
}

HeapPred P(node x, node y).
HeapPred Q(node x, node y).

ll<n> == self = null & n = 0
	or self::node<_, q> * q::ll<n-1>
  inv n >= 0;

node fcode(node x, node y)
  requires P(x, y)
  ensures Q(x, y);

void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & x!=null
  ensures x::ll<n1+n2>;
{
	if (x.next == null){
  // x!= null
        x.next = y;

// x::ll<n1+n2>
// x::node<v1, m> * m::ll<n1+n2-1>
   }
	else {
      append(x.next, y);
       //fcode(x,y);
    }
}

/*
input1:   x'::node<Anon_1926,q_1927>@M * q_1927::ll<flted_10_1925>@M * y::ll<n2>
 & !(v_bool_21_1904') & y'=y & x'=x & x!=null & flted_10_1925+1=n1 & 
q_1927!=null
input2:   P(x',y')
output:   T0(Anon_1926,n2,y',y,x',x,flted_10_1925,n1,q_1927) * Q(x',y')


input1: T0(Anon_1926,n2,y',y,x',x,flted_10_1925,n1,q_1927) * Q(x',y') 
input2: (exists flted_19_99: x::ll<flted_19_99>@M&flted_19_99=n2+n1&
output: emp

*/

