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
        fcode(x,y);
        //x.next = y;
   } else {
       append(x.next, y);
    }
}

// x::node<Anon_1929,q_1930> * q_1930::ll<flted_10_1928> * y::ll<n2> &
// v_bool_21_1907 & y=y & x=x & x!=null & flted_10_1928+1=n1 & q_1930=null
// |- P(x,y)

// Q(x,y) * T(x,y,..)

// T0(..) * Q(x,y,..) |- post ~> emp
// if there are only two entailment, then the synthesis pair is (hd fst, snd snd)
// ./hip examples/working/hip/repair/append-tmpl.ss --songbird --en-repair --en-repair-templ