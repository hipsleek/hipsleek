data node {
	node next;
}

HeapPred P(node y).
HeapPred Q(node y).

ll<n> == self = null & n = 0
	or self::node<q> * q::ll<n-1>
  inv n >= 0;

node fcode(node y)
  requires P(y)
  ensures Q(y);

void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & x!=null
  ensures x::ll<n1+n2>;
{
	if (x.next == null){
        //x.next = fcode(y);
        // x::node<q> * y::ll<n2> & q = null & n1 = 1
        x.next = y.next;
        // x::ll<n1+n2>
        // try first: x is different in pre and post ->
        // x.sth = sth
   }
	else {
	 	append(x.next, y);
    }
}

// x::node<q> * y::ll<n2> * q = null
// x.next = y
// x::ll<n2+1> & x = y

// x -> node<a> * y -> node<b>

// x -> node<y> * y -> node<b>


// x::ll<n1> * y ::ll<n2>

// x::ll<n2> & y = x

