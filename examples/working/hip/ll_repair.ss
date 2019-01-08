data node {
  int val;
	node next;
}

HeapPred P(node y).
HeapPred Q(node y).

ll<n> == self = null & n = 0
	or self::node<_, q> * q::ll<n-1>
  inv n >= 0;

node fcode(node y)
  requires P(y)
  ensures Q(y);

// void append(node x, node y)
//   requires x::ll<n1> * y::ll<n2> & x!=null
//   ensures x::ll<n1+n2>;
// {
// 	if (x.next == null){
//         //x.next = fcode(y);
//         // x::node<q> * y::ll<n2> & q = null & n1 = 1
//         x.next = y.next;
//         // x.next = y;
//         // x::ll<n1+n2>
//         // try first: x is different in pre and post ->
//         // x.sth = sth
//    }
// 	else {
// 	 	append(x.next, y);
//     }
// }

int foo(int x, int y)
requires true ensures res = 3 + y;
{
  x = 1;
  // dprint;
  x = 3 + y;
  // dprint;
  return x;
}


// x::node<q> * y::ll<n2> * q = null
// x.next = y
// x::ll<n2+1> & x = y

// x -> node<a> * y -> node<b>

// x -> node<y> * y -> node<b>


// x::ll<n1> * y ::ll<n2>

// x::ll<n2> & y = x

// {bind x to (next_24_1892) [write] in 
// next_24_1892 = y}]



// pre: : x::node<n1,a>@M&{FLOW,(4,5)=__norm#E}[]
// x::node<n2,a>@M&{FLOW,(4,5)=__norm#E}[]
// bind x to (val_4390) [write] in 
// val_4390 = n2Stop z3... 155 invocations 

// pre: x::node<n1, a> * y :: node<n2, b>
// post: x:node<n1, a> * y :: node<n3, b>

// pre: x =a ; vars = {x, b}
// post: x = b; 
