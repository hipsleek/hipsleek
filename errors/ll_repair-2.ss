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
       bool b = x.next==null;

       /*
             q_1934::ll<flted_10_1932>@M * y::ll<n2>@M * x::node<Anon_1933,q_1934>@M&
b' & x!=null & y'=y & x'=x & flted_10_1932+1=n1 & q_1934=null&
\/
    CtxOR
      q_1934::ll<flted_10_1932>@M * y::ll<n2>@M * x::node<Anon_1933,q_1934>@M&
!(b') & x!=null & y'=y & x'=x & flted_10_1932+1=n1 & q_1934!=null&

requires x::ll<n1> & x!=null
ensures q_1934::ll<flted_10_1932>@M * x::node<Anon_1933,q_1934>@M&
   b' & x!=null & x'=x & flted_10_1932+1=n1 & q_1934=null&
    \/  q_1934::ll<flted_10_1932>@M * x::node<Anon_1933,q_1934>@M&
   !(b') & x!=null & x'=x & flted_10_1932+1=n1 & q_1934!=null&

--> // immutability and frame seems to be important here.

requires x::node<Anon_1933,q_1934> & x!=null
ensures  x::node<Anon_1933,q_1934>@M&
   b' & x!=null & x'=x & q_1934=null&
    \/  x::node<Anon_1933,q_1934>@M&
   !(b') & x!=null & x'=x & q_1934!=null&

       */ 
       dprint;
	if (b){
        //x.next = fcode(y);
        // x::node<q> * y::ll<n2> & q = null & n1 = 1
        /*
     q_1934::ll<flted_10_1932>@M * y::ll<n2>@M * x::node<Anon_1933,q_1934>@M&
b' & q_1934=null & flted_10_1932+1=n1 & x'=x & y'=y & x!=null&
        */
        dprint;
        x.next = y;
        dprint;
        /*
     q_1934::ll<flted_10_1932>@M * y::ll<n2>@M * x'::node<Anon_1933,y'>@M&
flted_10_1932=n1-1 & y'=y & q_1934=null & x'=x & b' & x!=null&
        */
        // x.next = y;
        // x::ll<n1+n2>
        // try first: x is different in pre and post ->
        // x.sth = sth
   }
	else {
          /*
     q_1934::ll<flted_10_1932>@M * y::ll<n2>@M * x::node<Anon_1933,q_1934>@M&
!(b') & q_1934!=null & flted_10_1932+1=n1 & x'=x & y'=y & x!=null&
           */
          dprint;
          node x1 = x.next;
          dprint;
          /*
     x1'::ll<flted_10_1932>@M * y::ll<n2>@M * x::node<Anon_1933,x1'>@M&
flted_10_1932=n1-1 & y'=y & x'=x & !(b') & x1'!=null & x!=null&
           */
          append(x1, y);
          //fcode(x,y);
    }
}

// int foo(int x, int y)
// requires true ensures res = 3 + y;
// {
//   x = 1;
//   // dprint;
//   x = 3 + y;
//   // dprint;
//   return x;
// }


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
