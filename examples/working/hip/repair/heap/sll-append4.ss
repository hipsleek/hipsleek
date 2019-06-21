data node {
   node next;
}

ll<n> == self = null & n = 0
      or self::node<q> * q::ll<n-1>;

void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & x!=null
  ensures x::ll<n1+n2>;
{
  if (x.next == null){
     x.next = x;
     // x.next = y;
  } else append(x.next, y);
}



// [LABEL! 101,0: {bind x to (next_13_1888) [write] in 
// next_13_1888 = x}]

