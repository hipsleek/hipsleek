data node {
  int val;
  node next;
}

/* non-redundant version of bigint where 0 is denoted uniquely */

bigint<v> == self = null & v = 0 or
     self::node<p, q> * q::bigint<v1> & 0 <= p <= 9 & v = 10*v1 + p 
     inv v >= 0;

node bigint_of(int v)
  requires v >= 0
  ensures res::bigint<v>;

node add_one_digit(node x, int c)
  requires x::bigint<v>@L & 0 <= c <= 9
  ensures res::bigint<v+c>;

node add(node x, node y)
  requires (x::bigint<v1>@L * y::bigint<v2>@L) & true
  ensures res::bigint<v1+v2>;

node sub_one_digit(node x, int c)
  requires x::bigint<v>@L & 0 <= c <= 9 & c <= v
  ensures res::bigint<v-c>;

node sub(node x, node y)
  requires (x::bigint<v1>@L * y::bigint<v2>@L) & v1 >= v2
  ensures res::bigint<v1-v2>;

/* left shift all digits one pos (multiplied by ten) */
node shift_left(node x)
  case {
    x=null -> ensures res=null;
   x!=null -> ensures res::node<0,x>;
  }
{
  if (x == null) { return x;}
  node t = new node(0, x);
//  dprint;
  return t;
}



node mult(node x, node y)
  requires (x::bigint<v1>@L * y::bigint<v2>@L) & true
  ensures res::bigint<v1*v2>;

node karatsuba_mult(node x, node y)
  requires (x::bigint<v1>@L * y::bigint<v2>@L) & true
  ensures res::bigint<v2*v1>; // * x::bigint<v1>@L * y::bigint<v2>@L;
{
  if (x == null || y == null) {
			       //assume false;
			       return null;
				      }
  if (x.next == null || y.next == null) 
     {
      //assume false;
      return mult(x, y);
     }
  // x = x1*10+x2
  // y = y1*10+y2
  // A = x1*y1
  node A = karatsuba_mult(x.next, y.next);
  // B = x2*y2
  node B = bigint_of(x.val * y.val);
  // C= (x1+x2)*(y1+y2)
  node C = karatsuba_mult(add_one_digit(x.next, x.val), add_one_digit(y.next, y.val));
  // K = C - A - B = x1*y2 + x2*y1
  node K = sub(C, add(A, B));
  // node K = add(mult_c(x.next, y.val, 0), mult_c(y.next, x.val, 0));
  // x * y = A*100 + K*10 + B
  return add(shift_left(shift_left(A)), add(shift_left(K), B));
  //assume false;
  //dprint;
  //return r;
}

