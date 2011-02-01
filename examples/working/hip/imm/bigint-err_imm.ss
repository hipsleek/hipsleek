data node {
  int val;
  node next;
}

bigint<v> == self = null & v = 0 or
             self::node<p, q> * q::bigint<v1> & 0 <= p <= 9 & v = 10*v1 + p
             inv v >= 0;

node clone(node x)
  requires x::bigint<v>@I
  ensures res::bigint<v>;

int int_value(node x)
  requires x::bigint<v>@I
  ensures res = v;

node bigint_of(int v)
  requires v >= 0
  ensures res::bigint<v>;

node add_one_digit(node x, int c)
/*  requires x::bigint<v> & 0 <= c <= 9
  ensures res::bigint<v+c> * x::bigint<v>;*/
  requires x::bigint<v>@I & 0 <= c <= 9
  ensures res::bigint<v+c> ;


node test(node x) 
 requires x::bigint<v>@I
 ensures res::bigint<2*v>;

node add_c(node x, node y, int c)
/*
  requires x::bigint<v1> * y::bigint<v2> & 0 <= c <= 1
  ensures res::bigint<v1+v2+c> * x::bigint<v1> * y::bigint<v2>;
*/
/*
  requires x::bigint<v1> * y::bigint<v2> & 0 <= c <= 1
  ensures res::bigint<v1+v2+c> ;

 requires (x::bigint<v1>@I & y::bigint<v2>@I) & 0 <= c <= 1
  ensures res::bigint<v1+v2+c>;

*/
// above should fail but did not

/*
  requires x::bigint<v1>@I * y::bigint<v2>@I & 0 <= c <= 1
  ensures res::bigint<v1+v2+c>;
*/
  requires (x::bigint<v1>@I & y::bigint<v2>@I) & 0 <= c <= 1
  ensures res::bigint<v1+v2+c>;


node add(node x, node y)
  requires (x::bigint<v1>@I & y::bigint<v2>@I) & true
  ensures res::bigint<v1+v2>;
/*
  requires x::bigint<v1>@I * y::bigint<v2>@I
  ensures res::bigint<v1+v2>;
*/

node sub_one_digit(node x, int c)
  requires x::bigint<v>@I & 0 <= c <= 9 & c <= v
  ensures res::bigint<v-c>;

node sub_c(node x, node y, int c)
/*
  requires (x::bigint<v1>@I) ; y::bigint<v2>@I & 0 <= c <= 1 & v1 >= v2+c
  ensures res::bigint<v1-v2-c>;

 requires x::bigint<v1>@I * y::bigint<v2>@I & 0 <= c <= 1 & v1 >= v2+c
  ensures res::bigint<v1-v2-c>;

  requires x::bigint<v1>@I * y::bigint<v2>@I & 0 <= c <= 1 & v1 >= v2+c
  ensures res::bigint<v1-v2-c>;

 requires (y::bigint<v2>@I & x::bigint<v1>@I) & 0 <= c <= 1 & v1 >= v2+c
 ensures res::bigint<v1-v2-c>;

  requires x::bigint<v1>@I * y::bigint<v2>@I & 0 <= c <= 1 & v1 >= v2+c
  ensures res::bigint<v1-v2-c>;

 requires (y::bigint<v2>@I & x::bigint<v1>@I) & 0 <= c <= 1 & v1 >= v2+c
 ensures res::bigint<v1-v2-c>;

*/ 

/*
 requires x::bigint<v1>@I * y::bigint<v2>@I & 0 <= c <= 1 & v1 >= v2+c
  ensures res::bigint<v1-v2-c>;
*/

 requires (y::bigint<v2>@I & x::bigint<v1>@I) & 0 <= c <= 1 & v1 >= v2+c
 ensures res::bigint<v1-v2-c>;


node sub(node x, node y)
  requires (x::bigint<v1>@I & y::bigint<v2>@I) & v1 >= v2
  ensures res::bigint<v1-v2>;
  requires x::bigint<v1>@I * y::bigint<v2>@I & v1 >= v2
  ensures res::bigint<v1-v2>;

node mult_c(node x, int d, int c)
  requires x::bigint<v>@I & 0 <= c <= 9 & 0 <= d <= 9 
  ensures res::bigint<v*d+c>;

/* left shift all digits one pos (multiplied by ten) */
node shift_left(node x)
  requires x::bigint<v>@I
  ensures res::bigint<v*10>@I;

node mult(node x, node y)
  requires (x::bigint<v1>@I & y::bigint<v2>@I) & true
  ensures res::bigint<v1*v2>;
  requires x::bigint<v1>@I * y::bigint<v2>@I
  ensures res::bigint<v1*v2>;

node karatsuba_mult(node x, node y)


/*
Checking procedure karatsuba_mult$node~node... 
Procedure karatsuba_mult$node~node result FAIL
Halting Reduce... 
Stop Omega... 81 invocations 


*/

 requires x::bigint<v1>@I * y::bigint<v2>@I
 ensures res::bigint<v1*v2> ;// x::bigint<v1> * y::bigint<v2>;

 requires (x::bigint<v1>@I & y::bigint<v2>@I) & true
 ensures res::bigint<v1*v2> ;// x::bigint<v1> * y::bigint<v2>;

{
  if (x == null || y == null) return null;
  if (x.next == null || y.next == null) return mult(x, y);
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
}

bool is_zero(node x)
  requires x::bigint<v>@I
  ensures true & (res & v = 0 | !res & v != 0);

bool is_equal(node x, node y)
  requires x::bigint<v1>@I * y::bigint<v2>@I
  ensures true & (res & v1 = v2 | !res & v1 != v2);

int compare(node x, node y)

  requires( x::bigint<v1>@I & y::bigint<v2>@I) & 1=1
  ensures true & (res = 0 & v1 = v2 | res = 1 & v1 > v2 | res = -1 & v1 < v2);
/*
  requires x::bigint<v1>@I * y::bigint<v2>@I
  ensures true & (res = 0 & v1 = v2 | res = 1 & v1 > v2 | res = -1 & v1 < v2);
*/
 /*
  // fail: why?
Procedure compare$node~node FAIL-2

ExceptionStack overflowOccurred!

Error(s) detected when checking procedure compare$node~node
Halting Reduce... 
Stop Omega... 69 invocations 
0 false contexts at: ()


 */
 

{
  if (x == null) {
    if (is_zero(y)) return 0;
    return -1;
  }
  if (y == null) {
    if (is_zero(x)) return 0;
    return 1;
  }
  int c = compare(x.next, y.next);
  if (c == 0) return compare_int(x.val, y.val);
  return c;
}

int compare_int(int x, int y)
  requires true
  ensures true & (res = 0 & x = y | res = 1 & x > y | res = -1 & x < y);

int div_with_remainder(int a, int b, ref int r)
  requires a >= 0 & b >= 1
  ensures a = b*res + r' & res >= 0 & 0 <= r' <= b-1;
