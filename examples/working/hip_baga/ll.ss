data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0
  or self::node<_, q> * q::ll<n-1>
  /* inv n >= 0 */
  inv_exact BG([],self=null & n=0) | BG([self],n>0)
  /* inv_sat BG([],self=null & n=0) | BG([self],n>0) */
  ;

void append2(node x, node y)
  requires x::ll<n1> * y::ll<n2> & n1>0
  ensures x::ll<n1+n2> ;
{
  if (x.next == null)
    x.next = y;
  else
    append2(x.next, y);
}

void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & x!=null
  ensures x::ll<n1+n2>;
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

node ret_first(node x)
  requires x::ll<n> * y::ll<m> & n < m
  ensures x::ll<n>;
{
  return x;
}

node get_next(node x)
  requires x::ll<n> & n > 0
  ensures x::ll<1> * res::ll<n-1>;
{
  node tmp = x.next;
  x.next = null;
  return tmp;
}

void set_next(node x, node y)
  requires x::ll<i> * y::ll<j> & i > 0
  ensures x::ll<j+1>;
{
  x.next = y;
}

void set_null2(node x)
  requires x::ll<i> & i > 0
  ensures x::ll<1>;
{
  if (4>3)
    x.next = null;
  else
    x.next = null;
}

void set_null(node x)
  requires x::ll<i> & i > 0
  ensures x::ll<1>;
{
  x.next = null;
}

node get_next_next(node x)
  requires x::ll<n> & n > 1
  ensures res::ll<n-2>;
{
  return x.next.next;
}

void insert(node x, int a)
  requires x::ll<n> & n > 0
  ensures x::ll<n+1>;
{
  node tmp = null;
  if (x.next == null)
    x.next = new node(a, tmp);
  else
    insert(x.next, a);
}

void delete(node x, int a)
  requires x::ll<n> & n > a & a > 0
  ensures x::ll<n - 1>;
{
  if (a == 1)
    {
      x.next = x.next.next;
    }
  else
    {
      delete(x.next, a-1);
    }
}


node create_list(int a)
  requires a >= 0
  ensures res::ll<a>;
{
  node tmp;

  if (a == 0) {
    return null;
  }
  else {
    a  = a - 1;
    tmp = create_list(a);
    return new node (0, tmp);
  }
}

void reverse(node@R xs, node@R ys)
  requires xs::ll<n> * ys::ll<m>
  ensures ys'::ll<n+m> & xs' = null;
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}


void reverse2(node@R xs, node@R ys)
  requires xs::ll<n> * ys::ll<m>
  ensures ys'::ll<n+m> & xs' = null;
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}

void reverse3(node@R xs, node@R ys)
  requires xs::ll<n> * ys::ll<m>
  ensures ys'::ll<n+m> & xs' = null;
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}

void reverse4(node@R xs, node@R ys)
  requires xs::ll<n> * ys::ll<m>
  ensures ys'::ll<n+m> & xs' = null;
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}

void reverse5(node@R xs, node@R ys)
  requires xs::ll<n> * ys::ll<m>
  ensures ys'::ll<n+m> & xs' = null;
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}

void reverse6(node@R xs, node@R ys)
  requires xs::ll<n> * ys::ll<m>
  ensures ys'::ll<n+m> & xs' = null;
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}

void reverse7(node@R xs, node@R ys)
  requires xs::ll<n> * ys::ll<m>
  ensures ys'::ll<n+m> & xs' = null;
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}

void reverse8(node@R xs, node@R ys)
  requires xs::ll<n> * ys::ll<m>
  ensures ys'::ll<n+m> & xs' = null;
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}

void reverse9(node@R xs, node@R ys)
  requires xs::ll<n> * ys::ll<m>
  ensures ys'::ll<n+m> & xs' = null;
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}

void reverse10(node@R xs, node@R ys)
  requires xs::ll<n> * ys::ll<m>
  ensures ys'::ll<n+m> & xs' = null;
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}

void reverse11(node@R xs, node@R ys)
  requires xs::ll<n> * ys::ll<m>
  ensures ys'::ll<n+m> & xs' = null;
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}

void reverse12(node@R xs, node@R ys)
  requires xs::ll<n> * ys::ll<m>
  ensures ys'::ll<n+m> & xs' = null;
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}

void reverse13(node@R xs, node@R ys)
  requires xs::ll<n> * ys::ll<m>
  ensures ys'::ll<n+m> & xs' = null;
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}

void reverse14(node@R xs, node@R ys)
  requires xs::ll<n> * ys::ll<m>
  ensures ys'::ll<n+m> & xs' = null;
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}

void reverse15(node@R xs, node@R ys)
  requires xs::ll<n> * ys::ll<m>
  ensures ys'::ll<n+m> & xs' = null;
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}


void reverse16(node@R xs, node@R ys)
  requires xs::ll<n> * ys::ll<m>
  ensures ys'::ll<n+m> & xs' = null;
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}

void reverse17(node@R xs, node@R ys)
  requires xs::ll<n> * ys::ll<m>
  ensures ys'::ll<n+m> & xs' = null;
{
  if (xs != null) {
    node tmp;
    tmp = xs.next;
    xs.next = ys;
    ys = xs;
    xs = tmp;
    reverse(xs, ys);
  }
}
