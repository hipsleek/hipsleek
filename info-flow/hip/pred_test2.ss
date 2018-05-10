data node {
  int  val;
  node nxt;
}

/* lemma_safe self::safell<n> -> self::unsafell<n>; */
/* lemma_safe self::unsafell<n> -> self::safell<n>; */
/* lemma_safe self::safell<n> -> self::safell<n> & self <^ @Lo; */

pred safell<n> == self = null & n = 0 & self <^ @Lo
  or self::node<v,q> * q::safell<n-1> & n > 0 & self <^ @Lo & v <^ @Lo
  inv n >= 0 & self <^ @Lo;

pred unsafell<n> == self = null & n = 0 & self <^ @Hi
  or self::node<v,q> * q::unsafell<n-1> & n > 0 & self <^ @Hi & v <^ @Hi
  inv n >= 0 & self <^ @Hi;

int sum1(node p)
  requires p::safell<n> & p <^ @Lo
  ensures  res <^ @Lo;
{
  if(p == null) {
    return 0;
  } else {
    return p.val + sum1(p.nxt);
  }
}

int sum2_fail(node p)
  requires p::unsafell<n> & p <^ @Lo
  ensures  res <^ @Lo;
{
  if(p == null) {
    return 0;
  } else {
    return p.val + sum2_fail(p.nxt);
  }
}

int sum3(node p)
  requires p::safell<n> & p <^ @Lo
  ensures  res <^ @Hi;
{
  if(p == null) {
    return 0;
  } else {
    return p.val + sum3(p.nxt);
  }
}

int sum4_fail(node p)
  requires p::unsafell<n> & p <^ @Lo
  ensures  res <^ @Hi;
{
  if(p == null) {
    return 0;
  } else {
    return p.val + sum4_fail(p.nxt); // precond failure
  }
}

int sum5_fail(node p)
  requires p::safell<n> & p <^ @Hi
  ensures  res <^ @Lo;
{
  if(p == null) {
    return 0;
  } else {
    return p.val + sum5_fail(p.nxt);
  }
}

int sum6_fail(node p)
  requires p::unsafell<n> & p <^ @Hi
  ensures  res <^ @Lo;
{
  if(p == null) {
    return 0;
  } else {
    return p.val + sum6_fail(p.nxt);
  }
}

int sum7(node p)
  requires p::safell<n> & p <^ @Hi
  ensures  res <^ @Hi;
{
  if(p == null) {
    return 0;
  } else {
    return p.val + sum7(p.nxt);
  }
}

int sum8(node p)
  requires p::unsafell<n> & p <^ @Hi
  ensures  res <^ @Hi;
{
  if(p == null) {
    return 0;
  } else {
    return p.val + sum8(p.nxt);
  }
}
