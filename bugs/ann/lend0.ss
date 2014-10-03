data node {
  int val;
  node next;
}

/* node snd1(node x) */
/*  requires (x::node<_,q>@L & q::node<_,r>@L) */
/*  ensures  res=r; */
/* { */
/*   return x.next.next; */
/* } */


/* node snd2(node x) */
/*  requires x::node<_,q>@L * q::node<_,r>@L */
/*  ensures  res=r; */
/* { */
/*   return x.next.next; */
/* } */



get_next<n> == self::node<_,n>;


node snd3(node x)
 requires x::get_next<q> & q::get_next<r>
 ensures  res=r;
{
  return x.next.next;
}

/*   pred get_snd<n> == self::node<_,n>@L /\ q::node<_,n>@L */
/*   pred get_foo<n> == self::node<_,n> * q::node<_,n>@I */



/*  requires x::get_next<q>/\q::get_next<r> */
/*  ensures  res=r; */

/*  requires x::get_snd<r> */
/*  ensures  res=r; */


/* void setsnd(node x) */
/*  requires x::node<_,q>@L /\ q::node<_,r>@L /\ r::node<_,_> */
/*  ensures  r::node<_,null>; */
/* { */
/*   x.next.next= null */
/* } */

/* void setsnd(node x) */
/*  requires x::node<_,q>@f1 * q::node<_,r>@f2 * r::node<_,_> */
/*  ensures  r::node<_,null>; */
/* { */
/*   x.next.next= null */
/* } */


