data node {
  int val;
  node next;
}

// success - ok
/* node snd1(node x) */
/*  requires (x::node<_,q>@L & q::node<_,r>@L) */
/*  ensures  res=r; */
/* { */
/*   return x.next.next; */
/* } */

// success - ok
/* node snd2(node x) */
/*  requires x::node<_,q>@L * q::node<_,r>@L */
/*  ensures  res=r; */
/* { */
/*   return x.next.next; */
/* } */



/* get_next<n> == self::node<_,n>; */

/* //ok */
/* node snd3(node x) */
/*   requires (x::get_next<q>@L & q::get_next<r>@L) */
/*  ensures  res=r; */
/* { */
/*   return x.next.next; */
/* } */

/* //ok */
/* node snd4(node x) */
/*   requires (x::get_next<q>@L * q::get_next<r>@L) */
/*  ensures  res=r; */
/* { */
/*   return x.next.next; */
/* } */


/* get_snd<n> == self::node<_,q>@L & q::node<_,n>@L; */

/* // success - ok */
/* node snd5(node x) */
/*  requires x::get_snd<r> */
/*  ensures  res=r; */
/* { */
/*   return x.next.next; */
/* } */


/* get_foo<n> == self::node<_,n> * q::node<_,n>@I */

//fail - ok
void setsnd(node x)
  requires (x::node<_,q>@L & q::node<_,r>@L & r::node<_,_>@L)
  ensures  r::node<_,null>;
{
  x.next.next= null;
}

void setsnd0(node x)
  requires x::node<_@A,q@L> * q::node<_@A,r> * r::node<_,_>
  ensures  true;//r=null;
{
  x.next.next= null;
}

/* void setsnd(node x) */
/*  requires x::node<_,q>@f1 * q::node<_,r>@f2 * r::node<_,_> */
/*  ensures  r::node<_,null>; */
/* { */
/*   x.next.next= null */
/* } */


