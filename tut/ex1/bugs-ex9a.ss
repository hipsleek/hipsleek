data node {
  int val;
  node next;
}

ll<> == emp & self=null
  or self::node<_,q>*q::ll<>
  inv true;

/* non-touching list segment */
ls_nt<p> == emp & self=p
  or self::node<_,q>*q::ls_nt<p> & self!=p
  inv true;


int length(node x,node p)
 case {
  x=p -> ensures emp & res=0;
  x!=p -> requires x::ls_nt<p>
          ensures x::ls_nt<p> & res>0;
  }
{
  if (x==p) return 0;
  else return 1+length(x.next,p);
}

/*
# bugs-ex9a.ss

There is no Term nor MayLoop proven for 
this length method. Can we omit this message?
Can this message be highlighted when we have
at least one Term/Loop proven.

Termination checking result: SUCCESS

*/

