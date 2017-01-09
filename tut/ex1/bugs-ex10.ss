data node {
  int val;
  node prev;
  node next;
}

sll<> == emp & self=null
  or self::node<_,_,q>*q::sll<>
  inv true;

dll<pr> == emp & self=null
  or self::node<_,pr,q>*q::dll<self>
  inv true;

int length(node x,node prlnk)
  requires x::dll<prlnk>
  ensures x::dll<prlnk> & res>=0;
{
  if (x==null) return 0;
  else {
     assert x.prev = prlnk;
     return 1+length(x.next,x);
  }
}

/*
# bug-ex10.ss

why is this going into a loop with Omega timeout?

Checking procedure length$node~node...  Timeout after 10. secs
[omega.ml]Timeout when checking sat for 
10. Restarting Omega after ... 74 invocations Stop Omega... 74 invocations Starting Omega.../usr/local/bin/oc
*/
