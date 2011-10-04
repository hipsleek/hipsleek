data node {int val; node next;}

barrier bn, 2,  x;  //shared var list


f1(node x, bn b)   
requres x::node<_,q>*q::ll<n> ensures x::ll<n+1>
{
  node t = x;
  t.val = t.val+1;
  t = t.next;
  while (t<>null) 
    requires t::ll<a> ensures t::ll<a>
  {
    t.val = t.val+1;
    t=t.next;
  }
  barrier b; // should i take x::node <_,_> or x::ll<n+1>
}