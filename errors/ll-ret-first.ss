
data node {
	int val;
	node next;
}

int front(node x)
  requires x::node<a,b>
  ensures x::node<a,b> & res=a ;
  // ensures htrue ;
/* --classic fail for this,
   I guess we need to support intuitive
   reasoning at intermediate steps..

  x::node<a,b> |- x::node<c,d>@L -->

*/
{
  return x.val;
}

