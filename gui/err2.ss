// case specs

/* representation of a node */
data node {
	int val;
	node next;
}

/* view for a singly linked list */
ll<n> == self = null & n = 0
	or self::node<_, q> * q::ll<n-1>
  inv n >= 0;


//case specs: poscond OK
bool empty(node x)
  requires x::ll<n>
  case {
  n = 0 -> ensures !res;
  n!= 0 -> ensures !res;
  }
{
  if (x == null) 
    return true;
  else 
    return false;
}

//case specs: poscond: ok
bool Own_Above_Threat(int Other_Tracked_Alt, int Own_Tracked_Alt)
case {
   Other_Tracked_Alt < Own_Tracked_Alt ->
      ensures res;
   Other_Tracked_Alt >= Own_Tracked_Alt ->
      ensures !res;
   }
{
    return (Other_Tracked_Alt <= Own_Tracked_Alt);
}

node get_tl(node x)
  requires x::node<_,p> * p::ll<n>
  ensures  p::ll<n> & res=p;

//todo: should include pre which can not prove
 void test1 (node x)
   requires x::ll<n>
   ensures true;
{
  get_tl(x);
}

void test2 (node x)
   requires x=null
   ensures true;
{
  get_tl(x);
}
