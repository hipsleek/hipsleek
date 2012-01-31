data node {
	node next;
}

lseg<p> == self = p
	or self::node<q> * q::lseg<p>;

cll<> == self = null
	or self::lseg<p> * p::node<self>;

pcll<c> == self::lseg<null> & c = 0
	or self::lseg<p> * p::cll<> & c = 1;

bool floyd(node h)
	requires h::pcll<c>
	ensures res & c = 0 or !res & c = 1;
{
	if (h.next == null)
		return false;
	
	
}

bool floyd_helper(node t, node h)
{
	if (h.next == null)
		return false;

	if (t == h)
		return true;
	
	floyd_helper(t.next, h.next.next);
}
