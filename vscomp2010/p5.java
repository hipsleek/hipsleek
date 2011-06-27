/**
 Problem 5 in VSComp 2010: Amortized Queue
 @author Vu An Hoa
 @date 24/06/2011
 **/

// linked list
data llist {
	int hd;
	llist tl;
}

// linked list of a particular size
ll<n> == self = null & n = 0
		or self::llist<_,t> * t::ll<n-1> & n >= 1
		inv n >= 0;

int ListLength(llist L)
	requires L::ll<n>@I
	ensures res = n;
{
	if (L == null)
		return 0;
	else
		return 1 + ListLength(L.tl);
}

llist ListReverse(llist L)
	requires L::ll<n>
	ensures res::ll<n>;
{
	if (L == null)
		return null;
	else
		return ListConcat(ListReverse(L.tl),new llist(L.hd,null));
}

llist ListConcat(llist L1, llist L2)
	requires L1::ll<n1> * L2::ll<n2>
	ensures res::ll<n1+n2>;
{
	if (L1 == null)
		return L2;
	else {
		llist temp = ListConcat(L1.tl, L2);
		return new llist(L1.hd,temp);
	}
}

// amortized queue
data aqueue {
	llist front;
	llist rear;
}

// amortized queue predicate
aq<> == self::aqueue<f,r> * f::ll<nf> * r::ll<nr> & nf >= nr;

aqueue QueueCreate(llist f, llist r) 
	requires f::ll<nf> * r::ll<nr>
	ensures res::aq<>;
{
	if (ListLength(r) <= ListLength(f))
		return new aqueue(f,r);
	else
		return new aqueue(ListConcat(f,ListReverse(r)),null);
}

int Front(aqueue q)
	requires q::aq<>@I
	ensures true;
{
	if (q.front != null)
		return q.front.hd;
	else
		return 0;
}

aqueue Tail(aqueue q)
	requires q::aq<>
	ensures res::aq<>;
{
	if (q.front != null)
		return QueueCreate(q.front.tl, q.rear);
	else
		return new aqueue(null,null);
}

aqueue Enqueue(aqueue q, int h)
	requires q::aq<>
	ensures res::aq<>;
{
	return QueueCreate(q.front, new llist(h,q.rear));
}

