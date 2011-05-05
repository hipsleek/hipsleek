data node {
	int val1;
	node next1;
	
	int val2;
	node next2;
}

ll1<n>
	== self = null & n = 0
	or self::node<_,_,p,_> * p::ll1<n-1>
	inv n >= 0;

ll2<n>
	== self = null & n = 0
	or self::node<_,_,_,q> * q::ll2<n-1>
	inv n >= 0;

/* How to combine ll1 and ll2 together */
ll<n1,n2>
	== self = null & n1 = 0 & n2 = 0
	/* self may share with the second part of p1 and the first part of p2 */
	/*or self::node<_,_,p1,p2> * (p1::ll<n1-1,_> /\ p2::ll<_,n2-1>)*/
	or (self::node<_,_,p1,_> <*,/\> p1::ll<n1-1,_>) /\ (self::node<_,_,_,p2> </\,*> p2::ll<_,n2-1>)
	inv n1 >= 0 & n2 >= 0;

sll<n,lb,ub>
	== self::node<lb,_@I,null> & lb = ub & n = 1
	or self::node<lb,_@I,q> * q::sll<n-1,lb1,ub> & q != null & lb <= lb1
	inv n >= 1 & lb <= ub;

node insert_last (node x, node p)

requires x::ll<n1, n2> * p::node<_,_,null,null>
ensures res::ll<n1+1, n2+1>;

{
	if (x == null)
		return p;
	else {
		x = aux_insert_last (x, p, 1);
		x = aux_insert_last (x, p, 2);
		return x;
	}
}

node aux_insert_last (node x, node p, int n)

requires x::ll<n1, n2> & x != null
case {
	n = 1 -> ensures res::ll<n1+1, n2>;
	n = 2 -> ensures res::ll<n1, n2+1>;
	otherwise -> ensures res = x;
}

{
	if (n == 1) {
		node p1 = x.next1;
		if (p1 == null)
			x.next1 = p;
		else {
			p1 = aux_insert_last (p1, p, n);
			x.next1 = p1;
		}
	}

	if (n == 2) {
		node p2 = x.next2;
		if (p2 == null)
			x.next2 = p;
		else {
			p2 = aux_insert_last (p2, p, n);
			x.next2 = p2;
		}
	}

	return x;
}

node insert_sorted_list (node x, node p)

requires x::node<_,_,p1,p2> * (p1::sll<n1> /\ p2::sll<n2>) * p::node<_,_,null,null>
ensures res::node<_,_,q1,q2> * (q1::sll<n1+1> /\ q2::sll<n2+1>) & x=res;

{
	if (x == NULL)
		return p;
	else {
		x = aux_dummy_insert_sorted_list (x, p, 1);
		x = aux_dummy_insert_sorted_list (x, p, 2);
		return x;
	}
}

node aux_dummy_insert_sorted_list (node x, node p, int n)

case {
	n = 1 -> requires x::node<_,_,p1,p2@I> * (p1::sll<n1> /\ p2::sll<n2>)
	         ensures x::node<_,_,q1,_> * q1::sll<n1+1> & res=x;
	n = 2 -> requires x::node<_,_,p1@I,p2> * (p1::sll<n1> /\ p2::sll<n2>)
	         ensures x::node<_,_,_,q2> * q2::sll<n2+1> & res=x;
}

{
	if (n == 1) {
		node p1 = x.next1;
		if (p1 == null)
			x.next1 = p;
		else if (p1.val1 > p.val1) {
			p.next1 = p1;
			x.next1 = p;
		} else {
			p1 = aux_dummy_insert_sorted_list (p1, p, n);
			x.next1 = p1;
		}
	}

	if (n == 2) {
		node p2 = x.next2;
		if (p2 == null)
			x.next2 = p;
		else if (p2.val2 > p.val2) {
			p.next2 = p2;
			x.next2 = p;
		} else {
			p2 = aux_dummy_insert_sorted_list (p2, p, n);
			x.next2 = p2;
		}
	}

	return x;
}
