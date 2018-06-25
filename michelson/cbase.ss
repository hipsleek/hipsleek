data Transfer {
	int from;
	int rcv;
	int amount;
	int result;
}

data Money {
	int owner;
	int amount;
	Money next;
}

// View for a user
user<k,n> == self = null & n = 0
	or self::Money<k,a,r> * r::user<k,m> & n = m+1
	inv m >= 0 & a >= 0;

// Transfer function
void transfer(ref Transfer t, ref Money u1, ref Money u2)
	requires t::Transfer<from,rcv,amount,1> * u1::Money<from,amount,p> * p::user<from,n> * u2::user<rcv,m> & amount >= 0 & n > 0 & m > 0
	ensures u1'::user<from,n> * u2'::Money<rcv,amount,k> * k::user<rcv,m>;
	/*
	requires t::Transfer<from,rcv,amount,1> * u1::Money<from1,amount1,p>@L * p::user<from1,n>@L * u2::user<rcv1,m>@L & n > 0 & m > 0
	ensures true;
	*/
{
	if (u1.owner == t.from) {
		if (u2.owner == t.rcv) {
			if (t.amount == u1.amount) {
				u2 = new Money(t.rcv,t.amount,u2);
				u1 = u1.next;
			}
		}
	}
	return;
}

// Design for a list
data Node {
	int val;
	Node next;
}

list<n> == self = null & n = 0
	or self::Node<_,r> * r::list<m> & n = m + 1
	inv n >= 0;

/*
// Contract
data Storage1 {
}

data Parameter1 {
}

int code1(Parameter1 p, ref Storage1 s, ref Transfer t)
	requires true
	ensures true;
{
}

void contract1(INPUT, Transfer t, Storage1 s, Money u1, Money u2)
	requires s::Storage1<> * t::Transfer<from,rcv,amount,result> * u1::Money<from,amount,p> * p::user<from,n> * u2::user<rcv,m> & n > 0 & m > 0 & amount >= 0
	ensures true;
{
	// Create Parameter
	Parameter1 p = new Parameter1();
	// Run the code
	int result = code1();
	// Carry out transfer if pass
	if (t.result == 1) {
		transfer(t,u1,u2);
	}
	return;
}
*/
