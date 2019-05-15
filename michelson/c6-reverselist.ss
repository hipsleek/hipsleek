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
	requires t::Transfer<from,rcv,amount,0> * u1::Money<from1,amount1,p>@L * p::user<from1,n>@L * u2::user<rcv1,m>@L & n > 0 & m > 0
	ensures true;
	*/
{
	if (u1.owner == t.from) {
		if (u2.owner == t.rcv) {
			if (t.result == 1) {
				if (t.amount == u1.amount) {
					u2 = new Money(t.rcv,t.amount,u2);
					u1 = u1.next;
				}
			}
		}
	}
	return;
}

// Reverse Contract
// No Storage

data Node {
	int val;
	Node next;
}

ll<n> == self = null & n = 0
	or self::Node<_,r> * r::ll<m> & n = m + 1
	inv n >= 0;

data Parameter1 {
	Node ls;
}

void loop(ref Node temp, ref Node result) 
	requires temp::ll<n> * result::ll<m> & m >= 0 & n >= 0
	ensures result'::ll<m+n>;
{
	if (temp != null) {
		result = new Node(temp.val,result);
		loop(temp.next,result);
	}
	return;
}

Node code1(Parameter1 p, ref Transfer t)
	requires p::Parameter1<l> * l::ll<k> * t::Transfer<from,rcv,amount,result> & amount >= 0 & k >= 0
	ensures res::ll<n> * t'::Transfer<from,rcv,amount,1>;
{	
	Node temp = p.ls;
	Node result = null;
	loop(temp,result);
	t.result = 1;
	return result;		
}

void contract1(Node ls, ref Transfer t, ref Money u1, ref Money u2)
	requires ls::ll<k> * t::Transfer<from,rcv,amount,0> * u1::Money<from,amount,p> * p::user<from,n> * u2::user<rcv,m> & n > 0 & m > 0 & amount >= 0 & k >= 0
	ensures true;
{
	// Create Parameter
	Parameter1 p = new Parameter1(ls);
	// Run the code
	Node result = code1(p,t);
	// Carry out transfer if pass
	transfer(t,u1,u2);
	return;
}
