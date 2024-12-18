data Transfer {
	int from;
	int rcv;
	int amount;
	int result;
}

data Money {
	int owner;
	int amount;
}

// Data for a user
data User {
	int key;
	int total_amount;
}

/*
Money divide(User u, int amount)
	requires u::User<key,total_amount> & amount <= total_amount & amount >= 0 & total_amount >= 0
	ensures u::User<key,total_amount - amount> * res::Money<key,amount>;
{
	u.total_amount = u.total_amount - amount;
	Money result = new Money(u.key,amount);
	return result;
}

void merge(User u, Money m)
	requires u::User<key,total_amount> * m::Money<owner,amount> & total_amount >= 0 & amount >= 0 & owner = key
	ensures u::User<key,total_amount + amount> * m::Money<owner,0>; // Setting to 0 as a precautionary measure?
{
	u.total_amount = u.total_amount + m.amount;
	m.amount = 0;
	return;
}
*/

// Transfer function (Simpler version)
void transfer(Transfer t, ref User u1, ref User u2)
	requires t::Transfer<from,rcv,amount,1>@L * u1::User<from,total_u1> * u2::User<rcv,total_u2> & amount >= 0 & total_u1 >= amount & total_u2 >= 0
	ensures u1'::User<from,total_u1-amount> * u2'::User<rcv,total_u2+amount>;
{
	u1.total_amount = u1.total_amount - t.amount;
	u2.total_amount = u2.total_amount + t.amount;
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

// Take my money contract
data Parameter1 {
	int key;
}

void code1(Parameter1 p, ref Transfer t, ref User u1, ref User u2)
	requires p::Parameter1<key> * t::Transfer<from,rcv,amount,result> * u1::User<from,total_u1> * u2::User<rcv,total_u2> & amount >= 0 & total_u1 >= 0 & total_u2 >= 0 & key = from 
	case {
		total_u2 >= 1 -> ensures t'::Transfer<from,rcv,amount,1> * u1'::User<from,total_u1+1> * u2'::User<rcv,total_u2-1>;
		total_u2 < 1 -> ensures t'::Transfer<from,rcv,amount,0>;
	}
{
	if (u2.total_amount >= 1) {
		Transfer t1 = new Transfer(t.rcv,p.key,1,1);
		transfer(t1,u2,u1);
		t.result = 1;
		return;
	}
	else {
		t.result = 0;
		return;
	}
}

void contract1(int key, Transfer t, User u1, User u2)
	requires t::Transfer<from,rcv,amount,result> * u1::User<from,total_u1> * u2::User<rcv,total_u2> & amount >= 0 & total_u1 >= amount & total_u2 >= 0 & key = from
	ensures true;
{
	// Create Parameter
	Parameter1 p = new Parameter1(key);
	// Run the code
	code1(p,t,u1,u2);
	// Carry out transfer if pass
	if (t.result == 1) {
		transfer(t,u1,u2);
	}
	return;
}
