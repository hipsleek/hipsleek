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
	inv m >= 0;

// Design for a map
data Item {
	int index;
	int value;
	Item next;
}

imap<n> == self = null & n = 0
	or self::Item<_,_,r> * r::imap<m> & n = m + 1
	inv n >= 0;

data mapVal {
	int option;
	int value;
}

mapVal get(int index, Item from)
	requires from::imap<n>@L & n >= 0
	ensures res::mapVal<0,0> or res::mapVal<1,_>; // What to check?
{
	mapVal result = new mapVal(0,0);
	if (from != null) {
		if (from.index == index) {
			result.option = 1;
			result.value = from.value;
		}
		else {
			result = get(index,from.next);
		}
	}
	return result;
}

Item update(int index, mapVal i, Item from)
	requires from::imap<n> * i::mapVal<option,value> & n >= 0
	ensures true; // What to check?
{
	if (from != null) {
		if (from.index == index) {
			if (i.option == 0) {
				return from.next;
			}
			else {
				from.value = i.value;
				return from;
			}
		}
		else {
			from.next = update(index,i,from.next);
			return from;
		}
	}
	else {
		return from;
	}
}

// System of accounts contract (In this we have map key_hash tez)
data Parameter1 {
	int option; // Represents the or LEFT RIGHT type
	int key; // LEFT
	int key_r;
	int tez;
	int sign; // Signature of tez
}

data Storage1 {
	Item balancemap;
}

void code1(Parameter1 p, ref Storage1 s, ref Transfer t /*, ref User u1, ref User u2*/)
	requires p::Parameter1<option,key,key,tez,sign> * s::Storage1<balancemap> * balancemap::imap<n> * t::Transfer<from,rcv,amount,result> & amount >= 0 & n >= 0
	ensures true;
{
	// LEFT CASE
	if (p.option == 0) {
		// Search for the key in map
		mapVal result = get(p.key,s.balancemap);
		// Cannot find case:
		if (result.option == 0) {
			s.balancemap = new Item(p.key,t.amount,s.balancemap);
			t.result = 1;
		}
		else {
			result.value = result.value + t.amount;
			s.balancemap = update(p.key,result,s.balancemap);
			t.result = 1;
		}
	}
	return;
}

/*
void contract1( INPUT , Transfer t, User u1, User u2)
	requires t::Transfer<from,rcv,amount,result> * u1::User<from,total_u1> * u2::User<rcv,total_u2> & amount >= 0 & total_u1 >= amount & total_u2 >= 0
	ensures true;
{
	// Create Parameter
	Parameter1 p = new Parameter1( INPUT );
	// Run the code
	code1(p,t,u1,u2);
	// Carry out transfer if pass
	if (t.result == 1) {
		transfer(t,u1,u2);
	}
	return;
}
*/
