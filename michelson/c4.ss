data Transfer {
	int from;
	int rcv;
	int amount;
	bool result;
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
void transfer(Transfer t, Money u1, Money u2)
	requires t::Transfer<from,rcv,a,false> * u1::Money<from,a,p>@L * p::user<from,n>@L * u2::user<rcv,m>@L & amount >= 0 & m > 0
        ensures true;
	/*requires t::Transfer<from,rcv,a,true> * u1::Money<from,a,p> * p::user<from,n> * u2::user<rcv,m> & amount >= 0 & m > 0 & n > 0
        ensures u1'::user<from,n> * u2'::Money<rcv,a,k> * k::user<rcv,m>;*/
{
	dprint;
	if (u1.owner == t.from) {
		dprint;
		if (u2.owner == t.rcv) {
			dprint;
			if (t.result) { // If the contract evaluates properly, carry out the transfer
				dprint;
				if (t.amount == u1.amount) {
					u2 = new Money(t.rcv,t.amount,u2);
					u1 = u1.next;
				}
			}
		}
	}
        dprint;
	return;
}

// Our first contract:
// Data publishing
data Storage1 {
	int key;
	int nat; // Keeps track of order
	int value;
}

data Parameter1 {
	bool option;
	int signature;
	int value;
	int nat;
}

global Storage1 s1;

int code1(Parameter1 p, Transfer t)
	requires t::Transfer<from,rcv,amount,_> * p::Parameter1<true,sign,val,nat> * s1::Storage1<key,nat,value> & sign = key
	ensures s1::Storage1<key,nat+1,val> & res = 0;
{
	if (!(p.option)) { // GET Part
		if (t.amount <= 1) {
			t.result = false;
			return 0;
		}
		t.result = true;
		return s1.value;
	}
	else { // UPDATE Part
		// CHECK_SIGNATURE
		if (s1.nat != p.nat) {
			t.result = false;
			return 0;
		}
		if (s1.key != p.signature) { //HASH
			t.result = false;
			return 0;
		}
		else {
			s1.nat = s1.nat + 1;
			s1.value = p.value;
			t.result = true;
			return 0;
		}
	}
}
