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

/*
// View for a user
user0<k,n> == self = null & n = 0
        or self::Money<k,a,r> * r::user0<k,m> & n = m+a
        inv n >= 0 & a >= 0;


void transfer(ref Transfer t, ref Money u1, ref Money u2)
        requires t::Transfer<from,rcv,amount,1>@L * u1::user0<from,total_u1> * u2::user0<rcv,total_u2> & amount >= 0 & total_u1 >= amount
        ensures u1'::user0<from,total_u1-amount> * u2'::user0<rcv,total_u2+amount>;
	/*
	requires t::Transfer<from,rcv,amount,1> * u1::Money<from,amount,p> * p::user<from,n> * u2::user<rcv,m> & amount >= 0 & n > 0 & m > 0
	ensures u1'::user<from,n> * u2'::Money<rcv,amount,k> * k::user<rcv,m>;
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
*/

// Data Publishing Contract
data Storage1 {
	int key;
	int nat;
	int value;
}

data Parameter1 {
	int option;
	int sign;
	int value;
	int nat;
}

int code1(Parameter1 p, ref Storage1 s, ref Transfer t)
	requires p::Parameter1<1,sign,value1,nat>@L * s::Storage1<key,nat,value2> * t::Transfer<from,rcv,amount,result> & amount >= 0 & sign = key
	ensures t'::Transfer<from,rcv,amount,1> * s::Storage1<key,m,value1> & res = 0 & m = nat + 1;
	requires p::Parameter1<0,sign,value1,nat>@L * s::Storage1<key,nat2,value2>@L * t::Transfer<from,rcv,amount,result> & amount > 1
	ensures t'::Transfer<from,rcv,amount,1> & res = value2;
{
	if (p.option == 0) { // GET Part
		if (t.amount > 1) {
			t.result = 1;
			return s.value;
		}
		else {
			t.result = 0;
			return 0;
		}
	}
	else { // UPDATE Part
		// CHECK sign of value+nat in parameter corr to key in storage
		// For now treat it as sign == key
		if (p.sign != s.key) {
			t.result = 0;
			return 0;
		}
		else {
			// CHECK nat is same
			if (p.nat != s.nat) {
				t.result = 0;
				return 0;
			}
			else {
				s.nat = s.nat + 1;
				s.value = p.value;
				t.result = 1;
				return 0;
			}
		}
	}
}

void contract1(int option, int sign, int value, int nat, Transfer t, Storage1 s, Money u1, Money u2)
	requires s::Storage1<key,nat2,value2> * t::Transfer<from,rcv,amount,result> * u1::Money<from,amount,p> * p::user<from,n> * u2::user<rcv,m> & n > 0 & m > 0 & amount > 1 & option = 0
	ensures true;
	requires s::Storage1<key,nat2,value2> * t::Transfer<from,rcv,amount,result> * u1::Money<from,amount,p> * p::user<from,n> * u2::user<rcv,m> & n > 0 & m > 0 & amount >= 0 & option = 1 & sign = key & nat = nat2
	ensures true;
{
	// Create Parameter
	Parameter1 p = new Parameter1(option,sign,value,nat);
	// Run the code
	int result = code1(p,s,t);
	// Carry out transfer if pass
	if (t.result == 1) {
		transfer(t,u1,u2);
	}
	return;
}
