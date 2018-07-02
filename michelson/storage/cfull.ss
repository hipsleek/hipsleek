data Transfer {
	int from;
	int rcv;
	int amount;
	int result;
}

data Money {
	int owner;
	Money next;
}

// List structure
data Node {
	int val;
	Node next;
}

list<n> == self = null & n = 0
	or self::Node<_,r> * r::list<m> & n = m + 1
	inv n >= 0;

// View for a user
user<k,n> == self = null & n = 0
	or self::Money<k,r> * r::user<k,m> & n = m+1
	inv n >= 0;

data User {
	int key;
	int total_amt;
	Money balance;
}

Money takeout(ref Money k)
	requires k::user<from,n> & n > 0
	ensures k'::user<from,n-1> * res::Money<from,null>;
{
	Money temp = k;
	k = k.next;
	temp.next = null;
	return temp;
}

Money append(ref Money k, Money l)
	requires k::user<from,n> * l::Money<from,null>
	ensures res::user<from,n+1>;
{
	l.next = k;
	return l;
}

void trans_amt(Transfer t, int amount, ref Money k, ref Money l)
	requires t::Transfer<from,rcv,amt,result>@L * k::user<from,n> * l::user<rcv,m> & amount >= 0 & n >= amount
	ensures k'::user<from,n-amount> * l'::user<rcv,m+amount>;
{
	if (amount > 0) {
		// Transfer 1 block
		Money temp = takeout(k);
		temp.owner = t.rcv;
		Money temp2 = append(l,temp);
		l = temp2;
		trans_amt(t,amount-1,k,l);
		return;
	}
	else {
		return;
	}
}

void transfer(Transfer t, ref User u1, ref User u2, ref Money k, ref Money l)
        requires t::Transfer<from,rcv,amount,1>@L * u1::User<from,n,k> * u2::User<rcv,m,l> * k::user<from,n> * l::user<rcv,m> & amount >= 0 & n >= amount
        ensures u1::User<from,n-amount,a> * u2::User<rcv,m+amount,b> * a::user<from,n-amount> * b::user<rcv,m+amount>;
{
	// Technically we do some search here
	// Do some check
	/*if (u1.total_amt >= t.amount) { */
		// Do the money transfer
		trans_amt(t,t.amount,k,l);
		// Update
		u1.balance = k;
		u2.balance = l;
		u1.total_amt = u1.total_amt - t.amount;
		u2.total_amt = u2.total_amt + t.amount;
	/*}*/
	return;
}

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

void contract1(int option, int sign, int value, int nat, Transfer t, Storage1 s, User u1, User u2)
	requires s::Storage1<key,nat2,value2> * t::Transfer<from,rcv,amount,result> * u1::User<from,n,p> * p::user<from,n> * u2::User<rcv,m,q> * q::user<rcv,m> & amount > 1 & option = 0 & n >= amount
	ensures true;
	requires s::Storage1<key,nat2,value2> * t::Transfer<from,rcv,amount,result> * u1::User<from,n,p> * p::user<from,n> * u2::User<rcv,m,q> * q::user<rcv,m> & amount >= 0 & option = 1 & sign = key & nat = nat2 & n >= amount
	ensures true;
{
	// Create Parameter
	Parameter1 p = new Parameter1(option,sign,value,nat);
	// Run the code
	int result = code1(p,s,t);
	// Carry out transfer if pass
	if (t.result == 1) {
		transfer(t,u1,u2,u1.balance,u2.balance);
	}
	return;
}

// Reverse Contract
// No Storage
data Parameter2 {
	Node ls;
}

void loop(ref Node temp, ref Node result)
	requires temp::list<n> * result::list<m>
	ensures result'::list<m+n>;
{
	if (temp != null) {
		result = new Node(temp.val,result);
		loop(temp.next,result);
	}
	return;
}

Node code2(Parameter2 p, ref Transfer t)
	requires p::Parameter2<l>@L * l::list<k> * t::Transfer<from,rcv,amount,result> & amount >= 0
	ensures res::list<k> * t'::Transfer<from,rcv,amount,1>;
{
	Node temp = p.ls;
	Node result = null;
	loop(temp,result);
	t.result = 1;
	return result;
}

void contract2(Node ls, Transfer t, User u1, User u2)
	requires ls::list<k> * t::Transfer<from,rcv,amount,0> * u1::User<from,n,p> * p::user<from,n> * u2::User<rcv,m,q> * q::user<rcv,m> & amount >= 0 & n >= amount
	ensures true;
{
	Parameter2 p = new Parameter2(ls);
	Node result = code2(p,t);
	if (t.result == 1) {
		transfer(t,u1,u2,u1.balance,u2.balance);
	}
	return;
}
