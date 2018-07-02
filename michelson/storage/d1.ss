data Transfer {
	int from;
	int rcv;
	int amount;
	int result;
}

pred_prim Wallet<owner,amount>;

// List structure
data Node {
	int val;
	Node next;
}

list<n> == self = null & n = 0
	or self::Node<_,r> * r::list<m> & n = m + 1
	inv n >= 0;

// View for a user
money<n> == self = null & n = 0
	or self::Coin<r> * r::money<m> & n = m+1
	inv n >= 0;

data User {
	int key;
	Wallet wallet;
}

lemma w::Wallet<k,n> & a+b=n -> w::Wallet<k,a> * w::Wallet<k,b>. 

Coin takeout(ref User k)
	requires k::User<from,w> * w::Coin<nxt> * nxt::money<n>@L & n >= 0
	ensures k'::User<from,nxt> * res::Coin<null>;
{
	Coin temp = k.wallet;
	k.wallet = k.wallet.next;
	temp.next = null;
	return temp;
}

void append(ref User dest, Coin src)
	requires dest::User<rcv,w> * w::money<n>@L * src::Coin<null>
	ensures dest'::User<rcv,w2> * w2::Coin<w>;
{
	src.next = dest.wallet;
	dest.wallet = src;
	return;
}

void trans_amt(int amount, ref User src, ref User dest)
	requires src::User<from,w1> * dest::User<rcv,w2> * w1::money<n> * w2::money<m> & amount >= 0 & n >= amount
	ensures src'::User<from,w3> * dest'::User<rcv,w4> * w3::money<n-amount> * w4::money<m+amount>;
{
	if (amount > 0) {
		// Transfer 1 block
		Coin temp = takeout(src);
		append(dest,temp);
		trans_amt(amount-1,src,dest);
		return;
	}
	else {
		return;
	}
}

int length(Coin u)
	requires u::money<n>@L
	ensures res = n;
{
	if (u == null) {
		return 0;
	}
	else {
		return 1 + length(u.next);
	}
}

void transfer(Transfer t, ref User u1, ref User u2)
	requires t::Transfer<from,rcv,amount,1>@L * u1::User<from,w1> * u2::User<rcv,w2> * w1::money<n> * w2::money<m> & amount >= 0
	case {
		n >= amount -> ensures u1'::User<from,w3> * u2'::User<rcv,w4> * w3::money<n-amount> * w4::money<m+amount>;
		n < amount -> ensures u1::User<from,w1> * u2::User<rcv,w2> * w1::money<n> * w2::money<m>;
	}
{
	// Technically we do some search here
	// Do some check
	if (length(u1.wallet) >= t.amount) {
		// Do the money transfer
		trans_amt(t.amount,u1,u2);
		// Update
	}
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
	requires p::Parameter1<option,sign,value1,nat>@L * s::Storage1<key,nat2,value2> * t::Transfer<from,rcv,amount,result>
	case {
		option!=0 -> 
			case {
				sign=key & nat=nat2 -> ensures t'::Transfer<from,rcv,amount,1> * s'::Storage1<key,m,value1> & res = 0 & m = nat+1;
				!(sign=key & nat=nat2) -> ensures t'::Transfer<from,rcv,amount,0> * s::Storage1<key,nat2,value2> & res = 0;
			}
		option=0 -> 
			case {
				amount > 1 -> ensures t'::Transfer<from,rcv,amount,1> * s::Storage1<key,nat2,value2> & res = value2;
				amount <= 1 -> ensures t'::Transfer<from,rcv,amount,0> * s::Storage1<key,nat2,value2> & res = 0;
			}
	}
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

void contract1(int option, int sign, int value, int nat, Transfer t, ref Storage1 s, ref User u1, ref User u2)
	requires s::Storage1<key,nat2,value2> * t::Transfer<from,rcv,amount,result> * u1::User<from,w1> * w1::money<n> * u2::User<rcv,w2> * w2::money<m> & amount >= 0
	case {
                option!=0 ->
                        case {
                                sign=key & nat=nat2 -> 
					case {
                				n >= amount -> ensures u1'::User<from,w3> * u2'::User<rcv,w4> * w3::money<n-amount> * w4::money<m+amount> * s'::Storage1<key,nat3,value> & nat3 = nat+1;
                				n < amount -> ensures u1::User<from,w1> * u2::User<rcv,w2> * w1::money<n> * w2::money<m> * s::Storage1<key,nat2,value2>;
        				}
                                !(sign=key & nat=nat2) -> ensures s::Storage1<key,nat2,value2> * u1::User<from,w1> * u2::User<rcv,w2> * w1::money<n> * w2::money<m>;
                        }
                option=0 ->
                        case {
                                amount > 1 -> 
					case {
                                                n >= amount -> ensures u1'::User<from,w3> * u2'::User<rcv,w4> * w3::money<n-amount> * w4::money<m+amount> * s::Storage1<key,nat2,value2>;
                                                n < amount -> ensures u1::User<from,w1> * u2::User<rcv,w2> * w1::money<n> * w2::money<m> * s::Storage1<key,nat2,value2>;
                                        }
                                amount <= 1 -> ensures s::Storage1<key,nat2,value2> * u1::User<from,w1> * u2::User<rcv,w2> * w1::money<n> * w2::money<m>;
                        }
        }

{
	// Create Parameter
	Parameter1 p = new Parameter1(option,sign,value,nat);
	// Run the code
	t.result = 0;
	if (length(u1.wallet) >= t.amount) {
		int result = code1(p,s,t);
	}
	// Carry out transfer if pass
	if (t.result == 1) {
		transfer(t,u1,u2);
	}
	return;
}
