// Transaction data
data Transfer {
        int from;
        int rcv;
        int amount;
        int result;
}

transfer<from,rcv,amount,n> == self::Transfer<from,rcv,amount,n>
	inv n >= 0 & n <= 2 & amount >= 0;

// Money
data wallet {
	int amount;
}

pred_prim Wallet<k,n> inv n >= 0;

lemma "wallet" self::Wallet<k,n> <-> (exists w1: self::User<from,w1> * w1::wallet<n> & n >= 0);

// User info
data User {
	int key;
	Wallet wallet;
}

void transfer(ref Transfer t, ref User u1, ref User u2)
	requires t::transfer<from,rcv,amount,r> * u1::User<from,w1> * u2::User<rcv,w2> * w1::Wallet<n> * w2::Wallet<m>
	case {
		r = 0 -> 
			case {
				n >= amount -> ensures t'::transfer<from,rcv,amount,1> * u1'::User<from,n-amount> * u2'::User<rcv,m+amount>;
				n < amount -> ensures t'::transfer<from,rcv,amount,2> * u1::User<from,n> * u2::User<rcv,m>;
			}
		r != 0 -> ensures t::transfer<from,rcv,amount,r> * u1::User<from,n> * u2::User<rcv,m>;
	}
{
/*
	if (t.result == 0){
		if (u1.balance >= t.amount) {
			u1. = u1.balance - t.amount;
			u2.balance = u2.balance + t.amount;
			t.result = 1;
		}
		else {
			t.result = 2;
		}
	}
*/
	int n = u1.wallet.n;
	return;
}

// Contract
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

/*
int code1(Parameter1 p, ref Storage1 s, ref Transfer t)
        requires p::Parameter1<option,sign,value1,nat>@L * s::Storage1<key,nat2,value2> * t::transfer<from,rcv,amount,0>
        case {
                option!=0 ->
                        case {
                                sign=key & nat=nat2 -> ensures t'::transfer<from,rcv,amount,0> * s'::Storage1<key,m,value1> & res = 0 & m = nat+1;
                                !(sign=key & nat=nat2) -> ensures t'::transfer<from,rcv,amount,2> * s::Storage1<key,nat2,value2> & res = 0;
                        }
                option=0 ->
                        case {
                                amount > 1 -> ensures t'::transfer<from,rcv,amount,0> * s::Storage1<key,nat2,value2> & res = value2;
                                amount <= 1 -> ensures t'::transfer<from,rcv,amount,2> * s::Storage1<key,nat2,value2> & res = 0;
                        }
        }
{
        if (p.option == 0) { // GET Part
                if (t.amount > 1) {
                        return s.value;
                }
                else {
			t.result = 2;
                        return 0;
                }
        }
        else { // UPDATE Part
                // CHECK sign of value+nat in parameter corr to key in storage
                // For now treat it as sign == key
                if (p.sign != s.key) {
			t.result = 2;
                        return 0;
                }
                else {
                        // CHECK nat is same
                        if (p.nat != s.nat) {
				t.result = 2;
                                return 0;
                        }
                        else {
                                s.nat = s.nat + 1;
                                s.value = p.value;
                                return 0;
                        }
                }
        }
}

void contract1(int option, int sign, int value, int nat, Transfer t, ref Storage1 s, ref User u1, ref User u2)
        requires s::Storage1<key,nat2,value2> * t::transfer<from,rcv,amount,result> * u1::User<from,n> * u2::User<rcv,m>
        case {
                option!=0 ->
                        case {
                                sign=key & nat=nat2 ->
                                        case {
                                        	n >= amount -> ensures u1'::User<from,n-amount> * u2'::User<rcv,m+amount> * s'::Storage1<key,nat3,value> & nat3 = nat+1;
                                                n < amount -> ensures u1::User<from,n> * u2::User<rcv,m> * s::Storage1<key,nat2,value2>;
                                        }
                                !(sign=key & nat=nat2) -> ensures s::Storage1<key,nat2,value2> * u1::User<from,n> * u2::User<rcv,m>;
                        }
                option=0 ->
                        case {
                                amount > 1 ->
                                        case {
                                                n >= amount -> ensures u1'::User<from,n-amount> * u2'::User<rcv,m+amount> * s::Storage1<key,nat2,value2>;
                                                n < amount -> ensures u1::User<from,n> * u2::User<rcv,m> * s::Storage1<key,nat2,value2>;
                                        }
                                amount <= 1 -> ensures s::Storage1<key,nat2,value2> * u1::User<from,n> * u2::User<rcv,m>;
                        }
        }
{
	// Create Parameter
        Parameter1 p = new Parameter1(option,sign,value,nat);
        // Run the code
        t.result = 0;
        if (u1.balance >= t.amount) {
                int result = code1(p,s,t);
        }
        // Carry out transfer if pass
        if (t.result == 0) {
                transfer(t,u1,u2);
        }
        return;
}
*/
