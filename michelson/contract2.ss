// Contract that sends 1 tez to anyone that asks for it (Trial of a transaction with a transfer in it)

// Transaction data
data Transfer {
        int from;
        int rcv;
        int amount;
        int result;
}

// This condition did not go through somehow
transfer<from,rcv,amount,n> == self::Transfer<from,rcv,amount,n>
	inv n >= 0 & n <= 2 & amount >= 0;

// Money
data Wallet {
	int owner;
	int balance;
}

pred_prim wallet<k,n> inv n >= 0;

lemma "wallet" self::wallet<k,n> <-> self::Wallet<k,n> & n >= 0;

// These 2 should "technically" be applied
/*
lemma "split" self::wallet<k,n> & n=a+b & a>=0 & b>=0 -> self::wallet<k,a> * self::wallet<k,b>;
lemma "combine" self::wallet<k,a> * self::wallet<k,b> -> self::wallet<k,a+b>;
*/

// For now do the manual split and combine:
void split_wallet(ref User u, int a)
	requires u::User<k,w> * w::wallet<k,n> & a <= n
	ensures u'::User<k,w> * w::wallet<k,a> * w::wallet<k,n-a>;

void join_wallet(ref User u)
	requires u::User<k,w> * w::wallet<k,a> * w::wallet<k,b>
	ensures u'::User<k,w> * w::wallet<k,a+b>;

// User info for now I treat contract as User also
data User {
	int key;
	Wallet w;
}

// User predicate (doesnt work when split combine is used)
user<k,n> == self::User<k,w> * w::wallet<k,n>;

// Transfer function (NEW: sends from user to contract?)
// Here using user<k,n> in predicate does not work
void transfer(ref Transfer t, ref User u1, ref User u2)
	requires t::Transfer<from,rcv,amount,r> * u1::User<from,w> * w::wallet<from,n> * u2::user<rcv,m> & amount >= 0 & n = amount
	case {
		r = 1 -> ensures t'::Transfer<from,rcv,amount,2> * u1'::User<from,w> * w::wallet<from,n-amount> * u2'::user<rcv,m+amount>;
		r != 1 -> ensures t::Transfer<from,rcv,amount,r> * u1::User<from,w> * w::wallet<from,n> * u2::user<rcv,m>;
	}
{
	if (t.result == 1){
		u1.w.balance = 0;
		u2.w.balance = u2.w.balance + t.amount;
		t.result = 2;
	}
	return;
}	

// Contract
/*
unit storage
data Storage {
	STOR_PARAMS
}
*/

data Parameter {
	int key;
}

void code(Parameter p, ref Transfer t, ref User u1, ref User u2)
	requires p::Parameter<from>@L * t::Transfer<from,rcv,amount,0> * u1::User<from,w1> * u2::User<rcv,w2> * w1::wallet<from,n> * w2::wallet<rcv,m>
	case {
		m >= 1 -> ensures t'::Transfer<from,rcv,amount,1> * u1'::User<from,w3> * w3::wallet<from,n1> * u2'::User<rcv,w4> * w4::wallet<rcv,m1> & n1 = n + 1 & m1 = m - 1;
		m < 1 -> ensures t'::Transfer<from,rcv,amount,0> * u1::user<from,n> * u2::user<rcv,m>;
	}
{
	// Create new Transfer variable 
	Transfer t1 = new Transfer(u2.key,p.key,1,0);
	if (u2.w.balance >= 1) {
		t1.result = 1;
		split_wallet(u2,t1.amount);
		transfer(t1,u2,u1);
		join_wallet(u2);
		t.result = 1;
	}
	return;
}

// Parameter & Transfer? have the intention to be gone in the contract: What changes are 1. Storage, 2. User 3. Maybe Transfer?
void contract(Parameter p, Transfer t, ref User u1, ref User u2)
	requires p::Parameter<from> * t::Transfer<from,rcv,amount,result> * u1::user<from,n> * u2::user<rcv,m>
	case {
		n >= amount -> case {
			m >= 1 -> ensures u1'::user<from,n+1-amount> * u2'::user<rcv,m-1+amount>;
			m < 1 -> ensures u1::user<from,n> * u2::user<rcv,m>;
		}
		n < amount -> ensures u1::user<from,n> * u2::user<rcv,m>;
	}
{
        // Run the code
        t.result = 0;
        if (u1.w.balance >= t.amount) {
                code(p,t,u1,u2);
        	// Carry out transfer if pass
        	if (t.result == 1) {
			split_wallet(u1,t.amount);
	                transfer(t,u1,u2);
			join_wallet(u1);
		}
	}
        return;
}

