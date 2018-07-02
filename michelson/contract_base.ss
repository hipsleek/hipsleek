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
	requires t::Transfer<from,rcv,amount,r> * u1::User<from,w> * w::wallet<from,amount> * u2::user<rcv,m> & amount >= 0
	case {
		r = 1 -> ensures t'::Transfer<from,rcv,amount,2> * u1'::User<from,w> * w::wallet<from,0> * u2'::user<rcv,m+amount>;
		r != 1 -> ensures t::Transfer<from,rcv,amount,r> * u1::User<from,w> * w::wallet<from,amount> * u2::user<rcv,m>;
	}
{
	if (t.result == 1){
		u1.w.balance = 0;
		u2.w.balance = u2.w.balance + t.amount;
		t.result = 2;
	}
	return;
}	

// List data structure
data Node {
        int val;
        Node next;
}

list<n> == self = null & n = 0
        or self::Node<_,r> * r::list<m> & n = m+1
        inv n >= 0;

Node first(ref Node l)
        requires l::list<n>
        case {
                n = 0 -> ensures l::list<n> & res = null;
                n != 0 -> ensures res::Node<a,null> * l'::list<n-1>;
        }
{
        if (l == null) {
                return null;
        }
        else {
                Node temp = l;
                l = l.next;
                temp.next = null;
                return temp;
        }
}

int size(ref Node l)
        requires l::list<n>@L
        ensures res = n;
{
        if (l == null) {
                return 0;
        }
        else {
                return 1 + size(l.next);
        }
}

// Contract
data Storage {
	STOR_PARAMS
}

data Parameter {
	INPUTS
}

RETURN_TYPE code(Parameter p, ref Storage s, ref Transfer t)
	requires true
	ensures true;
{
	MICHELSON_CODE
}

// Parameter & Transfer? have the intention to be gone in the contract: What changes are 1. Storage, 2. User 3. Maybe Transfer?
void contract(Parameter p, Transfer t, ref Storage s, ref User u1, ref User u2)
	requires true
	ensures true;
{
        // Run the code
        t.result = 0;
        if (u1.w.balance >= t.amount) {
                RETURN_TYPE result = code(p,s,t);
        	// Carry out transfer if pass
        	if (t.result == 1) {
			split_wallet(u1,t.amount);
                	transfer(t,u1,u2);
			join_wallet(u1);
        	}
	}
        return;
}

