// Transaction data
data Transfer {
        int from;
        int rcv;
        int amount;
        int result;
}

// This condition did not go through
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
/*
 checkentail (exists v_int_56_2108',
v_int_56_2107': w_2448::wallet<k_2446,n_2447>@M * 
                w_2479::wallet<k_2477,n_2478>@M * 
                u1'::User<k_2445,w_2448>@M * u2'::User<k_2476,w_2479>@M * 
                t'::Transfer<k_2445,k_2476,v_int_56_2108',v_int_56_2107'>@M&
k_2476=flted_53_2450 & k_2477=flted_53_2450 & n_2478=flted_53_2449 & 
flted_53_2449=100 & flted_53_2450=2 & flted_53_2451=100 & flted_53_2452=1 & 
u2'=u2 & u1'=u1 & n_2447=flted_53_2451 & k_2446=flted_53_2452 & 
k_2445=flted_53_2452 & v_int_56_2108'=20 & v_int_56_2107'=1 & MayLoop[]&
{FLOW,(4,5)=__norm#E}[])
 |-  (exists from_160,amount_161,
rcv_162: t'::Transfer<from,rcv,amount,r>@M * 
         u1'::user<from_160,amount_161>@M * u2'::user<rcv_162,m>@M&
0<=amount & from_160=from & amount_161=amount & rcv_162=rcv&
{FLOW,(4,5)=__norm#E}[]). 
ho_vars: nothing?
res:  failctxfe_kind: MUST
        fe_name: logical bug
        fe_locs: {
    fc_message:  0<=n_2447 & amount=20 & n_2447=100 |-  n_2447=amount. LOCS:[56;53;19;0;34;38] (must-bug)
    fc_current_lhs_flow: {FLOW,(4,5)=__norm#E}
  }
[[ SEARCH ==>  Match(t',t') ==>  SEARCH ==>  Fold ==>  SEARCH ==>  Match(u1',u1') ==>  SEARCH ==>  COND ==>  Match(w_2448,w_2496) ==>  SEARCH ==>  Fold ==>  SEARCH ==>  Match(u2',u2') ==>  SEARCH ==>  COND ==>  Match(w_2479,w_2509)]]false
*/

// For now do the manual split and combine:
void split_wallet(ref User u, int a)
	requires u::User<k,w> * w::wallet<k,n> & a <= n
	ensures u'::User<k,w> * w::wallet<k,a> * w::wallet<k,n-a>;

void join_wallet(ref User u)
	requires u::User<k,w> * w::wallet<k,a> * w::wallet<k,b>
	ensures u'::User<k,w> * w::wallet<k,a+b>;

// User info
data User {
	int key;
	Wallet w;
}

// User predicate
user<k,n> == self::User<k,w> * w::wallet<k,n>;

// Transfer function (NEW: sends from user to contract?)
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

void main(ref User u1, ref User u2)
	requires u1::user<1,100> * u2::user<2,100>
	ensures u1'::user<1,80> * u2'::user<2,120>;
{
	Transfer t = new Transfer(u1.key,u2.key,20,1);
	// Check balance
	if (u1.w.balance >= t.amount){
		split_wallet(u1,t.amount);
		transfer(t,u1,u2);
		join_wallet(u1);
	}
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

int code1(Parameter1 p, ref Storage1 s, ref Transfer t)
        requires p::Parameter1<option,sign,value1,nat>@L * s::Storage1<key,nat2,value2> * t::Transfer<from,rcv,amount,0>
        case {
                option!=0 ->
                        case {
                                sign=key & nat=nat2 -> ensures t'::Transfer<from,rcv,amount,1> * s'::Storage1<key,m,value1> & res = 0 & m = nat+1;
                                !(sign=key & nat=nat2) -> ensures t'::Transfer<from,rcv,amount,(-1)> * s::Storage1<key,nat2,value2> & res = 0;
                        }
                option=0 ->
                        case {
                                amount > 1 -> ensures t'::Transfer<from,rcv,amount,1> * s::Storage1<key,nat2,value2> & res = value2;
                                amount <= 1 -> ensures t'::Transfer<from,rcv,amount,(-1)> * s::Storage1<key,nat2,value2> & res = 0;
                        }
        }
{
        if (p.option == 0) { // GET Part
                if (t.amount > 1) {
			t.result = 1;
                        return s.value;
                }
                else {
			t.result = (-1);
                        return 0;
                }
        }
        else { // UPDATE Part
                // CHECK sign of value+nat in parameter corr to key in storage
                // For now treat it as sign == key
                if (p.sign != s.key) {
			t.result = (-1);
                        return 0;
                }
                else {
                        // CHECK nat is same
                        if (p.nat != s.nat) {
				t.result = (-1);
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
        requires s::Storage1<key,nat2,value2> * t::Transfer<from,rcv,amount,result> * u1::user<from,n> * u2::user<rcv,m>
        case {
                option!=0 ->
                        case {
                                sign=key & nat=nat2 ->
                                        case {
                                        	n >= amount -> ensures u1'::user<from,n-amount> * u2'::user<rcv,m+amount> * s'::Storage1<key,nat3,value> & nat3 = nat+1;
                                                n < amount -> ensures u1::user<from,n> * u2::user<rcv,m> * s::Storage1<key,nat2,value2>;
                                        }
                                !(sign=key & nat=nat2) -> ensures s::Storage1<key,nat2,value2> * u1::user<from,n> * u2::user<rcv,m>;
                        }
                option=0 ->
                        case {
                                amount > 1 ->
                                        case {
                                                n >= amount -> ensures u1'::user<from,n-amount> * u2'::user<rcv,m+amount> * s::Storage1<key,nat2,value2>;
                                                n < amount -> ensures u1::user<from,n> * u2::user<rcv,m> * s::Storage1<key,nat2,value2>;
                                        }
                                amount <= 1 -> ensures s::Storage1<key,nat2,value2> * u1::user<from,n> * u2::user<rcv,m>;
                        }
        }
{
	// Create Parameter
        Parameter1 p = new Parameter1(option,sign,value,nat);
        // Run the code
        t.result = 0;
        if (u1.w.balance >= t.amount) {
                int result = code1(p,s,t);
        }
        // Carry out transfer if pass
        if (t.result == 1) {
		split_wallet(u1,t.amount);
                transfer(t,u1,u2);
		join_wallet(u1);
        }
        return;
}

