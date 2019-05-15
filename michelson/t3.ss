// Data types:
data Storage {
	int value;
	int key;
}

data Money {
	int key;
	int amount;
	Money next;
}

user<k,n> == self = null & n = 0
	or self::Money<key = k, amount = a, next = p> * p::user<k, m> & n = m + 1
	inv n >= 0 & a >= 0 & m >= 0;


data Contract {
	int owner;
	Storage store;
}

data Transfer {
	int from;
	Contract to_contract;
	int amount;
}

global Money u1;
global Money u2;
global Contract c;

int update(int value2, int key2)
        requires c::Contract<owner,store> * store::Storage<value,key> & key = key2
        ensures store::Storage<value2,key>;
        requires c::Contract<owner,store> * store::Storage<value,key> & key != key2
        ensures store::Storage<value,key>;
{
        if (c.store.key == key2) {
                c.store.value = value2;
        }
        return 0;
}


void transfer(int from, Contract to_c, int amount) 
	requires u1::Money<from,amount,next> * next::user<from,n>@L * to_c::Contract<own, s>@L * u2::user<own,m> & amount >= 0 & n >= 0 & m >= 0
	ensures u1::Money<from,0,next> * u2'::Money<own,amount,k> * k::user<own,m>;
{
	// Find the user
	if (u1.key == from) {
		if (amount == u1.amount) {
			// Transfer the money
			u2 = new Money(to_c.owner,u1.amount,u2);
			u1.amount = 0;
		}
	}
	return;
}

int get(Transfer y)
	requires to_c::Contract<owner,store>@L * store::Storage<value,key>@L * y::Transfer<from,to_c,amount>  & amount > 1
	ensures res = value;
	requires to_c::Contract<owner,store>@L * store::Storage<value,key>@L * y::Transfer<from,to_c,amount> & amount <= 1
	ensures res = 0;
{
	if (y.amount > 1) {
		return y.to_contract.store.value;
	}
	return 0;
}
