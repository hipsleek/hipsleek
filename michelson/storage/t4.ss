data Storage {
	int timestamp;
	int amount;
	int king;
}

data Money {
	int key;
	int amount;
	Money next;
}

user<k,n> == self = null & n = 0
	or self::Money<key = k, amount = a, next = p> * p::user<k,m> & n = m + 1
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

global int now;
global Contract default;

void usurp(int key, Transfer t)
	requires t::Transfer<from, to_contract, amount> * to_contract::Contract<owner, store> * store::Storage<timestamp, amount2, king>
	ensures true;
{
	// Case 1: Time more than 2 week
	if (now >= t.to_contract.store.timestamp) {
		t.to_contract.store.amount = t.amount;
		t.to_contract.store.timestamp = now + 604800;
		t.to_contract.store.king = key;	
	}
	else {
	// Case 2: Time is within 2 weeks
		if (t.amount > t.to_contract.store.amount) {
			int temp = t.to_contract.store.king;
			// Carry out the transfer to previous king
			t.to_contract.store.amount = t.amount;
			t.to_contract.store.timestamp = now + 604800;
			t.to_contract.store.king = key;
		}
	}
	return;
}
