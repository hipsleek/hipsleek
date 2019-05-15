data Money {
	int key;
	int amount;
	Money next;
}

user<k,n> == self = null & n = 0
	or self::Money<k,a,p> * p::user<k,m> & n = m + 1
	inv n >= 0 & a >= 0 & m >= 0;

// Transfer should take a key/identifier to a key/identifier and do some lookup in the function for the money object
data Transfer {
	Money from;
	Money receiver;
	int amount;
}

void transfer(Transfer t)
	requires t::Transfer<from,receiver,amount> * from::Money<k1,amount,next> * receiver::user<k2,m> & amount >= 0 & m > 0
	ensures true;
{
	if (t.amount == t.from.amount) {
		t.receiver = new Money(t.receiver.key,t.amount,t.receiver);
		t.from = t.from.next;
	}
}

/*
1. Contract/Storage are not created here because storage type differs across contracts

How it should look like:
data Contract {
	int owner;
	Storage store;
}

Storage should be any data type
*/

// Start of Contract:
