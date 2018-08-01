// Define some of the Data types:
data Storage {
	int value;
	int key;
}

data Money {
	int key;
	int amount;
}

data Transfer {
	Money from;
	int to_key;
	int amount;
}


// Globally existing Contract:
global Storage x;
global Money m2;
global Money m;

// Update data:
int update(int value2, int key2)
	requires x::Storage<value,key> & key = key2
	ensures x'::Storage<value2,key>;
	requires x::Storage<value,key> & key != key2
	ensures x'::Storage<value,key>;
{
	if (x.key == key2) {
		x.value = value2;
	}
	return 0;
}

// Get data:
int get(Transfer y)
	requires x::Storage<value,key>@L * y::Transfer<m2,key,amount> * m2::Money<key2,balance2> * m::Money<key,balance> & balance2 >= amount & amount > 1
	ensures m2'::Money<key2,balance2-amount> * m'::Money<key,balance+amount> & res = value;
	requires x::Storage<value,key>@L * y::Transfer<m2,key,amount> * m2::Money<key2,balance2> * m::Money<key,balance> & balance2 >= amount & amount <= 1
	ensures m2'::Money<key2,balance2> * m'::Money<key,balance> & res = 0;
{
	if (y.amount > 1) {
		if (y.from.amount >= y.amount) {
			m.amount = y.amount + m.amount;
			m2.amount = m2.amount - y.amount;
			return x.value;
		}
	}
	return 0;
}

/* Questions:
1. New resource created - requires m = null?, representing money as linked list?
2. Contract/function takes in the Transfer rather than the Transfer calling the contract?
3. String
4. CHECK_SIGNATURE function?
*/
