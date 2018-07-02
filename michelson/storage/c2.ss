data Contract {
	int owner;
}

data Storage {
	int timestamp;
	int tez;
	Contract ctr;
}

/*
data Parameter {
}
*/

data Transfer {
	int from;
	int amount;
	int result;
}

global int now;
global int owner;

// Technically this code is inside a class

void code(Storage s, Transfer t)
	requires s::Storage<timestamp,tez,ctr> * t::Transfer<from,amount,0>
	ensures true;
{
	// CDR; DUP; CAR; NOW;
	int timestamp = s.timestamp;
	// CMPLT; IF {FAIL} {};
	if (now < timestamp) { 
		t.result = 0;
		return;
	}
	// DUP; CDR; DUP; CAR; DIP{CDR}; UNIT;
	int tez = s.tez;
	Contract ctr = s.ctr;
	Transfer u = new Transfer(owner,tez,0);
	/* ctr here should be a class with its own code */
	/* ctr.code(t); */
	// PAIR
	t.result = 1;
	return;
}
