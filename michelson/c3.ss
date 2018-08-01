data Transfer {
	int from;
	int amount;
	int result;
}

void transfer(Transfer t)
        requires t::Transfer<from,amount,1>
        ensures true;
{
        return;
}

// 2 contracts from unit to unit
// Should be a class
data contract1 { 
	int owner; 
}
data contract2 { 
	int owner; 
}
data contract3 { 
	int owner; 
}
global int now;

// class Contract:

global int owner;

data Storage {
	int option; 
	contract1 c1;
	contract2 c2;
	int timestamp;
	contract3 c3;
	int tez;
	int value;
}

/*
data Parameter {
}
*/

global Storage s;

void code(Transfer t)
	requires t::Transfer<from,amount,0> * s::Storage<option,c1,c2,timestamp,c3,tez,value>
	ensures t::Transfer<from,amount,0>;
{
	// CDR
	Storage temp = s;
	// IF_NONE {FAIL} {}
	if (temp.option == 0) {
		t.result = 0;
		return;
	}
	// DUP;CDAAR;NOW;CMPLT;IF {FAIL} {};
	int timestamp = s.timestamp;
	if (now < timestamp) {
		t.result = 0;
		return;
	}
	// DUP;CDADR;DIP{SOME};PUSH tez "1.01";NONE (pair signature int);
	contract3 c3 = s.c3;
	Transfer t1 = new Transfer(owner,1,0);
	// TRANSFER_TOKENS;DIP{IF_NONE{FAIL} {}};
	// c3.package(t1) [WITH THE INPUTS] - should return some value
	int value = 1;
	if (t1.result == 0) {
		t.result = 0;
		return;
	}
	// DIP{DUP;CDDR;DUP;CDR};CMPGT;
	// SWAP;DIP{IF{CAAR}{CADR};
	int tez = s.tez;
	int val = s.value;
	if (value > val) {
		contract1 c1 = s.c1;
		Transfer t2 = new Transfer(owner,tez,0);
		// c1.package(t2)
	}
	else {
		contract2 c2 = s.c2;
		Transfer t2 = new Transfer(owner,tez,0);
		// c2.package(t2)
	}
	// DIP{NONE ....]
	Storage s = new Storage(0,s.c1,s.c2,timestamp,c3,tez,val);
	// CAR;UNIT;TRANSFER_TOKENS;PAIR} (at if loop)
	return;
}

void package(Transfer t)
	requires t::Transfer<from,amount,0> * s::Storage<_,c1,c2,timestamp,c3,tez,value>
	ensures true;
{
	// Should be same throughout
	//code(t); // compute contract
	if (t.result == 1) { 
		transfer(t); 
	}
	return;
}

// End of Contract
