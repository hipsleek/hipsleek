// Transaction data
data Transfer {
        int from;
        int rcv;
        int amount;
        State result;
}

data State {
	int state;
}

status<n> == self::State<0> & n = 0 // Unverified transaction
	or self::State<1> & n = 1 // Successful transaction
	or self::State<-1> & n = -1 // Failed transaction
	inv n >= -1 & n <= 1;

// User info
data User {
	int key;
	int balance;
}

void transfer(ref Transfer t, ref User u1, ref User u2)
	requires t::Transfer<from,rcv,amount,r> * r::State<k> * u1::User<from,n> * u2::User<rcv,m> & amount >= 0
	case {
		k = 0 -> 
			case {
				n >= amount -> ensures t'::Transfer<from,rcv,amount,r> * r::status<1> * u1'::User<from,n-amount> * u2'::User<rcv,m+amount>;
				n < amount -> ensures t'::Transfer<from,rcv,amount,r> * r::status<-1> * u1::User<from,n> * u2::User<rcv,m>;
		k != 0 -> ensures t::Transfer<from,rcv,amount,r> * r::status<k> * u1::User<from,n> * u2::User<rcv,m>;
{
	if (t.result.state == 0){
		if (u1.balance >= t.amount) {
			u1.balance = u1.balance - t.amount;
			u2.balance = u2.balance + t.amount;
			t.result.state = 1;
		}
		else {
			t.result.state = -1;
		}
	}
	return;
}
