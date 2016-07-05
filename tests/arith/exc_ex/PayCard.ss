class CardException extends __Exc{}
class IllegalStateException extends __Exc{}

data PayCard{
    int limit;
    int unsuccessfulOperations;
    int id;
    int balance;}  


PayCard n_PayCard(int l) 
	requires true ensures res::PayCard<l,0,5,0>; 
	{
        PayCard p = new PayCard(100,0,0,0);
		p.balance = 0;
        p.unsuccessfulOperations=0;
        p.limit=l;
		p.id = 5;
		return p;
    }

PayCard	n1_PayCard() 
	requires true ensures res::PayCard<0,0,5,0>; 
	{
        return n_PayCard(0);
    }

	
void addRecord(PayCard pc) throws CardException 
	requires pc::PayCard<a,b,c,t> case {
		t<0  -> ensures pc::PayCard<a,b,c,t> *res::CardException<>& flow CardException;
		t>=0 -> ensures pc::PayCard<a,b,c,t>;}
	{
	if(pc.balance < 0) raise new CardException();
    }
	
void charge(PayCard pc, int amount) throws IllegalStateException
	requires pc::PayCard<l,uo,z,b> case { 
		amount <=0 -> ensures pc::PayCard<x,uo+1,z,b>;
		amount > 0 & b+amount>=l -> ensures pc::PayCard<x,uo+1,z,b>;
		amount > 0 & b+amount<l -> 
			case { 
				b+amount <0 -> ensures pc::PayCard<x,uo,z,b+amount>*res::IllegalStateException<> & flow IllegalStateException;
				b+amount >= 0 -> ensures pc::PayCard<x,uo,z,b+amount>;}}
	{
        if (pc.balance+amount>=pc.limit || amount <= 0) {
            pc.unsuccessfulOperations++;
        } else {
            pc.balance=pc.balance+amount;
			try{
				addRecord(pc);
			}catch(CardException e){
			raise new IllegalStateException();
			};
        }
    }

 int available(PayCard pc) 
	requires pc::PayCard<a,uo,c,b> case {
		uo<=3 -> ensures pc::PayCard<a,uo,c,b> & res=b;
		uo>3 -> ensures pc::PayCard<a,uo,c,b> & res=0;}
	{
	if (pc.unsuccessfulOperations<=3) {
	    return pc.balance;
        }
        return 0;
    }

 int infoCardMsg(PayCard pc) 
	requires pc::PayCard<a,c,d,b> ensures pc::PayCard<a,c,d,b> & res = b ;
	{
	return pc.balance;
    }


