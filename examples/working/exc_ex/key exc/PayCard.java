
data PayCard{
    int limit=1000;
    int unsuccessfulOperations;
    int id;
    int balance=0;}
    


 PayCard n_PayCard(int l) 
	requires true ensures res::PayCard<l,0,5,0>; 
	{
        PayCard p = new PayCard(100,0,0,0);
		p.balance = 0;
        p.unsuccessfulOperations=0;
        p.limit=l;
		p.id = 5;
    }

PayCard	n1_PayCard() 
	requires true ensures res::PayCard<0,0,5,0>; 
	{
        return n_PayCard(0);
    }

void charge(PayCard pc, int amount) {
        if (pc.balance+amount>=pc.limit || amount <= 0) {
            pc.unsuccessfulOperations++;
        } else {
            pc.balance=pc.balance+amount;
	    try{
		log.addRecord(balance);
	    }catch(CardException e){
		throw new IllegalStateException();
	    }
        }
    }

    /*@
      public normal_behavior
       requires true;
       ensures \result == balance || unsuccessfulOperations > 3;
      @*/
    public /*@pure@*/ int available() {
	if (unsuccessfulOperations<=3) {
	    return this.balance;
        }
        return 0;
    }

    public String infoCardMsg() {
	return (" Current balance on card is " + balance);
    }

}
