data account 
	{ 	int number;
		int balance;
	}

class NoCreditException extends __Exc { int s;}
	
void withdraw(account ac, int sum) throws NoCreditException

	requires ac::account<i,b> & b>sum ensures ac::account<i,q>&b=q+sum ;
	requires ac::account<i,b> & b<=sum  ensures ac::account<i,b>*res::NoCreditException<q>&b=q+sum&flow NoCreditException ;
{
	if 
		(ac.balance > sum )
			ac.balance = ac.balance - sum;
	else 
		raise new NoCreditException(ac.balance - sum);
}

int remove10 (account ac1) 
requires ac1::account<n1,v1>& v1>10 ensures ac1::account<n1,v>&v1 = v+10 & res= 1;
requires ac1::account<n1,v1>& v1<=10 ensures ac1::account<n1,v1>& res=0;
{
	try{
		withdraw (ac1, 10);
	} 
	catch (NoCreditException v){ return 0;};
	return 1;
}