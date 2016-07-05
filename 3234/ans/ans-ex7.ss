int Ack(int m, int n) 
case {
  m<0 -> requires Loop 
         ensures false;
  m=0 -> requires Term
         ensures res=n+1;
  m>0 -> case 
          { 
			n<0 -> requires Loop 
                   ensures false;
            n>=0 -> requires Term[m,n] // MayLoop
                    ensures res>0;
          }  
}
{ 
	if (m==0) return n+1;
    else if (n==0) return Ack(m-1,1);
  	else return Ack(m-1, Ack(m,n-1));
}
