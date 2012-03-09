// Change each of the MayLoop below to
// either (i) Term[..] or (ii) Loop, so that 
// termination or non-termination property for 
// Ackermann function is completely proven.

int Ack(int m, int n) 
case {
  m<0 -> requires MayLoop 
         ensures false;
  m=0 -> requires MayLoop
         ensures res=n+1;
  m>0 -> case 
          { 
			n<0 -> requires MayLoop 
                   ensures false;
            n>=0 -> requires MayLoop
                    ensures res>0;
          }  
}
{ 
	if (m==0) return n+1;
    else if (n==0) return Ack(m-1,1);
  	else return Ack(m-1, Ack(m,n-1));
}
