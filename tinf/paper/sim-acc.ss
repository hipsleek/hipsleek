int Ack(int m, int n)
 infer [@term] requires true ensures true;
/*
 case {
  m<0 & n<0 -> requires Loop ensures false;
  m<0 & n=0 -> requires Term[] ensures res=1;
  m<0 & n>0 -> requires Loop ensures false;
  m=0 & n<0 -> requires Term[] ensures res=1;
  m>0 & n<0 -> requires Loop ensures false;
  m>=0 & n>=0 -> requires Term[m,n] ensures res=1;
}
*/
{ 
	if (m==0 || n==0) return 1;
 	else {
		int m1=m-1;
                int n1=n-1;
                int r = Ack(m, n1);
                return Ack(m-1, r);
 	}
}
/*
# sim-acc.ss

	if (m==0 || n==0) return 1;
 	else {
		int m1=m-1;
                int n1=n-1;
                int r = Ack(m, n1);
                return Ack(m-1, r);
 	}

GOT:

Ack:  
case {
  ((m=0 & 1<=n) | (m=0 & n<=(0-1)) | 
  n=0) -> requires emp & Term[3,1]
     ensures emp & res=1; 
  1<=m & 1<=n -> requires emp & Term[3,2,0+(1*m)+(1*
  n)]
     ensures emp & res=1; 
  ((m<=(0-1) & 1<=n) | (m<=(0-1) & n<=(0-1))) -> requires emp & Loop
  { 11:23}[]
     ensures false & false; 
  n<=(0-1) & 1<=m -> requires emp & MayLoop[]
     ensures emp & res=1; 

Expecting:
 case {
  m<0 & n<0 -> requires Loop ensures false;
  m<0 & n=0 -> requires Term[] ensures res=1;
  m<0 & n>0 -> requires Loop ensures false;
  m=0 & n<0 -> requires Term[] ensures res=1;
  m>0 & n<0 -> requires Loop ensures false;
  m>=0 & n>=0 -> requires Term[m,n] ensures res=1;
}


*/

