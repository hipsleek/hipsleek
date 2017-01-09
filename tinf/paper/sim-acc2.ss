int ranPos ()
 requires Term[]
  ensures res>=0;

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
                int p = ranPos();
                int r = Ack(m, n1);
                return Ack(m-1, r+p);
 	}
}
/*
# sim-acc2.ss

	if (m==0 || n==0) return 1;
 	else {
		int m1=m-1;
                int n1=n-1;
                int r = Ack(m, n1);
                return Ack(m-1, r+ranPos());
 	}

GOT:
Ack:  case {
  ((m=0 & 1<=n) | (m=0 & n<=(0-1)) | 
  n=0) -> requires emp & Term[5,1]
     ensures emp & res=1; 
  ((n<=(0-1) & 1<=m) | (n<=(0-1) & m<=(0-1)) | (1<=n & 
  6<=m)) -> requires emp & MayLoop[]
     ensures emp & res=1; 
  m=5 & 1<=n -> requires emp & Term[5,6,-1+(0*m)+(1*
  n)]
     ensures emp & res=1; 
  m=4 & 1<=n -> requires emp & Term[5,5,-1+(0*m)+(1*
  n)]
     ensures emp & res=1; 
  m=3 & 1<=n -> requires emp & Term[5,4,-1+(0*m)+(1*
  n)]
     ensures emp & res=1; 
  m=2 & 1<=n -> requires emp & Term[5,3,-1+(0*m)+(1*
  n)]
     ensures emp & res=1; 
  m=1 & 1<=n -> requires emp & Term[5,2,-1+(0*m)+(1*
  n)]
     ensures emp & res=1; 
  m<=(0-1) & 1<=n -> requires emp & Loop
  { 24:23}[]
     ensures false & false; 
  }

--infer-lex

Ack:  case {
  ((m=0 & 1<=n) | (m=0 & n<=(0-1)) | n=0) -> 
     requires emp & Term[5,1]
     ensures emp & res=1; 
  1<=m & 1<=n -> 
     requires emp & Term[5,2,0+(1*m)+(0*n),0+(0*m)+(1*n)]
     ensures emp & res=1; 
  ((m<=(0-1) & 1<=n) | (m<=(0-1) & n<=(0-1))) -> 
     requires emp & Loop {24:23}[]
     ensures false & false; 
  n<=(0-1) & 1<=m -> 
     requires emp & MayLoop[]
     ensures emp & res=1; 
  }

Expect
======
 case {
  m<0 & n<0 -> requires Loop ensures false;
  m<0 & n=0 -> requires Term[] ensures res=1;
  m<0 & n>0 -> requires Loop ensures false;
  m=0 & n<0 -> requires Term[] ensures res=1;
  m>0 & n<0 -> requires Loop ensures false;
  m>=0 & n>=0 -> requires Term[m,n] ensures res=1;
}


*/

