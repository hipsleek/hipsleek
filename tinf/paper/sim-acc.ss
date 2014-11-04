int ranPos ()
 requires Term[]
  ensures res>=0;

int Ack(int mmm, int n)
infer [@term] requires true ensures true;
/*
 case {
  m<0 & n<0 -> requires Loop ensures false;
  m<0 & n=0 -> requires Term[] ensures res=1;
  m<0 & n>0 -> requires Loop ensures false;
  m=0 & n<0 -> requires Term[] ensures res=1;
  m>0 & n<0 -> requires Loop ensures false;
  m>=0 & n>=0 -> requires Term[m+n] ensures res=1;
}
*/
{ 
	if (mmm==0 || n==0) return 1;
 	else {
		int mmm1=mmm-1;
                int n1=n-1;
                //int p = ranPos();
                int r = Ack(mmm, n1);
                int rr = Ack(mmm-1, r); 
                dprint;
                return rr;
 	}
}

void main()
 infer[@term] requires true
  ensures true;
{
  int t = Ack(-1,6);
}
/*
# sim-acc.ss

 termAssume 
res=v_int_25_1318' & v_int_25_1318'=1 & v_int_25_1473+1=m & 
m!=0 & !(v_boolean_18_1440) & m!=0 & n!=0 & !(v_boolean_18_1441) & n!=0 & 
!(v_bool_18_1319') & !(v_boolean_18_1441) & !(v_boolean_18_1440) & 
!(v_bool_18_1319') & m1_1471+1=m & n1_1472+1=n & 
r_1474=1 & Ackpost_1406(m',n1_1472) & Ackpost_1406(v_int_25_1473,r_1474) 
--> Ackpost_1406(m,n).

Why wasn't information on m' captured in above relational assumption?
Why aren't there two post in this dprint?

 State:(exists v_int_24_1318': emp&r_30'=1 & n1_29'+1=n' & m1_28'+1=m' & !(v_bool_18_1319') & !(v_boolean_18_1440) & !(v_boolean_18_1441) & !(v_bool_18_1319') & n'!=0 & !(v_boolean_18_1441) & n'!=0 & m'!=0 & !(v_boolean_18_1440) & m'=m & n'=n & m'!=0 & v_int_24_1318'+1=m' & rr_31'=1 & Ackpost_1406(v_int_24_1318',r_30')[]&{FLOW,(4,5)=__norm#E})[]

=====================================================

	if (m==0 || n==0) return 1;
 	else {
		int m1=m-1;
                int n1=n-1;
                int r = Ack(m, n1);
                return Ack(m-1, r);
 	}

GOT:


Ack:  case {
  ((m=0 & 1<=n) | (m=0 & n<=(0-1)) | n=0) -> 
     requires emp & Term[3,1]
     ensures emp & res=1; 
  1<=m & 1<=n -> 
     requires emp & Term[3,2,0+(1*m)+(1*n)]
     ensures emp & res=1; 
  ((m<=(0-1) & 1<=n) | (m<=(0-1) & n<=(0-1))) -> 
     requires emp & Loop{ 24:23}[]
     ensures false & false; 
  n<=(0-1) & 1<=m -> 
     requires emp & MayLoop[]
     ensures emp & res=1; 
  }

--infer-lex

Ack:  case {
  ((m=0 & 1<=n) | (m=0 & n<=(0-1)) | n=0) -> 
     requires emp & Term[3,1]
     ensures emp & res=1; 
  1<=m & 1<=n -> 
     requires emp & Term[3,2,0+(1*m)+(1*n)]
     ensures emp & res=1; 
  ((m<=(0-1) & 1<=n) | (m<=(0-1) & n<=(0-1))) -> 
     requires emp & Loop{ 24:23}[]
     ensures false & false; 
  n<=(0-1) & 1<=m -> 
     requires emp & MayLoop[]
     ensures emp & res=1; 
  }

Expecting:
 case {
  m<0 & n<0 -> requires Loop ensures false;
  m<0 & n=0 -> requires Term[] ensures res=1;
  m<0 & n>0 -> requires Loop ensures false;
  m=0 & n<0 -> requires Term[] ensures res=1;
  m>0 & n<0 -> requires Loop ensures false;
  m>=0 & n>=0 -> requires Term[m+n] ensures res=1;
}


*/

