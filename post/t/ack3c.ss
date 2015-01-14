UTPre@ack fpre(int m,int n).
UTPre@ack fpost(int m,int n).

int ack(int m, int n)
 infer [@term]
 case {
  m<0 -> requires Loop ensures false;
  m>=0 -> 
   case {
    n<0 -> requires MayLoop ensures true;
    n>=0 -> requires fpre(m,n) ensures res>=0 & fpost(m,n);
   }
  }
{ 
	if (m==0) return n+1;
	else if (n==0) {
		int m1 = m-1;
                //assert m'-m1'>0; //'
                //assert m1'>=0; //'
    return ack(m1, 1);
  }
 	else {
		int m1=m-1;
   	int n1=n-1;
   	//assert m'=m' & /* n1'>=0 & */ n'-n1'>0; //'
   	int r = ack(m, n1);
   	//assert m'-m1'>0 /* & m1'>=0 */; //'
   	return ack(m-1, r);
 	}
}
/*
# ack3c.ss

UTPre@ack fpre(int m,int n).
UTPre@ack fpost(int m,int n).

int ack(int m, int n)
 infer [@term]
 case {
  m<0 -> requires Loop ensures false;
  m>=0 -> 
   case {
    n<0 -> requires MayLoop ensures true;
    n>=0 -> requires fpre(m,n) ensures res>=0 & fpost(m,n);
   }
  }


Why did we have error below? Is it due to the presence of
implicit MayLoop?

Context of Verification Failure: 1 File "ack3c.ss",Line:10,Col:36
Last Proving Location: 1 File "ack3c.ss",Line:28,Col:11

ERROR: at _0:0_0:0 
Message: [term.ml][strip_lexvar_lhs]: More than one LexVar to be stripped.
 
Procedure ack$int~int FAIL.(2)

Exception Failure("[term.ml][strip_lexvar_lhs]: More than one LexVar to be stripped.") Occurred!


*/

