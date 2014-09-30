
ranking term_r(int m, int n). // = (m,n).
int Ack(int m, int n)
   infer @pre [term_r]
   requires n>=0 & m>=0 & Term[term_r(m,n)]
   ensures res>0;

{ 
	if (m==0) return n+1;
	else if (n==0) {
		int m1 = m-1;
        //assert m'-m1'>0; //'
        //assert m1'>=0; //'
    return Ack(m1, 1);
  }
 	else {
		int m1=m-1;
   	int n1=n-1;
   	//assert m'=m' & /* n1'>=0 & */ n'-n1'>0; //'
   	int r = Ack(m, n1);
   	//assert m'-m1'>0 /* & m1'>=0 */; //'
   	return Ack(m-1, r);
 	}
}

/*
( 0<=m & 0<=n) -->  (term_r(m,n))>=0, 
   ===> r[1]>=0; r[2]>=0

( n=0 & v=1 & m1=m - 1 & 1<=m) 
  -->  (term_r(m,n))>(term_r(m1,v)), 
( v=m - 1 & 1<=n & 1<=m & 1<=r) 
  -->  (term_r(m,n))>(term_r(v,r)), 
( n1=n - 1 & m'=m & 1<=n & 1<=m) 
  -->  (term_r(m,n))>(term_r(m',n1))]

1: r(m,n)->r(m1,v) [r[1]->r[1]:DEC(1);  r[2]->r[2]:CONST(1)]
2: r(m,n)->r(v,r) [r[1]->r[1]:DEC(1);  r[2]->r[2]:UNKNOWN(>=1)]
3: r(m,n)->r(m',n1) [r[1]->r[1]:NC;  r[2]->r[2]:DEC(1)]
*/

