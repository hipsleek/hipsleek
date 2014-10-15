
ranking r1(int m). // = (m,n).
ranking term_r2(int n). // = (m,n).
int Ack(int m, int n)
  infer @pre [r1]
  requires n>=0 & m>=0 & Term[m,r1(n)]
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

