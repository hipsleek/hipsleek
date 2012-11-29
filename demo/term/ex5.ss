int foo (int n)
/*
	case {
 		n<0 -> requires Loop ensures false; // non-terminating inputs
 		n>=0 -> requires Term[n] ensures res = 2*n;
 	}
*/
// A better specification
	case {
 		n<0 -> requires Loop ensures false; // non-terminating inputs
		n=0 -> requires Term ensures res = 0;
 		n>0 -> requires Term[n] ensures res = 2*n;
 	}

{
 	if (n==0) return 0;
 	else {
		int m;
    m = n-1;
		assert n>m'; //'
    return 2+foo(m);
  }
}

