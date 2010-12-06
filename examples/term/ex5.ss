int foo(int n)
 	case {
 		n<0 -> requires [xx] xx=0 ensures false; // non-terminating inputs..
 		n>=0 -> requires [xx] xx=1 ensures res= 2*n;
 	}
	// variance n
{
 	if (n==0) return 0;
 	else {
       		int m;
       		m=n-1;
       		assert n>m'; //'
       		assert xx!=1 or n>=0; //'
       		return 2+foo(m);
      	}
}

