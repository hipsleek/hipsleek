int foo(int n)
 	case {
 		n<0 ->  ensures false; // non-terminating inputs..
 		n>=0 -> variance (1) [n]
		        ensures res= 2*n;
 	}
{
 	if (n==0) return 0;
 	else {
       		return 2+foo(n-1);
      	}
}

