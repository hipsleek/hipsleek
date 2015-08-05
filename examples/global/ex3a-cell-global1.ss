data cell {
  int val;
}

global cell kc;
global int n;

void increase()
        requires kc::cell<k>
        ensures kc::cell<k+1> & n'=n+1;
        // writes k,n
{
        int k = kc.val;
	k = k+1;
        kc.val = k;
	n = n+1;
}
