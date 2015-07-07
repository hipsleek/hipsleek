data cell {
  int val;
}

global int t;
global cell nc;

void increase_n(int k)
	requires nc::cell<v> & k > 0
        ensures nc::cell<k+v> ;
        // writes n
{
       int n = nc.val;
	n = n+k;
        nc.val = n;
}

void main()
	requires nc::cell<_>
	ensures nc::cell<3> & t'=2 ;
        // writes n,t
{
	int n = 1;
        nc.val = n;
	t = 2;
	increase_n(t);
}

