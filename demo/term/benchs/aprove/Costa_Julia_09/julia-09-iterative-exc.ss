 
 data node {int f;}
 
 void rec_f(ref node n, ref int i)
	case {i<20 -> requires n::node<_> & Term [20-i] ensures true ;
		  i>=20 -> requires Term[] ensures true;
		 }
 {
	if (i<20)
		{
		try {
		if (i > 10) n.f = 5;
		i += 2;
	    }
	    catch (__Exc e) ;
		;
		rec_f(n,i);
		}
 }
 
 void main() 
	requires Term[] ensures true;
 {
	node n = new node(0);
	int i = 0;
	rec_f (n,i);
}