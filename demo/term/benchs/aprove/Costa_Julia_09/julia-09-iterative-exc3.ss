 
 void rec_f(ref int i)
	case { i>=20 -> requires Term[] ensures true;
		   i<20 -> requires Term[20-i] ensures true;
		 }
 {
	if (i<20) {
	    try {
		if (i > 10) raise new __Exc();
		i++;
	    }
	    catch (__Exc e) {i++;};
	rec_f(i);
	}
 }
 
 void main() 
	requires Term[] ensures true;
 {
	int i = 0;
	rec_f (i);
}
