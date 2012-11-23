 
 void rec_f(ref int i)
	case { i>=20 -> requires Term[] ensures true;
		   i<20 -> requires Loop ensures false;
		 }
 {
	if (i<20) {
	    try {
		if (i > 10) raise new __Exc();
		i++;
	    }
	    catch (__Exc e) ;;
	rec_f(i);
	}
 }
 
 void main() 
	requires Loop ensures false;
 {
	int i = 0;
	rec_f (i);
}