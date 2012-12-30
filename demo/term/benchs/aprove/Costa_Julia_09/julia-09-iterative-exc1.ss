 
 void rec_f(ref int i)
	requires true & Loop ensures false;
 {
	if (true) {
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
