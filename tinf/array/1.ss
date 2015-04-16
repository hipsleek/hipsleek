/*
 * Date: 2014-06-01
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(a[3], b[1+2], a[2+1]) = a[3]
 *
 */

int main() {
	int[10] a;
	while (a[3] >= 0)
          requires true
            ensures a'[3]<0;
        {
               // assert a < 0    
		a[3] = -11;
               // asssert a (a') 
        }
        
	return 0;
}
