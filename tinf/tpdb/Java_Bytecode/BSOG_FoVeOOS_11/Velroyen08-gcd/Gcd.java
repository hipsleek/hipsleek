package simple.gcd;

public class Gcd {

	/* kaputter gcd, inspired by:
	 * http://www.tekpool.com/?p=56
	 * 
	 * int GCD(int a, int b, int& x, int& y)
{
      int prevX, prevY;
      int gcd;

      if(b > a)
      {
      return GCD(b,a,y,x);
      }

      if(b == 0)
      {
            x=1;
            y=0;
            return a;
      }

      gcd = GCD(b, a%b, prevX, prevY);
      x = prevY;
      y = prevX - FLOOR(q/b) * prevY;
      return gcd;
}
	It does not terminate for negative inputs.
	 */
	
	public static int gcd (int a, int b) {
		int t = 0;
		
		// swap:
		if (b > a) {
			t = a;
			a = b;
			b = t;
		}
		
		while (b != 0) {
			t = a-b;
			a = b;
			b = t;
		}
		return a;
	}
}
