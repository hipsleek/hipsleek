package simple.flip2;

public class Flip {
	
	/* inspired by this example:
	 * http://www.lri.fr/~marche/termination-competition/2006/webform.cgi?command=viewpb&id=TRS.HM.n007.trs
	 * (VAR x y)
(RULES
f(x,y) -> f(x,x)
f(s(x),y) -> f(y,x)
)
(COMMENT
Non-terminating.
)
	 */

	public static void flip(int i, int j) {
		int t = 0;
		while (i > 0 && j > 0) {
			if (i < j) {
				t = i;
				i = j;
				j = t;
			} else {
				if (i > j) {
					j = i;
				} else {
					i--;
				}
			}
		}
	}
}
