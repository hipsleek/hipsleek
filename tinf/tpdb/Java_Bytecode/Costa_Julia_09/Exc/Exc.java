/**
 * A loop that might potentially throw a <tt>NullPointerException</tt>
 * because of the instance field access <tt>exc.f</tt>. If that happened,
 * the loop would diverge since the exception handler does not include any
 * progress statement. However, Julia can prove that <tt>exc</tt> is not
 * <tt>null</tt> at the point where <tt>exc.f</tt> is accessed, so that
 * no exception can be thrown there. Hence the loop is proved to terminate.
 *
 * All calls terminate.
 *
 * Julia + BinTerm prove that all calls terminate.
 *
 * Note: without a preliminary nullness analysis, termination could not
 *       be proved.
 *
 * @author <A HREF="mailto:fausto.spoto@univr.it">Fausto Spoto</A>
 */

public class Exc {
    private int f;

    public static void main(String[] args) {
	Exc exc = new Exc();
	int i = 0;

	while (i < 20) {
	    try {
		if (i > 10) exc.f = 5;
		i += 2;
	    }
	    catch (NullPointerException e) {
	    }
	}
    }
}