/**
 * A loop continously throwing and catching an exception.
 * Since the exception is thrown before the statement that makes the loop
 * progress, that loop diverges.
 *
 * The call to <tt>main()</tt> diverges.
 *
 * Julia + BinTerm cannot prove that the call to <tt>main()</tt> terminates.
 *
 * @author <A HREF="mailto:fausto.spoto@univr.it">Fausto Spoto</A>
 */

public class Exc2 {
    public static void main(String[] args) {
	int i = 0;

	while (i < 20) {
	    try {
		if (i > 10) throw null;
		i++;
	    }
	    catch (NullPointerException e) {
	    }
	}
    }
}