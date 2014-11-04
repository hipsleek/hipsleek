/**
 * A loop continously throwing and catching an exception.
 * The exception is thrown before the statement that makes the loop
 * progress, but the exception body contains another statement making the
 * loop progress.
 *
 * All calls terminate.
 *
 * Julia + BinTerm prove that all calls terminate.
 *
 * @author <A HREF="mailto:fausto.spoto@univr.it">Fausto Spoto</A>
 */

public class Exc5 {
    public static void main(String[] args) {
	int i = 0;

	while (i < 20) {
	    i--;

	    try {
		if (i > 10) throw null;
		i += 2;
	    }
	    catch (NullPointerException e) {
		i += 2;
	    }
	}
    }
}