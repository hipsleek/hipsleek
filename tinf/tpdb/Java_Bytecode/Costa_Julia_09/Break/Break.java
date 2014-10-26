/**
 * A loop whose termination depends on a <tt>break</tt> statement.
 *
 * All calls terminate.
 *
 * Julia + BinTerm prove that all calls terminate
 *
 * @author <A HREF="mailto:fausto.spoto@univr.it">Fausto Spoto</A>
 */

public class Break {

    public static void main(String[] args) {
	int i = 0;

	while (true) {
	    if (i > 10) break;
	    i++;
	}
    }
}