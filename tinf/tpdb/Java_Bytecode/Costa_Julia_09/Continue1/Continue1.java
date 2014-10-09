/**
 * A loop using the <tt>continue</tt> statement.
 *
 * All calls terminate.
 *
 * Julia + BinTerm prove that all calls terminate
 *
 * @author <A HREF="mailto:fausto.spoto@univr.it">Fausto Spoto</A>
 */

public class Continue1 {
    public static void main(String[] args) {
	int i = 0;

	while (i < 20) {
	    i++;
	    if (i <= 10) continue;
	}
    }
}