/**
 * A loop using the <tt>continue</tt> statement before making the loop
 * progress.
 *
 * The call to <tt>main()</tt> does not terminate.
 *
 * Julia + BinTerm cannot prove that the call to <tt>main()</tt> terminates.
 *
 * @author <A HREF="mailto:fausto.spoto@univr.it">Fausto Spoto</A>
 */

public class Continue {
    public static void main(String[] args) {
	int i = 0;

	while (i < 20) {
	    if (i <= 10) continue;
	    i++;
	}
    }
}