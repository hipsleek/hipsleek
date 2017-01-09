/**
 * An example of nested iterations.
 *
 * All calls terminate.
 *
 * Julia + BinTerm prove that all calls terminate
 *
 * @author <A HREF="mailto:fausto.spoto@univr.it">Fausto Spoto</A>
 */

public class Nested {
    public static void main(String[] args) {
	for (int i = 0; i < 10; i++)
	    for (int j = 3; j < 12; j += 2) {
		j -= 1;
	    }
    }
}