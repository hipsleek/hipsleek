public class Test11 {
    public static void main(String[] args) {
	Random.args = args;

	int x = args.length * 100, y = args.length * 200 / 13;

	while (x + y > 0) {
	    if (Random.random() * Random.random() > 9)
		x--;
	    else
		y--;
	}
    }
}