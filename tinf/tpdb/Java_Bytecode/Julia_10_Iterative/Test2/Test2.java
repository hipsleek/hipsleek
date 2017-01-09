public class Test2 {
    public static void main(String[] args) {
	iter(args.length, args.length % 5, args.length % 4);
    }

    private static void iter(int x, int y, int z) {
	while (x + y + 3 * z >= 0) {
	    if (x > y)
		x--;
	    else if (y > z) {
		x++;
		y -= 2;
	    }
	    else if (y <= z) {
		x = add(x, 1);
		y = add(y, 1);
		z = z - 1;
	    }
	}
    }

    private static int add(int v, int w) {
	return v + w;
    }
}
