class NQueen {

	public static void main(String[] args) {
		int N = Integer.parseInt(args[0]);
		int[] b = new int[N];
		if (nqueens(b))
			printboard(b);
		else
			System.out.println("No solution!");
	}

	private static boolean nqueens(int[] b) {
		return nqueenshelper(b,0);
	}

	private static boolean nqueenshelper(int[] b, int i) {
		if (i == b.length)
			return true;
		for(b[i] = 0; b[i] < b.length; b[i]++) {
			if (issafe(b,i))
				if (nqueenshelper(b,i+1))
					return true;
		}
		return false;
	}

	private static boolean issafe(int[] b, int i) {
		for (int j = 0; j < i; j++) {
			int t = b[i] - b[j];
			int k = i - j;
			// check if queen j attacks queen i
			if (t == 0 || t == k || t == -k)
				return false;
		}
		return true;
	}

	private static void printboard(int[] b) {
		for(int i = 0; i < b.length; i++) {
			String r = "|";
			for(int j = 0; j < b[i]; j++)
				r += ".";
			r += "x";
			for(int j = b[i]+1; j < b.length; j++)
				r += ".";
			r += "|";
			System.out.println(r);
		}
	}

}
