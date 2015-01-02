class BubbleSort {
    public static void main(String[] args) {
	sort(new int[100]);
    }

    public static void sort(int[] x) {
	int n = x.length;
	for (int pass=1; pass < n; pass++)  // count how many times
	    // This next loop becomes shorter and shorter
	    for (int i=0; i < n - pass; i++)
		if (x[i] > x[i+1]) {
		    // exchange elements
		    int temp = x[i]; x[i] = x[i+1];  x[i+1] = temp;
		}
    }
}
