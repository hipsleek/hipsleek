public class NestedLoop {
	public static void main(String[] args) {
		int i, j, z, n;
		n = args.length;
		int[] a = new int[n];
		for(i = 0;i< n-1;i++){
			a[i] = args[i].length();
		}

		for (i = 0; i < n - 1; i++) {
			for (j = i + 1; j < n; j++) {
				if(a[i]< a[j]){
					z = a[i]; a[i] = a[j]; a[j] = z;
				}
			}
		}
		for(i = 0;i< n -1;i++){
		}
	}
}
