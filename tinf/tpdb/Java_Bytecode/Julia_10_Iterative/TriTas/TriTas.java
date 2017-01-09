public class TriTas {
    static int N; 
    static int[] a; 
    static int nTas = 0; 

    static void Ajouter(int v) {
	int i,j;
	nTas++; 
	i = nTas - 1; 
	while (i > 0 && a[(i - 1)/2] <= v){
	    a[i] = a[(i - 1)/2]; 
	    j = (i - 1)/2;
	    if (j >= i) break; else i = j;
	}
	a[i] = v;
    }

    static int Maximum() {
	return a[0]; 
    }

    static void Supprimer() {
	int i, j, v;
	a[0] = a[nTas - 1]; 
	nTas--; 
	i = 0; v = a[0];
	while (2 * i + 1 < nTas)
	    {
		j = 2*i + 1; 
		if (j + 1 < nTas)
		    if (a[j + 1] > a[j]) 
			j++;
		if (v >= a[j]) break;
		a[i] = a[j]; 
		i = j;
	    }
	a[i] = v;
    }

    static void HeapSort(){
	int i, v;
	nTas = 0; 
	for (i = 0; i < N; i++)
	    Ajouter(a[i]); 
	for (i = N - 1; i >= 0; i--)
	    { 
		v = Maximum(); 
		Supprimer(); 
		a[i]=v;
	    }
    }

    public static void main(String[] args){
	Random.args = args;
	N = args.length;
	a = new int[N];
	for (int i = 0; i < N; i++)
	    a[i] = Random.random();
	//for (int i = 0; i < N; i++)
	//    System.out.print(a[i]+" ");
	//System.out.println();
	HeapSort();
	//for (int i = 0; i < N; i++)
	//    System.out.print(a[i]+" ");
	//System.out.println();
    }
}