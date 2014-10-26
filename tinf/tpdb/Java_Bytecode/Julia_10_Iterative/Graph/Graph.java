public class Graph {
    private Weight[][] adjMat;
    private int pi[];   // predecessor for each node
    private Weight d[]; // for each node, an upper bound on the weight of the shortest path
    
    public Graph(int n) {
	this.adjMat = new Weight[n][n];
	this.pi = new int[n];
	this.d  = new Weight[n];
	
	for (int i = 0; i < adjMat.length; i++)
	    for (int j = 0; j < adjMat.length; j++)
		this.adjMat[i][j] = null;
	
	init();
    }
    
    private void init() {
	for (int i = 0; i < adjMat.length; i++) {
	    pi[i] = -1;   // -1 -> nil
	    d[i]  = null; // null -> infinity
	}
    }

    public void addEdge(int origin, int end, double weight) {
	if (0 <= origin && origin < adjMat.length && 0 <= end && end < adjMat.length)
	    adjMat[origin][end] = new Weight(weight);
    }

    public void relax(int u, int v) {
	// must be called with adjMat[u][v] != null
	Weight W = null;
	if (d[u] != null) W = new Weight(d[u].w + adjMat[u][v].w);

	if (W != null)
	    if (d[v] == null || d[v].w > W.w) {
		d[v] = W;
		pi[v] = u;
	    }
    }

    public void dijkstra(int origin) {
 	if (0 <= origin && origin < adjMat.length) {
	    init();
	    d[origin] = new Weight(0.0);

	    boolean F[] = new boolean[adjMat.length];
	    for (int i = 0; i < F.length; i++) F[i] = true;

	    for (int i = 0; i < adjMat.length; i++) {
		// extract the minimim d from F:
		int u;
		for (u = 0; u < F.length; u++) 
		    if (F[u]) break;
		for (int v = u+1; v < F.length; v++)
		    if (F[v] && d[v] != null && (d[u] == null || d[v].w < d[u].w))
			u = v;
		F[u] = false;
		// relax each vertex that is adjacent to u:
		for (int v = 0; v < adjMat.length; v++) 
		    if (adjMat[u][v] != null)
			relax(u, v);
	    }
	}
    }

    public boolean bellmanFord(int origin) {
 	if (0 <= origin && origin < adjMat.length) {
	    init();
	    d[origin] = new Weight(0.0);
	    for (int i = 1; i < adjMat.length; i++)
		for (int u = 0; u < adjMat.length; u++)
		    for (int v = 0; v < adjMat.length; v++)
			if (adjMat[u][v] != null)
			    relax(u, v);
	    for (int u = 0; u < adjMat.length; u++)
		for (int v = 0; v < adjMat.length; v++)
		    if (adjMat[u][v] != null)
			if ( (d[v] == null && d[u] != null) ||
			     (d[v] != null && d[u] != null
			      && d[v].w > d[u].w + adjMat[u][v].w) )
			    return false;
	    return true;
	}
	else return false;
    }

    /*
    public String toString() {
	String result = "";

	for (int i = 0; i < adjMat.length; i++) {
	    for (int j = 0; j < adjMat.length; j++)
		result += adjMat[i][j] + " ";
	    result += "\n";
	}

	return result;
    }
    */

    /*
    public String printPath(int origin, int end) {
	String result = null;

	if (end == origin)
	    result = origin + " ";
	else if (pi[end] == -1)
	    result = "no path from " + origin + " to " + end;
	else result = printPath(origin, pi[end]) + end + " ";

	return result;
    }
    */

    public static Graph example(String args[]) {
	int n = args.length;
	Graph G = new Graph(n);

	if (n >= 2) {
	    int a = args[n-2].length();
	    int b = args[n-1].length();
	    
	    for (int i = 0; i < n; i++)
		if (i % 2 == 0) {
		    if (i+1 < n) G.addEdge(i, i+1, a);
		    if (i >= 2)  G.addEdge(i, i-2, args[i-2].length());
		}
		else {
		    if (i+1 < n) G.addEdge(i, i+1, b);
		    if (i+2 < n) G.addEdge(i, i+2, args[i].length());
		}
	}

	return G;
    }

    public static void main(String args[]) {
	Graph G = example(args);

	/*
	Graph G = new Graph(5);
	G.addEdge(0, 1, 10);
	G.addEdge(0, 3, 5);
	G.addEdge(1, 2, 1);
	G.addEdge(1, 3, 2);
	G.addEdge(2, 4, 4);
	G.addEdge(3, 1, 3);
	G.addEdge(3, 2, 9);
	G.addEdge(3, 4, 2);
	G.addEdge(4, 2, 6);
	G.addEdge(4, 0, 7);
	*/

	// System.out.println(G + "\n");

	// System.out.println("DIJKSTRA:");
	for (int u = 0; u < G.adjMat.length; u++) {
	    G.dijkstra(u);
	    /*
	    for (int i = 0; i < G.adjMat.length; i++)
		if (i != u)
		    System.out.println(u + "->" + i + " : " + G.printPath(u, i) +
				       " -- len = " + G.d[i]);
	    */
	}

	// System.out.println("\nBELLMAN-FORD:");
	for (int u = 0; u < G.adjMat.length; u++)
	    G.bellmanFord(u);
	/*
	    if (G.bellmanFord(u))
		for (int i = 0; i < G.adjMat.length; i++)
		    if (i != u)
			System.out.println(u + "->" + i + " : " + G.printPath(u, i) +
					   " -- len = " + G.d[i]);
	*/
    }
}