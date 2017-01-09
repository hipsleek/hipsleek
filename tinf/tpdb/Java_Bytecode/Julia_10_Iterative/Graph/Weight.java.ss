

data Weight
{
double w;
}
 



data Graph
{
Weight[][] adjMat;

int[] pi;

Weight[] d;
}
 void Graph_init(Graph _this)
{
  
  int i = 0;
  while (i < _this.adjMat.length) {
    _this.pi[i] = -1;
    _this.d[i] = null;
    i++;
  }
  
}

void Graph_addEdge(Graph _this, int origin, int end, double weight)
{
  if (0 <= origin && origin < _this.adjMat.length && 0 <= end && end < _this.adjMat.length)
    _this.adjMat[origin][end] = new Weight(weight);
}

void Graph_relax(Graph _this, int u, int v)
{
  Weight W = null;
  if (_this.d[u] != null)
    W = new Weight(_this.d[u]_w + _this.adjMat[u][v]_w);
  if (W != null)
    if (_this.d[v] == null || _this.d[v]_w > W.w) {
      _this.d[v] = W;
      _this.pi[v] = u;
    }
}

void Graph_dijkstra(Graph _this, int origin)
{
  if (0 <= origin && origin < _this.adjMat.length) {
    Graph_init(_this);
    _this.d[origin] = new Weight(0.0);
    boolean[] F = new boolean[_this.adjMat.length];
    
    int i = 0;
    while (i < F.length) {
      F[i] = true;
      i++;
    }
    
    
    int i = 0;
    while (i < _this.adjMat.length) {
      int u;
      
      u = 0;
      while (u < F.length) {
        if (F[u])
          break;
        u++;
      }
      
      
      int v = u + 1;
      while (v < F.length) {
        if (F[v] && _this.d[v] != null && (_this.d[u] == null || _this.d[v]_w < _this.d[u]_w))
          u = v;
        v++;
      }
      
      F[u] = false;
      
      int v = 0;
      while (v < _this.adjMat.length) {
        if (_this.adjMat[u][v] != null)
          Graph_relax(_this, u, v);
        v++;
      }
      
      i++;
    }
    
  }
}

boolean Graph_bellmanFord(Graph _this, int origin)
{
  if (0 <= origin && origin < _this.adjMat.length) {
    Graph_init(_this);
    _this.d[origin] = new Weight(0.0);
    
    int i = 1;
    while (i < _this.adjMat.length) {
      
      int u = 0;
      while (u < _this.adjMat.length) {
        
        int v = 0;
        while (v < _this.adjMat.length) {
          if (_this.adjMat[u][v] != null)
            Graph_relax(_this, u, v);
          v++;
        }
        
        u++;
      }
      
      i++;
    }
    
    
    int u = 0;
    while (u < _this.adjMat.length) {
      
      int v = 0;
      while (v < _this.adjMat.length) {
        if (_this.adjMat[u][v] != null)
          if (_this.d[v] == null && _this.d[u] != null || _this.d[v] != null && _this.d[u] != null && _this.d[v]_w > _this.d[u]_w + _this.adjMat[u][v]_w)
            return false;
        v++;
      }
      
      u++;
    }
    
    return true;
  } else
    return false;
}

Graph Graph_example(String[] args)
{
  int n = args.length;
  Graph G = new Graph(n);
  if (n >= 2) {
    int a = args[n - 2]_length();
    int b = args[n - 1]_length();
    
    int i = 0;
    while (i < n) {
      if (i % 2 == 0) {
        if (i + 1 < n)
          Graph_addEdge(i, i + 1, a);
        if (i >= 2)
          Graph_addEdge(i, i - 2, args[i - 2]_length());
      } else {
        if (i + 1 < n)
          Graph_addEdge(i, i + 1, b);
        if (i + 2 < n)
          Graph_addEdge(i, i + 2, args[i]_length());
      }
      i++;
    }
    
  }
  return G;
}

void Graph_main(String[] args)
{
  Graph G = Graph_example(args);
  
  int u = 0;
  while (u < G.adjMat.length) {
    Graph_dijkstra(u);
    u++;
  }
  
  
  int u = 0;
  while (u < G.adjMat.length) {
    Graph_bellmanFord(u);
    u++;
  }
  
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;