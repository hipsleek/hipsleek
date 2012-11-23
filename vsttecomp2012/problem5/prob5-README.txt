+++++++++++++++++++++++++++++++++++
Problem 5:
+++++++++++++++++++++++++++++++++++

The solution is provided in the file prob5.ss. 
----------------------------------
To run: 
----------------------------------   
./hip prob5.ss -tp z3

+++++++++++++++++++++++++++++++++++
Implementation Task.
+++++++++++++++++++++++++++++++++++
We have implemented an equivalent program to the given
breath-first search algorithm, which returns the length of
the shortest path from one vertex to another. To model
exactly the behavior of the algorithm, the data structure
of set is necessary. Though set is not a primitive type
in our system, the operations on set in this algorithm
is simple, i.e., getting or removing an element
of the sets, so that we can use an array to simulate a set.
In the simulation of set operations using arrays,
an element is in a set if its respective value in the array
is not 0; otherwise, this value is 0. However, by doing like this,
we need an assumption that the used sets have a finite number
of elements.

To facilitate the tasks of implementation and verification,
we model a graph using adjacency matrix i.e., a two-dimensional array 
A where A[i,j] != 0 iff there is a (directed) edge from vertex i to 
vertex j.

Let us fix a convention: We always use 
  +  A      :  adjacency matrix of the input graph
  +  n      :  the number of vertices in the graph
  +  C,V,N  :  array correspondences of sets in the given pseudo-code
  +  source :  the starting vertex
  +  target :  the destination vertex
  +  d      :  distance (correspond to variable d in the given code)

We break the loops in the given pseudo-code into three simpler recursive functions, namely:

- int bfs_loop1(int[,] A, int n, int source, int target,
                int d, int[] V, int[] C)
  This function models exactly the behavior of the outest loop
  of the algorithm i.e., while C is not empty ... endwhile. 
  It returns the shortest distance from source to target (if any), 
  given
   *  set V consisting of vertices reachable within d arcs ; and 
   *  the set C consisting of all vertices with shortest distance d 
      from source.
  Like the given algorithm, this recursive function is initialized 
  with d=0; C={source} and V={source} by the main function bfs.
  
- int bfs_loop2(int[,] A, int n, int source, int target, int d, 
			    ref int[] V, int[] C, ref int[] N, int v)
  This function models the iteration through all vertices v in C
  in correspondence with the action of 
  	"remove a vertex v in C" 
  one by one in the given code. The purpose is to eventually construct
  the "next" set C i.e. the set N consisting of all vertices whose 
  shortest distance from source is d+1. The reference to array N 
  consist of the "partially" constructed set N.
  
  The parameters for this function can be explained as follows:
  +  The set V of vertex such that all vertex x in V is either
        -  reachable within d arcs; or 
        -  reachable in exactly d+1 arcs with the final intermediate
           vertex is limited in the subset of vertices {0,1,...,v-1}.
           This means: there is a path
                x_0 = source, x_1, x_2, ..., x_d, x_{d+1} = x
           with 0 <= x_d < v.

     Here, we make some terminologies: 
        -  for any v, a {v-path from s to t} is either empty or 
           a path from s to t with the last intermediate vertex is 
           in the set {0,1,...,v-1}.
        -  the {v-shortest-distance from s to t} is the length of the
           shortest v-path from s to t.

     One easily observes from these definitions that:
        -  any n-path from s to t is a path from s to t and vice versa
        -  the n-shortest-distance from s to t is the shortest distance
           from s to t

     We shall make use of this observation to define these relations
     formally in our system.
     
  +  The partially constructed set N of vertices with v-shortest
     distance d+1 from source.
  One can see that when v finally reaches n, every element of N is 
  of n-shortest-distance (equivalently, shortest distance) d from 
  source to it.

- void bfs_loop3(int[,] A, int n, int source, int target, int d, 
				 ref int[] V, int[] C, ref int[] N, int v, int w)
  Analogous to earlier functions, this function corresponds to 
  the instruction
            for each w in succ(v) do 
            	... 
            endfor
  in the given pseudocode.

+++++++++++++++++++++++++++++++++++
Solution description:   
+++++++++++++++++++++++++++++++++++
1. Soundness
   We prove the soundness of the algorithm by indicating that the value
   return by bfs is the length of the shorted path from source to dest.
   Obviously, this proof is put under the assumption that there exists
   a path from source to dest.
   
   To start with, let's (A, n) be a graph representation. We define the
   notions concerning v_path, namely
   +  has_bounded_length_v_path(A, n, s, t, d, v)
   +  has_exact_length_v_path(A, n, s, t, d, v)
   +  v_shortest_distance(A, n, s, t, d, v)
   to mean there is a v-path from s to t in the graph of length <= d,
   is exactly d and d is the v-shortest-distance from s to t
   respectively. Also using the observation above, we also have 
   define the original notion (concerning paths) by appealing to 
   the extreme case of v:
   +  has_bounded_length_path(A, n, s, t, d, v) := has_bounded_length_v_path(A, n, s, t, d, n)
   +  has_exact_length_path(A, n, s, t, d) := has_exact_length_v_path(A, n, s, t, d, n)
   +  shortest_distance(A, n, s, t, d) := v_shortest_distance(A, n, s, t, d, n)
   
   These relations can be defined (mutually) recursively, such as
       has_bounded_length_v_path(A, n, s, t, d, v) :=
           d = 0 & s = t
       \/  d > 0 & (exists i : 0 <= i < v &
	       		has_exact_length_v_path(A, n, s, i, d - 1, n) &
	       		A[i,t] != 0)

   The exact definitions of these relations can be referenced in
   our submitted solution. We also defined 'aggregate' relations
   for instance, 
        all_has_shortest_distance(A, n, s, d, C)
   where C is a set to means that for any x in C, 
        shortest_distance(A,n,s,x,d)
   holds. These are 'short-hands' to write our concise specifications.

   Using these specified relations, we can express the invariants of each
   loop in the algorithm by the specification of the respective recursive
   functions. (Loop invariants are pre-conditions of our functions.) 
   These invariants can be informally described above.

   The soundness of the algorithm is proved based on the specified
   invariants and 4 given axioms.
   
   We notice that the returned value (if any) is only given out at
   the point of checking 
	   v == target
   under the assumption v in C. But as C is assumed to be the set of
   all vertices which have shortest-distance d from source, d must
   be the shortest distance from source to target i.e. v. Thus, 
   soundness is ensured.
    
2. Completeness

   For completeness, we only give a 'human' proof.
   
Theorem: If there is no vertex with shortest distance d (C is empty)
         then there is no vertex with shortest distance > d.

Proof: Suppose that there is a vertex v with a shortest path 
               source = x_0, x_1, ..., x_k = v
where k > d. Then x_d must be of shortest distance d. Otherwise, we 
can replace part of the original path, namely
                     x_0, x_1, ..., x_d
with a shorter path from source to x_d and hence, obtain a shorter 
path for x_k. Contradiction!

Theorem: Any reachable vertex from source must have a shortest path.

Proof: Well-ordering principle.

Consequence: If at the point C is empty and V does not contain target,
then target must not be reachable from source.

Proof: Suppose otherwise, then target must have a shortest path of
length <= d. But our invariant says that any vertex in V is reachable 
within d arcs. Thus, target must be in V. Contradiction.
