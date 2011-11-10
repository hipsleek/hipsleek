+++++++++++++++++++++++++++++++++++
Problem 5:
+++++++++++++++++++++++++++++++++++

The solution is provided in the file prob5.ss. 
----------------------------------
To run: 
----------------------------------   
./hip prob5.ss -tp auto 

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
is 1; otherwise, this value is 0. However, by doing like this,
we need an assumption that the used sets have a finite number
of elements.

To facilitate the tasks of implementation and verification,
we model a graph by a two-dimensional array and break the loops
in the given pseudo-code into three simpler recursive functions,
which are:

- int bfs_loop1(int[,] A, int n, int source, int target,
                int d, int[] V, int[] C)
  This function models exactly the behavior of the outest loop
  of the algorithm. It returns the shortest distance from source
  to target, given the set V consisting of vertices reachable
  within d arcs; and the set C of vertices with shortest distance
  d from source. Like the given algorithm, this recursive function
  is initialized with d=0; C={source} and V={source} by the main
  function bfs.
  
- int bfs_loop2(int[,] A, int n, int source, int target, int d, 
			    ref int[] V, int[] C, ref int[] N, int v)
  This function constructs the set N of vertices whose shortest
  distance from source is d+1 by traverse all elements of set C
  in turn. The parameters for this function can be explained as
  follows:
  +  The set V of vertex such that all vertex v in V is either
  reachable within d arcs or in exactly d+1 arcs with the final
  intermediate vertex is limited in the set of {0,1,...,v-1} (* TODO *)
  + The partially constructed set N of vertices with shortest
  distance d from source. Each element in the set N has shortest
  distance d+1 if the last intermediate vertex is in {0,1,...,v-1} (* TODO *)

- void bfs_loop3(int[,] A, int n, int source, int target, int d, 
				 ref int[] V, int[] C, ref int[] N, int v, int w)
  This function returns the set N described above. It models exactly
  the behavior of the nestest for-loop of the algorithm. The meanings
  of the parameter C and N are the same as above.

+++++++++++++++++++++++++++++++++++
Solution description:   
+++++++++++++++++++++++++++++++++++
1. Soundness
   We prove the soundness of the algorithm by indicating that the value
   return by bfs is the length of the shorted path from source to dest.
   Obviously, this proof is put under the assumption that there exists
   a path from source to dest.

   The existence of a shortest path from source to dest is described
   by the relation
         shortest_distance(int[,] A, int n, int s, int t, int d)
   that specifies that d is the shortest distance from s to t in the
   graph A with n vertices. This relation is based on two sub-relations
   has_exact_length_path and has_bounded_length_path (* TODO *). A more restrict
   relation of the relation shortest_distance is shortest_distance_via which
   requires the shortest path from source to target must contain a specific
   vertex (* TODO *)

   Using these specified relations, we can express the invariants of each
   loop in the algorithm by the specification of the respective recursive
   functions. These invariants can be informally described that (* TODO *)

   The soundness of the algorithm is proved based on the specified invariants
   and the given axioms. (* TODO *)

2. Completeness
