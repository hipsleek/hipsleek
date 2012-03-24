/*
   Description: count the number of node in the tree in parallel.
   Using a stack variable for counting
*/

data node2 {
	int val;
	node2 left;
	node2 right; 
}

/* view for trees with number of nodes */
tree<n> == self = null & n = 0 
	or self::node2<_, p, q> * p::tree<n1> * q::tree<n2> & n = 1 + n1 + n2 
	inv n >= 0; 

//valid
//two child thread
void parallelCount2(node2 t, ref int count)
  requires t::tree(f)<n> // & @value[t] & @full[count]
     ensures t::tree(f)<n> & count'=n & n >= 0; // & @full[count]; //'
{
  int cleft=0;
  int cright=0;
  if (t==null){
    count = 0;
  }
  else{
    int id1,id2;
    id1 = fork(parallelCount2,t.left,cleft);
    id2 = fork(parallelCount2,t.right,cright);
    //
    join(id1);
    join(id2);
    count = 1 + cleft + cright;
  }
}
