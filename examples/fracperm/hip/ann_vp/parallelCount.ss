/*
   Description: count the number of node in the tree in parallel.
   Using a heap location (int2) for counting
*/

data node2 {
	int val;
	node2 left;
	node2 right; 
}

data int2{
  int val;
}

/* view for trees with number of nodes */
tree<n> == self = null & n = 0 
	or self::node2<_, p, q> * p::tree<n1> * q::tree<n2> & n = 1 + n1 + n2 
	inv n >= 0; 


//valid
//one child thread
void seqCount(node2 t, int2 count)
  requires t::tree(f)<n> * count::int2<m> & @value[t,count]
     ensures t::tree(f)<n> * count::int2<n> & n >= 0;
{
  int2 cleft = new int2(0);
  int2 cright = new int2(0);
  if (t==null){
    count.val = 0;
  }
  else{
    seqCount(t.left,cleft);
    seqCount(t.right,cright);
    count.val = 1+cleft.val+cright.val;
  }
}

//valid
//one child thread
void parallelCount(node2 t, int2 count)
  requires t::tree(f)<n> * count::int2<m> & @value[t,count]
     ensures t::tree(f)<n> * count::int2<n> & n >= 0;
{
  int2 cleft = new int2(0);
  int2 cright = new int2(0);
  if (t==null){
    count.val = 0;
  }
  else{
    int id = fork(parallelCount,t.left,cleft);
    parallelCount(t.right,cright);
    join(id);
    count.val = 1+cleft.val+cright.val;
  }
}

//valid
// 2 child threads
void parallelCount2(node2 t, int2 count)
  requires t::tree(f)<n> * count::int2<m> & @value[t,count]
     ensures t::tree(f)<n> * count::int2<n> & n >= 0;
{
  int2 cleft = new int2(0);
  int2 cright = new int2(0);
  if (t==null){
    count.val = 0;
  }
  else{
    int id1, id2; 
    id1 = fork(parallelCount2,t.left,cleft);
    id2 = fork(parallelCount2,t.right,cright);
    join(id1);
    join(id2);
    count.val = 1+cleft.val+cright.val;
  }
}
