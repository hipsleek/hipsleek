/* 
   Inspired by Verifast example at
   verifast-11.12/tutorial_solutions/threads.c

   Description: concurrent threads access a tree in parallel
*/

int rand()
  requires true
  ensures true;

int fac(int x)
  requires true //@value[x]
  ensures true;

data node {
	int val;
	node left;
	node right; 
}

data int2{
  int val;
}

/* view for trees with number of nodes, n is the depth of the tree */
tree<n> == self = null & n = 0 
  or self::node<_, p, q> * p::tree<n-1> * q::tree<n-1>
  inv n >= 0; 


node make_tree(int depth)
  requires true //@value[depth]
  ensures res::tree<depth>;
{
  if (depth==0) {return null;}
  else{
    node l = make_tree(depth-1);
    node r = make_tree(depth-1);
    int v = rand();
    node t = new node(v,l,r);
    //left
    //right
    //value
    return t;
  }
}

//do not care about the value of sum
int tree_compute_sum_facs(node t)
  requires t::tree<n> //& @value[t]
  ensures t::tree<n>;
{
  if (t==null) 
    { return 1;}
  else{
    int leftSum = tree_compute_sum_facs(t.left);
    int rightSum = tree_compute_sum_facs(t.right);
    int f = fac(t.val);
    return leftSum + rightSum + f;
  }
}

//do not care about the value of sum
void summator(node t, ref int sum)
  requires t::tree<n> // & @value[t] & @full[sum]
  ensures t::tree<n>; // & @full[sum];
{
  int tmp = tree_compute_sum_facs(t);
  sum = tmp;
}

//fork a thread, return its id
//do not care about the value of sum
int start_sum_thread(node t, ref int sum)
  requires t::tree<n> //& @value[t] & @full[sum]
  ensures res=id
          and t::tree<n> & @full[sum] & thread = id;
{
  int id;
  id = fork(summator,t,sum);
  return id;
}

//do not care about the value of sum
void join_sum_thread(node t, ref int sum, int id)
  requires @value[t,id]
           and t::tree<n> & @full[sum] & thread = id
  ensures t::tree<n>; // & @full[sum];
{
  join(id);
}

int main()
  requires true
  ensures true;
{
  node tree = make_tree(22);
  int sumLeft,sumRight;
  int id1,id2;
  id1 = start_sum_thread(tree.left,sumLeft);
  id2 = start_sum_thread(tree.right,sumRight);
  join_sum_thread(tree.left,sumLeft,id1);
  join_sum_thread(tree.right,sumRight,id2);
  int f;
  f = fac(tree.val);
  return sumLeft + sumRight + f;
}
