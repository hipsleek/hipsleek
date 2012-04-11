/*
	COMPLETE TREES
*/

data node2 {
	int val;
	node2 left;
	node2 right;
}
/*
	- complete binary tree:
		- a binary tree in which every level, except possibly the deepest is completely filled;
		- at depth n, the height of the tree, all nodes are as far left as possible.
*/

/* the view that we used:
 	- n is the height
	- nmin is the "minim height"
		- is the length of the shortest path to a leaf (the minimum between the heights for the two children)
		- we used it to make the insertion easier (because in the insertion there are points where we need to
		know if a subtree is perfect or not)
*/
//->memory safety
complete<n, nmin> == self = null & n = 0 & nmin = 0
  or self::node2<_, l, r> * l::complete<n-1, nmin1> * r::complete<n-2, nmin2> & nmin = min(nmin1, nmin2) + 1
  or self::node2<_, l, r> * l::complete<n-1, nmin1> * r::complete<n-1, nmin2> & nmin = min(nmin1, nmin2) + 1
	inv nmin >= 0 & n >= nmin;

complete3<> == self = null
  or self::node2<_, l, r> * l::complete3<> * r::complete3<>
	inv true;

int maxim(int a, int b)
	requires true
	ensures (a < b | res = a) & (a >= b | res = b);
{
	if(a >= b)
		return a;
	else
		return b;
}

int minim(int a, int b)
	requires true
	ensures (a < b | res = b) & (a >= b | res = a);
{
	if(a >= b)
		return b;
	else
		return a;
}

int maxim1(int a, int b)
  infer @post []
	requires true
	ensures true;
{
	if(a >= b)
		return a;
	else
		return b;
}

int minim1(int a, int b)
  infer @post []
	requires true
	ensures true;
{
	if(a >= b)
		return b;
	else
		return a;
}

/* function to count the number of nodes in a tree */
int count(node2 t)
//infer @post []
  requires t::complete3<>
  ensures t::complete3<> & res >= 0;
{
	int cleft, cright;

	if (t == null)
		return 0;
	else
	{
		cleft = count(t.left);
		cright = count(t.right);
		return (1 + cleft + cright);
	}
}

//relation HGT(int a).
int height1(node2 t)
// infer[t,HGT]
  requires t::complete3<>
  ensures t::complete3<> & res>=0;//HGT(res);////res>=0 & res=h
{
	if (t != null)
		return maxim(height1(t.left), height1(t.right)) + 1;
	else return 0;
}

//relation MHGT(int a).
int min_height1(node2 t)
  requires t::complete3<>
  ensures t::complete3<> & res>=0;//res = nmin;
{
	if (t != null)
		return minim(min_height1(t.left), min_height1(t.right)) + 1;
	else return 0;
}

//relation INS1(int a, int b, int c).
//relation INS2(int a, int b, int c).
//relation INS3(int a, int b).
//relation INS(node2 a).
void insert(ref node2 t, int v)
//  infer[INS]
  requires t::complete3<> // there is still place to insert
  ensures t'::complete3<> & t'!=null;
{
	node2 aux;

	if(t == null) {
		t = new node2(v, null, null);
		return;
	}
	else {
      if(min_height1(t.left) < height1(t.left)) {		// there is still space in the left subtree
        aux = t.left;
        insert(aux, v);
        t.left = aux;
        return;
      }
      else {
        if(min_height1(t.right) < height1(t.right)) {	// there is still space in the right subtree
          aux = t.right;
          insert(aux, v);
          t.right = aux;
          return;
        }
        else {
          node2 tmp = t.right;
          if(height1(t.left) == height1(t.right)) { // tree is full - we must start another level
            aux = t.left;
            insert(aux, v);
            t.left = aux;
            return;
          }
          else {
            aux = t.right;
            insert(aux, v);
            t.right = aux;
            return;
          }
        }
      }
	}
}

//relation PEF(int a).
int is_perfect(node2 t)
// infer[PEF]
  requires t::complete3<>
  ensures t::complete3<> & (res=0 | res=1);//PEF(res);//(res=0 | res=1);
{
  if(t == null)
    return 1;
  else
    {
      if(height1(t.left) != height1(t.right))
        return 0;
      else
        {
          if(is_perfect(t.left) == 1)
            return is_perfect(t.right);
          else
            return 0;
		}
	}
}
