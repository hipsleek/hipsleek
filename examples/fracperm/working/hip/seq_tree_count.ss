/* 
 Testing fractional permissions and predicates in sequential settings
*/

/* representation of a node */

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
void count(node2 t, int2 count)
     requires t::tree(0.5)<n> * count::int2(1.0)<m>
     ensures t::tree(0.5)<n> * count::int2(1.0)<n> & n >= 0 ;
{
  int2 cleft = new int2(0);
  int2 cright = new int2(0);
  if (t==null){
    count.val = 0;
  }
  else{
    count(t.left,cleft);
    count(t.right,cright);
    count.val = 1+cleft.val+cright.val;
  }
}

//fail because of insufficient permission to write to count
void count2(node2 t, int2 count)
     requires t::tree(0.5)<n> * count::int2(0.5)<m>
     ensures t::tree(0.5)<n> * count::int2(0.5)<n> & n >= 0 ;
{
  int2 cleft = new int2(0);
  int2 cright = new int2(0);
  if (t==null){
    count.val = 0; //write
  }
  else{
    count2(t.left,cleft);
    count2(t.right,cright);
    count.val = 1+cleft.val+cright.val; //write
  }
}

//fail because loss of permission (0.5 -> 0.4)
void count3(node2 t, int2 count)
     requires t::tree(0.5)<n> * count::int2(0.5)<m>
     ensures t::tree(0.5)<n> * count::int2(0.4)<n> & n >= 0 ;
{
  int2 cleft = new int2(0);
  int2 cright = new int2(0);
  if (t==null){
    count.val = 0;
  }
  else{
    count3(t.left,cleft);
    count3(t.right,cright);
    count.val = 1+cleft.val+cright.val;
  }
}
