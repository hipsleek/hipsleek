/* test read-write permissions
   f=1.0 => write
   0<f<=1.0 => read
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
void test_write(int2 x)
     requires x::int2(f)<1> & f=1.0
     ensures x::int2(f)<1>;
{
  int i;
  i=x.val;
  x.val = i;
}

//fail
void test_read(int2 x)
     requires x::int2(f)<1> & f=0.5
     ensures x::int2(f)<1>;
{
  int i;
  i=x.val;
  x.val = i;
}


//valid
void test_write2(node2 x)
     requires x::node2(f)<v,l,r> & f=1.0
     ensures x::node2(f)<v,l,r>;
{
  node2 i;
  i=x.left;
  x.left = i;
  i=x.left;
}

//fail
void test_read2(node2 x)
     requires x::node2(f)<v,l,r> & f=0.5
     ensures x::node2(f)<v,l,r>;
{
  node2 i;
  i=x.left;
  x.left = i;
  i=x.left;
}

//valid
void test_write3(node2 x)
     requires x::tree(f)<n> & f=1.0 & n>0
     ensures x::tree(f)<n>;
{
  node2 i;
  i=x.left;
  x.left = i;
  i=x.left;
}


//fail
void test_read3(node2 x)
     requires x::tree(f)<n> & f=0.5 & n>0
     ensures x::tree(f)<n>;
{
  node2 i;
  i=x.left;
  x.left = i;
  i=x.left;
}
