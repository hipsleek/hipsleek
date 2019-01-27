data node{
   int val;
   node next;
}


void update_cell1(node x)
  requires x::node<_,t>
  ensures  x::node<0,t>;
{
 x.val = 0;
}


void update_cell2(ref node x)
  requires x::node<_,t>
  ensures  x'::node<0,t> & x = x'; //x != x'
{
 x.val = 0;
}

void update_cell3(ref node x)
  requires x::node<_,t>
  ensures  x::node<0,t> & x = x'; //x != x'
{
 x.val = 0;
}

// VALID
void replace_cell1(node x,node y)
  requires x::node<_,t> * y::node<_,t>
  ensures  x::node<_,t> * y::node<_,t>;
{
 x = y;
}

// VALID
void replace_cell2(ref node x, node y)
  requires x::node<_,t> * y::node<_,t>
  ensures  x::node<_,t> * y::node<_,t> & y = x'; //& y = x;
{
 x = y;
}

// should FAIL
void replace_cell3(ref node x, node y)
  requires x::node<_,t> * y::node<_,t>
  ensures  x'::node<_,t> * y::node<_,t>;
{
 x = y;
}

// VALID
void replace_cell4(ref node x, ref node y)
  requires x::node<_,t> * y::node<_,t>
  ensures  x::node<_,t> * x'::node<_,t> & y' = x';
{
 x = y;
}

//
void replace_cell5(ref node x, ref node y)
  requires x::node<_,t> * y::node<_,t>
  ensures  x'::node<_,t> & y' = x';
{
 x = y;
}
