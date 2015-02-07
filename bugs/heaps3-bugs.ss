/* priority queues */

data node {
  int val;
}


/* function to delete a leaf */
void foo(ref int i)
  requires true
  ensures i'=i+1;//'
{
  i = i+1;
}

void main(node x)
  requires x::node<a>
  ensures x::node<a+1>;
{
  bind x to (v) in
  {
    foo(v);
  }
}




