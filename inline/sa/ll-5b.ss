//#include <stdio.h>
data node {
  int val;
  node next;
}

int main()
 requires true
 ensures  true;
{
  node p=new node();
  int m = p.val;
  return m;
}

