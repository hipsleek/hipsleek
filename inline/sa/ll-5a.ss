//#include <stdio.h>
data node {
  int val;
  node next;
}

int main()
 requires true
 ensures  res=0;
{
  node p=new node();
  int m = p.val;
  return m;
}

