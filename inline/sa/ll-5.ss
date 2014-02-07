//#include <stdio.h>
data node {
  int val;
  node next;
}

int main()
 requires true
 ensures  res=0;
{
  node p=new node(0,null);
  int m = p.val;
  return m;
}

