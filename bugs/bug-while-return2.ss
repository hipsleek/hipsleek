data node{
  int val;
}

int main(node x)
requires x::node<a> & a>0
ensures x::node<a> & res=1;
{
 int i=1;
 while (true)
  requires x::node<a> & a>0
  ensures x::node<a> & eres=1 & flow __RET;
 {
  if (x.val>0){
    return 1;
  }
 }
 dprint;
 return 2;
}