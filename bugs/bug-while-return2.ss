data node{
  int val;
}

class rexc extends __Exc{}

int main(node x)
requires x::node<a> & a>0
ensures x::node<a> & res=1;
{
 int i=1;
 while (true)
  requires x::node<a> & a>0
  ensures x::node<a>;
  // or x::node<a> & flow _rexc & res=1;
 {
  if (x.val>0){
    return 1;
  }
 }
 dprint;
 return 2;
}