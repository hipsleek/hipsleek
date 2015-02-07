data node{
  int val;
}

class rexc extends __Exc{}

int main(node x)
requires x::node<a> & a>0
ensures x::node<a> & res=1;
{
 int i=1;
 try {
 while (true)
  requires x::node<a> & a>0
  ensures x::node<a> & flow rexc;
 {
  if (x.val>0){
    raise new rexc();
  }
 }
 } catch (__Exc rexc) {
     return 1;
 };
 dprint;
 return 2;
}