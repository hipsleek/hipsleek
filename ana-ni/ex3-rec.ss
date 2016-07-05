data node {
  int val;
  node next;
}


relation R(node x).
relation P(node x).

bool rand()
   requires true
  ensures true;

int hoo(node x,node y)
  infer [@ana_ni,R,P]
  requires R(x) & P(y)
  ensures true;
{
  int t = x.val;
  if (rand()) return  t;
    else return hoo(y,x);
 }




