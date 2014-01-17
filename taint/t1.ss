data node {
  int val;
  node next;
}

relation tainted(int x).
relation sanitize(int x).

ll<n> == self=null & n=0
  or self::node<v,q>*q::ll<n-1> & sanitize(v)
     inv n>=0;

unll<n> == self=null & n=0
  or self::node<v,q>*q::unll<n-1> 
     inv n>=0;

     /*
int readS () 
  requires emp
  ensures emp & tainted(res) ;

int cleanse (int xs) 
  requires emp
  ensures emp & sanitize(res) ;

int prop (int xs) 
  requires emp
  ensures  res=xs ;

void writeData (int xs) 
  requires emp & sanitize(xs)
  ensures emp ;

void main()
  requires true
  ensures true;
{
  int x = readS();
  int a = prop(x);
  int b = cleanse(a);
  writeData(b);
}

node szlist(node xs)
  requires xs::unll<n>
  ensures res::ll<n> & res=xs;
{
  if (xs==null) return xs;
  else {
    xs.val = cleanse(xs.val);
    szlist(xs.next);
    return xs;
  }
}
     */
