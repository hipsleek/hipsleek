
relation tainted(int x).
relation sanitize(int x).

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
