data str {
  int sanitize; // 1-sanitize; 0 :tainted
  int val;
}


str readS () 
  requires true
  ensures res::str<1,_> ;

str cleanse (str xs) 
  requires xs::str<_,x>@L
  ensures res::str<0,x> ;

str prop (str xs) 
  requires xs::str<_,_>@L
  ensures res=xs ;

void writeData (str xs) 
  requires xs::str<0,_>@L
  ensures true ;

void main()
  requires true
  ensures true;
{
  str x = readS();
  str a = prop(x);
  str b = cleanse(a);
  writeData(a);
}
