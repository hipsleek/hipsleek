// Simple String emulator with sanitization bit
data str {
  int sanitize; // 1-sanitized; 0 :tainted
  int val;
}



// Read String: source --> tainted
str readS () 
  requires true
  ensures  res::str<0,_> ;

// Sanitization Process: remove taint-bit
str cleanse (str xs) 
  requires xs::str<_,x>@L
  ensures  res::str<1,x> ;

// Propagation Function:
//   - doesn't add/remove taint, only propagates
//   - may change data/val
str prop (str xs) 
  requires xs::str<t,_>
  ensures  xs::str<t,_> & res=xs ;

// Sink: data must be sanitized
void writeData (str xs) 
  requires xs::str<1,_>@L // xs is unchanged
  ensures  true ;



// SHOULD FAIL!
void main()
  requires true
  ensures  true;
{
  str x = readS();    // x <- SOURCE
  str a = prop(x);    // a <- x
  str b = cleanse(a); // b <- sanitized(a)
  writeData(a);       // SINK should not accept unsanitized data
}
