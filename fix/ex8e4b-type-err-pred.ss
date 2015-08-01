
data str {
  int val;
  str next;
}


EEE<> == emp inv true;

HHH<> == self::EEE<> 
  or self::str<_,_> inv true;


/*
# ex8e4b.ss

Fixed with a warning and treating "" object as universal.

WARNING: _0:0_0:0:self of EEE cannot have its type determined


*/


