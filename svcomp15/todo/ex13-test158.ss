
data char_n {int val;}

data str {
  char_n c_1;
  int p1;
  int p2;
}

bool nondet_int()
  requires true ensures true;

str free1(str x)
  requires x::str<_,_,_> ensures res=null;

int main()
{
    // alloc 37B on heap
  str datap = new str(null, 0, 0);

    // this should be fine
    if(nondet_int()) {
      datap.p2 = 20;
    } else {
      datap.p2 = 30;
    }
    
    if(20 > datap.p2) {
       // this introduces a memleak, but dead branch
       datap.c_1.val = 0;
    }

    // valid free()
    free1(datap);

    return 0;
}
