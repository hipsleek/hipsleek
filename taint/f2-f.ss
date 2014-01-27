data intp {
  int val;
}

void main(intp l, intp l2, int h, int h2)
  requires l::intp<v> * l2::intp<v2> & v=v2
  ensures l::intp<v3> * l2::intp<v4> & (v3=v4 | v3!=v4);
{
  if(h == 2) {
    l.val = 0;
  }

  if(h2 == 2) {
    l2.val = 0;
  }
}
