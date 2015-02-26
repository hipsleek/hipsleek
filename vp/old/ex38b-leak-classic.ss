data cell {
  int val;
}

void foo1(cell x)
  requires x::cell<_>
  ensures emp;
{ 
  x = x;
}

void foo2(cell x)
  requires x::cell<_>
  ensures x::cell<_>;
{ 
  x = x;
}


void foo3(cell x)
  infer[@leak]
  requires x::cell<_>
  ensures emp;
{ 
  x = x;
}

void foo4(cell x)
  infer[]
  requires x::cell<_>
  ensures emp;
{ 
  x = x;
}
