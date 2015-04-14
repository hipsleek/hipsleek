

bool bool_nd()
requires true
  ensures true;

void foo(int x)
{
  while(x<10){
    if (bool_nd()) break;
    x++;
  }
  assert (x=10);
}
