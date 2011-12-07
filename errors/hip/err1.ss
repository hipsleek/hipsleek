

int testme(int index)
requires index >=0 & index <3
 ensures res >=0 & res<3;
{
  int i;
  if (index >= 2) index = 1;
  else index = index +2;

  i = index;
  //dprint;
  return i;
}
