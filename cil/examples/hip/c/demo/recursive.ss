int sum(int nnnn)
  case
  {
    nnnn <= 0 ->  requires true  ensures res = 0;
    nnnn >  0 ->  requires true  ensures res = nnnn;
  }
{
  if (nnnn <= 0)
    return 0;
  else
    return sum(nnnn-1) + 1;
}
