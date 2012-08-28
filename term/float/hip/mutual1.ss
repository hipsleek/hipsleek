void fff(int x)
  case {
    x <= 0 -> requires Term ensures true;
    x > 0  -> requires Term[x,1] ensures true;
  }
{
  if (x > 0) ggg(x);
}

void ggg(int x)
  case {
    x <= 0 -> requires Term ensures true;
    x > 0  -> requires Term[x,0] ensures true;
  }
{
  if (x >0) fff(x-1);
}
