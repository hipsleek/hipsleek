int main()
{
  int a = 3;
  int b = 4;
  if (a > 2)
  {
    if ( b > 3) {
      return a;
    }
    else
      goto __Label;
  }
  else {
  __Label:
    a = 2;
    return a;
  }
}


=================

int main()
{
  int a = 3;
  int b = 4;
  try {
  if (a > 2)
  {
    if ( b > 3) {
      return a;
    }
    else
      throw __Label;
    // goto __Label;
    
  }
  else {
    throw Label;
    __//Label:
      //a = 2;
      //return a;
  }
  } catch __Label {
    a = 2;
    return a;
  }
}
