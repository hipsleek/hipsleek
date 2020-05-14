class exn extends __Exc{}

int foo1()
  requires true
  ensures res = 1;
{
  try {
    raise new exn();
    return 0;
  }
  catch (__Exc e) {
    return 1;
  };
}