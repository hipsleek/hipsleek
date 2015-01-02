int f(int x)
  infer [@term]
//requires true ensures true;
  case {
    x <= 0 -> requires Term ensures true;
    x > 0 -> requires MayLoop ensures true;
  }
{
  if (x <= 0) return 0;
  else return f(x) + g(x + 1);
}

int g(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x <= 0) return 0;
  else return f(x - 1) + f(x - 2);
}
/*
# mutual-5b1.ss
# case {
    x <= 0 -> requires Term ensures true;
    x > 0 -> requires MayLoop ensures true;
  }

If @term is turned on, can we change MayLoop to
become Loop if user declared false post that can be proven.
This is a spec strengthening that we expect from infer @term.

However, if user declare:
  requires MayLoop ensures true;
I wonder if we should still insert fpost(..),
to help us determine if false can be detected.
This may be a little challenging.

Currently, when we detect:
  requires Loop ensures true;
We insert fpost(..) to try determine false
or failure.

*/
