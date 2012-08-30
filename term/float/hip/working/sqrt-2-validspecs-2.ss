/*
  sqrt examples 
  specification isn't inferred based on the base case
*/

//---- hip ----

float sqrt(float x)
  requires x >= 0.0 & Term
  ensures res = __sqrt(x);      // __sqrt(x) is the built-in function

void foo(float x)
    case
    {
      x >= 1.0      -> requires Term ensures true;
      x < 0         -> requires Term ensures true;
      x = 0         -> requires Loop ensures false;
      0 < x < 1.0   -> requires Term[Seq{-x, (-1.0, 0), -0.9}] ensures true;
    }
{
  if ((0 <= x) && (x < 0.9))
  {
    foo(sqrt(x));
  }
}
