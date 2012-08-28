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
      x <= 1.0 -> requires Term ensures true;
      x > 1.0  -> requires Term[SeqDec{x, (1.0, +infinity), 1.1}] ensures true;
    }
{
  if (x > 1.1)
  {
    foo(sqrt(x));
  }
}


//---- sleek ----
/*
// 1
checkentail (x <= 1.0) & Term & (x > 1.1) & (x1 = __sqrt(x)) & (x1 <= 1.0)
                      |- Term.

// 2
checkentail (x <= 1.0) & Term & (x > 1.1) & (x1 = __sqrt(x)) & (x1 > 1.0)
                      |- Term[SeqDec{x1, 1.0, 1.1}].
                      
// 3
checkentail (x > 1.0) & Term[SeqDec{x, 1.0, 1.1}] & (x > 1.1) & (x1 = __sqrt(x)) & (x1 <= 1.0)
                      |- Term.

// 4
checkentail (x > 1.0) & Term[SeqDec{x, 1.0, 1.1}] & (x > 1.1) & (x1 = __sqrt(x)) & (x1 > 1.0)
                      |- Term[SeqDec{x1, 1.0, 1.1}].
*/
