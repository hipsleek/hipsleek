void foo(int@R x)
requires true
ensures x' = x + 2;
{
  x = x + 5;
}

// void foo(int@R x)
// requires true
// ensures x' = x + 2;
// {
//   x = x + 2;
// }

