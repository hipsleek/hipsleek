//

float pow(float x, int n)
  requires Term[]
  ensures res = __pow(x,n);

void loop(float x, float y)
  case
  {
    y - x*x >= 100 -> requires Term[] ensures true;
    // y - x*x >  100 -> requires Term[Seq{x*x-y@(-infty,-100), y-x*x > 100}] ensures true;
    y - x*x <  100 -> requires Loop ensures false;
  }
{
  if ((y - x*x) < 100)
  {
    float y1 = y*y*y*y + 1000;
    float x1 = x-1;
    loop(x1,y1);
  }
}
