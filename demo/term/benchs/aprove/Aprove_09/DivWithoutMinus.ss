void main () 
requires Term
ensures true;
{
	int x = rand_int();
  int y = rand_int();
  int z = y;
  int r = 0;

  while (z > 0 && (y == 0 || y > 0 && x > 0))
	/*
	case {
		z<=0 -> requires Term ensures true;
		z>0 -> case {
			y>=0 -> case {
				y!=0 -> case {
					x<=0 -> requires Term ensures true;
					x>0 -> case {
						x<y -> requires Term[x] ensures true;
						x>=y -> requires Term[x-r] ensures true;
					}
				}
				y=0 -> case {
					x<=0 -> requires Term ensures true;
					x>0 -> requires Term[x-r] ensures true;
				}
			}
			y<0 -> requires Term ensures true; 
		}
	}
	*/

	case {
		z<=0 -> requires Term ensures true;
		z>0 -> case {
			y>=0 -> case {
				y!=0 -> case {
					x<=0 -> requires Term ensures true;
					x>0 -> case {
						x<y -> requires Term[x] ensures true;
						x>=y -> requires Term[x-y,x] ensures true;
					}
				}
				y=0 -> case {
					x<=0 -> requires Term ensures true;
					x>0 -> requires Term[x-y] ensures true;
				}
			}
			y<0 -> requires Term ensures true; 
		}
	}

	{
		if (y == 0) 
		{
    	r++;
      y = z;
    } else {
      x--;
      y--;
    }
  }
}

int rand_int ()
requires Term
ensures true;

