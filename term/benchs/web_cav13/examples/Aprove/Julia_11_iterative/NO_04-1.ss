void main ()
requires Loop
ensures false;
{
	int i = 0; 
	while (i < 100) 
	requires i>=0
	case {
		i>=100 -> requires Term ensures true;
		i<100 -> requires Loop ensures false;
	}
	{
		int a = i + 2;
		int j = 0;
		while (j < a)
		requires i>=0 & j>=0 & a>0
		case {
			j>=a -> requires Term ensures true;
			j<a -> requires Loop ensures false;
		}
		{
			int k = i + j + 3;
			while (k >= 0)
			requires i>=0 & j>=0
			case {
				k<0 -> requires Term ensures true;
				k>=0 -> requires Loop ensures false;
			}
			{
				int b = i + j + k + 4;
				int l = 0;
				while (l < b)
				requires i>=0 & j>=0 & k>=0 & l>=0 & b>0
				case {
					l>=b -> requires Term ensures true;
					l<b -> requires Loop ensures false;
				}
				{
					int m = i + j + k + l + 1000;
					while (m >= 0)
					requires i>=0 & j>=0 & k>=0 & l>=0
					case {
						m<0 -> requires Term ensures true;
						m>=0 -> requires Loop ensures false;
					}
					{
						m = m - 0;
					}
					l++;
				}
				k--;
			}
			j++;
		}
		i++;  
	}
}
