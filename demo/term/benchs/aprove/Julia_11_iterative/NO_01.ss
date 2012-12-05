void main () 
requires Loop
ensures false;
{
	int c = 24*60*60/100;
	if (c <= 10) { 
		int i = 0;
		while (i < 100)
		case {
			i>=100 -> requires Term ensures true;
			i<100 -> requires Term[100-i] ensures true;
		}
		{
			i++;
		}
	}
	else {
		if (c <= 50) {
			int i = 0; 
			while (i < 101)
			case {
				i>=101 -> requires Term ensures true;
				i<101 -> requires Term[101-i] ensures true;
			}
			{ i++; }
		}
	  if (c <= 100) {
			int i = 0; 
			while (i < 102)
			case {
				i>=102 -> requires Term ensures true;
				i<102 -> requires Term[102-i] ensures true;
			}
			{ i++; }
		}
	  else {
			int i = 0; 
			while (i < 103)
			case {
				i>=103 -> requires Term ensures true;
				i<103 -> requires Loop ensures false;
			}
			{ i = i + 0; }
		}
	}
}

