//This is a good example for case inference

void complxStruc (int i)
requires true
ensures true;
{
	int j = i;
	while (i > 0) 
	requires MayLoop
	ensures true;
	{
		if (i >= j) {
			i--;
			if (j < 5) {
				j++;
				if (i-j > 2) {
					i++;
				} else {
					j++;
				}
			} else {
				j--;
			}
		} else { // i < j
			if (i > 0 && j < 0) { // unreachable 
				i--;
				if (j < -1) {
					j++;
				} else {
					i++;
				}
			} else {
				i++;
				if (j*2 > i) {
					j--;
				} else {
					j++;
				}
			}
		}
	}
}
