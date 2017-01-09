int sum(int n) {
	int s = 0, i = 1;
	while (i <= n) {
		s += i;
		i++;
	}
	return s;
}
