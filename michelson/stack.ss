data cell {
	int value;
	cell next;
}

stack<n> == self = null & n = 0
	or self::cell<_,next> * next::stack<m> & n = m + 1 & m >= 0
	inv n >= 0;




