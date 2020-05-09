//Ex8: null pointer dereference inside struct

struct P{
	int *a;
	int *b;
};

struct P foo(){
	struct P n;
	n.a = NULL;
	n.b = 0;
	return n;
}

int main()
{
	struct P tmp = foo();
	int x = *(tmp.a); // NULL
	int y = *(tmp.b); // NULL
	x = x + y;
	y = y + x;
	return 0;
}
