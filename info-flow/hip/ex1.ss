pred_prim security<i : int>;

int const_int(int i)
  requires true
  ensures res::security<R> & res=i & R<=0;

int constant1(int p)
  requires true
  ensures res::security<R> & R <= 0;
{
	return const_int(1);
}

int constant2(int p)
  requires true
  ensures res::security<R> & R <= 1;
{
	return const_int(1);
}

int constant5(int p)
  requires p::security<P> & P <= 0
  ensures res::security<R> & R <= 0;
{
	return const_int(1);
}

int constant6(int p)
  requires p::security<P> & P <= 0
  ensures res::security<R> & R <= 1;
{
	return const_int(1);
}

int constant7(int p)
  requires p::security<P> & P <= 1
  ensures res::security<R> & R <= 0;
{
	return const_int(1);
}

int constant8(int p)
  requires p::security<P> & P <= 1
  ensures res::security<R> & R <= 1;
{
	return const_int(1);
}

int id1(int p)
  requires p::security<P> & P <= 0
  ensures res::security<R> & R <= 0;
{
	return p;
}

int id2(int p)
  requires p::security<P> & P <= 0
  ensures res::security<R> & R <= 1;
{
	return p;
}

int id3_(int p)
  requires p::security<P> & P <= 1
  ensures res::security<R> & R <= 0;
{
	return p;
}

int id4(int p)
  requires p::security<P> & P <= 1
  ensures res::security<R> & R <= 1;
{
	return p;
}
