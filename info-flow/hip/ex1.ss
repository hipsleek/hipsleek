hip_include 'ex2.ss'

intobj constant1(intobj p)
  requires true
  ensures res::intobj<_, R> & R <= 0;
{
	return const_int(1);
}

intobj constant2(intobj p)
  requires true
  ensures res::intobj<_, R> & R <= 1;
{
	return const_int(1);
}

intobj constant5(intobj p)
  requires p::intobj<_, P> & P <= 0
  ensures res::intobj<_, R> & R <= 0;
{
	return const_int(1);
}

intobj constant6(intobj p)
  requires p::intobj<_, P> & P <= 0
  ensures res::intobj<_, R> & R <= 1;
{
	return const_int(1);
}

intobj constant7(intobj p)
  requires p::intobj<_, P> & P <= 1
  ensures res::intobj<_, R> & R <= 0;
{
	return const_int(1);
}

intobj constant8(intobj p)
  requires p::intobj<_, P> & P <= 1
  ensures res::intobj<_, R> & R <= 1;
{
	return const_int(1);
}

intobj id1(intobj p)
  requires p::intobj<_, P> & P <= 0
  ensures res::intobj<_, R> & R <= 0;
{
	return p;
}

intobj id2(intobj p)
  requires p::intobj<_, P> & P <= 0
  ensures res::intobj<_, R> & R <= 1;
{
	return p;
}

intobj id3_(intobj p)
  requires p::intobj<_, P> & P <= 1
  ensures res::intobj<_, R> & R <= 0;
{
	return p;
}

intobj id4(intobj p)
  requires p::intobj<_, P> & P <= 1
  ensures res::intobj<_, R> & R <= 1;
{
	return p;
}
