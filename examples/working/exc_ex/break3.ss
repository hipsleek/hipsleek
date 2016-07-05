class r{}
r t()
requires true
ensures res::r<>;
{
	return new r();
}
