

data Kernel68
{
Kernel68 next;
}
 void Kernel68_main(String[] args)
{
  int random1 = args[0]_length();
  int random2 = args[1]_length();
  Kernel68_slide68(random1, random2);
}

Kernel68 Kernel68_create(int x)
{
  Kernel68 last;
  Kernel68 current;
  last = current = new Kernel68(null);
  while (--x > 0)
    current = new Kernel68(current);
  return last.next = current;
}

boolean Kernel68_check(int x)
{
  return x % 2 > 0;
}

void Kernel68_slide68(int random1, int random2)
{
  Kernel68 h = Kernel68_create(random1);
  Kernel68 p = h;
  Kernel68 c = p.next;
  while (c != h) {
    Kernel68 o = c;
    c = c.next;
    if (Kernel68_check(random2)) {
      p.next = c;
      o = null;
    } else {
      p = o;
    }
    random2 = random2 / 2;
  }
}

void Kernel68_slide88(int random1, int random2)
{
  Kernel68 h = Kernel68_create(random1);
  Kernel68 p = h;
  Kernel68 c = p.next;
  while (c != h) {
    Kernel68 o = c;
    if (Kernel68_check(random2)) {
      Kernel68 e = o.next;
      p.next = e;
      o = null;
      c = o;
    } else {
      p = o;
    }
    c = c.next;
    random2 = random2 / 2;
  }
}

void Kernel68_slide93(int random1, int random2)
{
  Kernel68 h = Kernel68_create(random1);
  Kernel68 p = h;
  Kernel68 c = p.next;
  while (c != h) {
    Kernel68 o = c;
    if (Kernel68_check(random2)) {
      Kernel68 e = o.next;
      p.next = e;
      o.next = o;
    } else {
      p = o;
    }
    c = c.next;
    random2 = random2 / 2;
  }
}

void Kernel68_slide95(int random1, int random2)
{
  Kernel68 h = Kernel68_create(random1);
  Kernel68 p = h;
  Kernel68 c = p.next;
  while (c != h) {
    Kernel68 o = c;
    c = c.next;
    if (Kernel68_check(random2)) {
      Kernel68 e = o.next;
      p.next = e;
      o.next = o;
    } else {
      p = o;
    }
    random2 = random2 / 2;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;