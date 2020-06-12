//Ex.11

extern unsigned char getInitialPosition();
extern int getNextValue();

int main() {
   unsigned char pos = getInitialPosition();
   int arr[256];
   while(1) {
       arr[pos] = getNextValue();
       arr[pos + 1] = getNextValue();
       pos += 2;
   }
   return 0;
}
