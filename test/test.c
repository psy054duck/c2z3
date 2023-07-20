#include <stdbool.h>
extern int unknown1(void);
extern int unknown2(void);
extern void assert(bool);

int main()
{
	unsigned int x = 0;
	unsigned int z=5000000;
	while(x<z){	
		x += 2;
	}
	assert(x == z);
	return 0;
}