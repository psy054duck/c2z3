#include <stdbool.h>
extern int unknown1(void);
extern int unknown2(void);
extern void assert(bool);

int main()
{
	unsigned int x = 0;
	unsigned int y = 0;
	unsigned int z=5000000;
	while(x<z){	
		x += 2;
		y += 4;
	}
	// assert(x == z);
	assert(y == 2*z);
	return 0;
}